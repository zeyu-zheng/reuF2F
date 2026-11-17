"""Is the checkout well formed?

The checkout is the source of truth, so a malformed item is a broken instance later:
an item missing from its root is never built, a second target or stray sorry makes
the challenge ambiguous, and metadata that disagrees with a root publishes the wrong
module. This is a structural scan; Lean remains the syntax and type authority, and
check.lean, shipped beside this file, asks the kernel about the built checkout.
"""

from __future__ import annotations

import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

from reuf2f.task.repo import LEAN_DIR, PROBLEM_MANIFEST, ROOT

# found through the package, not the checkout, so an installed copy carries it
LEAN_CHECK = Path(__file__).with_name("check.lean")

# Lean identifiers may use apostrophes, punctuation suffixes, letter-like
# Unicode characters, and escaped components containing spaces or dots.
_LETTERLIKE = r"\u2100-\u214f\U0001d49c-\U0001d59f"
_SUBSCRIPT = r"\u2080-\u209c\u1d62-\u1d6a\u2c7c"
_IDENT_PART = rf"(?:\u00ab[^\u00bb]*\u00bb|[^\W\d][\w\'!?{_LETTERLIKE}{_SUBSCRIPT}]*|[{_LETTERLIKE}][\w\'!?{_LETTERLIKE}{_SUBSCRIPT}]*)"
_IDENTIFIER = rf"{_IDENT_PART}(?:\.{_IDENT_PART})*"
_IDENT_RE = re.compile(_IDENTIFIER)
_PART_RE = re.compile(_IDENT_PART)


@dataclass
class Problem:
    where: str
    message: str
    # errors stop a publish; warnings are reported and do not
    severity: str = "error"

    def __str__(self) -> str:
        return f"{self.severity}: {self.where}: {self.message}"


def errors(problems: list[Problem]) -> list[Problem]:
    return [p for p in problems if p.severity == "error"]


def lean_code(text):
    """Mask strings and nested comments, preserving character/line positions."""
    out = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i : i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i : i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif quoted:
            if text[i] == "\\":
                out[i : i + 2] = "  "
                i += 2
            else:
                if text[i] == '"':
                    quoted = False
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text[i] == "\u00ab":
            end = text.find("\u00bb", i + 1)
            if end < 0:
                raise ValueError("Unterminated Lean identifier escape")
            i = end + 1
        elif text.startswith("/-", i):
            out[i : i + 2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
        elif text[i] == "r" and (raw := re.match(r'r(#+)"', text[i:])):
            delimiter = '"' + raw.group(1)
            end = text.find(delimiter, i + raw.end())
            if end < 0:
                raise ValueError("Unterminated Lean raw string")
            end += len(delimiter)
            for j in range(i, end):
                if text[j] != "\n":
                    out[j] = " "
            i = end
        elif text[i] == "'" and (
            char := re.match(
                r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'", text[i:]
            )
        ):
            end = i + char.end()
            out[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            out[i] = " "
            quoted = True
            i += 1
        else:
            i += 1
    if depth or quoted:
        raise ValueError("Unterminated Lean block comment or string")
    return "".join(out)


def root_imports(text):
    """src/task/check.lean reads roots line by line, so one plain import per line."""
    modules = []
    for line in text.splitlines():
        if not line.strip():
            continue
        if not re.fullmatch(r"import [\w.]+", line):
            raise ValueError(
                "Root must use one plain import per line (no comments or tabs)"
            )
        modules.append(line[7:])
    return modules


def target_scan(code):
    """The target theorems, the sorry count, and what is wrong with them.

    The target theorem is the one whose proof is `by sorry`; the manifest names it.
    """
    messages = []
    sorries = list(re.finditer(r"\bsorry\b", code))
    # each sorry belongs to the theorem declared before it
    targets = [
        names[-1]
        for sorry in sorries
        if (names := re.findall(r"theorem\s+([^\s(:{]+)", code[: sorry.start()]))
    ]
    if len(sorries) != len(targets):
        messages.append(f"{len(sorries)} sorries for {len(targets)} target theorems")
    if len(re.findall(r":=\s*by\s+sorry\b", code)) != len(targets):
        messages.append("target theorems must use exact by sorry bodies")
    # the target is the last declaration, followed only by section/namespace ends
    if targets and len(sorries) == 1:
        tail = code[sorries[0].end() :]
        if not re.fullmatch(rf"\s*(?:end(?:\s+{_IDENTIFIER})?\s*)*", tail):
            messages.append("unexpected code after target sorry")
    return targets, len(sorries), messages


def check_item_scopes(code):
    """Keep an item in one namespace, with explicit, meaningful inner scopes.

    One file-wide `noncomputable section` is allowed before the namespace.
    Named sections may isolate local instances/variables; nested namespaces
    may organize a source object's API.
    """
    messages, stack, namespaces = [], [], set()
    outer_namespaces, noncomputable_sections = 0, 0
    # Skip identifier escapes as indivisible tokens; a keyword inside an
    # escaped name must not open a scope. Names may continue on an indented
    # later line, matching Lean's checkColGt command parser convention.
    scope_token = re.compile(
        r"\u00ab[^\u00bb]*\u00bb|^[ \t]*(?P<kind>noncomputable\s+section|namespace|section|end)(?=\s|$)",
        re.M,
    )
    reserved = {
        "namespace",
        "section",
        "noncomputable",
        "end",
        "def",
        "abbrev",
        "theorem",
        "lemma",
        "instance",
        "structure",
        "class",
        "inductive",
        "open",
        "attribute",
        "variable",
        "universe",
        "set_option",
        "import",
    }
    cursor = 0
    while match := scope_token.search(code, cursor):
        cursor = match.end()
        if match.group("kind") is None:
            continue
        kind = " ".join(match.group("kind").split())
        column = match.start("kind") - code.rfind("\n", 0, match.start("kind")) - 1
        name_start = cursor
        while name_start < len(code) and code[name_start].isspace():
            name_start += 1
        later_line = "\n" in code[cursor:name_start]
        name_column = name_start - code.rfind("\n", 0, name_start) - 1
        name_match = _IDENT_RE.match(code, name_start)
        name = None
        if name_match and (not later_line or name_column > column):
            raw_name = name_match.group()
            if raw_name not in reserved:
                # Tuple components distinguish X.Y from the one-part name
                # escaped as <X.Y>, while X and an escaped X are equal names.
                name = tuple(
                    p[1:-1] if p.startswith("\u00ab") else p
                    for p in _PART_RE.findall(raw_name)
                )
                cursor = name_match.end()
        if kind != "end":
            if kind == "namespace":
                if name is None:
                    messages.append("namespace must be named")
                    continue
                parents = tuple(
                    part for k, n in stack if k == "namespace" for part in n
                )
                full_name = parents + name
                if full_name in namespaces:
                    messages.append(f"reopened namespace {full_name}")
                namespaces.add(full_name)
                if not parents:
                    outer_namespaces += 1
            elif kind == "noncomputable section":
                noncomputable_sections += 1
                if stack or outer_namespaces or name or noncomputable_sections > 1:
                    messages.append("use at most one file-wide noncomputable section")
            elif name is None:
                messages.append("anonymous section; remove it or name its real scope")
            stack.append((kind, name))
        else:
            if name is None:
                messages.append("anonymous end; close the intended named scope")
            if not stack:
                messages.append("unmatched end")
                continue
            _, expected = stack.pop()
            if name != expected:
                messages.append(f"end {name} does not match scope {expected}")
    if outer_namespaces != 1:
        messages.append(f"expected one item namespace, found {outer_namespaces}")
    if stack not in ([], [("noncomputable section", None)]):
        messages.append("unclosed named scope")
    return messages


def _check_item(path: Path, where: str) -> list[Problem]:
    code = lean_code(path.read_text())
    messages = check_item_scopes(code)
    targets, sorries, target_messages = target_scan(code)
    messages += target_messages
    for forbidden in (
        r"\b(?:axiom|constant|opaque|admit|sorryAx)\b",
        r":\s*Prop\s*:=\s*True\b",
        r"^\s*(?:unsafe|partial)\s+",
    ):
        if re.search(forbidden, code, re.M):
            messages.append(f"forbidden pattern {forbidden}")
    if len(targets) != 1 or sorries != 1:
        messages.append(f"expected exactly one target theorem, found {targets}")
    return [Problem(where, message) for message in messages]


def _check_environment(repo_path: Path) -> list[Problem]:
    """Run the kernel checks on a built checkout, reporting what Lean prints."""
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(LEAN_CHECK)],
            cwd=repo_path / LEAN_DIR,
            capture_output=True,
            text=True,
        )
    except OSError as e:
        return [Problem(LEAN_CHECK.name, f"cannot run the Lean checks: {e}")]
    if result.returncode == 0:
        return []
    output = (result.stdout + result.stderr).strip()
    return [
        Problem(
            LEAN_CHECK.name,
            f"the Lean checks failed (run `lake build` in lean/ first): {output}",
        )
    ]


def check_task_repo(repo_path: str | Path) -> list[Problem]:
    """Every problem found, in reporting order."""
    repo_path = Path(repo_path)
    lean_path = repo_path / LEAN_DIR
    problems: list[Problem] = []
    metadata = [
        json.loads(line)
        for line in (repo_path / PROBLEM_MANIFEST).read_text().splitlines()
        if line.strip()
    ]
    by_key = {row["id"]: row for row in metadata}
    if len(by_key) != len(metadata):
        problems.append(Problem(PROBLEM_MANIFEST, "duplicate keys"))
    membership = set()
    try:
        modules = root_imports((lean_path / f"{ROOT}.lean").read_text())
    except ValueError as e:
        problems.append(Problem(f"{ROOT}.lean", str(e)))
        modules = []
    if len(modules) != len(set(modules)):
        problems.append(Problem(f"{ROOT}.lean", "duplicate imports"))
    for module in modules:
        if not re.fullmatch(ROOT + r"\.[^.]+", module):
            problems.append(Problem(f"{ROOT}.lean", f"unexpected import {module}"))
            continue
        key = module.split(".")[1]
        if key in membership:
            problems.append(Problem(key, "imported more than once"))
        membership.add(key)
        row = by_key.get(key, {})
        if row.get("module") != module:
            problems.append(Problem(key, "root/module metadata mismatch"))
        item_file = lean_path / ROOT / f"{key}.lean"
        if not item_file.is_file():
            problems.append(Problem(key, f"missing {ROOT}/{key}.lean"))
            continue
        problems.extend(_check_item(item_file, f"{ROOT}/{key}.lean"))
    # an item file the root does not import is never built
    disk_keys = {f.stem for f in (lean_path / ROOT).glob("*.lean")}
    problems.extend(
        Problem(f"{ROOT}/{key}.lean", f"not imported by {ROOT}.lean")
        for key in sorted(disk_keys - membership)
    )
    problems.extend(
        Problem(row["id"], "listed in metadata but not imported")
        for row in metadata
        if row["id"] not in membership
    )
    # the kernel checks need a built tree and repeat the scan's questions, so a
    # tree the scan already refuses is not handed to Lean
    if not errors(problems):
        problems.extend(_check_environment(repo_path))
    return problems
