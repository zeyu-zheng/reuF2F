"""Lean-specific task export and workspace layout."""

from __future__ import annotations

import json
import tomllib
from pathlib import Path
from typing import Any

from reuf2f.task.checks import lean_code, target_scan
from reuf2f.task.repo import LEAN_DIR
from reuf2f.utils import checked, json_bytes


def answer_source(
    source: str, relative: str, declaration: str, exported: dict[str, Any]
) -> bytes:
    """Preserve the original statement and scopes; append its full-type negation.

    `type_of%` elaborates to the target's own type, so the negation is exact and
    readable without printing it, and does not refer to the admitted target.
    """
    code = lean_code(source)
    targets, _, errors = target_scan(code)
    if errors or len(targets) != 1:
        raise ValueError(f"cannot export noncanonical item {relative}: {errors}")
    levels = exported["universes"]
    universes = ".{" + ", ".join(levels) + "}" if levels else ""
    return (
        source.rstrip()
        + f"\n\ntheorem {declaration}_neg{universes} : "
        + f"¬ type_of% @{declaration}{universes} := by\n  sorry\n"
    ).encode()


def workspace_config(
    root: Path,
    roots: tuple[str, ...],
) -> dict[str, bytes]:
    """The image project's config, with its `Main` root replaced by the task's."""
    toolchain = (root / LEAN_DIR / "lean-toolchain").read_bytes()
    manifest = json.loads((root / LEAN_DIR / "lake-manifest.json").read_bytes())
    manifest["name"] = "project"
    version = toolchain.decode().strip().rsplit(":", 1)[-1]
    recipe = root / "docker/tags" / version
    if (recipe / "lean-toolchain").read_bytes() != toolchain:
        raise ValueError("image recipe toolchain differs from the benchmark")
    text = (recipe / "lakefile.toml").read_text()
    if len(roots) != 1 or text.count('roots = ["Main"]') != 1:
        raise ValueError("expected one image Project root named Main")
    lakefile = text.replace('roots = ["Main"]', "roots = " + json.dumps(list(roots)))
    for dep in tomllib.loads(lakefile).get("require", []):
        locked = next(
            (p for p in manifest["packages"] if p["name"] == dep["name"]), None
        )
        if locked is None or (dep.get("git"), dep.get("rev")) != (
            locked.get("url"),
            locked.get("inputRev"),
        ):
            raise ValueError("image recipe dependency differs from the benchmark lock")
    return {
        "lakefile.toml": lakefile.encode(),
        "lake-manifest.json": json_bytes(manifest),
        "lean-toolchain": toolchain,
        ".gitignore": b".lake/\n*.olean\n*.ilean\n*.trace\n",
    }


def trusted_build(problems: list[dict[str, str]], repo: Path) -> None:
    modules = ["Export", *(p["module"] for p in problems)]
    checked(["lake", "build", *modules], repo / LEAN_DIR, timeout=600)


def export_types(
    problems: list[dict[str, str]], scratch: Path, repo: Path
) -> dict[str, Any]:
    trusted_build(problems, repo)
    manifest, output = scratch / "manifest.json", scratch / "types.json"
    manifest.write_bytes(json_bytes(problems))
    script = scratch / "Export.lean"
    script.write_text(
        "\n".join(f"import {p['module']}" for p in problems)
        + "\nimport Export\n\n"
        + f"#reuf2f_export_types {json.dumps(str(manifest))} to {json.dumps(str(output))}\n"
    )
    checked(["lake", "env", "lean", str(script)], repo / LEAN_DIR, timeout=1800)
    return {row["declaration"]: row for row in json.loads(output.read_bytes())}
