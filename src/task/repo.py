"""Trusted Lean checkout, problem manifest and image-recipe discovery."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

# Shared image recipes, not mathematical tasks.
TASKS_SUBDIR = "tags"
TASK_FILE = "task.yaml"
# The Lean project lives in this checkout subdirectory; its root module and
# item directory share the library name.
LEAN_DIR = "lean"
# one row per problem, kept beside the Lean files it describes
PROBLEM_MANIFEST = f"{LEAN_DIR}/metadata.jsonl"
ROOT = "reuF2F"
REQUIRED_PROBLEM_FIELDS = {
    "id",
    "module",
    "declaration",
    "source_label",
    "title",
    "program",
    "year",
    "area",
    "source_url",
}


def tasks_root(repo_path: str | Path) -> Path:
    root = Path(repo_path) / TASKS_SUBDIR
    if not root.is_dir():
        raise FileNotFoundError(f"{repo_path} has no {TASKS_SUBDIR}/ directory")
    return root


def task_dirs(repo_path: str | Path) -> list[Path]:
    return sorted(
        d for d in tasks_root(repo_path).iterdir() if (d / TASK_FILE).exists()
    )


def validate_problem_manifest(problems: list[Any]) -> None:
    seen_ids: set[str] = set()
    seen_declarations: set[str] = set()
    for index, problem in enumerate(problems):
        if not isinstance(problem, dict) or set(problem) != REQUIRED_PROBLEM_FIELDS:
            raise ValueError(f"problem {index} has invalid manifest fields")
        if any(
            not isinstance(value, int if key == "year" else str) or not value
            for key, value in problem.items()
        ):
            raise ValueError(f"problem {index} has a mistyped or empty field")
        problem_id = problem["id"]
        if not re.fullmatch(r"[a-z0-9]+", problem_id) or problem[
            "module"
        ] != f"{ROOT}.{problem_id}":
            raise ValueError(f"problem id is not its {ROOT} file stem: {problem_id}")
        if problem_id in seen_ids:
            raise ValueError(f"duplicate problem id in manifest: {problem_id}")
        seen_ids.add(problem_id)
        declaration = problem["declaration"]
        if declaration in seen_declarations:
            raise ValueError(f"duplicate declaration in manifest: {declaration}")
        seen_declarations.add(declaration)


def load_task_repo(
    repo_path: str | Path, instance_ids: list[str] | None = None
) -> list[dict[str, str]]:
    """Every problem in the checkout, or just the ones asked for.

    Unknown ids are an error rather than a silent omission: a typo should not
    quietly shrink the run.
    """
    path = Path(repo_path) / PROBLEM_MANIFEST
    problems = [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if not problems:
        raise ValueError(f"invalid problem manifest: {path}")
    validate_problem_manifest(problems)
    if not instance_ids:
        return problems
    instance_ids = set(instance_ids)
    problem_ids = {problem["id"] for problem in problems}
    if instance_ids - problem_ids:
        raise ValueError(
            (
                "Some instance IDs not found in the checkout!"
                f"\nMissing IDs:\n{' '.join(instance_ids - problem_ids)}"
            )
        )
    return [problem for problem in problems if problem["id"] in instance_ids]


def resolve_repo(path: str | Path | None = None) -> Path:
    """Resolve an explicit checkout, or search current-directory ancestors only.

    Installed package paths are not benchmark data. In particular, no fallback
    walks out of site-packages or guesses an editable install's source checkout.
    """
    start = (
        Path(path).expanduser().resolve() if path is not None else Path.cwd().resolve()
    )
    candidates = (start,) if path is not None else (start, *start.parents)
    for candidate in candidates:
        if (candidate / PROBLEM_MANIFEST).is_file() and all(
            (candidate / LEAN_DIR / name).is_file()
            for name in (
                "lakefile.lean",
                "lake-manifest.json",
                "lean-toolchain",
                f"{ROOT}.lean",
            )
        ):
            return candidate
    raise ValueError(
        "Lean benchmark checkout not found; pass --repo /path/to/ReuF2F"
    )
