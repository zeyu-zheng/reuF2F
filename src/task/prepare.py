"""Compiling the trusted checkout into the dataset people consume.

The dataset reads the checkout and nothing else, so what gets published is always
what the repo says. The checkout is checked first: publishing from a malformed
tree is how a broken instance reaches a leaderboard.
"""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

from reuf2f.harness.constants import INSTRUCTION
from reuf2f.image_builder.image_spec import get_shared_image
from reuf2f.task.checks import check_task_repo, errors
from reuf2f.task.lean import answer_source, export_types
from reuf2f.task.repo import LEAN_DIR, load_task_repo


class CheckFailed(RuntimeError):
    """The repo is not well formed, so nothing was published."""


def guard(repo_path: str | Path) -> None:
    """Refuse to go further if the repo has errors."""
    blocking = errors(check_task_repo(repo_path))
    if blocking:
        listed = "\n".join(f"  {p}" for p in blocking[:20])
        more = f"\n  ... and {len(blocking) - 20} more" if len(blocking) > 20 else ""
        raise CheckFailed(f"{len(blocking)} problem(s) in {repo_path}:\n{listed}{more}")


def compile_dataset(
    repo_path: str | Path, instance_ids: list[str] | None = None
) -> list[dict]:
    """One flat record per open problem; exporting the refutations runs Lean."""
    repo = Path(repo_path)
    guard(repo)
    problems = load_task_repo(repo, instance_ids)
    version = (repo / LEAN_DIR / "lean-toolchain").read_text().strip().rsplit(":", 1)[-1]
    image = get_shared_image(repo).name
    with tempfile.TemporaryDirectory(prefix="reuf2f-export-") as temporary:
        types = export_types(problems, Path(temporary), repo)
    records = []
    for problem in problems:
        relative = problem["module"].replace(".", "/") + ".lean"
        challenge = answer_source(
            (repo / LEAN_DIR / relative).read_text(),
            relative,
            problem["declaration"],
            types[problem["declaration"]],
        )
        records.append(
            {
                "instance_id": problem["id"],
                "declaration": problem["declaration"],
                "program": problem["program"],
                "source_url": problem["source_url"],
                "title": problem["title"],
                "version": version,
                "year": problem["year"],
                "area": problem["area"],
                "source_label": problem["source_label"],
                "problem_statement": INSTRUCTION.format(
                    source_file=problem["id"] + ".lean",
                    declaration=problem["declaration"],
                ),
                "challenge": challenge.decode(),
                "image": image,
                "log_parser": "parse_log_comparator",
                "eval_type": "proof_or_refutation",
            }
        )
    return records


def write_dataset(
    repo_path: str | Path, out_dir: str | Path, instance_ids: list[str] | None = None
) -> Path:
    """Write the dataset as test.jsonl, the file `reuf2f eval` reads."""
    records = compile_dataset(repo_path, instance_ids)
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    path = out / "test.jsonl"
    path.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in records))
    return path
