"""The problem manifest names exactly the accepted items, one target each.

`reuf2f dataset build` compiles the dataset from it, so an item it misses or
misnames silently leaves or corrupts the benchmark.
"""

import copy
from pathlib import Path

import pytest

from reuf2f.task import repo
from reuf2f.task.checks import root_imports

ROOT = Path(__file__).resolve().parents[1]


def _problems():
    return copy.deepcopy(repo.load_task_repo(ROOT))


def test_the_manifest_lists_the_items_in_root_order():
    imports = root_imports((ROOT / "lean" / "reuF2F.lean").read_text())
    assert [p["module"] for p in _problems()] == imports


def test_a_problem_id_is_its_file_stem():
    problems = _problems()
    problems[0]["id"] = "legacy-hyphenated-id"
    with pytest.raises(ValueError, match="not its reuF2F file stem"):
        repo.validate_problem_manifest(problems)


def test_a_year_must_be_an_integer():
    problems = _problems()
    problems[0]["year"] = str(problems[0]["year"])
    with pytest.raises(ValueError, match="mistyped or empty field"):
        repo.validate_problem_manifest(problems)


def test_a_duplicate_id_is_refused():
    problems = _problems()
    problems.append(problems[0])
    with pytest.raises(ValueError, match="duplicate problem id"):
        repo.validate_problem_manifest(problems)


def test_a_missing_field_is_refused():
    problems = _problems()
    del problems[0]["title"]
    with pytest.raises(ValueError, match="invalid manifest fields"):
        repo.validate_problem_manifest(problems)
