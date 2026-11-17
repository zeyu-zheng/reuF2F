"""Preparing the dataset reads the checkout, and refuses a malformed one.

The checkout is the source of truth for the dataset, so anything wrong in the tree
becomes a broken instance on a leaderboard. Compiling therefore runs the checks
first rather than trusting the caller to have run them.
"""

import json
from pathlib import Path

import pytest

from reuf2f.task import checks, lean, prepare, repo
from reuf2f.task.checks import check_task_repo

ROOT = Path(__file__).resolve().parents[1]
FIELDS = [
    "instance_id",
    "declaration",
    "program",
    "source_url",
    "title",
    "version",
    "year",
    "area",
    "source_label",
    "problem_statement",
    "challenge",
    "image",
    "log_parser",
    "eval_type",
]
NEGATION = {"universes": []}


def _source(body="theorem target : True := by sorry\n"):
    return f"import Mathlib\nnamespace Example\n{body}end Example\n"


@pytest.fixture(autouse=True)
def built_environment(monkeypatch):
    """Stand in for the kernel checks, which need a `lake build`."""
    monkeypatch.setattr(checks, "_check_environment", lambda _: [])


def test_a_well_formed_repo_has_no_problems():
    assert check_task_repo(ROOT) == []


def test_compile_writes_one_record_per_problem(tmp_path, monkeypatch):
    problem = repo.load_task_repo(ROOT)[0]
    monkeypatch.setattr(
        prepare, "export_types", lambda *_: {problem["declaration"]: NEGATION}
    )
    path = prepare.write_dataset(ROOT, tmp_path, [problem["id"]])
    [record] = [json.loads(line) for line in path.read_text().splitlines()]
    assert path == tmp_path / "test.jsonl"
    assert list(record) == FIELDS
    assert record["instance_id"] == problem["id"]


def test_the_challenge_appends_the_negation():
    text = lean.answer_source(_source(), "reuF2F/example.lean", "Example.target", NEGATION)
    assert "theorem target : True := by sorry" in text.decode()
    assert "theorem Example.target_neg : ¬ type_of% @Example.target := by\n  sorry" in text.decode()


def test_the_negation_names_its_universes():
    exported = {"universes": ["u0"]}
    text = lean.answer_source(_source(), "reuF2F/example.lean", "Example.target", exported)
    assert "theorem Example.target_neg.{u0} : ¬ type_of% @Example.target.{u0}" in text.decode()


def test_every_problem_exports():
    for problem in repo.load_task_repo(ROOT):
        relative = problem["module"].replace(".", "/") + ".lean"
        text = lean.answer_source(
            (ROOT / "lean" / relative).read_text(), relative, problem["declaration"], NEGATION
        ).decode()
        assert text.startswith((ROOT / "lean" / relative).read_text().rstrip())


@pytest.mark.parametrize(
    "body",
    [
        "theorem target : True := by sorry\ntheorem extra : False := by sorry\n",
        "lemma helper : True := by sorry\ntheorem target : True := by sorry\n",
    ],
    ids=["second-target", "setup-sorry"],
)
def test_a_second_target_or_stray_sorry_is_refused(body):
    with pytest.raises(ValueError):
        lean.answer_source(_source(body), "reuF2F/example.lean", "Example.target", NEGATION)
