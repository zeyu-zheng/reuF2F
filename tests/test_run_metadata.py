"""A run records what it graded against (#report).

Re-grading needs the challenge and declaration, which live in the dataset rather
than in the run's logs. Without a record, `reuf2f report` has to be told the
dataset again, and grades against the wrong one silently if told wrongly.
"""

import json

import pytest

from reuf2f.harness import run_evaluation


@pytest.fixture
def run_dir(tmp_path, monkeypatch):
    monkeypatch.setattr(run_evaluation, "RUN_EVALUATION_LOG_DIR", tmp_path)
    return tmp_path


def test_metadata_round_trips(run_dir):
    run_evaluation.write_run_metadata("my-run", "/data/test.jsonl", "/repo", {})
    got = run_evaluation.read_run_metadata("my-run")
    assert got["dataset"] == "/data/test.jsonl"
    assert got["repo"] == "/repo"
    assert got["created_at"]


def test_the_predictions_are_recorded_for_report(run_dir):
    pred = {"instance_id": "one", "model_name_or_path": "m", "model_patch": ""}
    run_evaluation.write_run_metadata("my-run", "ds", "/repo", {"one": pred})
    assert run_evaluation.get_run_predictions("my-run") == [pred]


def test_a_run_without_metadata_reads_as_none(run_dir):
    (run_dir / "old-run").mkdir()
    assert run_evaluation.read_run_metadata("old-run") is None


def test_metadata_is_written_beside_the_instance_logs(run_dir):
    path = run_evaluation.write_run_metadata("my-run", "ds", "/repo", {})
    assert path == run_dir / "my-run" / "run.json"
    assert json.loads(path.read_text())["dataset"] == "ds"
