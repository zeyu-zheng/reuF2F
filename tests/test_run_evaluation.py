"""The shared image is set up the way an instance image would be.

The challenge and image config are committed in /testbed, and the submitted diff
is applied there with `git apply`, so a patch adds files exactly as it would to a
per-instance repository.
"""

import json
from pathlib import Path

import pytest

from docker_fixtures import git, init_baseline, replay_patch
from reuf2f.harness.utils import load_reuf2f_dataset
from reuf2f.task.lean import workspace_config

ROOT = Path(__file__).resolve().parents[1]
CHALLENGE = b"theorem Example.target : True := by sorry\n"


def test_a_patch_edits_the_challenge_and_adds_helpers(tmp_path):
    baseline = {**workspace_config(ROOT, ("one",)), "one.lean": CHALLENGE}
    init_baseline(tmp_path, baseline)
    (tmp_path / "one.lean").write_bytes(CHALLENGE.replace(b"sorry", b"trivial"))
    (tmp_path / "Helpers.lean").write_bytes(b"import Mathlib\n")
    git(tmp_path, "add", "-A")
    patch = git(tmp_path, "diff", "--cached", "HEAD").decode()
    result = replay_patch(baseline, patch)
    assert result["one.lean"] == CHALLENGE.replace(b"sorry", b"trivial")
    assert result["Helpers.lean"] == b"import Mathlib\n"


def test_unknown_instance_id_is_an_error(tmp_path):
    path = str(tmp_path / "test.jsonl")
    Path(path).write_text(json.dumps({"instance_id": "one"}) + "\n")
    assert load_reuf2f_dataset(path, ["one"]) == [{"instance_id": "one"}]
    with pytest.raises(ValueError, match="Some instance IDs not found in dataset"):
        load_reuf2f_dataset(path, ["two"])
