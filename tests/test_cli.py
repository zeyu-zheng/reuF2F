import json
import subprocess
import sys
from pathlib import Path

import docker
import pytest

from docker_fixtures import git, init_baseline
from reuf2f.image_builder.image_spec import get_shared_image

ROOT = Path(__file__).resolve().parents[1]
REUF2F = str(Path(sys.executable).with_name("reuf2f"))
CHALLENGE = (
    "import Mathlib\n\n"
    "theorem SmokeTest.target : ∀ n : ℕ, n + 1 ≤ 2 * n := by sorry\n\n"
    "theorem SmokeTest.target_neg : ¬ type_of% @SmokeTest.target := by\n  sorry\n"
)
REFUTATION = CHALLENGE.replace("by\n  sorry\n", "fun h => absurd (h 0) (by decide)\n")


def test_smoke_test():
    cmd = [REUF2F, "--help"]
    result = subprocess.run(cmd, capture_output=True)
    print(result.stdout)
    print(result.stderr)
    assert result.returncode == 0


def test_one_instance(tmp_path):
    try:
        image = get_shared_image(ROOT).name
        docker.from_env(timeout=5).images.get(image)
    except (docker.errors.DockerException, docker.errors.ImageNotFound):
        pytest.skip("needs the Docker daemon and the shared Lean image")
    record = {
        "instance_id": "smoke",
        "declaration": "SmokeTest.target",
        "challenge": CHALLENGE,
        "image": image,
        "log_parser": "parse_log_comparator",
        "eval_type": "proof_or_refutation",
    }
    (tmp_path / "test.jsonl").write_text(json.dumps(record) + "\n")
    solver = tmp_path / "solver"
    init_baseline(solver, {"smoke.lean": CHALLENGE.encode()})
    (solver / "smoke.lean").write_text(REFUTATION)
    patch = git(solver, "diff").decode()
    pred = {"instance_id": "smoke", "model_name_or_path": "smoke", "model_patch": patch}
    (tmp_path / "preds.jsonl").write_text(json.dumps(pred) + "\n")

    cmd = [REUF2F, "--repo", str(ROOT), "eval", "test.jsonl", "-p", "preds.jsonl", "--run-id", "validate-refutation"]
    result = subprocess.run(cmd, capture_output=True, cwd=tmp_path)
    print(result.stdout)
    print(result.stderr)
    assert result.returncode == 0
    report = json.loads((tmp_path / "logs/evaluation/validate-refutation/results.json").read_text())
    assert report["resolved_ids"] == ["smoke"]
