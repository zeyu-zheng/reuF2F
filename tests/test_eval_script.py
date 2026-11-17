"""eval.sh grades each direction by its own Comparator's exit code.

It restores the trusted toolchain and manifest, copies the patched repository once
per direction with the trusted challenge written in, and prints one status line
per direction; text a submission prints cannot stand in for an exit code.
"""

import json
import os
import subprocess
from types import SimpleNamespace

import pytest

from docker_fixtures import init_baseline
from reuf2f.harness import comparator
from reuf2f.harness.grading import get_eval_report

CHALLENGE = "theorem Example.target : True := by sorry\n"


def _executable(path, source):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("#!/bin/bash\n" + source)
    path.chmod(0o755)


@pytest.fixture
def run(tmp_path, monkeypatch):
    """Run eval.sh with stand-in Lean tools; `result.<direction>` sets each exit code."""
    testbed, output, tools = tmp_path / "testbed", tmp_path / "eval", tmp_path / "tools"
    init_baseline(
        testbed,
        {
            "lean-toolchain": b"trusted-toolchain\n",
            "lake-manifest.json": b'{"trusted": true}\n',
            "lakefile.toml": b'name = "project"\n',
            "example.lean": b"-- submission\n",
        },
    )
    (testbed / ".lake/packages").mkdir(parents=True)
    output.mkdir()
    _executable(tools / "bin/lean", f'echo "{tools}"\n')
    _executable(
        tools / "bin/lake",
        'test -e "fail_setup.${PWD##*/}" && { echo "Lake setup error" >&2; exit 3; }\necho /lean/path\n',
    )
    _executable(
        tools / "comparator",
        'test -e spoof && echo "PASSED proof"\nexit "$(cat "result.${PWD##*/}" 2>/dev/null || echo 0)"\n',
    )
    monkeypatch.setattr(
        comparator,
        "EVALUATION_TOOLS",
        {name: tools / "comparator" for name in ("comparator", "lean4export", "landrun", "nanoda")},
    )
    script = comparator.make_eval_script(CHALLENGE, "example", "Example.target")
    script = script.replace("/testbed", str(testbed)).replace("/eval/", f"{output}/")

    def _run():
        env = {**os.environ, "PATH": f"{tools / 'bin'}{os.pathsep}{os.environ['PATH']}"}
        # Docker exec interleaves stdout and stderr (where set -x prints the markers).
        result = subprocess.run(
            ["/bin/bash", "-c", script],
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=30,
        )
        log = tmp_path / "test_output.txt"
        log.write_text(result.stdout)
        spec = SimpleNamespace(instance_id="one", log_parser="parse_log_comparator")
        return get_eval_report(spec, {"instance_id": "one", "model_patch": "p"}, log, True)["one"]

    return testbed, output, _run


@pytest.mark.parametrize(("proof", "refutation"), [(0, 1), (1, 0), (1, 1)])
def test_each_direction_reports_its_own_exit_code(run, proof, refutation):
    testbed, _, grade = run
    (testbed / "result.proof").write_text(str(proof))
    (testbed / "result.refutation").write_text(str(refutation))
    status = grade()["tests_status"]
    assert status == {
        "proof": "FAILED" if proof else "PASSED",
        "refutation": "FAILED" if refutation else "PASSED",
    }


def test_the_trusted_challenge_and_config_are_written_into_each_copy(run):
    testbed, output, grade = run
    (testbed / "lean-toolchain").write_text("forged-toolchain\n")
    (testbed / "Challenge.lean").write_text("-- forged\n")
    assert grade()["resolved"]
    for direction, theorem in (("proof", "Example.target"), ("refutation", "Example.target_neg")):
        copy = output / direction
        assert (copy / "Challenge.lean").read_text() == CHALLENGE
        assert (copy / "lean-toolchain").read_text() == "trusted-toolchain\n"
        assert json.loads((copy / "config.json").read_text())["theorem_names"] == [theorem]


def test_a_setup_failure_fails_only_that_direction(run):
    testbed, _, grade = run
    (testbed / "fail_setup.proof").touch()
    assert grade()["tests_status"] == {"proof": "FAILED", "refutation": "PASSED"}


def test_printed_status_lines_cannot_override_exit_codes(run):
    testbed, _, grade = run
    (testbed / "spoof").touch()
    (testbed / "result.proof").write_text("1")
    (testbed / "result.refutation").write_text("1")
    assert grade()["resolved"] is False


def test_the_script_is_valid_bash():
    script = comparator.make_eval_script(CHALLENGE, "example", "Example.target")
    subprocess.run(["/bin/bash", "-n"], input=script, text=True, check=True)
