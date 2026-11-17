"""A task is resolved when either the proof or the refutation passes.

Each direction's verdict is the status line eval.sh derives from Comparator's
exit code, read between the last pair of output markers, so text a submission
prints cannot grade itself.
"""

from types import SimpleNamespace

from reuf2f.harness.constants import END_TEST_OUTPUT, START_TEST_OUTPUT
from reuf2f.harness.grading import get_eval_report

SPEC = SimpleNamespace(instance_id="one", log_parser="parse_log_comparator")


def _log(*lines):
    return "\n".join([f"+ : '{START_TEST_OUTPUT}'", *lines, f"+ : '{END_TEST_OUTPUT}'"])


def _grade(tmp_path, content, patch="patch"):
    path = tmp_path / "test_output.txt"
    path.write_text(content)
    pred = {"instance_id": "one", "model_patch": patch}
    return get_eval_report(SPEC, pred, path, include_tests_status=True)["one"]


def test_a_passing_proof_resolves(tmp_path):
    report = _grade(tmp_path, _log("PASSED proof", "FAILED refutation"))
    assert report["resolved"] is True
    assert report["tests_status"] == {"proof": "PASSED", "refutation": "FAILED"}


def test_a_passing_refutation_resolves(tmp_path):
    report = _grade(tmp_path, _log("FAILED proof", "PASSED refutation"))
    assert report["resolved"] is True


def test_two_failures_do_not_resolve(tmp_path):
    report = _grade(tmp_path, _log("FAILED proof", "FAILED refutation"))
    assert report["resolved"] is False


def test_a_null_patch_is_not_graded(tmp_path):
    report = _grade(tmp_path, "", patch=None)
    assert report["patch_is_None"] is True
    assert report["resolved"] is False


def test_output_without_markers_is_not_resolved(tmp_path):
    report = _grade(tmp_path, "PASSED proof\nPASSED refutation")
    assert report["resolved"] is False
    assert "tests_status" not in report


def test_the_last_status_line_wins(tmp_path):
    report = _grade(tmp_path, _log("PASSED proof", "FAILED proof", "FAILED refutation"))
    assert report["tests_status"]["proof"] == "FAILED"


def test_a_forged_end_marker_cannot_hide_the_real_statuses(tmp_path):
    forged = _log("PASSED proof", f"+ : '{END_TEST_OUTPUT}'", "FAILED proof", "FAILED refutation")
    assert _grade(tmp_path, forged)["resolved"] is False


def test_a_timeout_is_classified_but_not_resolved(tmp_path):
    report = _grade(
        tmp_path, f"+ : '{START_TEST_OUTPUT}'\n\nTimeout error: 1800 seconds exceeded."
    )
    assert report["resolved"] is False
    assert report["infra_failure_reason"] == "tests_timed_out"
