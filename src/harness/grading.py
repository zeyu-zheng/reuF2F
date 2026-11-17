from typing import Any

from reuf2f.harness.constants import (
    APPLY_PATCH_FAIL,
    END_TEST_OUTPUT,
    RESET_FAILED,
    START_TEST_OUTPUT,
    TESTS_ERROR,
    TESTS_TIMEOUT,
    TestStatus,
)
from reuf2f.harness.infra_failure import TIER_ENVIRONMENT, classify_logs
from reuf2f.types import TestSpec
from reuf2f.harness.log_parsers import PARSER_REGISTRY


# MARK: Evaluation report functions
def get_logs_eval(test_spec: TestSpec, log_fp: str) -> tuple[dict[str, str], bool]:
    """
    Retrieve evaluation results for a task instance from its corresponding log file

    Args:
        log_fp (str): path to log file
    Returns:
        bool: whether the patch applied successfully
        dict: status map
    """
    log_parser = PARSER_REGISTRY[test_spec.log_parser]

    with open(log_fp) as f:
        content = f.read()
        bad_codes = list(
            filter(
                lambda x: x in content,
                [
                    APPLY_PATCH_FAIL,
                    RESET_FAILED,
                    TESTS_ERROR,
                    TESTS_TIMEOUT,
                ],
            )
        )
        if bad_codes:
            return {}, False
        elif not (START_TEST_OUTPUT in content and END_TEST_OUTPUT in content):
            return {}, False

        # Get status map of evaluation results. Comparator output (which submitted
        # code can influence) precedes eval.sh's own end marker, so use the last one.
        sliced = content.split(START_TEST_OUTPUT)[1].rsplit(END_TEST_OUTPUT, 1)[0]
        status_map = log_parser(sliced, test_spec)
        if not status_map:
            return {}, False
        return status_map, True


def get_eval_report(
    test_spec: TestSpec,
    prediction: dict[str, str],
    test_log_path: str,
    include_tests_status: bool,
) -> dict[str, Any]:
    """
    Generate a report of model evaluation results from a prediction, task instance,
    and evaluation log.

    Args:
        test_spec (dict): test spec containing keys "instance_id" and "log_parser"
        prediction (dict): prediction containing keys "instance_id", "model_name_or_path", and "model_patch"
        log_path (str): path to evaluation log
        include_tests_status (bool): whether to include the status of each test in the returned report
    Returns:
        report (dict): report of metrics
    """
    report_map = {}

    instance_id = prediction["instance_id"]
    report_map[instance_id] = {
        "patch_is_None": False,
        "patch_exists": False,
        "patch_successfully_applied": False,
        "resolved": False,
        "infra_failure": False,
    }

    # Check if the model patch exists
    if prediction["model_patch"] is None:
        report_map[instance_id]["patch_is_None"] = True
        return report_map
    report_map[instance_id]["patch_exists"] = True

    # Get evaluation logs
    eval_status_map, found = get_logs_eval(test_spec, test_log_path)

    if not found:
        # No parseable test output: flag a likely environment fault for triage.
        # Advisory only -- `resolved` stays False either way (#586).
        classification = classify_logs(test_log_path)
        if classification:
            reason, tier = classification
            report_map[instance_id]["infra_failure"] = tier == TIER_ENVIRONMENT
            report_map[instance_id]["infra_failure_reason"] = reason
        return report_map
    report_map[instance_id]["patch_successfully_applied"] = True

    # Proof and refutation are alternatives: either one passing resolves the task.
    if TestStatus.PASSED.value in eval_status_map.values():
        report_map[instance_id]["resolved"] = True

    if include_tests_status:
        report_map[instance_id]["tests_status"] = eval_status_map  # type: ignore

    return report_map
