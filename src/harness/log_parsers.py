import re

from reuf2f.harness.constants import TestStatus
from reuf2f.types import TestSpec


def parse_log_comparator(log: str, test_spec: TestSpec) -> dict[str, str]:
    """
    Parser for the status lines eval.sh prints after both Comparator runs

    Args:
        log (str): log content
    Returns:
        dict: test case to test status mapping
    """
    test_status_map = {}
    for line in log.split("\n"):
        match = re.fullmatch(r"(PASSED|FAILED) (proof|refutation)", line.strip())
        if match:
            test_status_map[match.group(2)] = TestStatus(match.group(1)).value
    return test_status_map


PARSER_REGISTRY = {
    "parse_log_comparator": parse_log_comparator,
}
