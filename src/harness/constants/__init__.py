from enum import Enum
from pathlib import Path


class TestStatus(Enum):
    FAILED = "FAILED"
    PASSED = "PASSED"


# Constants - Log Directories
RUN_EVALUATION_LOG_DIR = Path("logs/evaluation")

# Constants - Evaluation Execution
CONTAINER_PATCH_FILE = "/tmp/patch.diff"
LOG_REPORT = "report.json"
# what a run was: written at eval time so `reuf2f report` can re-grade it later
LOG_RUN_METADATA = "run.json"
LOG_INSTANCE = "run_instance.log"
LOG_TEST_OUTPUT = "test_output.txt"

# Constants - Evaluation Logging
APPLY_PATCH_FAIL = ">>>>> Patch Apply Failed"
APPLY_PATCH_PASS = ">>>>> Applied Patch"
RESET_FAILED = ">>>>> Reset Failed"
TESTS_ERROR = ">>>>> Tests Errored"
TESTS_TIMEOUT = ">>>>> Tests Timed Out"
START_TEST_OUTPUT = ">>>>> Start Test Output"
END_TEST_OUTPUT = ">>>>> End Test Output"

# Constants - Comparator
EVALUATION_TOOLS = {
    "comparator": Path("/usr/local/bin/comparator/.lake/build/bin/comparator"),
    "lean4export": Path(
        "/usr/local/bin/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
    ),
    "landrun": Path("/usr/local/bin/comparator/landrun"),
    "nanoda": Path("/usr/local/bin/nanoda_lib/target/release/nanoda_bin"),
}
PERMITTED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
CONTAINER_USER = "root"
CONTAINER_WORKDIR = "/testbed"

INSTRUCTION = (
    "In {source_file}, prove either {declaration} or refute it by proving its "
    "logical negation {declaration}_neg."
)
