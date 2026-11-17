"""eval.sh generation; no submitted code runs on the host."""

from __future__ import annotations

import json

from reuf2f.harness.constants import (
    CONTAINER_WORKDIR,
    END_TEST_OUTPUT,
    EVALUATION_TOOLS,
    PERMITTED_AXIOMS,
    START_TEST_OUTPUT,
    TestStatus,
)
from reuf2f.utils import generate_heredoc_delimiter


def write_file_command(path: str, content: str) -> str:
    content = content if content.endswith("\n") else content + "\n"
    delimiter = generate_heredoc_delimiter(content)
    return f"cat > {path} <<'{delimiter}'\n{content}{delimiter}"


def make_eval_script(challenge: str, module: str, declaration: str) -> str:
    """Reset trusted inputs, then run both Comparator checks on copies of the repo."""
    configs = {
        polarity: json.dumps(
            {
                "challenge_module": "Challenge",
                "solution_module": module,
                "theorem_names": [
                    declaration if polarity == "proof" else declaration + "_neg"
                ],
                "permitted_axioms": PERMITTED_AXIOMS,
                "external_kernels": {"nanoda": [str(EVALUATION_TOOLS["nanoda"])]},
            }
        )
        + "\n"
        for polarity in ("proof", "refutation")
    }
    eval_script_list = [
        f"cd {CONTAINER_WORKDIR} || exit 1",
        "git checkout HEAD -- lean-toolchain lake-manifest.json || exit 1",
        "rm -f lakefile.lean",
        "lean_prefix=$(lean --print-prefix) || exit 1",
        'export PATH="$lean_prefix/bin:/usr/bin:/bin"',
        f"export COMPARATOR_LANDRUN={EVALUATION_TOOLS['landrun']}",
        f"export COMPARATOR_LEAN4EXPORT={EVALUATION_TOOLS['lean4export']}",
        "",
        # Comparator builds in the project directory; each direction needs its own copy.
        "for polarity in proof refutation; do",
        '    mkdir -p /eval/"$polarity"/.lake || exit 1',
        f"    tar -C {CONTAINER_WORKDIR} --exclude=.git --exclude=.lake -cf - . "
        '| tar -C /eval/"$polarity" -xf - || exit 1',
        f'    ln -s {CONTAINER_WORKDIR}/.lake/packages /eval/"$polarity"/.lake/packages || exit 1',
        "    " + write_file_command('/eval/"$polarity"/Challenge.lean', challenge),
        "    printf '\\n[[lean_lib]]\\nname = \"Challenge\"\\n' "
        '>> /eval/"$polarity"/lakefile.toml',
        "done",
        *(write_file_command(f"/eval/{p}/config.json", c) for p, c in configs.items()),
        "",
        "check() {",
        '    cd /eval/"$1" || return 1',
        '    LEAN_PATH=$(lake env printenv LEAN_PATH 2>/eval/"$1".log) || return 1',
        "    export LEAN_PATH",
        f'    {EVALUATION_TOOLS["comparator"]} config.json >>/eval/"$1".log 2>&1',
        '    echo "$?" > /eval/"$1".exit_code',
        "}",
        "",
        "check proof &",
        "check refutation &",
        "wait",
        "",
        f": '{START_TEST_OUTPUT}'",
        "cat /eval/proof.log /eval/refutation.log",
        "for polarity in proof refutation; do",
        '    if [ "$(cat /eval/"$polarity".exit_code 2>/dev/null)" = 0 ]; then',
        f'        echo "{TestStatus.PASSED.value} $polarity"',
        "    else",
        f'        echo "{TestStatus.FAILED.value} $polarity"',
        "    fi",
        "done",
        f": '{END_TEST_OUTPUT}'",
    ]
    return "\n".join(["#!/bin/bash", "set -uxo pipefail"] + eval_script_list) + "\n"
