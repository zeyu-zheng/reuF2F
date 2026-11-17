"""Actual Lean dependency checks for the dual-target protocol (not Comparator)."""

import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize(
    ("declarations", "selected", "has_sorry"),
    [
        (
            "theorem Example.target : True := by trivial\n"
            "theorem Example.target_neg : Not True := by sorry\n",
            "Example.target",
            False,
        ),
        (
            "theorem Example.target : False := by sorry\n"
            "theorem Example.target_neg : Not False := by intro h; exact h\n",
            "Example.target_neg",
            False,
        ),
        (
            "theorem Example.target : False := by sorry\n"
            "theorem Example.target_neg : Not False := by sorry\n",
            "Example.target_neg",
            True,
        ),
        (
            "theorem Example.target_neg : Not True := by sorry\n"
            "theorem helper : False := Example.target_neg True.intro\n"
            "theorem Example.target : True := False.elim helper\n",
            "Example.target",
            True,
        ),
    ],
)
def test_actual_lean_transitive_axioms(tmp_path, declarations, selected, has_sorry):
    if not shutil.which("lake"):
        pytest.skip("Lean/Lake is required for dependency checks")
    path = tmp_path / "Dual.lean"
    path.write_text(
        "import Lean\n"
        + declarations
        + "\nrun_cmd do\n"
        + f"  let axioms <- Lean.collectAxioms `{selected}\n"
        + f"  unless axioms.contains `sorryAx == {str(has_sorry).lower()} do\n"
        + '    throwError "Unexpected selected-target axiom closure: {axioms}"\n'
    )
    result = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=ROOT / "lean",
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert result.returncode == 0, result.stdout + result.stderr
