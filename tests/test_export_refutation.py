"""A task's refutation is exactly the negation of its target's full type.

The exporter only names the target's universes; `¬ type_of% @target` then
elaborates to the target's own type, so nothing is printed and nothing can drift.
"""

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
TARGET = "theorem Fixture.target {a : Type u} (x : a) (h : x = x) : x = x := by sorry\n"


def _lean(env, *args):
    return subprocess.run(
        ["lean", *map(str, args)], cwd=ROOT / "lean", env=env, capture_output=True, text=True, timeout=120
    )


def test_the_refutation_is_the_exact_negation_of_the_target(tmp_path):
    if not shutil.which("lean"):
        pytest.skip("Lean is required")
    # Compile the actual exporter externally; no root build or Mathlib import.
    shutil.copyfile(ROOT / "lean" / "Export.lean", tmp_path / "Export.lean")
    env = {**os.environ, "LEAN_PATH": str(tmp_path)}
    result = _lean(env, f"--root={tmp_path}", "-o", tmp_path / "Export.olean", tmp_path / "Export.lean")
    assert result.returncode == 0, result.stdout + result.stderr
    manifest, output = tmp_path / "manifest.json", tmp_path / "types.json"
    manifest.write_text(json.dumps([{"declaration": "Fixture.target"}]))
    source = tmp_path / "Fixture.lean"
    source.write_text(
        "import Export\nuniverse u\n" + TARGET
        + f"#reuf2f_export_types {json.dumps(str(manifest))} to {json.dumps(str(output))}\n"
    )
    result = _lean(env, source)
    assert result.returncode == 0, result.stdout + result.stderr
    assert json.loads(output.read_text()) == [{"declaration": "Fixture.target", "universes": ["u0"]}]

    source.write_text(
        "import Lean\nuniverse u\n" + TARGET
        + "theorem Fixture.target_neg.{u0} : ¬ type_of% @Fixture.target.{u0} := by sorry\n"
        + "open Lean Elab Command Meta\n"
        + "run_cmd liftTermElabM do\n"
        + "  let target ← getConstInfo `Fixture.target\n"
        + "  let neg ← getConstInfo `Fixture.target_neg\n"
        + "  let truth := mkNot (target.type.instantiateLevelParams target.levelParams [mkLevelParam `u0])\n"
        + "  unless neg.type == truth do throwError \"Refutation is not the exact negation\"\n"
        + "  if neg.type.getUsedConstants.contains `Fixture.target then\n"
        + "    throwError \"Refutation refers to the admitted target\"\n"
    )
    result = _lean(env, source)
    assert result.returncode == 0, result.stdout + result.stderr
