"""Each task's project is the image's, with only its root replaced.

The lakefile, manifest and toolchain come from the image recipe, so a task builds
against exactly the dependencies the image already has.
"""

import json
import shutil
import tomllib
from pathlib import Path

import pytest

from reuf2f.task.lean import workspace_config

ROOT = Path(__file__).resolve().parents[1]


def test_only_the_root_differs_from_the_image_project():
    image = (ROOT / "docker/tags/v4.34.0/lakefile.toml").read_bytes()
    config = workspace_config(ROOT, ("example",))
    assert config["lakefile.toml"] == image.replace(b'["Main"]', b'["example"]')
    manifest = json.loads((ROOT / "lean" / "lake-manifest.json").read_bytes())
    assert json.loads(config["lake-manifest.json"]) == {**manifest, "name": "project"}


def test_a_recipe_pinning_other_dependencies_is_refused(tmp_path):
    (tmp_path / "lean").mkdir()
    for name in ("lean-toolchain", "lake-manifest.json"):
        shutil.copy2(ROOT / "lean" / name, tmp_path / "lean" / name)
    recipe = tmp_path / "docker/tags/v4.34.0"
    shutil.copytree(ROOT / "docker/tags/v4.34.0", recipe)
    path = recipe / "lakefile.toml"
    revision = tomllib.loads(path.read_text())["require"][0]["rev"]
    path.write_text(path.read_text().replace(f'rev = "{revision}"', 'rev = "wrong"'))
    with pytest.raises(ValueError, match="dependency differs"):
        workspace_config(tmp_path, ("example",))
