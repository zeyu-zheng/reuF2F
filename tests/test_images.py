"""The shared image is read from its recipe, and grading picks it by Lean version.

A recipe is `tags/<version>/` with a Dockerfile and a task.yaml naming the image,
so the image a run uses is always the one the checkout's lean-toolchain pins.
"""

import pytest
import yaml
from typer.testing import CliRunner

from reuf2f.cli.cli import app
from reuf2f.image_builder.image_spec import get_shared_image, load_image_specs

VERSION = "v4.34.0"


@pytest.fixture
def image_repo(tmp_path):
    context = tmp_path / "docker" / "tags" / VERSION
    context.mkdir(parents=True)
    (context / "Dockerfile").write_text("FROM example/base:fixed\n")
    (context / "task.yaml").write_text(
        yaml.safe_dump(
            {"instance_id": VERSION, "image": "example/lean4:v4.34.0", "platform": "linux/amd64"}
        )
    )
    return tmp_path / "docker"


def test_the_recipe_names_the_image(image_repo):
    spec = load_image_specs(image_repo)[0]
    assert spec.name == "example/lean4:v4.34.0"
    assert spec.dockerfile == "FROM example/base:fixed\n"


def test_grading_picks_the_recipe_by_lean_version(image_repo):
    (image_repo.parent / "lean").mkdir()
    (image_repo.parent / "lean" / "lean-toolchain").write_text(f"leanprover/lean4:{VERSION}\n")
    assert get_shared_image(image_repo.parent).name == "example/lean4:v4.34.0"


def test_another_lean_version_has_no_image(image_repo):
    (image_repo.parent / "lean").mkdir()
    (image_repo.parent / "lean" / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    with pytest.raises(ValueError, match="no unique shared Lean image"):
        get_shared_image(image_repo.parent)


@pytest.mark.parametrize(
    "changes",
    [{"image": "example/image"}, {"platform": "linux/arm64"}, {"instance_id": "other"}],
)
def test_an_invalid_recipe_is_refused(image_repo, changes):
    path = image_repo / "tags" / VERSION / "task.yaml"
    path.write_text(yaml.safe_dump(yaml.safe_load(path.read_text()) | changes))
    with pytest.raises(ValueError):
        load_image_specs(image_repo)


@pytest.mark.parametrize("operation", ["build", "push"])
def test_a_dry_run_does_not_call_docker(image_repo, operation):
    result = CliRunner().invoke(app, ["images", operation, str(image_repo), "--dry-run"])
    assert result.exit_code == 0, result.output
    assert "Built " not in result.stdout and "Pushed " not in result.stdout
