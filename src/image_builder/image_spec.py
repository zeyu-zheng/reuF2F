import re
from dataclasses import dataclass
from pathlib import Path

import yaml

from reuf2f.task.repo import LEAN_DIR, TASK_FILE, task_dirs


@dataclass
class ImageSpec:
    """
    A dataclass that represents an image specification for building Docker images
    for the shared Lean environment that every reuF2F task runs in.
    """

    name: str
    dockerfile: str
    platform: str
    context_dir: Path

    def __post_init__(self):
        """Validate the dataclass fields after initialization."""
        if not isinstance(self.name, str) or not re.fullmatch(
            r"[a-z0-9][a-z0-9._:/-]*:[A-Za-z0-9_][A-Za-z0-9_.-]{0,127}", self.name
        ):
            raise ValueError("image name must include a repository and tag")
        if not self.dockerfile.strip():
            raise ValueError("dockerfile cannot be empty")
        if self.platform != "linux/amd64":
            raise ValueError("the shared Lean image requires linux/amd64")

    @property
    def filesafe_name(self):
        return self.name.replace("/", "__").replace(":", "__")


def load_image_specs(task_repo: str | Path) -> list[ImageSpec]:
    """Read tags/<id>/{task.yaml,Dockerfile}; do not render or select a version."""
    repo_path = Path(task_repo).expanduser().resolve()
    specs = []
    for context_dir in task_dirs(repo_path):
        metadata_path = context_dir / TASK_FILE
        try:
            metadata = yaml.safe_load(metadata_path.read_text(encoding="utf-8"))
        except yaml.YAMLError as e:
            raise ValueError(f"invalid YAML in {metadata_path}: {e}") from e
        if not isinstance(metadata, dict) or set(metadata) != {
            "instance_id",
            "image",
            "platform",
        }:
            raise ValueError(
                f"{metadata_path} must contain instance_id, image and platform"
            )
        if metadata["instance_id"] != context_dir.name:
            raise ValueError(f"{metadata_path}: instance_id must match its directory")
        specs.append(
            ImageSpec(
                name=metadata["image"],
                dockerfile=(context_dir / "Dockerfile").read_text(encoding="utf-8"),
                platform=metadata["platform"],
                context_dir=context_dir,
            )
        )
    if not specs:
        raise ValueError(f"no image recipes found in {repo_path}/tags")
    if len({spec.name for spec in specs}) != len(specs):
        raise ValueError("each environment must declare a distinct image name")
    return specs


def get_shared_image(repo: Path) -> ImageSpec:
    version = (repo / LEAN_DIR / "lean-toolchain").read_text().strip().rsplit(":", 1)[-1]
    images = [
        s for s in load_image_specs(repo / "docker") if s.context_dir.name == version
    ]
    if len(images) != 1:
        raise ValueError(f"no unique shared Lean image for {version}")
    return images[0]
