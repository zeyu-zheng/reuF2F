"""Docker filesystem/exec test double: executes Git only, never submitted Lean."""

import io
import os
import shlex
import subprocess
import tarfile
import tempfile
from pathlib import Path, PurePosixPath
from types import SimpleNamespace

from reuf2f.harness.constants import CONTAINER_PATCH_FILE, CONTAINER_WORKDIR
from reuf2f.harness.docker_utils import copy_to_container
from reuf2f.harness.run_evaluation import GIT_APPLY_CMDS
from reuf2f.harness.utils import setup_repo
from reuf2f.utils import checked, write_files


def git(workspace, *args):
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
    return checked(
        ["git", "-c", "user.name=reuF2F", "-c", "user.email=test@reuf2f.invalid", *args],
        workspace,
        env=env,
    )


def init_baseline(workspace, files):
    """A solver-side repository whose diffs become test predictions."""
    write_files(workspace, files)
    git(workspace, "init", "-q")
    git(workspace, "add", "--", *sorted(files))
    git(workspace, "commit", "-qm", "baseline")


class LocalGitContainer:
    def __init__(self, root):
        self.root = root

    def exec_run(self, command, workdir=None, **_kwargs):
        if isinstance(command, str) and command.startswith("mkdir -p "):
            (self.root / command.removeprefix("mkdir -p ").lstrip("/")).mkdir(
                parents=True, exist_ok=True
            )
            return SimpleNamespace(exit_code=0, output=b"")
        if isinstance(command, list):
            assert command[:2] == ["/bin/bash", "-c"] and command[2].startswith("git ")
            return self._run(command, workdir)
        args = shlex.split(command)
        assert args[0] == "git", command
        args = [
            str(self.root / arg.lstrip("/")) if arg.startswith("/") else arg
            for arg in args
        ]
        return self._run(args, workdir)

    def _run(self, args, cwd):
        directory = self.root / cwd.lstrip("/")
        directory.mkdir(parents=True, exist_ok=True)
        result = subprocess.run(args, cwd=directory, capture_output=True)
        return SimpleNamespace(
            exit_code=result.returncode, output=result.stdout + result.stderr
        )

    def put_archive(self, parent, data):
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            # Inputs come from the harness, not the submitted diff.
            archive.extractall(self.root / parent.lstrip("/"), filter="data")
        return True


def replay_patch(baseline, patch):
    """Production repo setup and patch command; return the repository's files."""
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        patch_file = root / "patch.diff"
        patch_file.write_text(patch)
        container = LocalGitContainer(root / "container")
        testbed = container.root / CONTAINER_WORKDIR.lstrip("/")
        setup_repo(container, baseline)
        copy_to_container(container, patch_file, PurePosixPath(CONTAINER_PATCH_FILE))
        val = container.exec_run(
            f"{GIT_APPLY_CMDS[0]} {CONTAINER_PATCH_FILE}", workdir=CONTAINER_WORKDIR
        )
        if val.exit_code != 0:
            raise ValueError(val.output.decode(errors="replace"))
        return {
            path.relative_to(testbed).as_posix(): path.read_bytes()
            for path in testbed.rglob("*")
            if path.is_file() and path.relative_to(testbed).parts[0] != ".git"
        }
