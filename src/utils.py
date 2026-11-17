import json
import subprocess
from hashlib import blake2b
from pathlib import Path
from typing import Any


def _get_log_objects(logger):
    if not logger:
        # if logger is None, print to stdout
        log_info = print
        log_error = print
        raise_error = True
    elif logger == "quiet":
        # if logger is "quiet", don't print anything
        log_info = lambda x: None
        log_error = lambda x: None
        raise_error = True
    else:
        # if logger is a logger object, use it
        log_info = logger.info
        log_error = logger.info
        raise_error = False
    return (log_info, log_error, raise_error)


def generate_heredoc_delimiter(content: str) -> str:
    delimiter = f"EOF_{blake2b(content.encode()).hexdigest()[:12]}"
    while delimiter in content:
        delimiter = (
            f"EOF_{blake2b(content.encode() + delimiter.encode()).hexdigest()[:12]}"
        )
    return delimiter


def json_bytes(value: Any) -> bytes:
    """Stable JSON for files Lean and Lake read back."""
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    ).encode()


def checked(command: list[str], cwd: Path, **kwargs: Any) -> bytes:
    """Run a host command, raising with the tail of its output when it fails."""
    result = subprocess.run(
        command,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=kwargs.pop("timeout", 600),
        **kwargs,
    )
    if result.returncode:
        log = result.stdout + result.stderr
        raise RuntimeError(
            f"{command[0]} failed: {log.decode(errors='replace')[-12000:]}"
        )
    return result.stdout


def write_files(workspace: Path, files: dict[str, bytes]) -> None:
    """Write relative paths under a workspace, creating parents as needed."""
    workspace.mkdir(parents=True, exist_ok=True)
    for name, content in files.items():
        path = workspace / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
