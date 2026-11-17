"""
Type definitions for reuf2f.
"""

from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class TestSpec:
    """
    A dataclass that represents a test specification for evaluation of a single instance of reuF2F.
    Assumes images are already built and available.
    """

    instance_id: str
    repo: Path
    challenge: str
    declaration: str
    image: str = ""
    log_parser: str = "parse_log_comparator"

    @property
    def source_file(self) -> str:
        return f"{self.instance_id}.lean"
