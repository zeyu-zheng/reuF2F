from __future__ import annotations

import subprocess

from reuf2f.image_builder.image_spec import (
    ImageSpec,
)
from reuf2f.logger import setup_logger, close_logger


class BuildImageError(Exception):
    def __init__(self, image_name, message, logger):
        super().__init__(message)
        self.super_str = super().__str__()
        self.image_name = image_name
        self.log_path = logger.log_file
        self.logger = logger

    def __str__(self):
        return (
            f"Error building image {self.image_name}: {self.super_str}\n"
            f"Check ({self.log_path}) for more information."
        )


def build_image(
    image_spec: ImageSpec,
    nocache: bool = False,
    dry_run: bool = False,
):
    """
    Builds a docker image using Docker Buildx with proper platform support.
    This fixes the "no specific platform was requested" warning.

    Args:
        image_spec (ImageSpec): Image specification containing dockerfile and metadata
        nocache (bool): Whether to use the cache when building
        dry_run (bool): If True, create docker files and build contexts but don't build images
    """
    log_dir = (
        image_spec.context_dir.parent.parent
        / ".lake/image-builder"
        / image_spec.filesafe_name
    )
    logger = setup_logger(
        image_spec.name,
        log_dir / "build_image.log",
    )
    logger.info(
        f"Building image {image_spec.name}\n"
        f"Using dockerfile:\n{image_spec.dockerfile}\n"
    )
    dockerfile_path = log_dir / "Dockerfile"

    try:
        with open(dockerfile_path, "w", encoding="utf-8") as f:
            f.write(image_spec.dockerfile)

        target_platform = image_spec.platform
        logger.info(
            f"Building docker image {image_spec.name} in {dockerfile_path} "
            f"with platform {target_platform} using Docker Buildx"
        )

        if not dry_run:
            cmd = [
                "docker",
                "buildx",
                "build",
                f"--platform={target_platform}",
                f"--tag={image_spec.name}",
                f"--file={dockerfile_path}",
                "--progress=plain",
                "--load",
            ]

            if nocache:
                cmd.append("--no-cache")
            cmd.append(str(image_spec.context_dir))

            print(f"Building {image_spec.name}; log: {logger.log_file}", flush=True)
            logger.info(f"Executing: {' '.join(cmd)}")

            with open(logger.log_file, "a+", encoding="utf-8") as log_file:
                process = subprocess.Popen(
                    cmd,
                    stdout=log_file,
                    stderr=subprocess.STDOUT,
                    text=True,
                    cwd=image_spec.context_dir,
                )
                return_code = process.wait()

            if return_code == 0:
                logger.info("Image built successfully!")
            else:
                error_msg = f"Docker buildx failed with exit code {return_code}"
                logger.error(error_msg)
                raise BuildImageError(image_spec.name, error_msg, logger)
        else:
            logger.info("Build context created successfully!")
            print(f"Build context created: {dockerfile_path}")
    except BuildImageError:
        raise
    except Exception as e:
        logger.error(f"Error building image {image_spec.name}: {e}")
        raise BuildImageError(image_spec.name, str(e), logger) from e
    finally:
        close_logger(logger)


def push_image(image_spec: ImageSpec, dry_run: bool = False):
    """Push one image to its configured registry."""
    name = image_spec.name
    print(f"docker push {name}", flush=True)
    if dry_run:
        return
    result = subprocess.run(
        ["docker", "push", name],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            result.stderr.strip()
            or f"docker push failed with exit code {result.returncode}"
        )
    print(result.stdout, end="")
