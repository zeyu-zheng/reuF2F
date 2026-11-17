# Docker Setup Guide

## Introduction

ReuF2F uses a Docker-based evaluation harness to ensure consistent, reproducible results across different platforms. Every task runs in one shared Lean image, `reuf2f-eval:v4.34.0` (`linux/amd64`), and each evaluation gets a fresh container from it.

The anonymous release uses a local image tag. Run `reuf2f images build ./docker`
before evaluating; this tag is not a published registry image.

## Prerequisites

Before setting up Docker for reuF2F, ensure you have:

- Docker installed on your system ([Docker installation guide](https://docs.docker.com/engine/install/))
- For Linux users, follow the [post-installation steps](https://docs.docker.com/engine/install/linux-postinstall/)
- Docker Buildx, used to build the image for `linux/amd64`
- Sufficient disk space (the shared image is about 15GB; keep at least 60GB free for pulling and unpacking)

## Docker Installation

### macOS

1. Download and install Docker Desktop for Mac from the [official website](https://www.docker.com/products/docker-desktop)
2. Increase resource allocation in Docker Desktop settings:
   - Open Docker Desktop preferences
   - Go to Resources > Advanced
   - Allocate enough CPUs and memory for the workers you plan to run
   - Set the disk image size to hold the shared image

On Apple silicon, the `linux/amd64` image runs under emulation.

### Linux

1. Install Docker using your distribution's package manager or follow the [official guide](https://docs.docker.com/engine/install/)
2. Add your user to the docker group to run Docker without sudo:
   ```bash
   sudo groupadd docker
   sudo usermod -aG docker $USER
   newgrp docker  # Apply changes without logging out
   ```

### Windows

1. Install Docker Desktop for Windows from the [official website](https://www.docker.com/products/docker-desktop)
2. Ensure WSL 2 is installed and configured
3. Increase resource allocation in Docker Desktop settings, as for macOS

## Testing Your Docker Installation

Verify your Docker installation with these commands:

```bash
# Check Docker version
docker --version

# Run a simple test container
docker run hello-world

# Check available disk space
docker system df
```

## Docker Resource Management

### Understanding reuF2F's Docker Usage

The reuF2F evaluation harness uses a single image for every task. Its recipe is in `docker/tags/v4.34.0/`:

```text
docker/tags/v4.34.0/
  task.yaml
  Dockerfile
  lean-toolchain
  lakefile.toml
  entrypoint.sh
  .dockerignore
```

`task.yaml` declares the shared environment:

```yaml
instance_id: v4.34.0
image: reuf2f-eval:v4.34.0
platform: linux/amd64
```

The `instance_id` must match the directory name. The recipe's `lean-toolchain` and Mathlib revision must match the checkout's `lean/lean-toolchain` and `lean/lake-manifest.json`; otherwise evaluation fails.

| Component | Version source |
| --- | --- |
| Base image | `ghcr.io/openai/codex-universal:latest` |
| Lean | `leanprover/lean4:v4.34.0` in `lean-toolchain`, under `/root/.elan` |
| Mathlib | `v4.34.0` tag in `lakefile.toml`, built in `/testbed` |
| Comparator | Tag matching `lean-toolchain`, in `/usr/local/bin/comparator` |
| lean4export | Comparator's locked dependency |
| Landrun | `v0.1.17` release |
| nanoda | Pinned `nanoda_lib` commit, in `/usr/local/bin/nanoda_lib` |

Rebuilding or pushing the same tag can change the image contents, so record the image digest for reproducible experiments.

### Building and Pushing the Image

From the reuF2F checkout:

```bash
reuf2f images build ./docker --dry-run
reuf2f images build ./docker
```

`build` builds every recipe under `docker/tags/` locally with `docker buildx build --platform=linux/amd64 --load`, reusing the layer cache. It does not push. `--dry-run` writes the Dockerfile snapshot without running Docker. Build logs and snapshots are written to `docker/.lake/image-builder/<image>/`, where `<image>` is the image name with `/` and `:` replaced by `__` (for the shared image: `docker/.lake/image-builder/reuf2f-eval__v4.34.0/`). The evaluation harness pulls the image named in the dataset if it is not present locally.

To publish your own image, first set a registry tag you control in `task.yaml`
and regenerate the dataset so its image fields match. The anonymous default
tag is intended for local builds.

```bash
docker login
reuf2f images push ./docker --dry-run
reuf2f images push ./docker
```

`push` runs `docker push` for each image under the name its `task.yaml` declares; it does not build first. `--dry-run` prints the push commands.

### Resource Management Commands

Useful commands for managing Docker resources:

```bash
# View Docker disk usage
docker system df

# Remove all stopped containers
docker container prune

# Remove dangling images (untagged)
docker image prune
```

## Performance Optimization

### Setting the Right Number of Workers

Each worker (`-j`) evaluates one task, which runs two Comparator processes at once, so `-j N` can run up to `2N` Lean checks. Choose `N` for the CPUs and memory available to Docker:

```bash
reuf2f eval test.jsonl -p <path_to_predictions> -j 4
```

Increasing worker count beyond your system's capabilities can actually slow down evaluation, or cause timeouts, due to resource contention.

## Troubleshooting Docker Issues

### Common Problems and Solutions

1. **Insufficient disk space**:
   - Free up disk space or increase Docker Desktop's disk image size

2. **Docker build failures**:
   - Check network connectivity
   - Inspect `docker/.lake/image-builder/reuf2f-eval__v4.34.0/build_image.log`

3. **Permission issues**:
   - Ensure your user is in the docker group (Linux)

4. **Slow evaluation times or timeouts**:
   - Reduce the number of parallel workers
   - Check CPU and memory usage during evaluation

5. **Network-related issues**:
   - Check Docker network settings:
     ```bash
     docker network ls
     docker network inspect bridge
     ```

## Cleaning Up After Evaluation

The harness removes each task container after evaluation and keeps the shared image. To reclaim disk space:

```bash
docker container prune  # Remove all stopped containers
docker image prune      # Remove dangling images
```
