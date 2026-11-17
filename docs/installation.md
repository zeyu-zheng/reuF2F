# Installation

ReuF2F is designed to be easy to install and run on most systems with Docker support.

## Prerequisites

Before installing reuF2F, make sure you have the following prerequisites:

* **Python 3.11+** - Required for running the package
* **elan** - Installs the Lean version pinned in `lean/lean-toolchain` (`v4.34.0`)
* **Docker** - Essential for the evaluation environment; it must run `linux/amd64` images and provide Buildx to build them

## Standard Installation

For most users, the standard installation is the best option:

```bash
# Extract the anonymous source archive, then enter its directory.
cd reuF2F

# Install the package
pip install -e .

# Fetch the Mathlib cache and build every problem
cd lean && lake exe cache get && lake build && cd ..

# Check the checkout
reuf2f dataset check .
```

This will install the `reuf2f` command in development mode, allowing you to make changes to the code if needed. The package does not bundle the Lean checkout: when running `reuf2f eval` or `reuf2f report` outside it, pass `--repo /path/to/ReuF2F`.

## Docker Setup

ReuF2F relies heavily on Docker for its evaluation environment. Make sure Docker is correctly installed and running:

```bash
# Test that Docker is installed correctly
docker --version
docker run hello-world
```

Then build the shared Lean image:

```bash
reuf2f images build ./docker
```

See the [Docker setup guide](guides/docker_setup.md) for details.

## Optional Dependencies

Depending on your use case, you might want to install additional dependencies:

```bash
# For development and testing
pip install -e '.[test]'

# Evaluate a one-problem dataset in Docker; skipped if Docker or the image is unavailable
pytest -rs tests/test_cli.py::test_one_instance
```

## Troubleshooting

If you encounter any issues during installation:

1. **Docker permission issues**: You might need to add your user to the Docker group
2. **Python version conflicts**: Make sure you're using Python 3.11+
3. **Package conflicts**: Consider using a virtual environment
4. **Lean check failures**: Run `(cd lean && lake build)` before `reuf2f dataset check .`

For more detailed troubleshooting, please refer to our [FAQ page](faq.md) or open an issue on GitHub.
