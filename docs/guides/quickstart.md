# Quick Start Guide

This guide will help you get started with reuF2F, from installation to running your first evaluation.

## Setup

First, install reuF2F and build the Lean problems:

```bash
# Extract the anonymous source archive, then enter its directory.
cd reuF2F
pip install -e '.[test]'
cd lean && lake exe cache get && lake build && cd ..
reuf2f dataset check .
```

Make sure Docker is installed and running on your system, then build the shared image:

```bash
reuf2f images build ./docker
```

## Accessing the Datasets

The reuF2F dataset is `test.jsonl` at the repository root:

```python
import json

# Load the reuF2F dataset
reuf2f = [json.loads(line) for line in open("test.jsonl")]
```

## Running a Basic Evaluation

To evaluate a model's predictions on reuF2F:

```bash
reuf2f eval test.jsonl -p <path_to_predictions> --run-id <run_id> -j 4

# one instance
reuf2f eval test.jsonl -p <path_to_predictions> -i abebe2019conjectural --run-id one
```

### Check That Your Evaluation Setup Is Correct

ReuF2F has no reference solutions. To verify your evaluation setup, run the Docker test, which evaluates a one-problem dataset whose submitted refutation must be accepted:

```bash
pytest -rs tests/test_cli.py::test_one_instance
```

A skip means Docker or the image was unavailable.

## Generating Predictions

Use a solver of your choice to generate patches in the [prediction format](evaluation.md#prediction-format), then pass the predictions file to `reuf2f eval -p`.

## Next Steps

- Learn about [running evaluations](evaluation.md) with more advanced options
- Explore the [dataset](datasets.md) and its records
- See the [CLI reference](../reference/cli.md) for every command and option
