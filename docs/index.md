# ReuF2F

ReuF2F is a benchmark for evaluating coding agents on open mathematical problems from undergraduate research formalized in Lean. Given a *Lean file* with an open *theorem*, a model is tasked with generating a *patch* that proves the theorem or its full negation.

## Overview

ReuF2F provides:

* **Open research problems** - 244 conjectures and open problems from papers produced in undergraduate research programs
* **Proof or refutation** - an accepted proof or an accepted refutation resolves a problem
* **Reproducible evaluation** - Docker-based grading with Comparator, the Lean kernel and nanoda

## Quick Start

```python
# Load the built dataset from the repository root
import json
reuf2f = [json.loads(line) for line in open("test.jsonl")]
```

```bash
# Setup with Docker
# Extract the anonymous source archive, then enter its directory.
cd reuF2F
pip install -e '.[test]'
cd lean && lake exe cache get && lake build && cd ..
reuf2f images build ./docker
```

## Documentation Structure

- **[Installation](installation.md)** - Setup instructions
- **Guides**
  - [Quickstart](guides/quickstart.md) - Get started with reuF2F
  - [Evaluation](guides/evaluation.md) - How to evaluate predictions on reuF2F
  - [Docker Setup](guides/docker_setup.md) - Configure Docker and the shared Lean image
  - [Datasets](guides/datasets.md) - The dataset, its records and how to build it
- **Reference**
  - [CLI](reference/cli.md) - Every `reuf2f` command and option
- **[FAQ](faq.md)** - Frequently asked questions

## Available Resources

| Dataset | Problem manifest |
| - | - |
| [test.jsonl](../test.jsonl) | [lean/metadata.jsonl](../lean/metadata.jsonl) |

## Contributing

We welcome new problems, corrections to formal statements and tooling fixes from the mathematics, formal verification and machine learning communities! Please report corrections through the anonymous review channel.
