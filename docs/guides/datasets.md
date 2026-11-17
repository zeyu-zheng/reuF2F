# ReuF2F Dataset

ReuF2F has a single dataset of open Lean problems from undergraduate research. This guide explains the dataset, its records and how to build it.

## Available Dataset

| Dataset | Description | Size | Use Case |
|---------|-------------|------|----------|
| **reuF2F** | Conjectures and open problems from undergraduate research papers | 244 instances | Proof or refutation of open problems |

| Primary area | Problems |
| --- | ---: |
| Discrete mathematics and combinatorics | 45 |
| Number theory and arithmetic | 45 |
| Algebra and algebraic geometry | 45 |
| Geometry and topology | 45 |
| Analysis, dynamics, probability, and PDE | 45 |
| Others | 19 |

Each problem comes from a paper or report produced in an undergraduate research program, whose authors explicitly state the selected target as a conjecture or an open problem. Openness was checked against later literature at a recorded time; it is not a guarantee that a problem is still open.

## Accessing the Dataset

The built dataset is `test.jsonl` at the repository root:

```python
import json
reuf2f = [json.loads(line) for line in open("test.jsonl")]
```

To rebuild it from the checkout:

```bash
cd lean && lake exe cache get && lake build && cd ..
reuf2f dataset check .
reuf2f dataset build .                                  # writes ./test.jsonl
reuf2f dataset build . -o /tmp/reuf2f -i allen2018non   # selected instances
```

`dataset check` verifies that every item has its file, its import in `lean/reuF2F.lean` and a matching `lean/metadata.jsonl` row, with exactly one target theorem and no forbidden constructs. It then runs Lean inside `lean/` on the built project, so run `lake build` there first. `dataset build` runs the same checks, exports the refutations with Lean on the host, and writes `test.jsonl` to the `-o` directory (default: the checkout). Repeat `-i` to select instances.

`validation.jsonl`, next to `test.jsonl`, holds one trivial problem in the same format, with its reference solution in `patch`, for checking a harness end to end.

## Dataset Structure

Each instance in the dataset has the following 14 fields:

```python
{
    "instance_id": "Item file stem, such as abebe2019conjectural",
    "declaration": "Fully qualified target theorem; the refutation is <declaration>_neg",
    "program": "Undergraduate research program",
    "source_url": "Source article or report",
    "title": "Source paper title",
    "version": "Lean version, such as v4.34.0",
    "year": "Earliest public year of the source (integer)",
    "area": "Primary mathematical area",
    "source_label": "Location in the source, such as Conjecture 3",
    "problem_statement": "One sentence naming the file, the target and its _neg refutation",
    "challenge": "Full task file, <instance_id>.lean",
    "image": "Shared evaluation image, reuf2f-eval:v4.34.0",
    "log_parser": "parse_log_comparator",
    "eval_type": "proof_or_refutation"
}
```

The `challenge` is the item file, with its definitions, namespace and original theorem, followed by the full negation:

```lean
theorem <declaration>_neg : ¬ type_of% @<declaration> := by
  sorry
```

with the target's universe parameters, if any. `type_of%` elaborates to the target's own type, so this is exactly its negation and does not refer to the admitted target. Both proofs start as `sorry`.

## Problem Files

The Lean project and the problem manifest live in `lean/`:

```text
README.md
test.jsonl               # built dataset
validation.jsonl         # one trivial problem for harness checks
lean/
  lakefile.lean, lean-toolchain, lake-manifest.json
  reuF2F.lean            # root module, imports every item
  reuF2F/<key>.lean      # one problem per file, module reuF2F.<key>
  Export.lean            # trusted refutation exporter
  metadata.jsonl         # problem manifest, one row per item
src/  tests/  docs/  docker/tags/v4.34.0/
```

Each problem is `lean/reuF2F/<key>.lean`, imported by `lean/reuF2F.lean`. The key follows the Google Scholar BibTeX form: first author's surname, year and first non-stopword title word, such as `allen2018non`. A file imports only Mathlib, puts everything in one item namespace (the key in UpperCamelCase, such as `Abebe2019Conjectural`), with nested namespaces only for the API of a structure it defines (such as `KFamily.boundaryMatrix`), contains complete definitions, and has exactly one target theorem whose proof is `sorry`. Its module docstring gives the title, authors, program origin and reference.

## Metadata

`lean/metadata.jsonl` has one row per item, with 9 fields, in the import order of `lean/reuF2F.lean`:

| Field | Meaning |
| --- | --- |
| `id` | Item file stem |
| `module` | `reuF2F.<id>` |
| `declaration` | Fully qualified target theorem |
| `source_label` | Location of the statement in the source |
| `title` | Source paper's original title |
| `program` | Undergraduate research program, without year |
| `year` | Earliest public year of the source literature (integer) |
| `area` | One of the six areas above |
| `source_url` | Source article or report |
