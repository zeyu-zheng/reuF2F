# Command line interface

Installing the package provides a `reuf2f` command. Every command takes
`-h/--help`, and the top level takes `-v/--verbose` (DEBUG logging) and
`--repo PATH`, the trusted Lean checkout, which defaults to current-directory
ancestors. `eval` and `report` also accept `--repo` after the command name.

`DATASET` is a local `.json` or `.jsonl` file built by `reuf2f dataset build`,
such as `test.jsonl` at the repository root.

## Evaluate

### `reuf2f eval DATASET`

Evaluate model predictions and save reports under `logs/evaluation/RUN_ID`.

```bash
reuf2f eval test.jsonl -p preds.json --run-id experiment -j 4
reuf2f eval test.jsonl -p preds.json -i abebe2019conjectural -i allen2018non
```

| Option | Meaning | Default |
| --- | --- | --- |
| `-p`, `--predictions TEXT` | Path to a predictions `.json`/`.jsonl` | Required |
| `-r`, `--run-id TEXT` | Names the log directory | `run` |
| `-i`, `--instance TEXT` | Limit to these instances (repeatable) | All |
| `-j`, `--workers INTEGER` | Instances evaluated in parallel | `4` |
| `-t`, `--timeout INTEGER` | Per-instance seconds | `7200` |
| `--repo PATH` | Trusted Lean checkout | Current-directory ancestors |

Artifacts go to `logs/evaluation/<run_id>/`, the summary to its `results.json`.
That path is relative to where you run the command.
Re-running a run id skips instances that already have a `report.json`.

### `reuf2f report RUN_ID`

Re-grade saved test output, without launching Lean or Comparator.

The dataset and predictions come from the run itself, recorded at evaluation
time in `logs/evaluation/<run_id>/run.json` and `predictions.json`. Pass `-d` if
the dataset moved.

```bash
reuf2f report experiment                     # dataset taken from the run itself
reuf2f report experiment -d test.jsonl -i abebe2019conjectural
```

| Option | Meaning | Default |
| --- | --- | --- |
| `-d`, `--dataset TEXT` | Dataset the run used | Taken from the run |
| `-i`, `--instance TEXT` | Limit to these instances (repeatable) | All with saved output |
| `--repo PATH` | Trusted Lean checkout | Recorded by the run |

## Images

Images are built from a recipe root containing `tags/<version>/`, such as
`./docker`. Each recipe's `task.yaml` names the image the dataset will tell the
harness to pull.

```bash
reuf2f images build ./docker
reuf2f images build ./docker --dry-run
reuf2f images push ./docker --dry-run
reuf2f images push ./docker
```

### `reuf2f images build TASK_REPO`

Build the shared images ahead of an evaluation, from a recipe root. Builds
every `tags/<version>/` recipe locally and does not push it.
`--dry-run` creates the build snapshot without running Docker.

### `reuf2f images push TASK_REPO`

Push each shared image to the registry, under the name its `task.yaml`
declares. The dataset tells the harness which image to pull, so the pushed name
has to match. `--dry-run` shows what would be pushed.

## Datasets

`TASK_REPO` is the reuF2F checkout:

```
test.jsonl                   the built dataset
lean/
    reuF2F.lean              root module, imports every item
    reuF2F/<key>.lean        one open problem per file
    metadata.jsonl           one manifest row per item
```

The tree is the source of truth: the dataset is built from the checkout alone.

### `reuf2f dataset check TASK_REPO`

Check that the checkout is well formed. Every item needs its file, its root
import and matching metadata, with exactly one open target. Lean then checks
the built environment against the manifest, so run `lake build` in `lean/`
first. Source faithfulness needs separate review.

```bash
reuf2f dataset check .
reuf2f dataset check ~/ReuF2F
```

### `reuf2f dataset build TASK_REPO`

Compile the checkout into `test.jsonl`. The checkout is checked
first; a malformed tree is not compiled. Exporting the refutations runs Lean on
the host.

```bash
reuf2f dataset build .
reuf2f dataset build ~/ReuF2F -o /tmp/reuf2f
```

| Option | Meaning | Default |
| --- | --- | --- |
| `-i`, `--instance TEXT` | Only these instances (repeatable) | All |
| `-o`, `--out TEXT` | Where to write the `.jsonl` | `TASK_REPO` |
