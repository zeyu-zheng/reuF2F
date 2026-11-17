# Evaluation Guide

This guide explains how to evaluate model predictions on reuF2F tasks.

## Overview

ReuF2F evaluates models by applying their generated patches to the task's Lean file and checking the result with [Comparator](https://github.com/leanprover/comparator). A task is resolved when either the original theorem (the proof) or its full negation `<declaration>_neg` (the refutation) is accepted. The evaluation is performed in a fresh Docker container per task to ensure consistent results across different platforms.

Predictions come from a solver of your choice and must follow the [prediction format](#prediction-format) below.

## Basic Evaluation

The main entry point for evaluation is `reuf2f eval`:

```bash
reuf2f eval test.jsonl \
    -p <path_to_predictions> \
    -j 4 \
    --run-id my_evaluation_run
```

`DATASET` is a local `.json` or `.jsonl` file built by `reuf2f dataset build`, such as the `test.jsonl` at the repository root. The command needs the trusted reuF2F checkout: run it inside the checkout or pass `--repo`. See the [CLI reference](../reference/cli.md) for every option.

## Prediction Format

Your predictions should be in JSONL format, with each line containing a JSON object with the following fields:

```json
{
  "instance_id": "abebe2019conjectural",
  "model_name_or_path": "your-model-name",
  "model_patch": "the patch content as a string"
}
```

Example:

```json
{"instance_id": "abebe2019conjectural", "model_name_or_path": "my-agent", "model_patch": "diff --git a/abebe2019conjectural.lean b/abebe2019conjectural.lean\n..."}
```

A `.json` file may instead hold a list of these objects or a mapping from instance ID to object. Patch paths are relative to the task project, whose task file is `<instance_id>.lean`. If an ID appears twice, the last record is used. Every prediction ID must be in the dataset. Empty or `null` patches are not run.

## Advanced Evaluation Options

### Evaluating Specific Instances

To evaluate only specific instances, repeat `-i`:

```bash
reuf2f eval test.jsonl -p <path_to_predictions> \
    -i abebe2019conjectural -i allen2018non -j 2
```

### Timeouts

`-t` (default `7200` seconds) limits each task's `eval.sh`, in which both Comparator checks run concurrently. Container startup and patch application are outside it. When it expires, the harness stops the script, saves the output to `test_output.txt` with a `Timeout error` line, and writes no `report.json`.

### Result Caching

The evaluation harness caches results by `run_id`, model name and `instance_id`. If an instance already has a `report.json` under the run, it is skipped, even with a different patch. Instances without a report, including those whose patch failed to apply or that timed out, run again when you repeat the command.

**Important**: If you want to re-evaluate an instance with a different patch, you must use a different `run_id` or delete that instance's `report.json`.

### Regenerating Reports

`reuf2f report` re-grades saved test output without running Lean or Comparator:

```bash
reuf2f report my_evaluation_run
reuf2f report my_evaluation_run -d test.jsonl -i abebe2019conjectural
```

It reads the predictions snapshot and dataset path recorded by the run; `-d` supplies the dataset if it moved. Only instances with a `test_output.txt` are re-graded, and their `report.json` files are overwritten. The Docker daemon must still be reachable.

## Understanding Evaluation Results

A run writes two things, both under `logs/evaluation/<run_id>/`, relative to the current directory.

A summary, `results.json`, together with `run.json` (the dataset path, checkout and creation time) and `predictions.json` (the predictions snapshot used by `reuf2f report`).

A folder per instance, at `logs/evaluation/<run_id>/<model>/<instance_id>/`, where `/` in the model name becomes `__`:

| File | What it holds |
| --- | --- |
| `report.json` | The result for that one instance |
| `test_output.txt` | Everything `eval.sh` printed |
| `run_instance.log` | What the harness did, and why it stopped if it failed |
| `eval.sh` | The script that ran Comparator |
| `patch.diff` | The patch that was applied |

`test_output.txt` contains, between the `>>>>> Start Test Output` and `>>>>> End Test Output` markers, both Comparator logs and then one status line per direction, such as `PASSED proof` or `FAILED refutation`. The harness parses the status lines inside the markers. A task whose proof passes has a report like:

```json
{
    "abebe2019conjectural": {
        "patch_is_None": false,
        "patch_exists": true,
        "patch_successfully_applied": true,
        "resolved": true,
        "infra_failure": false,
        "tests_status": {
            "proof": "PASSED",
            "refutation": "FAILED"
        }
    }
}
```

`patch_successfully_applied` is true only when the status lines were found. Without them the task is unresolved, and a recognized environment fault in the output sets `infra_failure` and `infra_failure_reason`.

### What the counts mean

| Field | Meaning |
| --- | --- |
| `total_instances` | Tasks in the dataset you chose (after `-i`) |
| `submitted_instances` | Predictions in the file |
| `completed_instances` | Instances that produced a `report.json` |
| `incomplete_ids` | In the dataset, but you gave no prediction for them |
| `resolved_instances` | The proof or the refutation was accepted |
| `unresolved_instances` | A report exists, but neither direction was accepted |
| `empty_patch_instances` | The prediction was empty, so nothing ran |
| `error_instances` | No valid `report.json` could be produced |
| `infra_failure_instances` | Failed for an environment reason, such as an unreachable Docker daemon |
| `ambiguous_failure_instances` | Failed for a reason that could be the environment or the patch, such as a timeout |
| `unstopped_containers`, `unremoved_images` | Docker leftovers, not results; the shared image is expected to remain |

The score is `resolved_instances / total_instances`. The two failure counts are also counted inside unresolved and errors, so they never remove anything from the total. Their reasons are in `failure_reasons`.

### Why "ran successfully" can disagree with the error count

While a run is going you see a line like `40 ran successfully, 0 failed`. That counts crashes in the harness. A failed evaluation is not a crash: the harness catches the problem, writes it to the log, and carries on.

`error_instances` counts something else: instances with no valid `report.json`. The usual causes are a patch that did not apply, a container that did not start, or a run that timed out.

So `0 failed` together with `error_instances: 1` means nothing crashed, and one instance could not be graded. Read that instance's `run_instance.log` to see why.

## How Grading Works

The harness commits the task file `<instance_id>.lean` and the image's project configuration as a baseline in `/testbed`, then applies the patch with `git apply`, falling back to `--3way`, `--reject` and `patch --fuzz=5`. It then runs `eval.sh`, which:

1. restores `lean-toolchain` and `lake-manifest.json` from the baseline and deletes any submitted `lakefile.lean`;
2. copies the patched project to `/eval/proof` and `/eval/refutation`;
3. writes the trusted challenge as `Challenge.lean` into each copy, registers it as a library, and writes each direction's Comparator `config.json`;
4. runs both Comparator checks concurrently and prints a status line for each from Comparator's exit code.

Comparator checks that the submitted theorem matches the challenge statement and definitions, that its proof uses only the axioms `propext`, `Quot.sound` and `Classical.choice`, and that both the Lean kernel and nanoda accept it. Either accepted direction resolves the task.

## Troubleshooting

If you encounter issues during evaluation:

1. Check the Docker setup ([Docker Setup Guide](docker_setup.md)) and run `pytest -rs tests/test_cli.py::test_one_instance`
2. Verify that your predictions file is correctly formatted
3. Examine `run_instance.log`, `patch.diff` and `test_output.txt` under `logs/evaluation/`
4. Try reducing the number of workers with `-j`, or raise `-t`
5. Set `REUF2F_DOCKER_TIMEOUT` (default `1800`) or `REUF2F_DOCKER_POOL_SIZE` (default `128`) if Docker API calls time out or the connection pool is exhausted
