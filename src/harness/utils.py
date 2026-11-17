import json
import tempfile
import traceback

from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path, PurePosixPath
from tqdm import tqdm
from reuf2f.harness.constants import CONTAINER_WORKDIR
from reuf2f.harness.docker_utils import copy_to_container
from reuf2f.types import TestSpec
from reuf2f.utils import write_files


class EvaluationError(Exception):
    def __init__(self, instance_id, message, logger):
        super().__init__(message)
        self.super_str = super().__str__()
        self.instance_id = instance_id
        self.log_path = logger.log_file
        self.logger = logger

    def __str__(self):
        return (
            f"Error in evaluation for {self.instance_id}: {self.super_str}\n"
            f"Check ({self.log_path}) for more information."
        )


def get_predictions_from_file(predictions_path: str):
    if predictions_path.endswith(".json"):
        with open(predictions_path, "r") as f:
            predictions = json.load(f)
            if isinstance(predictions, dict):
                predictions = list(
                    predictions.values()
                )  # compatible with SWE-agent predictions
            if not isinstance(predictions, list):
                raise ValueError(
                    "Predictions must be a list[prediction] or a dictionary[instance_id: prediction]"
                )
    elif predictions_path.endswith(".jsonl"):
        with open(predictions_path, "r") as f:
            predictions = [json.loads(line) for line in f]
    else:
        raise ValueError("Predictions path must be .json or .jsonl")

    # Validate that each prediction has an instance_id
    for pred in predictions:
        if not isinstance(pred, dict):
            raise ValueError(f"Each prediction must be a dictionary, got {type(pred)}")
        if "instance_id" not in pred:
            raise ValueError(f"Each prediction must contain '{'instance_id'}'")

    return predictions


def run_threadpool(func, payloads, max_workers):
    if max_workers <= 0:
        return run_sequential(func, payloads)
    succeeded, failed = [], []
    with tqdm(total=len(payloads), smoothing=0) as pbar:
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            # Create a future for running each instance
            futures = {executor.submit(func, *payload): payload for payload in payloads}
            # Wait for each future to complete
            for future in as_completed(futures):
                try:
                    # Check if instance ran successfully
                    future.result()
                    succeeded.append(futures[future])
                except Exception as e:
                    print(f"{type(e)}: {e}")
                    traceback.print_exc()
                    failed.append(futures[future])
                # Update progress bar
                pbar.update(1)
                pbar.set_description(
                    f"{len(succeeded)} ran successfully, {len(failed)} failed"
                )
    return succeeded, failed


def run_sequential(func, args_list):
    """
    Run a function with a list of arguments sequentially
    """
    succeeded, failed = [], []
    pbar = tqdm(total=len(args_list), smoothing=0)
    for args in args_list:
        try:
            func(*args)
            succeeded.append(args)
        except Exception:
            traceback.print_exc()
            failed.append(args)
        pbar.update(1)
        pbar.set_description(f"{len(succeeded)} ran successfully, {len(failed)} failed")
    pbar.close()
    return succeeded, failed


def load_reuf2f_dataset(name: str, instance_ids: list | None = None) -> list[dict]:
    """
    Load reuF2F dataset from local .json/.jsonl file
    """
    # check that all instance IDs are in the dataset
    if instance_ids:
        instance_ids = set(instance_ids)
    # Load from local file
    if name.endswith(".json"):
        dataset = json.loads(Path(name).read_text())
    elif name.endswith(".jsonl"):
        dataset = [json.loads(line) for line in Path(name).read_text().splitlines()]
    else:
        raise ValueError(f"Dataset must be a local .json or .jsonl file: {name}")
    dataset_ids = {instance["instance_id"] for instance in dataset}
    if instance_ids:
        if instance_ids - dataset_ids:
            raise ValueError(
                (
                    "Some instance IDs not found in dataset!"
                    f"\nMissing IDs:\n{' '.join(instance_ids - dataset_ids)}"
                )
            )
        dataset = [
            instance for instance in dataset if instance["instance_id"] in instance_ids
        ]
    return dataset


def make_test_spec(instance: dict, repo: Path) -> TestSpec:
    """
    Build a TestSpec from a dataset instance.

    The instance dict must contain: instance_id, challenge, declaration, image,
    log_parser.
    """
    return TestSpec(
        instance_id=instance["instance_id"],
        repo=repo,
        challenge=instance["challenge"],
        declaration=instance["declaration"],
        image=instance["image"],
        log_parser=instance["log_parser"],
    )


def setup_repo(container, baseline: dict[str, bytes]) -> None:
    """Commit the task baseline in the image project, as an instance image would."""
    with tempfile.TemporaryDirectory(prefix="reuf2f-baseline-") as tmp:
        write_files(Path(tmp), baseline)
        # One archive per file: a directory entry would chown the image's /testbed.
        for name in baseline:
            copy_to_container(
                container, Path(tmp) / name, PurePosixPath(CONTAINER_WORKDIR) / name
            )
    val = container.exec_run(
        [
            "/bin/bash",
            "-c",
            "git init -q && git add . && git -c user.name=reuf2f "
            "-c user.email=reuf2f@invalid commit -qm baseline",
        ],
        workdir=CONTAINER_WORKDIR,
    )
    if val.exit_code != 0:
        raise RuntimeError(
            f"cannot initialize baseline: {val.output.decode(errors='replace')}"
        )
