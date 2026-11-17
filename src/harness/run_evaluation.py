from __future__ import annotations

import docker
import json
from datetime import datetime, timezone
import os
import traceback

from pathlib import Path, PurePosixPath

from reuf2f.harness.constants import (
    APPLY_PATCH_FAIL,
    APPLY_PATCH_PASS,
    CONTAINER_PATCH_FILE,
    CONTAINER_USER,
    CONTAINER_WORKDIR,
    LOG_REPORT,
    LOG_RUN_METADATA,
    LOG_INSTANCE,
    LOG_TEST_OUTPUT,
    RUN_EVALUATION_LOG_DIR,
)
from reuf2f.harness.docker_utils import (
    cleanup_container,
    copy_to_container,
    exec_run_with_timeout,
)
import logging
from reuf2f.harness.comparator import make_eval_script
from reuf2f.harness.grading import get_eval_report
from reuf2f.harness.reporting import make_run_report
from reuf2f.types import TestSpec
from reuf2f.harness.utils import make_test_spec
from reuf2f.task.lean import workspace_config
from reuf2f.harness.utils import (
    EvaluationError,
    load_reuf2f_dataset,
    get_predictions_from_file,
    run_threadpool,
    setup_repo,
)

from reuf2f.logger import setup_logger, close_logger

GIT_APPLY_CMDS = [
    "git apply --verbose",
    "git apply --verbose --3way",
    "git apply --verbose --reject",
    "patch --batch --forward --fuzz=5 -p1 -i",
]

DOCKER_CLIENT_TIMEOUT = int(os.environ.get("REUF2F_DOCKER_TIMEOUT", "1800"))
DOCKER_CLIENT_POOL_SIZE = int(os.environ.get("REUF2F_DOCKER_POOL_SIZE", "128"))


def _docker_client() -> docker.DockerClient:
    return docker.from_env(
        timeout=DOCKER_CLIENT_TIMEOUT,
        max_pool_size=DOCKER_CLIENT_POOL_SIZE,
    )


def create_container(
    test_spec: TestSpec,
    client: docker.DockerClient,
    run_id: str,
    logger: logging.Logger,
):
    """
    Creates a container from an instance image for running evaluation.

    Args:
        test_spec (TestSpec): Test spec with evaluation details
        client (docker.DockerClient): Docker client for creating the container
        run_id (str): Run ID identifying process, used for the container name
        logger (logging.Logger): Logger to use for logging the creation process
    """
    container = None
    try:
        # Check if the image exists
        try:
            client.images.get(test_spec.image)
        except docker.errors.ImageNotFound:
            try:
                logger.info("Image not found locally, attempting to pull...")
                client.images.pull(test_spec.image)
            except docker.errors.ImageNotFound:
                raise EvaluationError(
                    test_spec.instance_id,
                    f"Image {test_spec.image} not found for {test_spec.instance_id}",
                    logger,
                )

        logger.info(f"Creating container for {test_spec.instance_id}...")

        container_name = f"reuf2f.eval.{test_spec.instance_id.lower()}.{run_id}"
        # Remove any existing container with this name (handles ghost containers)
        try:
            old = client.containers.get(container_name)
            old.remove(force=True)
            logger.info(f"Removed existing container {container_name}")
        except docker.errors.NotFound:
            pass
        except Exception:
            pass
        try:
            container = client.containers.create(
                image=test_spec.image,
                name=container_name,
                user=CONTAINER_USER,
                detach=True,
                command="tail -f /dev/null",
            )
        except docker.errors.APIError as e:
            if "409" in str(e) or "Conflict" in str(e):
                # Ghost container — use a unique suffix
                import time

                container_name = f"{container_name}.{int(time.time())}"
                logger.info(f"Retrying with unique name: {container_name}")
                container = client.containers.create(
                    image=test_spec.image,
                    name=container_name,
                    user=CONTAINER_USER,
                    detach=True,
                    command="tail -f /dev/null",
                )
            else:
                raise
        logger.info(f"Container for {test_spec.instance_id} created: {container.id}")
        return container
    except Exception as e:
        logger.error(f"Error creating container for {test_spec.instance_id}: {e}")
        logger.info(traceback.format_exc())
        cleanup_container(client, container, logger)
        raise EvaluationError(test_spec.instance_id, str(e), logger) from e


def run_instance(
    test_spec: TestSpec,
    pred: dict,
    client: docker.DockerClient,
    run_id: str,
    timeout: int | None = None,
    rewrite_reports: bool = False,
):
    """
    Run a single instance with the given prediction.

    Args:
        test_spec (TestSpec): TestSpec instance with pre-built image
        pred (dict): Prediction w/ model_name_or_path, model_patch, instance_id
        client (docker.DockerClient): Docker client
        run_id (str): Run ID
        timeout (int): Timeout for running tests
        rewrite_reports (bool): True if eval run is just to reformat existing report
    """
    # Set up logging directory
    instance_id = test_spec.instance_id
    model_name_or_path = pred.get("model_name_or_path", "None").replace("/", "__")
    log_dir = RUN_EVALUATION_LOG_DIR / run_id / model_name_or_path / instance_id

    # Set up report file
    report_path = log_dir / LOG_REPORT
    if rewrite_reports:
        test_output_path = log_dir / LOG_TEST_OUTPUT
        if not test_output_path.exists():
            raise ValueError(f"Test output file {test_output_path} does not exist")
        report = get_eval_report(
            test_spec=test_spec,
            prediction=pred,
            test_log_path=test_output_path,
            include_tests_status=True,
        )
        # Write report to report.json
        with open(report_path, "w") as f:
            f.write(json.dumps(report, indent=4))
        return instance_id, report
    if report_path.exists():
        return instance_id, json.loads(report_path.read_text())

    # Set up logger
    log_dir.mkdir(parents=True, exist_ok=True)
    log_file = log_dir / LOG_INSTANCE
    logger = setup_logger(instance_id, log_file)

    # Run the instance
    container = None
    try:
        # Create container from image
        container = create_container(test_spec, client, run_id, logger)
        container.start()
        logger.info(f"Container for {instance_id} started: {container.id}")

        # Shared image: commit the task baseline an instance image would contain
        baseline = {
            **workspace_config(test_spec.repo, (test_spec.instance_id,)),
            test_spec.source_file: test_spec.challenge.encode(),
        }
        setup_repo(container, baseline)

        # Copy model prediction as patch file to container
        patch_file = Path(log_dir / "patch.diff")
        patch_file.write_text(pred["model_patch"] or "")
        logger.info(
            f"Intermediate patch for {instance_id} written to {patch_file}, now applying to container..."
        )
        copy_to_container(container, patch_file, PurePosixPath(CONTAINER_PATCH_FILE))

        # Attempt to apply patch to container
        applied_patch = False
        for attempt, git_apply_cmd in enumerate(GIT_APPLY_CMDS):
            if attempt:
                # a failed attempt (notably --reject) leaves partial state behind,
                # which makes every later command fail; restart from a pristine tree
                container.exec_run(
                    ["/bin/bash", "-c", "git checkout -- . ; git clean -fd"],
                    workdir=CONTAINER_WORKDIR,
                    user=CONTAINER_USER,
                )
            val = container.exec_run(
                f"{git_apply_cmd} {CONTAINER_PATCH_FILE}",
                workdir=CONTAINER_WORKDIR,
                user=CONTAINER_USER,
            )
            if val.exit_code == 0:
                logger.info(f"{APPLY_PATCH_PASS}:\n{val.output.decode('utf-8')}")
                applied_patch = True
                break
            else:
                logger.info(f"Failed to apply patch to container: {git_apply_cmd}")
        if not applied_patch:
            # the chain can leave the patch fully applied while each command still exited non-zero
            reverse_check = container.exec_run(
                f"git apply --check --reverse {CONTAINER_PATCH_FILE}",
                workdir=CONTAINER_WORKDIR,
                user=CONTAINER_USER,
            )
            if reverse_check.exit_code == 0:
                logger.info(f"{APPLY_PATCH_PASS}: verified already applied")
                applied_patch = True
        if not applied_patch:
            logger.info(f"{APPLY_PATCH_FAIL}:\n{val.output.decode('utf-8')}")
            raise EvaluationError(
                instance_id,
                f"{APPLY_PATCH_FAIL}:\n{val.output.decode('utf-8')}",
                logger,
            )

        # Get git diff before running eval script
        git_diff_output_before = (
            container.exec_run(
                "git -c core.fileMode=false diff", workdir=CONTAINER_WORKDIR
            )
            .output.decode("utf-8")
            .strip()
        )
        logger.info(f"Git diff before:\n{git_diff_output_before}")

        eval_file = Path(log_dir / "eval.sh")
        eval_file.write_text(
            make_eval_script(
                test_spec.challenge, test_spec.instance_id, test_spec.declaration
            )
        )
        logger.info(
            f"Eval script for {instance_id} written to {eval_file}; copying to container..."
        )
        copy_to_container(container, eval_file, PurePosixPath("/eval.sh"))

        # Run eval script, write output to logs
        test_output, timed_out, total_runtime = exec_run_with_timeout(
            container, "/bin/bash /eval.sh", timeout
        )
        test_output_path = log_dir / LOG_TEST_OUTPUT
        logger.info(f"Test runtime: {total_runtime:_.2f} seconds")
        with open(test_output_path, "w") as f:
            f.write(test_output)
            logger.info(f"Test output for {instance_id} written to {test_output_path}")
            if timed_out:
                f.write(f"\n\nTimeout error: {timeout} seconds exceeded.")
                raise EvaluationError(
                    instance_id,
                    f"Test timed out after {timeout} seconds.",
                    logger,
                )

        # Get git diff after running eval script (ignore permission changes)
        git_diff_output_after = (
            container.exec_run(
                "git -c core.fileMode=false diff", workdir=CONTAINER_WORKDIR
            )
            .output.decode("utf-8")
            .strip()
        )

        # Check if git diff changed after running eval script
        logger.info(f"Git diff after:\n{git_diff_output_after}")
        if git_diff_output_after != git_diff_output_before:
            logger.info("Git diff changed after running eval script")

        # Get report from test output
        logger.info(f"Grading answer for {instance_id}...")
        report = get_eval_report(
            test_spec=test_spec,
            prediction=pred,
            test_log_path=test_output_path,
            include_tests_status=True,
        )
        logger.info(
            f"report: {report}\n"
            f"Result for {instance_id}: resolved: {report[instance_id]['resolved']}"
        )

        # Write report to report.json
        with open(report_path, "w") as f:
            f.write(json.dumps(report, indent=4))
        return instance_id, report
    except EvaluationError as e:
        error_msg = traceback.format_exc()
        logger.info(error_msg)
        print(e)
    except Exception as e:
        error_msg = (
            f"Error in evaluating model for {instance_id}: {e}\n"
            f"{traceback.format_exc()}\n"
            f"Check ({logger.log_file}) for more information."
        )
        logger.error(error_msg)
    finally:
        # Remove instance container + image, close logger
        cleanup_container(client, container, logger)
        close_logger(logger)
    return


def run_instances(
    predictions: dict,
    instances: list,
    max_workers: int,
    run_id: str,
    timeout: int,
    rewrite_reports: bool = False,
    repo: Path | None = None,
):
    """
    Run all instances for the given predictions in parallel.
    Expects instances to have pre-built images.

    Args:
        predictions (dict): Predictions dict generated by the model
        instances (list): List of instances with 'image' field
        max_workers (int): Maximum number of workers
        run_id (str): Run ID
        timeout (int): Timeout for running tests
        rewrite_reports (bool): True if eval run is just to reformat existing report
        repo (Path): Trusted reuF2F checkout
    """
    client = _docker_client()
    test_specs = [make_test_spec(instance, repo) for instance in instances]

    # run instances in parallel
    payloads = []
    for test_spec in test_specs:
        payloads.append(
            (
                test_spec,
                predictions[test_spec.instance_id],
                client,
                run_id,
                timeout,
                rewrite_reports,
            )
        )

    # run instances in parallel
    print(f"Running {len(instances)} instances...")
    run_threadpool(run_instance, payloads, max_workers)
    print("All instances run.")


def write_run_metadata(
    run_id: str,
    dataset_name: str,
    repo: Path,
    predictions: dict,
) -> Path:
    """Record what this run graded against.

    Re-grading needs the challenge and declaration, which live in the
    dataset, not in the run's logs. Without this a later `reuf2f report` has to
    be told the dataset again, and gets it wrong silently if told the wrong one.
    """
    path = RUN_EVALUATION_LOG_DIR / run_id / LOG_RUN_METADATA
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "dataset": dataset_name,
                "repo": str(repo),
                "created_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            },
            indent=2,
        )
        + "\n"
    )
    # there is no gold patch to re-grade with, so a re-grade reads the predictions back
    (path.parent / "predictions.json").write_text(
        json.dumps(predictions, indent=2) + "\n"
    )
    return path


def read_run_metadata(run_id: str) -> dict | None:
    """What a previous run graded against, if it recorded it."""
    path = RUN_EVALUATION_LOG_DIR / run_id / LOG_RUN_METADATA
    return json.loads(path.read_text()) if path.is_file() else None


def get_run_predictions(run_id: str) -> list[dict]:
    """The predictions snapshot a run recorded, so report needs no predictions file."""
    snapshot = RUN_EVALUATION_LOG_DIR / run_id / "predictions.json"
    if not snapshot.is_file():
        raise ValueError(f"run {run_id!r} recorded no predictions.json")
    return get_predictions_from_file(str(snapshot))


def get_dataset_from_preds(
    dataset_name: str,
    instance_ids: list | None,
    predictions: dict,
    run_id: str,
    rewrite_reports: bool,
    exclude_completed: bool = True,
):
    """
    Return only instances that have predictions and are in the dataset.
    If instance_ids is provided, only return instances with those IDs.
    If exclude_completed is True, only return instances that have not been run yet.
    """
    # load dataset
    dataset = load_reuf2f_dataset(dataset_name)
    dataset_ids = {i["instance_id"] for i in dataset}

    if instance_ids:
        # check that all instance IDs have predictions
        missing_preds = set(instance_ids) - set(predictions.keys())
        if missing_preds:
            print(
                f"Warning: Missing predictions for {len(missing_preds)} instance IDs."
            )

    # check that all prediction IDs are in the dataset
    prediction_ids = set(predictions.keys())
    if prediction_ids - dataset_ids:
        raise ValueError(
            (
                "Some prediction IDs not found in dataset!"
                f"\nMissing IDs:\n{' '.join(prediction_ids - dataset_ids)}"
            )
        )
    if instance_ids:
        dataset = [i for i in dataset if i["instance_id"] in instance_ids]

    if rewrite_reports:
        # we only return instances that have existing test outputs
        test_output_ids = set()
        for instance in dataset:
            if instance["instance_id"] not in predictions:
                continue
            prediction = predictions[instance["instance_id"]]
            test_output_file = (
                RUN_EVALUATION_LOG_DIR
                / run_id
                / prediction["model_name_or_path"].replace("/", "__")
                / prediction["instance_id"]
                / "test_output.txt"
            )
            if test_output_file.exists():
                test_output_ids.add(instance["instance_id"])
        dataset = [
            i
            for i in dataset
            if i["instance_id"] in prediction_ids
            and i["instance_id"] in test_output_ids
        ]
        return dataset

    # check which instance IDs have already been run
    completed_ids = set()
    for instance in dataset:
        if instance["instance_id"] not in prediction_ids:
            # skip instances without predictions
            continue
        prediction = predictions[instance["instance_id"]]
        report_file = (
            RUN_EVALUATION_LOG_DIR
            / run_id
            / prediction["model_name_or_path"].replace("/", "__")
            / prediction["instance_id"]
            / LOG_REPORT
        )
        if report_file.exists():
            completed_ids.add(instance["instance_id"])

    if completed_ids and exclude_completed:
        # filter dataset to only instances that have not been run
        print(f"{len(completed_ids)} instances already run, skipping...")
        dataset = [i for i in dataset if i["instance_id"] not in completed_ids]

    empty_patch_ids = {
        k
        for k, v in predictions.items()
        if v["model_patch"] == "" or v["model_patch"] is None
    }

    # filter dataset to only instances with predictions
    dataset = [
        i
        for i in dataset
        if i["instance_id"] in prediction_ids
        and i["instance_id"] not in empty_patch_ids
    ]
    return dataset


def main(
    dataset_name: str,
    instance_ids: list,
    predictions_path: str | None,
    max_workers: int,
    run_id: str,
    timeout: int,
    rewrite_reports: bool,
    repo: Path | None = None,
):
    """
    Run evaluation harness for the given dataset and predictions.
    """
    assert len(run_id) > 0, "Run ID must be provided"
    dataset_name = str(Path(dataset_name).expanduser().resolve())
    # load predictions as map of instance_id to prediction
    predictions = (
        get_run_predictions(run_id)
        if rewrite_reports
        else get_predictions_from_file(str(predictions_path))
    )
    predictions = {pred["instance_id"]: pred for pred in predictions}
    write_run_metadata(run_id, dataset_name, repo, predictions)

    # get dataset from predictions
    dataset = get_dataset_from_preds(
        dataset_name, instance_ids, predictions, run_id, rewrite_reports
    )
    full_dataset = load_reuf2f_dataset(dataset_name, instance_ids)

    client = _docker_client()

    if not dataset:
        print("No instances to run.")
        return make_run_report(predictions, full_dataset, run_id, client)
    else:
        # run instances (images assumed to be pre-built)
        run_instances(
            predictions,
            dataset,
            max_workers,
            run_id,
            timeout,
            rewrite_reports=rewrite_reports,
            repo=repo,
        )

    # make final report
    return make_run_report(predictions, full_dataset, run_id, client)
