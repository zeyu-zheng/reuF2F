"""`reuf2f eval` and `reuf2f report`."""

from pathlib import Path
from typing import Optional

import typer

from reuf2f.task.repo import resolve_repo

DATASET_ARG = typer.Argument(
    ...,
    metavar="DATASET",
    help="Dataset .jsonl built by reuf2f dataset build.",
)


def eval_command(
    ctx: typer.Context,
    dataset: str = DATASET_ARG,
    predictions: Optional[str] = typer.Option(
        None, "-p", "--predictions", help="Path to a predictions .json/.jsonl"
    ),
    run_id: str = typer.Option("run", "-r", "--run-id", help="Names the log directory"),
    instance_ids: Optional[list[str]] = typer.Option(
        None, "-i", "--instance", help="Limit to these instances (repeatable)"
    ),
    workers: int = typer.Option(
        4, "-j", "--workers", help="Instances evaluated in parallel"
    ),
    timeout: int = typer.Option(7200, "-t", "--timeout", help="Per-instance seconds"),
    repo: Optional[Path] = typer.Option(None, "--repo", help="Trusted Lean checkout."),
):
    """Evaluate model predictions and save reports under logs/evaluation/RUN_ID."""
    if not predictions:
        raise typer.BadParameter("pass --predictions <path>")

    from reuf2f.harness.run_evaluation import main as run_evaluation

    run_evaluation(
        dataset_name=dataset,
        instance_ids=list(instance_ids) if instance_ids else None,
        predictions_path=predictions,
        max_workers=workers,
        run_id=run_id,
        timeout=timeout,
        rewrite_reports=False,
        repo=resolve_repo(repo or ctx.obj.get("repo")),
    )


def report_command(
    ctx: typer.Context,
    run_id: str = typer.Argument(..., help="Run id to re-grade"),
    dataset: Optional[str] = typer.Option(
        None,
        "-d",
        "--dataset",
        help="Dataset the run used; taken from the run if omitted",
    ),
    instance_ids: Optional[list[str]] = typer.Option(None, "-i", "--instance"),
    repo: Optional[Path] = typer.Option(None, "--repo", help="Trusted Lean checkout."),
):
    """Re-grade saved test output, without launching Lean or Comparator."""
    from reuf2f.harness.run_evaluation import main as run_evaluation
    from reuf2f.harness.run_evaluation import read_run_metadata

    recorded = read_run_metadata(run_id) or {}
    if dataset is None:
        if not recorded.get("dataset"):
            typer.echo(
                f"Run {run_id!r} did not record which dataset it used, so pass -d. "
                "Runs made before this was added have no record of it.",
                err=True,
            )
            raise typer.Exit(1)
        dataset = recorded["dataset"]

    run_evaluation(
        dataset_name=dataset,
        instance_ids=list(instance_ids) if instance_ids else None,
        predictions_path=None,
        max_workers=1,
        run_id=run_id,
        timeout=7200,
        rewrite_reports=True,
        repo=resolve_repo(repo or ctx.obj.get("repo") or recorded.get("repo")),
    )
