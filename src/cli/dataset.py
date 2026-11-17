"""`reuf2f dataset` — build and check the benchmark dataset."""

from typing import Optional

import typer


def _list(values) -> list[str] | None:
    return list(values) if values else None


def _fail(error: Exception) -> int:
    typer.echo(str(error), err=True)
    return 1


dataset_app = typer.Typer(
    name="dataset",
    help="Build and check the benchmark dataset.",
    no_args_is_help=True,
    context_settings={"help_option_names": ["-h", "--help"]},
)


@dataset_app.command("build")
def build(
    task_repo: str = typer.Argument(
        ..., metavar="TASK_REPO", help="Path to the reuF2F checkout"
    ),
    instance_ids: Optional[list[str]] = typer.Option(
        None, "-i", "--instance", help="Only these instances (repeatable)"
    ),
    out: Optional[str] = typer.Option(
        None, "-o", "--out", help="Where to write the .jsonl (default: TASK_REPO)"
    ),
):
    """Compile the checkout into test.jsonl.

    Reads only the checkout, so what you get is what the tree says. The checkout
    is checked first; a malformed tree is not compiled. Exporting the refutations
    runs Lean on the host.

    [yellow][bold]Examples:[/bold][/yellow]

        reuf2f dataset build .

        reuf2f dataset build ~/ReuF2F -o /tmp/reuf2f
    """
    from reuf2f.task.prepare import CheckFailed, write_dataset

    try:
        path = write_dataset(task_repo, out or task_repo, _list(instance_ids))
    except (CheckFailed, ValueError, RuntimeError) as e:
        raise typer.Exit(_fail(e)) from e
    typer.echo(f"test: {path}")


@dataset_app.command("check")
def check(
    task_repo: str = typer.Argument(
        ..., metavar="TASK_REPO", help="Path to the reuF2F checkout"
    ),
):
    """Check that the checkout is well formed.

    Every item needs its file, its root import and matching metadata, with exactly
    one open target. Lean then checks the built environment against the manifest,
    so run `lake build` in lean/ first. Source faithfulness needs separate review.

    [yellow][bold]Examples:[/bold][/yellow]

        reuf2f dataset check .

        reuf2f dataset check ~/ReuF2F
    """
    from reuf2f.task.checks import check_task_repo, errors

    problems = check_task_repo(task_repo)
    for problem in problems:
        typer.echo(str(problem))
    blocking = errors(problems)
    if blocking:
        typer.echo(
            f"\n{len(blocking)} error(s), {len(problems) - len(blocking)} warning(s)"
        )
        raise typer.Exit(1)
    typer.echo(f"{task_repo} looks well formed")
