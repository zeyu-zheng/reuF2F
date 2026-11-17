"""Main CLI entry point. Defines the top-level app and wires the sub-apps."""

import logging
from pathlib import Path
from typing import Optional

import typer

_PANEL_EVAL = "Evaluate"
_PANEL_IMAGES = "Images"
_PANEL_DATA = "Datasets"

app = typer.Typer(
    name="reuf2f",
    help="""ReuF2F - evaluate submitted Git patches on open Lean problems.

[yellow][not dim][bold]Examples:[/bold][/not dim][/yellow]

    reuf2f eval data/test.jsonl -p preds.jsonl --run-id experiment -j 4
    reuf2f report experiment -d data/test.jsonl
    reuf2f images build ./docker
    reuf2f dataset check .
    reuf2f dataset build . -o data
""",
    no_args_is_help=True,
    pretty_exceptions_enable=False,
    add_completion=False,
    context_settings={"help_option_names": ["-h", "--help"]},
)


@app.callback()
def _global_options(
    ctx: typer.Context,
    verbose: bool = typer.Option(False, "-v", "--verbose", help="Enable DEBUG logging"),
    repo: Optional[Path] = typer.Option(
        None,
        "--repo",
        help="Trusted Lean checkout; defaults to current-directory ancestors.",
    ),
) -> None:
    if verbose:
        logging.getLogger("reuf2f").setLevel(logging.DEBUG)
        logging.basicConfig(level=logging.DEBUG)
    ctx.ensure_object(dict)
    ctx.obj["repo"] = repo


def main():
    app()


from reuf2f.cli.dataset import dataset_app  # noqa: E402
from reuf2f.cli.evaluate import eval_command, report_command  # noqa: E402
from reuf2f.cli.images import images_app  # noqa: E402

app.command("eval", rich_help_panel=_PANEL_EVAL)(eval_command)
app.command("report", rich_help_panel=_PANEL_EVAL)(report_command)
app.add_typer(images_app, name="images", rich_help_panel=_PANEL_IMAGES)
app.add_typer(dataset_app, name="dataset", rich_help_panel=_PANEL_DATA)
