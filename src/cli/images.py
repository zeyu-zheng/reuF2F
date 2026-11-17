"""`reuf2f images` — build and push shared environment images."""

import typer

images_app = typer.Typer(
    name="images",
    help="Build and push shared environment images from a recipe root.",
    no_args_is_help=True,
    context_settings={"help_option_names": ["-h", "--help"]},
)


@images_app.command("build")
def build(
    task_repo: str = typer.Argument(
        ..., metavar="TASK_REPO", help="Recipe root containing tags/ (e.g. ./docker)."
    ),
    dry_run: bool = typer.Option(
        False, "--dry-run", help="Create the build snapshot without running Docker."
    ),
):
    """Build the shared images ahead of an evaluation, from a recipe root.

    Builds every tags/<version>/ recipe locally and does not push it.

    [yellow][bold]Examples:[/bold][/yellow]

        reuf2f images build ./docker

        reuf2f images build ./docker --dry-run
    """
    from reuf2f.image_builder.docker_build import BuildImageError, build_image
    from reuf2f.image_builder.image_spec import load_image_specs

    try:
        for image_spec in load_image_specs(task_repo):
            build_image(image_spec, dry_run=dry_run)
            if not dry_run:
                typer.echo(f"Built {image_spec.name} locally; not pushed.")
    except (BuildImageError, OSError, ValueError) as e:
        typer.echo(str(e), err=True)
        raise typer.Exit(1) from e


@images_app.command("push")
def push(
    task_repo: str = typer.Argument(
        ..., metavar="TASK_REPO", help="Recipe root containing tags/ (e.g. ./docker)."
    ),
    dry_run: bool = typer.Option(False, "--dry-run", help="Show what would be pushed."),
):
    """Push each shared image to the registry, under the name its task.yaml declares.

    The dataset tells the harness which image to pull, so the pushed name has to
    match.

    [yellow][bold]Examples:[/bold][/yellow]

        reuf2f images push ./docker --dry-run

        reuf2f images push ./docker
    """
    from reuf2f.image_builder.docker_build import push_image
    from reuf2f.image_builder.image_spec import load_image_specs

    try:
        for image_spec in load_image_specs(task_repo):
            push_image(image_spec, dry_run=dry_run)
            if not dry_run:
                typer.echo(f"Pushed {image_spec.name}.")
    except (RuntimeError, OSError, ValueError) as e:
        typer.echo(str(e), err=True)
        raise typer.Exit(1) from e
