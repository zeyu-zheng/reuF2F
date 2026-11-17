from __future__ import annotations

import docker


def list_images(client: docker.DockerClient):
    """
    List all images from the Docker client.
    """
    # don't use this in multi-threaded context
    return {tag for i in client.images.list(all=True) for tag in i.tags}
