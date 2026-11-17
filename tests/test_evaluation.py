import json
import docker

from reuf2f.harness.run_evaluation import make_run_report

TEST_INSTANCE = {"instance_id": "test"}


def test_make_run_report(tmpdir) -> None:
    client = docker.from_env()
    with tmpdir.as_cwd():
        output_path = make_run_report(
            {"test": {"instance_id": "test", "model_name_or_path": "test"}},
            [TEST_INSTANCE],
            "test",
            client,
        )
        assert output_path.is_file()
        report = json.loads(output_path.read_text())
        assert report["schema_version"] == 2
