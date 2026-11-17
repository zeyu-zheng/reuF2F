import logging
from pathlib import Path


def setup_logger(instance_id: str, log_file: Path):
    """
    Set up a logger for evaluation and build processes.

    This logger is used for logging the evaluation process, build process of images and containers,
    and other operations that require file-based logging.

    Args:
        instance_id: Unique identifier for the instance being processed
        log_file: Path to the log file where logs will be written

    Returns:
        logging.Logger: Configured logger instance with log_file attribute
    """
    logger_name = (
        f"{instance_id}.{log_file.name}"
    )
    logger = logging.getLogger(logger_name)
    log_file.parent.mkdir(parents=True, exist_ok=True)
    handler = logging.FileHandler(log_file, mode="w", encoding="utf-8")
    formatter = logging.Formatter("%(asctime)s - %(levelname)s - %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    setattr(logger, "log_file", log_file)
    logger.setLevel(logging.INFO)
    logger.propagate = False
    return logger


def close_logger(logger):
    """
    Close all handlers associated with a logger and remove them.

    Args:
        logger: The logger instance to close
    """
    for handler in logger.handlers[:]:
        handler.close()
        logger.removeHandler(handler)
