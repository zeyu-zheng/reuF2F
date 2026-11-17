#!/bin/bash --login

set -euo pipefail

DOCKER_ENV_PYTHON_VERSION=${DOCKER_ENV_PYTHON_VERSION:-}
DOCKER_ENV_NODE_VERSION=${DOCKER_ENV_NODE_VERSION:-}
DOCKER_ENV_RUBY_VERSION=${DOCKER_ENV_RUBY_VERSION:-}
DOCKER_ENV_RUST_VERSION=${DOCKER_ENV_RUST_VERSION:-}
DOCKER_ENV_GO_VERSION=${DOCKER_ENV_GO_VERSION:-}
DOCKER_ENV_SWIFT_VERSION=${DOCKER_ENV_SWIFT_VERSION:-}
DOCKER_ENV_PHP_VERSION=${DOCKER_ENV_PHP_VERSION:-}
DOCKER_ENV_JAVA_VERSION=${DOCKER_ENV_JAVA_VERSION:-}

echo "Configuring language runtimes..."

if [ -n "${DOCKER_ENV_PYTHON_VERSION}" ]; then
  echo "# Python: ${DOCKER_ENV_PYTHON_VERSION}"
  pyenv global "${DOCKER_ENV_PYTHON_VERSION}"
  python3 --version
fi

if [ -n "${DOCKER_ENV_NODE_VERSION}" ]; then
  current=$(node -v | cut -d. -f1) # ==> v20
  echo "# Node.js: v${DOCKER_ENV_NODE_VERSION} (default: ${current})"
  if [ "${current}" != "v${DOCKER_ENV_NODE_VERSION}" ]; then
    nvm alias default "${DOCKER_ENV_NODE_VERSION}"
    nvm use --save "${DOCKER_ENV_NODE_VERSION}"
    corepack enable
  fi
fi

if [ -n "${DOCKER_ENV_RUBY_VERSION}" ]; then
  current=$(ruby -v | cut -d' ' -f2 | cut -d'p' -f1) # ==> 3.2.3
  echo "# Ruby: ${DOCKER_ENV_RUBY_VERSION} (default: ${current})"
  if [ "${current}" != "${DOCKER_ENV_RUBY_VERSION}" ]; then
    mise use --global "ruby@${DOCKER_ENV_RUBY_VERSION}"
    ruby --version
  fi
fi

if [ -n "${DOCKER_ENV_RUST_VERSION}" ]; then
  current=$(rustc --version | awk '{print $2}') # ==> 1.86.0
  echo "# Rust: ${DOCKER_ENV_RUST_VERSION} (default: ${current})"
  if [ "${current}" != "${DOCKER_ENV_RUST_VERSION}" ]; then
    rustup default "${DOCKER_ENV_RUST_VERSION}"
    rustc --version
  fi
fi

if [ -n "${DOCKER_ENV_GO_VERSION}" ]; then
  current=$(go version | awk '{print $3}') # ==> go1.23.8
  echo "# Go: go${DOCKER_ENV_GO_VERSION} (default: ${current})"
  if [ "${current}" != "go${DOCKER_ENV_GO_VERSION}" ]; then
    mise use --global "go@${DOCKER_ENV_GO_VERSION}"
    go version
  fi
fi

if [ -n "${DOCKER_ENV_SWIFT_VERSION}" ]; then
  current=$(swift --version | sed -n 's/^Swift version \([0-9]\+\.[0-9]\+\).*/\1/p') # ==> 6.2
  echo "# Swift: ${DOCKER_ENV_SWIFT_VERSION} (default: ${current})"
  if [ "${current}" != "${DOCKER_ENV_SWIFT_VERSION}" ]; then
    swiftly use "${DOCKER_ENV_SWIFT_VERSION}"
    swift --version
  fi
fi

if [ -n "${DOCKER_ENV_PHP_VERSION}" ]; then
  current=$(php -r 'echo PHP_MAJOR_VERSION.".".PHP_MINOR_VERSION;')
  echo "# PHP: ${DOCKER_ENV_PHP_VERSION} (default: ${current})"
  if [ "${current}" != "${DOCKER_ENV_PHP_VERSION}" ]; then
    phpenv global "${DOCKER_ENV_PHP_VERSION}snapshot"
    php --version
  fi
fi

if [ -n "${DOCKER_ENV_JAVA_VERSION}" ]; then
  current=$(java -version 2>&1 | awk -F'[ ."]+' '/version/ {print $3}')
  echo "# Java: ${DOCKER_ENV_JAVA_VERSION} (default: ${current})"
  if [ "${current}" != "${DOCKER_ENV_JAVA_VERSION}" ]; then
    mise use --global "java@${DOCKER_ENV_JAVA_VERSION}"
    java -version
  fi
fi

exec "$@"
