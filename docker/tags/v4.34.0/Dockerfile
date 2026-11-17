FROM ghcr.io/openai/codex-universal:latest

# Install Lean
WORKDIR /testbed
COPY lean-toolchain ./lean-toolchain

RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain "$(cat lean-toolchain)"

ENV PATH="/root/.elan/bin:${PATH}"

# Prepare Lean workspace
COPY lakefile.toml ./lakefile.toml

RUN toolchain="$(cat lean-toolchain)" && \
    lake update && \
    test "$(cat lean-toolchain)" = "$toolchain" && \
    lake exe cache get && \
    lake build Mathlib

# Build the Comparator tag matching this project's Lean toolchain.
RUN toolchain="$(cat lean-toolchain)" && \
    git clone --depth 1 --branch "${toolchain##*:}" https://github.com/leanprover/comparator.git /usr/local/bin/comparator && \
    ELAN_TOOLCHAIN="$toolchain" lake --dir /usr/local/bin/comparator build lean4export comparator
RUN curl -fL https://github.com/Zouuup/landrun/releases/download/v0.1.17/landrun-linux-amd64 -o /usr/local/bin/comparator/landrun && \
    chmod +x /usr/local/bin/comparator/landrun && \
    curl -fsSL https://raw.githubusercontent.com/Zouuup/landrun/v0.1.17/LICENSE -o /usr/local/bin/comparator/landrun.LICENSE
RUN git clone https://github.com/robsimmons/nanoda_lib.git /usr/local/bin/nanoda_lib && \
    git -C /usr/local/bin/nanoda_lib checkout 68d5ca9db226849b41a6fff59d796ff19d0a8840 && \
    . "$HOME/.cargo/env" && \
    cargo build --release --locked --manifest-path /usr/local/bin/nanoda_lib/Cargo.toml

# Version switcher: DOCKER_ENV_{PYTHON,NODE,RUST,GO,SWIFT,RUBY,PHP,JAVA}_VERSION
# COPY overwrites the base image's /opt/entrypoint.sh; drop Codex Cloud leftovers.
COPY entrypoint.sh /opt/entrypoint.sh
RUN rm -rf /opt/codex /opt/verify.sh

ENV PATH="/root/.pyenv/shims:${PATH}"

ENTRYPOINT ["/opt/entrypoint.sh"]
