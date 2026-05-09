FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

# Install build dependencies
RUN apt-get update && apt-get install -y \
    git \
    curl \
    build-essential \
    cmake \
    python3 \
    libssl-dev \
    pkg-config \
    clang \
    libclang-dev \
    && rm -rf /var/lib/apt/lists/*

# Build and install Z3 4.12.1 from source (matches z3-sys 0.8.1 bundled version)
RUN git clone --depth 1 --branch z3-4.12.1 https://github.com/Z3Prover/z3.git /tmp/z3 \
    && cmake -S /tmp/z3 -B /tmp/z3/build \
        -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_INSTALL_PREFIX=/usr/local \
    && cmake --build /tmp/z3/build --parallel $(nproc) \
    && cmake --install /tmp/z3/build \
    && ldconfig \
    && rm -rf /tmp/z3

# Point z3-sys at the Z3 we just installed (mirrors .cargo/config.toml on macOS)
ENV Z3_SYS_Z3_HEADER=/usr/local/include/z3.h
ENV RUSTFLAGS="-L /usr/local/lib"

# Install Rust (stable, matches rust-toolchain file)
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable
ENV PATH="/root/.cargo/bin:${PATH}"

WORKDIR /chompy
COPY . .

# Pre-build the release binary so `cargo run --release` at eval time is instant
RUN cargo build --release

CMD ["python3", "python/run_the_eval.py"]
