#!/usr/bin/env bash
set -euo pipefail
export ELAN_HOME=/workspace/toolchains/elan
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR=/workspace/cache/mathlib
cd /workspace/paper-formalizations
test "$(cat lean-toolchain)" = leanprover/lean4:v4.34.0
printf '%s\n' '8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632  lean-toolchain' '615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f  lake-manifest.json' | sha256sum -c -
mkdir -p /workspace/toolchains
if [ ! -x "$ELAN_HOME/bin/elan" ]; then
  curl -fLsS --proto '=https' --tlsv1.2 https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz -o /workspace/toolchains/elan.tar.gz
  tar -xzf /workspace/toolchains/elan.tar.gz -C /workspace/toolchains
  /workspace/toolchains/elan-init -y --no-modify-path --default-toolchain none
fi
if [ ! -x /workspace/toolchains/lean-4.34.0-linux/bin/lean ]; then
  curl -fLsS --proto '=https' --tlsv1.2 https://github.com/leanprover/lean4/releases/download/v4.34.0/lean-4.34.0-linux.tar.zst -o /workspace/toolchains/lean.tar.zst
  tar --zstd -xf /workspace/toolchains/lean.tar.zst -C /workspace/toolchains
fi
if ! elan toolchain list | rg -q '^leanprover/lean4:v4\.34\.0(\s|$)'; then
  elan toolchain link leanprover/lean4:v4.34.0 /workspace/toolchains/lean-4.34.0-linux
fi
lean --version
lake --version
lake exe cache get
printf '%s\n' '8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632  lean-toolchain' '615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f  lake-manifest.json' | sha256sum -c -
