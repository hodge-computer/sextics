#!/usr/bin/env bash
# Prepare a Codex Cloud checkout for Lean development. Safe to rerun.
set -euo pipefail

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
export SEXTICS_CLOUD_HOME="${SEXTICS_CLOUD_HOME:-$HOME/.cache/sextics-cloud}"
export ELAN_HOME="${ELAN_HOME:-$SEXTICS_CLOUD_HOME/elan}"
python=${SEXTICS_CLOUD_PYTHON:-python3.11}

fail() { printf 'Codex Cloud setup: %s\n' "$*" >&2; exit 1; }
for program in "$python" curl git tar make cc node; do
    command -v "$program" >/dev/null || fail "Missing $program; install it in the environment image, then rerun setup."
done
"$python" -c 'import sys, venv; assert sys.version_info[:2] == (3, 11), "Python 3.11 is required"'

# Select a pinned official elan release only when a local installation is absent.
# SHA256 digests are recorded by the leanprover/elan v4.2.4 GitHub release.
case "$(uname -s)/$(uname -m)" in
    Linux/x86_64)
        platform=x86_64-unknown-linux-gnu
        digest=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63 ;;
    Linux/aarch64 | Linux/arm64)
        platform=aarch64-unknown-linux-gnu
        digest=05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9 ;;
    Darwin/x86_64)
        platform=x86_64-apple-darwin
        digest=8a340b309d8ed2e96f930761fa223b3af57a38f5d253b53ac90293c9516f8cd4 ;;
    Darwin/arm64)
        platform=aarch64-apple-darwin
        digest=7ad829861392c718dfebde3a83b5c8508df47be02af68894b094b0b3952616e5 ;;
    *) fail 'Supported platforms are Linux and macOS on x86_64 or ARM64.' ;;
esac
if [[ $platform == *linux* ]]; then
    command -v zstd >/dev/null || fail 'Install zstd in the environment image to unpack the Lean toolchain.'
fi

scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
for name in lean-toolchain lakefile.toml lake-manifest.json; do
    cp "$repo/formal/lean/$name" "$scratch/$name"
done
"$python" - "$repo/formal/lean" <<'PY'
import json
import pathlib
import sys
import tomllib

root = pathlib.Path(sys.argv[1])
config = tomllib.loads((root / 'lakefile.toml').read_text())
manifest = json.loads((root / 'lake-manifest.json').read_text())
required = next(p for p in config['require'] if p['name'] == 'mathlib')
resolved = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
if required['rev'] != resolved['rev'] or required['git'] != resolved['url']:
    raise SystemExit('Mathlib pins disagree; fix the committed configuration before setup. No lake update was run.')
PY

mkdir -p "$SEXTICS_CLOUD_HOME"
"$python" -m venv "$SEXTICS_CLOUD_HOME/venv"
export PATH="$SEXTICS_CLOUD_HOME/venv/bin:$ELAN_HOME/bin:$PATH"
"$SEXTICS_CLOUD_HOME/venv/bin/python" -m pip install -r "$repo/scripts/requirements-content.txt"
"$SEXTICS_CLOUD_HOME/venv/bin/python" -m pip check

if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
    archive="$scratch/elan.tar.gz"
    # Preserve the environment's proxy and CA settings; follow release redirects.
    curl --fail --show-error --location --retry 3 --connect-timeout 30 \
        "https://github.com/leanprover/elan/releases/download/v4.2.4/elan-$platform.tar.gz" \
        --output "$archive"
    "$python" - "$archive" "$digest" <<'PY'
import hashlib
import pathlib
import sys

if hashlib.sha256(pathlib.Path(sys.argv[1]).read_bytes()).hexdigest() != sys.argv[2]:
    raise SystemExit('Elan release checksum mismatch; refusing to execute the download.')
PY
    mkdir "$scratch/elan"
    tar -xzf "$archive" -C "$scratch/elan"
    "$scratch/elan/elan-init" -y --no-modify-path --default-toolchain none
fi

toolchain=$(tr -d '\r\n' < "$repo/formal/lean/lean-toolchain")
"$ELAN_HOME/bin/elan" toolchain install "$toolchain"
export ELAN_TOOLCHAIN="$toolchain"
cd "$repo/formal/lean"
lean --version
if ! lake exe cache get 2>&1 | tee "$scratch/cache-get.log"; then
    fail 'Mathlib cache retrieval failed. Check Cloud network access, then rerun setup.'
fi
# The pinned cache client can report missing files with exit status zero.
if grep -Fq 'Warning: some files were not found in the cache.' "$scratch/cache-get.log"; then
    fail 'The Mathlib cache is incomplete; inspect the cache warning before starting a source build.'
fi
[[ -s .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean ]] || \
    fail 'The Mathlib cache did not provide Mathlib/Tactic.olean; inspect downloads before building.'
lake build HodgeComputer.Verify
for name in lean-toolchain lakefile.toml lake-manifest.json; do
    cmp -s "$repo/formal/lean/$name" "$scratch/$name" || fail "Lake changed $name; inspect the checkout before continuing."
done
printf 'Setup passed. In each new shell, set SEXTICS_CLOUD_HOME and ELAN_HOME,\n'
printf 'then prepend %s/venv/bin and %s/bin to PATH.\n' "$SEXTICS_CLOUD_HOME" "$ELAN_HOME"
