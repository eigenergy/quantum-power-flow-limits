#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
    echo "usage: $0 <powerio-root> <datasets-root> [core|publication]" >&2
    exit 2
fi

powerio_root=$1
datasets_root=$2
mode=${3:-core}
case "$mode" in
    core|publication)
        ;;
    *)
        echo "unknown mode: $mode" >&2
        exit 2
        ;;
esac

expected_powerio_version=0.7.3
expected_uv_version=0.12.3
expected_graphviz_version=15.1.0
script_dir=$(cd "$(dirname "$0")" && pwd)
venv_dir="$script_dir/.venv"
uv_cache_dir="${TMPDIR:-/tmp}/quantum-power-flow-uv-cache"
wheel_dir=$(mktemp -d "${TMPDIR:-/tmp}/powerio-wheel.XXXXXX")
publication_dir=""
cleanup() {
    rm -rf "$wheel_dir"
    if [[ -n "$publication_dir" ]]; then
        rm -rf "$publication_dir"
    fi
}
trap cleanup EXIT

uv_banner=$(uv --version)
case "$uv_banner" in
    "uv $expected_uv_version"|"uv $expected_uv_version "*)
        ;;
    *)
        echo "expected uv $expected_uv_version, got: $uv_banner" >&2
        exit 1
        ;;
esac

graphviz_banner=$(sfdp -V 2>&1)
case "$graphviz_banner" in
    *"graphviz version $expected_graphviz_version "*|*"graphviz version $expected_graphviz_version")
        ;;
    *)
        echo "expected Graphviz $expected_graphviz_version, got: $graphviz_banner" >&2
        exit 1
        ;;
esac

env UV_CACHE_DIR="$uv_cache_dir" uv sync \
    --project "$script_dir" --python 3.13.14 --locked

(
    cd "$powerio_root"
    env UV_CACHE_DIR="$uv_cache_dir" \
        CARGO_TARGET_DIR="$wheel_dir/target" \
        VIRTUAL_ENV="$venv_dir" \
        PATH="$venv_dir/bin:$PATH" \
        "$venv_dir/bin/maturin" build --release --out "$wheel_dir"
)

wheel_path=$(find "$wheel_dir" -maxdepth 1 -name 'powerio-*.whl' -print -quit)
if [[ -z "$wheel_path" ]]; then
    echo "PowerIO wheel build produced no wheel" >&2
    exit 1
fi

env UV_CACHE_DIR="$uv_cache_dir" uv pip install \
    --python "$venv_dir/bin/python" --force-reinstall "$wheel_path"

run_experiment() {
    env UV_CACHE_DIR="$uv_cache_dir" uv run \
        --project "$script_dir" --no-sync \
        python "$@"
}

run_core() {
    run_experiment "$script_dir/run_conditions.py" \
        --powerio-root "$powerio_root" \
        --datasets-root "$datasets_root" \
        --expected-powerio-version "$expected_powerio_version" \
        "$@"
}

case "$mode" in
    core)
        run_core
        ;;
    publication)
        publication_dir=$(mktemp -d "${TMPDIR:-/tmp}/power-flow-publication.XXXXXX")
        run_core \
            --publication \
            --output "$publication_dir/results.json" \
            --table-output "$publication_dir/conditions_table.tex"
        mv "$publication_dir/results.json" "$script_dir/results.json"
        mv "$publication_dir/conditions_table.tex" "$script_dir/conditions_table.tex"
        ;;
esac
