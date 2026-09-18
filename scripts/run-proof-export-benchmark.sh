#!/usr/bin/env bash
set -u

usage() {
    cat <<'EOF'
Usage: scripts/run-proof-export-benchmark.sh FZN_FOLDER OUTPUT_FOLDER [OUT_CSV]

Runs every .fzn file under FZN_FOLDER with proof export enabled.

Proofs are kept under:
  OUTPUT_FOLDER/proof_exports/<instance>/

The CSV contains only:
  instance,wall_seconds,proof_mb

Environment variables:
  TIMEOUT_SECONDS  Per-instance timeout, in seconds. Default: 3600.
  BUILD_DIR        Converter build dir. Default: ./build

Example:
  TIMEOUT_SECONDS=120 scripts/run-proof-export-benchmark.sh \
    /home/ubuntu/Desktop/Studije/MasterRad/minizinc-benchmarks/bibd \
    /home/ubuntu/Desktop/Studije/MasterRad/oms_encoding/bibd-proof-run
EOF
}

csv_escape() {
    local value=${1//\"/\"\"}
    printf '"%s"' "$value"
}

format_wall_time() {
    local seconds=$1
    if [[ -z "$seconds" || "$seconds" == "NA" ]]; then
        printf 'NA'
        return
    fi

    awk -v seconds="$seconds" 'BEGIN {
        total = int(seconds + 0.5);
        minutes = int(total / 60);
        secs = total % 60;
        printf "%dm%02ds", minutes, secs;
    }'
}

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$script_dir/.." && pwd)

if [[ $# -lt 2 || $# -gt 3 || "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
    usage
    exit 1
fi

input_dir=$1
output_dir=$2
out_csv=${3:-"$output_dir/results.csv"}
proof_root="$output_dir/proof_exports"
build_dir=${BUILD_DIR:-"$repo_root/build"}
timeout_seconds=${TIMEOUT_SECONDS:-3600}
converter="$build_dir/flatzinc_to_sat"
optimizer="$build_dir/optimizer"

if [[ ! -d "$input_dir" ]]; then
    echo "Input folder does not exist: $input_dir" >&2
    exit 1
fi

if [[ ! -x "$converter" ]]; then
    echo "Converter binary not found or not executable: $converter" >&2
    exit 1
fi

if [[ ! -x "$optimizer" ]]; then
    echo "Optimizer script not found or not executable: $optimizer" >&2
    exit 1
fi

mkdir -p "$proof_root"
printf 'instance,walltime,proof_mb\n' > "$out_csv"

count=0
while IFS= read -r -d '' fzn; do
    count=$((count + 1))
    relative_fzn=$(realpath --relative-to="$input_dir" "$fzn")
    instance_name=${relative_fzn%.fzn}
    safe_instance=${instance_name//\//__}
    workdir="$proof_root/${count}_${safe_instance}"
    rm -rf "$workdir"
    mkdir -p "$workdir"

    cp "$fzn" "$workdir/input.fzn"
    ln -sf "$converter" "$workdir/flatzinc_to_sat"
    ln -sf "$optimizer" "$workdir/optimizer"

    echo "[$count] $relative_fzn"

    (
        cd "$workdir" &&
        /usr/bin/time -f 'TIME_RESULT,%e,%U,%S,%M' timeout "$timeout_seconds" ./flatzinc_to_sat -export-proof input.fzn > stdout.txt
    ) 2> "$workdir/time.txt"
    exit_code=$?

    time_result=$(awk -F',' '/^TIME_RESULT/ {print $0}' "$workdir/time.txt" | tail -1)
    wall_seconds=$(printf '%s\n' "$time_result" | awk -F',' '{print $2}')
    if [[ -z "$wall_seconds" ]]; then
        wall_seconds="NA"
    fi
    wall=$(format_wall_time "$wall_seconds")

    proof_bytes=$(find "$workdir" \( -path "$workdir/proofs/*" -o -path "$workdir/proofs_step1/*" \) -type f -printf '%s\n' 2>/dev/null | awk '{sum += $1} END {print sum + 0}')
    proof_mb=$(awk -v bytes="$proof_bytes" 'BEGIN {printf "%.2f", bytes / 1048576}')

    {
        csv_escape "$instance_name"; printf ','
        csv_escape "$wall"; printf ','
        csv_escape "$proof_mb"; printf '\n'
    } >> "$out_csv"

    if [[ $exit_code -ne 0 ]]; then
        echo "    exited with code $exit_code; see $workdir/time.txt" >&2
    fi
done < <(find "$input_dir" -type f -name '*.fzn' -print0 | sort -z)

echo "Wrote: $out_csv"
echo "Proof exports under: $proof_root"
