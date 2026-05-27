#!/usr/bin/env bash
set -euo pipefail

# Lean files live at the repo root (lakefile.toml here, lib under MilnorThom/),
# so LEAN_ROOT is ROOT, not ROOT/lean.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_ROOT="$ROOT"
LOCKFILE="${LOCKFILE:-$LEAN_ROOT/.lake/lake-build.lock}"
MEMORY_MB="${MEMORY_MB:-16384}"

REAL_LAKE="${REAL_LAKE:-$(command -v lake)}"
REAL_LEAN="${REAL_LEAN:-$(command -v lean)}"

mkdir -p "$(dirname "$LOCKFILE")"

acquire_lock() {
  while true; do
    if (set -o noclobber; printf '%s\n' "$$" >"$LOCKFILE") 2>/dev/null; then
      return 0
    fi

    if IFS= read -r lock_pid <"$LOCKFILE" && [[ "$lock_pid" =~ ^[0-9]+$ ]] &&
        kill -0 "$lock_pid" 2>/dev/null; then
      echo "another lake build is already running (pid $lock_pid): $LOCKFILE" >&2
      exit 1
    fi

    rm -f "$LOCKFILE"
  done
}

WRAP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/milnor-thom-lake-wrap.XXXXXX")"

cleanup() {
  rm -rf "$WRAP_DIR"
  rm -f "$LOCKFILE"
}
trap cleanup EXIT INT TERM HUP

acquire_lock

cat >"$WRAP_DIR/lean" <<EOF
#!/usr/bin/env bash
exec "$REAL_LEAN" -M "$MEMORY_MB" "\$@"
EOF
chmod 755 "$WRAP_DIR/lean"

cd "$LEAN_ROOT"
PATH="$WRAP_DIR:$PATH" "$REAL_LAKE" build "$@"
