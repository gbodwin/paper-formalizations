#!/bin/bash -p
# SOURCE ONLY. Preserve startup -p and the reviewed original Lake/Bash boundary.
case $- in
  *p*)
    set -euo pipefail
    if [[ -n ${BASH_ENV-} || -n ${ENV-} ]]; then
      printf '%s\n' 'Batch replay requires absent shell startup hooks' >&2
      exit 2
    fi
    exec /usr/bin/python3 -I -B checkpoints/light-eft-global-replay-batches-20261026/batch_runtime.py before-lake
    ;;
  *) (( 0 ));;
esac
