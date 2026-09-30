#!/bin/bash
# Interval (Arb) certificates: C_T^+ for the six fixed-eta weights (ctplus_arb.py), R_w for the three log-smooth
# weights of Theorem thm:fixed(iii) (rw_arb.py), then the exact rational p(C) certificates (certify_ctplus_arb.py).
# All output (*.log, *.json) is written next to this script.
#   ./run_ctplus_arb.sh                        # JOBS=6 computations in parallel (default)
#   JOBS=2 ./run_ctplus_arb.sh                 # fewer parallel jobs (less memory)
#   PIN="taskset -c 4-9" ./run_ctplus_arb.sh   # optional CPU pinning prefix (Linux)
set -euo pipefail
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
JOBS=${JOBS:-6}
PIN=${PIN:-}
t0=$(date +%s)
printf '%s\n' "ctplus_arb.py lsmooth 10000" "ctplus_arb.py lsmooth 1000" "ctplus_arb.py lsmooth 100" \
              "rw_arb.py 100000" "rw_arb.py 10000" "rw_arb.py 1000" \
              "ctplus_arb.py sharp 10000" "ctplus_arb.py sharp 1000" "ctplus_arb.py sharp 100" |
  xargs -P "$JOBS" -I{} bash -c 'set -- {}; s=$1; shift;
      if [ "$s" = rw_arb.py ]; then log=rw_arb_lsmooth_$1.log; else log=ctplus_arb_$1_$2.log; fi
      '"$PIN"' python3 "$s" "$@" --out . > "$log" 2>&1 || { echo "FAILED: $s $* (see $log)"; exit 255; }'
python3 certify_ctplus_arb.py > certify_ctplus_arb.log 2>&1
cat certify_ctplus_arb.log
echo "# run_ctplus_arb.sh wall time $(( $(date +%s) - t0 )) s"
