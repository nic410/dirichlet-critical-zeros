#!/bin/bash
# Independent cross-check of the C_T^+ numerics (written from the definitions only; shares no code with
# ctplus.py or ctplus_arb.py): E, sup_t R_S1(t) for all 64 S1 and six weights at high precision, R^m spot values.
# Output: xcheck.log next to this script.  Optional CPU pinning: PIN="taskset -c 4-9" ./run_xcheck.sh
cd "$(dirname "$0")"
export OMP_NUM_THREADS=6 OPENBLAS_NUM_THREADS=6 MKL_NUM_THREADS=6
PIN=${PIN:-}
: > xcheck.log
for s in xcheck_E xcheck_sharp xcheck_lsmooth xcheck_Rm xcheck_Rm_bruteforce; do
  echo "######## $s.py ########" | tee -a xcheck.log
  st=$(date +%s)
  $PIN python3 $s.py 2>&1 | tee -a xcheck.log
  echo "[$s wall $(( $(date +%s) - st )) s]" | tee -a xcheck.log
done
