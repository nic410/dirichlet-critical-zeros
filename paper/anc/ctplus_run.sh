#!/bin/bash
# Driver: fixed-eta C_T^+ bounds.  CPU cores 0-3 only.
cd "$(dirname "$0")"
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4 MKL_NUM_THREADS=4
for N0 in 100 1000 10000; do
  taskset -c 0-3 python3 ctplus.py sharp $N0 10000000 1000000 > ctplus_sharp_$N0.log 2>&1
done
for N0 in 100 1000 10000; do
  taskset -c 0-3 python3 ctplus.py lsmooth $N0 10000000 1000000 2e-5 > ctplus_lsmooth_$N0.log 2>&1
done
