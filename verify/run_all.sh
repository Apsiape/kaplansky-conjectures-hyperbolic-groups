#!/bin/sh
# Rerun every check and overwrite its recorded output (*.out); `git diff verify/` then shows any change.
# Requires Python 3 with numpy, scipy, sympy, mpmath and networkx. Set PYTHON to choose the interpreter.
set -e
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
for f in bicyclic_algebra_check constants_check closure_lemma_check interval_lemma_check cat0_links_check \
         design_p3_explicit pg281_kernel pg2_81_kernel_r2 decay_quotient decay_constants_check exact_rows_r2 \
         signed_cancellation_test certificates_odd_p certificates_odd_p_extended; do
  echo "== $f"
  "$PY" -u "$f.py" > "$f.out" 2>&1
  tail -n 1 "$f.out"
done
