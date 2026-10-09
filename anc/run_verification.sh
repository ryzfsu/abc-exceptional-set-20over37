#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 1 ]]; then
  echo "usage: $0 FINAL_REPORT.json" >&2
  exit 2
fi

report=$1

python3 -m py_compile \
  dynamic_tree_ind.py \
  verify_tree_report_clean.py \
  verify_tree_report.py \
  verify_witness_clean.py \
  audit_clause_compiler.py \
  compiler_differential_used.py \
  verify_arch_faces.py \
  verify_group12_w152prime.py \
  verify_group12a_c_newface.py \
  verify_group1212a_thirdface.py \
  verify_group1212b_reflectedface.py

python3 verify_tree_report_clean.py "$report" --mutation-tests
python3 verify_tree_report.py "$report"
python3 verify_witness_clean.py --profile target-20/37
python3 audit_clause_compiler.py
python3 compiler_differential_used.py "$report"
python3 verify_survivor_79_139.py
python3 verify_survivor_6_11.py
python3 verify_unloc_6_11_candidate.py
python3 verify_pow3c_profiles.py
python3 verify_arch_faces.py
python3 verify_group12_w152prime.py
python3 verify_group12a_c_newface.py
python3 verify_group1212a_thirdface.py
python3 verify_group1212b_reflectedface.py

# Appendix A only: this audited POW2 family is not installed in the report.
python3 verify_pow2_profiles.py
