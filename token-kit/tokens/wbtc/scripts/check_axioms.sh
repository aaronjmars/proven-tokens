#!/bin/bash
# Check the axioms test in a build log: the count of theorems checked, every axiom name used,
# and (when Test/Axioms.lean is given) that the count is the count of `#print axioms` lines and
# that the scan of every constant passed. It fails on a name that is not one of the three
# standard axioms, on a sorry warning, on an empty log and on a wrong count. The work is done by
# check_axioms.py (same folder), which reads lists of axioms that wrap over several lines.
# Usage: check_axioms.sh <build log> [<Root>/Test/Axioms.lean]
exec python3 "$(dirname "$0")/check_axioms.py" "$@"
