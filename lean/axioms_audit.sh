#!/usr/bin/env bash
# Print the axioms of every theorem (MobiusLean/Axioms.lean) and fail on anything beyond Lean's standard three.
set -u
cd "$(dirname "$0")"
command -v lake >/dev/null || export PATH=${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.34.1/bin:$PATH
nice -n 19 lake env lean MobiusLean/Axioms.lean > axioms.out 2>&1 || { cat axioms.out; echo "FAIL: Axioms.lean"; exit 1; }
n=$(grep -c "depends on axioms\|does not depend on any axioms" axioms.out)
bad=$(grep -vE "depends on axioms: \[(propext|Classical.choice|Quot.sound|, )*\]$|does not depend on any axioms|^$" axioms.out)
if [ -n "$bad" ]; then echo "$bad"; echo "FAIL: non-standard axiom or error"; exit 1; fi
echo "axioms: $n theorems, standard axioms only (propext, Classical.choice, Quot.sound)"
