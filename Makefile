PYTHON ?= python3
.PHONY: check certificates lean

# Every certificate and check, through the tests (stdlib Python + a C compiler; numpy optional; about 2 minutes).
check:
	$(PYTHON) -m unittest discover -s tests -v

# The certificates alone, printing every claim.
certificates:
	cd certificates && $(PYTHON) -I x1_theorems.py --conjecture && $(PYTHON) -I x1_exponent_count.py \
		&& $(PYTHON) -I x1_prepass_check.py && $(PYTHON) -I x1_e1_check.py \
		&& $(PYTHON) -I x1_word_check.py && $(PYTHON) -I m6_word_verify.py

# The Lean 4 kernel checks (lean/README.md): elan with Lean v4.34.1 and the Mathlib cache (run `lake exe cache get`
# in lean/ once). Modules are built one at a time with a memory watchdog, then the axioms audit runs.
lean:
	cd lean && ./build_watch.sh build && ./axioms_audit.sh
