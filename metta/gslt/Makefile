# Public controls for the GSLT execution library.
#
# The Lean bridges quote the files in lib/ by sha256, so every engine runs the
# exact text the proofs are about. Engines are variables:
#
#   make gate                         CeTTa (PeTTa dialect)
#   make gate-petta PETTA=<run.sh>    a PeTTa checkout
#   make gate-all PETTA_RUNNERS="<run.sh> <run.sh> ..."
#
# Each run writes its full output to out/ and prints its sha256, so runs on
# different engines can be compared line for line.

CETTA ?= ../../../hyperon/cetta-prime-2.0-draft-20260910/cetta
PETTA ?=
PETTA_RUNNERS ?=

GATE := tools/test_gslt_match_automata.sh
OUT := out

.PHONY: gate gate-cetta gate-petta gate-all

gate: gate-cetta

$(OUT):
	mkdir -p $(OUT)

gate-cetta: | $(OUT)
	CETTA_BIN=$(CETTA) bash $(GATE) > $(OUT)/gate-cetta.out
	sha256sum $(OUT)/gate-cetta.out
	python3 tools/test_gslt_schema_typing.py --cetta "$(CETTA)" --output "$(OUT)/schema-typing-cetta"
	python3 tools/test_gslt_schema_typing.py --family constructor --cetta "$(CETTA)" --output "$(OUT)/constructor-typing-cetta"
	python3 tools/test_gslt_schema_typing.py --family scan --cetta "$(CETTA)" --output "$(OUT)/constructor-scan-cetta"
	python3 tools/test_gslt_schema_typing.py --family operations --cetta "$(CETTA)" --output "$(OUT)/retained-operations-cetta"
	python3 tools/test_gslt_schema_typing.py --family transitions --cetta "$(CETTA)" --output "$(OUT)/retained-transitions-cetta"
	python3 tools/test_gslt_schema_typing.py --family allocations --cetta "$(CETTA)" --output "$(OUT)/allocation-advance-cetta"
	python3 tools/test_gslt_schema_typing.py --family allocation-children --cetta "$(CETTA)" --output "$(OUT)/allocation-children-cetta"

gate-petta: | $(OUT)
	@test -n "$(PETTA)" || { echo "set PETTA=<path to a PeTTa run.sh>" >&2; exit 2; }
	PETTA_RUNNER=$(PETTA) bash $(GATE) > $(OUT)/gate-petta.out
	sha256sum $(OUT)/gate-petta.out
	python3 tools/test_gslt_schema_typing.py --petta "$(PETTA)" --output "$(OUT)/schema-typing-petta"
	python3 tools/test_gslt_schema_typing.py --family constructor --petta "$(PETTA)" --output "$(OUT)/constructor-typing-petta"
	python3 tools/test_gslt_schema_typing.py --family scan --petta "$(PETTA)" --output "$(OUT)/constructor-scan-petta"
	python3 tools/test_gslt_schema_typing.py --family operations --petta "$(PETTA)" --output "$(OUT)/retained-operations-petta"
	python3 tools/test_gslt_schema_typing.py --family transitions --petta "$(PETTA)" --output "$(OUT)/retained-transitions-petta"
	python3 tools/test_gslt_schema_typing.py --family allocations --petta "$(PETTA)" --output "$(OUT)/allocation-advance-petta"
	python3 tools/test_gslt_schema_typing.py --family allocation-children --petta "$(PETTA)" --output "$(OUT)/allocation-children-petta"

gate-all: gate-cetta
	@for runner in $(PETTA_RUNNERS); do \
	  $(MAKE) --no-print-directory gate-petta PETTA=$$runner || exit $$?; \
	  cmp -s $(OUT)/gate-cetta.out $(OUT)/gate-petta.out \
	    || { echo "$$runner differs from CeTTa" >&2; exit 1; }; \
	  cmp -s $(OUT)/schema-typing-cetta/cetta.out $(OUT)/schema-typing-petta/petta.out \
	    || { echo "$$runner schema typing differs from CeTTa" >&2; exit 1; }; \
	  cmp -s $(OUT)/constructor-typing-cetta/cetta.out $(OUT)/constructor-typing-petta/petta.out \
	    || { echo "$$runner constructor typing differs from CeTTa" >&2; exit 1; }; \
	  cmp -s $(OUT)/constructor-scan-cetta/cetta.out $(OUT)/constructor-scan-petta/petta.out \
	    || { echo "$$runner constructor scan differs from CeTTa" >&2; exit 1; }; \
	  cmp -s $(OUT)/retained-operations-cetta/cetta.out $(OUT)/retained-operations-petta/petta.out \
	    || { echo "$$runner retained operations differ from CeTTa" >&2; exit 1; }; \
	  cmp -s $(OUT)/retained-transitions-cetta/cetta.out $(OUT)/retained-transitions-petta/petta.out \
	    || { echo "$$runner retained transitions differ from CeTTa" >&2; exit 1; }; \
	  cmp -s $(OUT)/allocation-advance-cetta/cetta.out $(OUT)/allocation-advance-petta/petta.out \
	    || { echo "$$runner allocation advancement differs from CeTTa" >&2; exit 1; }; \
	  cmp -s $(OUT)/allocation-children-cetta/cetta.out $(OUT)/allocation-children-petta/petta.out \
	    || { echo "$$runner allocation children differ from CeTTa" >&2; exit 1; }; \
	done
