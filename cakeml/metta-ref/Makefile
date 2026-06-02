POLY ?= /home/zar/claude/CakeML/polyml-local/bin/poly
CAKE ?= /home/zar/claude/CakeML/cake-x64-64/cake
BASIS_FFI ?= /home/zar/claude/CakeML/cake-x64-64/basis_ffi.c
CC ?= cc
LDLIBS += -lm

.PHONY: fragment-manifest generate-fragments check-fragments check-generated-match-sexp test-sml test-capacity-sml test-cml test-ffi test-hol test-curated-local test-cetta-goldens test-selected-cetta-local test-oracle test clean

fragment-manifest:
	python3 tools/check_fragment_exports.py --emit-lint-manifest

generate-fragments: fragment-manifest

check-fragments:
	python3 tools/check_fragment_exports.py --check

check-generated-match-sexp: generated/bridge_eval_match_fragment.sexp
	tools/check_generated_match_sexp.sh

test-sml:
	$(POLY) --script tests/m1_tests.sml

test-capacity-sml:
	$(POLY) --script tests/capacity_prototypes.sml

test-cml: cml/metta_m1.cake
	./cml/metta_m1.cake

cml/metta_m1.S: cml/metta_m1.cml
	$(CAKE) < $< > $@

cml/metta_m1.cake: cml/metta_m1.S
	$(CC) $< $(BASIS_FFI) $(LDLIBS) -o $@

cml/metta_m1_runner.cml: cml/metta_m1.cml tools/make_cml_runner.sh
	tools/make_cml_runner.sh cml/metta_m1.cml $@

cml/metta_m1_runner.S: cml/metta_m1_runner.cml
	$(CAKE) < $< > $@

cml/metta_m1_runner.cake: cml/metta_m1_runner.S
	$(CC) $< $(BASIS_FFI) $(LDLIBS) -o $@

ffi/ffi_probe.S: ffi/ffi_probe.cml
	$(CAKE) < $< > $@

ffi/ffi_probe.cake: ffi/ffi_probe.S ffi/ffi_probe.c
	$(CC) ffi/ffi_probe.S $(BASIS_FFI) ffi/ffi_probe.c $(LDLIBS) -o $@

test-ffi: ffi/ffi_probe.cake
	./ffi/ffi_probe.cake

test-hol:
	cd hol && . /home/zar/claude/CakeML/env.sh && Holmake

test-cetta-goldens:
	oracle/run_cetta_goldens.sh

test-curated-local: cml/metta_m1_runner.cake
	oracle/run_curated_local.sh

test-selected-cetta-local: cml/metta_m1_runner.cake
	oracle/run_selected_cetta_compare.sh

test: check-fragments check-generated-match-sexp test-sml test-capacity-sml test-cml test-ffi test-hol

test-oracle: test test-curated-local test-cetta-goldens test-selected-cetta-local

clean:
	$(RM) cml/*.S cml/*.cake cml/metta_m1_runner.cml ffi/ffi_probe.S ffi/ffi_probe.cake generated/*.S
