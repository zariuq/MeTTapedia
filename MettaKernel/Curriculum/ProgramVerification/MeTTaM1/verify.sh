#!/usr/bin/env bash
# MeTTaM1 sub-ladder: WIRES INTO the existing metta-ref dev (do not reinvent).
#   proved + tested : make check-coverage (validates the curriculum_coverage.tsv ledger)
#                     make test          (HOL proofs + SML/CakeML tests)   [heavier]
#   executed        : make test-oracle   (CakeML/oracle comparison runs)   [heaviest]
set -u
MR=/home/aimama/aihub/Mettapedia/cakeml/metta-ref
exec make -C "$MR" "${1:-check-coverage}"
