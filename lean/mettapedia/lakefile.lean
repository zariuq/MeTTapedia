import Lake

open System Lake DSL

package Mettapedia where
  version := v!"0.1.0"
  weakLeanArgs := #["-j", "1"]

require "leanprover-community" / mathlib @ git "v4.31.0"

-- Editable local repos live in ../externals.
require ordered_semigroups from "../externals/ordered_semigroups"

require Foundation from "../externals/Foundation"

require exchangeability from "../externals/exchangeability"

require provenance from "../externals/provenance"

require borel_det from "Mettapedia/SetTheory/BorelDeterminacy"

require catLogic from "Mettapedia/CategoricalLogic"

require Metatheory from "../externals/Metatheory"

require algorithms from "../algorithms"

require mettail_core from "../batteries/mettail-core"

require gf_core from "../batteries/gf-core"

require certifyingDatalog from "../externals/certifyingDatalog"

require «mm-lean4» from "../externals/mm-lean4"

-- Standalone Knuth–Skilling external (canonical home; namespace `KnuthSkilling.*`).
-- Replaces the previously embedded copy at `Mettapedia/ProbabilityTheory/KnuthSkilling/`.
require «ks-foundations-of-inference-lean» from "../standalone/ks-foundations-of-inference"

@[default_target] lean_lib Mettapedia

lean_exe mettapedia where root := `Main
