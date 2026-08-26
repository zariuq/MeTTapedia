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

require MettaHyperonFull from "../externals/LeaTTa"

require algorithms from "../algorithms"

require mettail_core from "../batteries/mettail-core"

require gf_core from "../batteries/gf-core"

require certifyingDatalog from "../externals/certifyingDatalog"

require «mm-lean4» from "../standalone/mm-lean4"

-- Editable declarative Lean-core source used by the GSLT environment-growth bridge.
require lean4lean from "../externals/lean4lean"

-- Standalone Knuth–Skilling external (canonical home; namespace `KnuthSkilling.*`).
-- Replaces the previously embedded copy at `Mettapedia/ProbabilityTheory/KnuthSkilling/`.
require «ks-foundations-of-inference-lean» from "../standalone/ks-foundations-of-inference"

/-- Authored MeTTa sources consumed by compile-time program quotation.  Making
the directory an explicit text input prevents stale quoted constructor data
when a curriculum file changes without a Lean source edit. -/
input_dir primeMotivationSources where
  path := "../../MettaKernel/Curriculum/PrimeMotivation"
  text := true
  filter := .extension "metta"

@[default_target] lean_lib Mettapedia where
  needs := #[`@/primeMotivationSources]

lean_exe mettapedia where root := `Main

lean_exe metamathNIKAudit where
  root := `Mettapedia.Languages.Metamath.DatabaseNIKAudit

lean_exe checkRFC8259NativeForestExact where
  root := `Mettapedia.GSLT.Tools.CheckRFC8259NativeForestExact
