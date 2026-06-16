import Lake

open System Lake DSL

package Mettapedia where
  version := v!"0.1.0"
  weakLeanArgs := #["-j", "1"]
  -- Share compiled artifacts across local workspaces on this toolchain.
  enableArtifactCache := true
  -- Keep dependency artifacts visible in package build directories.
  restoreAllArtifacts := true

require "leanprover-community" / mathlib @ git "v4.28.0"

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

@[default_target] lean_lib Mettapedia

lean_exe mettapedia where root := `Main
