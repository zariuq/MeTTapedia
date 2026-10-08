import Lake

open System Lake DSL

package Mettapedia where
  version := v!"0.1.0"

require "leanprover-community" / mathlib @ git "0df444a360eaa60ab8c11dca51a86af692955474"

-- Editable local repos live in ../externals.
require TauCeti from "../externals/TauCeti"
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

@[default_target] lean_lib Mettapedia

-- Only this module quotes the curriculum files. Its importers inherit the
-- dependency through the normal module graph, without invalidating unrelated
-- libraries when an authored curriculum file changes.
lean_lib PrimeMotivationQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PrimeCandidates.CandidateMotivationProgramPackages]
  needs := #[`@/primeMotivationSources]

-- Concrete MM2 execution examples are an explicit proof audit, not a
-- dependency of the routine language umbrellas or the default library.
lean_lib MetamathProofRegression where
  roots := #[`Mettapedia.Languages.Metamath.MM2AssembledNormalExecution]

-- Each quotation depends on its own retained source files. Editing an
-- unquoted frontend module does not invalidate the kernel quotation.
input_file mm0MeTTaDataSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/data.metta"
  text := true

input_file mm0MeTTaKernelSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/kernel.generated.metta"
  text := true

input_file mm0MeTTaServiceSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/service.metta"
  text := true

input_file mm0MeTTaStreamSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/stream.metta"
  text := true

input_file mm0MeTTaTextualSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/textual.metta"
  text := true

input_file mm0MeTTaMMUSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/mmu.metta"
  text := true

input_file mm0MeTTaMMBSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/mmb.metta"
  text := true

lean_lib MM0MeTTaQuotation where
  roots := #[`Mettapedia.Languages.MM0.MeTTa.Program]
  needs := #[`@/mm0MeTTaDataSource, `@/mm0MeTTaKernelSource,
    `@/mm0MeTTaServiceSource, `@/mm0MeTTaStreamSource]

lean_lib MM0TextualQuotation where
  roots := #[`Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualExecution]
  needs := #[`@/mm0MeTTaTextualSource]

lean_lib MM0MMUQuotation where
  roots := #[`Mettapedia.Languages.MM0.MeTTa.Formats.MMU.MMUResolution]
  needs := #[`@/mm0MeTTaMMUSource]

-- The authored frontend quotation owns these exact inputs. Its proof
-- importers inherit changes through the ordinary module graph.
input_file mm0AuthoredGroundSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/experiments/gslt2parse_foundation/presentations/shared/ground_relations_v1.metta"
  text := true

input_file mm0AuthoredPeTTaGroundSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/experiments/gslt2parse_foundation/presentations/shared/cetta_petta_ground_relations_v1.metta"
  text := true

input_file mm0AuthoredFoldSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/source_fold_v1.metta"
  text := true

input_file mm0AuthoredSortSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/sort_environment_v1.metta"
  text := true

input_file mm0AuthoredTermSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/term_environment_v1.metta"
  text := true

input_file mm0AuthoredLexerSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/secondary_lexer_v1.metta"
  text := true

input_file mm0AuthoredNotationSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/notation_environment_v1.metta"
  text := true

input_file mm0AuthoredPrattSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/langdef/common/dynamic_pratt_v1.metta"
  text := true

input_file mm0AuthoredMathSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/math_parser_v1.metta"
  text := true

input_file mm0AuthoredExpressionSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/expression_environment_v1.metta"
  text := true

input_file mm0AuthoredAssertionSource where
  path := "../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/assertion_environment_v1.metta"
  text := true

lean_lib MM0TextualAuthoredQuotation where
  roots := #[`Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualAuthoredSource]
  needs := #[
    `@/mm0AuthoredGroundSource,
    `@/mm0AuthoredPeTTaGroundSource,
    `@/mm0AuthoredFoldSource,
    `@/mm0AuthoredSortSource,
    `@/mm0AuthoredTermSource,
    `@/mm0AuthoredLexerSource,
    `@/mm0AuthoredNotationSource,
    `@/mm0AuthoredPrattSource,
    `@/mm0AuthoredMathSource,
    `@/mm0AuthoredExpressionSource,
    `@/mm0AuthoredAssertionSource]

lean_lib MM0MMBQuotation where
  roots := #[`Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBExecution]
  needs := #[`@/mm0MeTTaMMBSource]

lean_exe mettapedia where root := `Main

lean_exe metamathNIKAudit where
  root := `Mettapedia.Languages.Metamath.DatabaseNIKAudit

lean_exe checkRFC8259NativeForestExact where
  root := `Mettapedia.GSLT.Tools.CheckRFC8259NativeForestExact

lean_exe sumoNativeSourceCheck where
  root := `Mettapedia.Languages.SUMO.Native.SourceElaborationCheck

lean_exe pettaRun where
  root := `Mettapedia.Languages.MeTTa.PeTTa.Main
