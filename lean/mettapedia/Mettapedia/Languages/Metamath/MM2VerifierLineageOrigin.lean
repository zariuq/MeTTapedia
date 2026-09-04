import Mettapedia.Languages.Metamath.MM2VerifierExecutableOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutableSchemaFixedHeadSafety

/-!
# Lineage authorization for the fixed Metamath verifier program

The fixed verifier compiler output is checked once against its own complete
recursive executable inventory. This is the source-specific seed consumed by
the generic rule-scoped lineage theorem; subsequent scheduler preservation is
symbolic in the source state and fuel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2VerifierLineageOrigin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.MM2VerifierExecutableOrigin
open Mettapedia.Languages.Metamath.MM2VerifierProgram
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

/-- The stronger executable authorization used by the generated syntax to
rule-scoped execution boundary. It retains both recursive fixed-head
structure and finite source-derived schema lineage. -/
def VerifierExecutableLineageAuthorized (atom : Atom) : Prop :=
  ExecutableSchemaAtomAuthorized verifierExecutableRawFacts atom

/-- The fixed verifier compiler output contains no variable-headed expression.
This bounded structural source check deliberately excludes executable-schema
membership, which is already supplied by the compiler-derived origin theorem. -/
theorem genericVerifierProgram_fixedExpressionHeads :
    (genericVerifierProgram authoredMetamathVerifierGSLT).all
      fixedExpressionHeads = true := by
  decide +kernel

/-- Every atom in the fixed verifier program is authorized for rule-scoped
execution by a finite compiler-derived schema lineage. -/
theorem genericVerifierProgram_executable_lineageAuthorized :
    AtomsWithin VerifierExecutableLineageAuthorized
      (genericVerifierProgram authoredMetamathVerifierGSLT) := by
  intro atom atomMember
  unfold VerifierExecutableLineageAuthorized
  apply fixedExpressionHeads_authorized
  · exact (List.all_eq_true.mp genericVerifierProgram_fixedExpressionHeads)
      atom atomMember
  · exact genericVerifierProgram_executable_schemaAuthorized atom atomMember

section AxiomAudit

#print axioms genericVerifierProgram_fixedExpressionHeads
#print axioms genericVerifierProgram_executable_lineageAuthorized

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2VerifierLineageOrigin
