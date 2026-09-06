import Mettapedia.GSLT.Core.OperationalRealization
import Mettapedia.GSLT.LanguageDef.TotalGSLT

/-!
# Proof-relevant paths for bounded first-reduct normalization

`normalizeFirstUsing` executes an authored `LanguageDef` with an explicit
relation environment, contextual-depth bound, and step bound.  This module
retains the corresponding GSLT path.  It does not introduce another execution
relation: every edge is justified by membership in the actual `rewriteAt`
result and the existing exact compiler theorem for `langReducesUsing`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NormalizationPath

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.TotalGSLT

/-- A bounded normalizer result retains its exact endpoint, its actual GSLT
path, agreement with the executable normalizer, and resource facts. -/
structure Run
    (relations : RelationEnv) (language : LanguageDef)
    (laws : ReductionRespectsEquationsUsing relations language)
    (contextFuel stepFuel : Nat) (term : Pattern) where
  endpoint : Pattern
  path : ExecutionPath (languageGSLTUsing relations language laws)
    term endpoint
  endpoint_eq : endpoint =
    normalizeFirstUsing relations language contextFuel stepFuel term
  length_le : path.length ≤ stepFuel
  nonempty_of_reduct :
    0 < stepFuel →
      rewriteAt (engineBasePremises relations) language contextFuel term ≠ [] →
        0 < path.length

/-- Execute the deterministic first-reduct strategy while retaining every
authored GSLT edge. -/
def normalizeFirstRunUsing
    (relations : RelationEnv) (language : LanguageDef)
    (laws : ReductionRespectsEquationsUsing relations language)
    (contextFuel : Nat) :
    (stepFuel : Nat) → (term : Pattern) →
      Run relations language laws contextFuel stepFuel term
  | 0, term =>
      { endpoint := term
        path := .refl term
        endpoint_eq := rfl
        length_le := Nat.le_refl 0
        nonempty_of_reduct := by
          intro positiveFuel
          simp at positiveFuel }
  | stepFuel + 1, term => by
      cases reductsEq : rewriteAt (engineBasePremises relations) language
          contextFuel term with
      | nil =>
          exact {
            endpoint := term
            path := .refl term
            endpoint_eq := by
              simp [normalizeFirstUsing, normalizeFirstAt, reductsEq]
            length_le := Nat.zero_le _
            nonempty_of_reduct := by
              intro _ hasReduct
              exact (hasReduct reductsEq).elim }
      | cons next rest =>
          have firstMember : next ∈
              rewriteAt (engineBasePremises relations) language
                contextFuel term := by
            rw [reductsEq]
            simp
          have firstStep :
              (languageGSLTUsing relations language laws).Step term next :=
            (TotalGSLT.languageGSLTUsing_step relations language laws term next).2
              ((langReducesUsing_iff_execUsing relations language term next).2
                ⟨contextFuel, firstMember⟩)
          let suffix := normalizeFirstRunUsing relations language laws
            contextFuel stepFuel next
          exact {
            endpoint := suffix.endpoint
            path := .cons ⟨firstStep⟩ suffix.path
            endpoint_eq := by
              simpa [normalizeFirstUsing, normalizeFirstAt, reductsEq] using
                suffix.endpoint_eq
            length_le := by
              change suffix.path.length + 1 ≤ stepFuel + 1
              exact Nat.add_le_add_right suffix.length_le 1
            nonempty_of_reduct := by
              intro _ _
              simp [Route.length] }

/-- Executable normalization cannot retain more target edges than its explicit
step budget. -/
theorem normalizeFirstRunUsing_length_le
    (relations : RelationEnv) (language : LanguageDef)
    (laws : ReductionRespectsEquationsUsing relations language)
    (contextFuel stepFuel : Nat) (term : Pattern) :
    (normalizeFirstRunUsing relations language laws contextFuel
      stepFuel term).path.length ≤ stepFuel :=
  (normalizeFirstRunUsing relations language laws contextFuel
    stepFuel term).length_le

/-- With positive step fuel, an available authored reduct forces the retained
normalization path to be nonempty. -/
theorem normalizeFirstRunUsing_length_pos
    (relations : RelationEnv) (language : LanguageDef)
    (laws : ReductionRespectsEquationsUsing relations language)
    (contextFuel stepFuel : Nat) (term : Pattern)
    (positiveFuel : 0 < stepFuel)
    (hasReduct :
      rewriteAt (engineBasePremises relations) language contextFuel term ≠ []) :
    0 < (normalizeFirstRunUsing relations language laws contextFuel
      stepFuel term).path.length :=
  (normalizeFirstRunUsing relations language laws contextFuel
    stepFuel term).nonempty_of_reduct positiveFuel hasReduct

#print axioms normalizeFirstRunUsing_length_le
#print axioms normalizeFirstRunUsing_length_pos

end Mettapedia.GSLT.LanguageDef.NormalizationPath
