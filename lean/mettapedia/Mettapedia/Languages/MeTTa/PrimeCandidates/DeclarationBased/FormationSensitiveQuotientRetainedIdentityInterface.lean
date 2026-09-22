import Mettapedia.TypeTheory.ContextualRetainedIdentityOperations
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientRetainedIdentity
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityNativeReindexing

/-!
# The retained based eliminator on its semantic interpretation image

The domain contains exactly the retained semantic inputs of independently
admitted native tuples. It includes every such tuple, not a chosen class
of motives. Membership contains no desired output or computation premise.
The function is an actual typed semantic term; no source identifier is
part of the input.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientRetainedIdentityInterface

open _root_.CategoryTheory FormationSensitive QuotientIdentity QuotientCwf

open Mettapedia.TypeTheory

variable {signature : Declaration.Signature Tower.Head}

abbrev Input (signature : Declaration.Signature Tower.Head) :=
  ContextualRetainedIdentityOperations.Input (formation (OpaqueRelatorExtension.rules signature))
    (@QuotientIdentityGeometry.reflSection _ (OpaqueRelatorExtension.rules signature))

noncomputable def nativeInput {context : Context (OpaqueRelatorExtension.rules signature)}
    (native : Based.Admitted context) : Input signature where
  body := QuotientIdentityInputCoherence.semanticInput native
  functionType := QType.mk (QuotientIdentityInputCoherence.motiveFunctionType native)
  function := TermFibre.mk (QuotientIdentityInputCoherence.motiveFunction native)

/-- The retained function and method are total typed term classes. Their
relation to the separately stored applied family is supplied by `Scope`. -/
def observation (input : Input signature) :
    QuotientRetainedIdentity.Observation input.body.context.as where
  type := input.body.type
  left := input.body.left
  motiveFunction := input.function.val
  method := input.body.base.val

theorem native_observation {context : Context (OpaqueRelatorExtension.rules signature)}
    (native : Based.Admitted context) :
    observation (nativeInput native) = QuotientRetainedIdentity.observe native := rfl

/-- Membership is an image of independently typed input data, not an
existential witness of elimination, beta, or substitution correctness. -/
def Scope (input : Input signature) : Prop :=
  ∃ native : Based.Admitted input.body.context.as, nativeInput native = input

theorem native_admitted {context : Context (OpaqueRelatorExtension.rules signature)}
    (native : Based.Admitted context) : Scope (nativeInput native) := ⟨native, rfl⟩

noncomputable def run : ContextualRetainedIdentityOperations.Run (Scope (signature := signature)) :=
  fun _input admitted => cast (congrArg (fun next : Input signature => next.Output)
    admitted.choose_spec) admitted.choose.chosenJ

theorem run_representative (input : Input signature) (admitted : Scope input) :
    HEq (run input admitted) admitted.choose.chosenJ := cast_heq _ _

theorem observation_heq {first second : Input signature} (same : first = second) :
    HEq (observation first) (observation second) := by
  cases same
  rfl

theorem run_heq {first second : Input signature} (same : first = second)
    (firstAdmitted : Scope first) (secondAdmitted : Scope second) :
    HEq (run first firstAdmitted) (run second secondAdmitted) := by
  cases same
  rfl

/-- Agreement holds for every admission proof and every admitted native
representative of this retained input, not only its chosen witness. -/
theorem run_native {context : Context (OpaqueRelatorExtension.rules signature)}
    (native : Based.Admitted context) (admitted : Scope (nativeInput native)) :
    run (nativeInput native) admitted = native.chosenJ := by
  apply eq_of_heq
  apply (run_representative (nativeInput native) admitted).trans
  exact QuotientRetainedIdentity.chosen_j_coherent admitted.choose native
    (eq_of_heq (observation_heq admitted.choose_spec))

theorem beta : ContextualRetainedIdentityOperations.Beta
    (run (signature := signature)) := by
  intro input admitted
  have admittedCopy := admitted
  obtain ⟨native, same⟩ := admittedCopy
  have nativeBeta : ∀ h : Scope (nativeInput native),
      tmSub (run (nativeInput native) h)
        (QuotientIdentityGeometry.reflSection (nativeInput native).body.left) =
      (nativeInput native).body.base := by
    intro h
    rw [run_native]
    exact Subtype.ext (QuotientIdentityGeometry.admitted_beta_value native)
  exact (same ▸ nativeBeta) admitted

noncomputable def reindexing : ContextualBasedIdentityOperations.Reindexing
    (formation (OpaqueRelatorExtension.rules signature)) :=
  QuotientIdentityReindexing.reindexing (OpaqueRelatorExtension.rules signature)

theorem section_square : ContextualRetainedIdentityOperations.SectionSquare
    (@QuotientIdentityGeometry.reflSection _ (OpaqueRelatorExtension.rules signature))
    reindexing := QuotientIdentityReindexing.reflexivity_square

private theorem body_ext
    {context : QContext (OpaqueRelatorExtension.rules signature)}
    {type : Ty context} (left : QuotientCwf.Tm context type)
    (firstMotive secondMotive : Ty (ContextualBasedIdentityOperations.basedContext
      (formation (OpaqueRelatorExtension.rules signature)) left))
    (firstBase : QuotientCwf.Tm context
      (tySub firstMotive (QuotientIdentityGeometry.reflSection left)))
    (secondBase : QuotientCwf.Tm context
      (tySub secondMotive (QuotientIdentityGeometry.reflSection left)))
    (motives : firstMotive = secondMotive) (bases : HEq firstBase secondBase) :
    (⟨context, type, left, firstMotive, firstBase⟩ : ContextualBasedIdentityScope.Input
      (formation (OpaqueRelatorExtension.rules signature))
      (@QuotientIdentityGeometry.reflSection _ (OpaqueRelatorExtension.rules signature))) =
      ⟨context, type, left, secondMotive, secondBase⟩ := by
  cases motives
  cases eq_of_heq bases
  rfl

/-- The canonical semantic request substitution is exactly the input of
the actual reindexed native tuple, including its retained function. -/
theorem native_reindex {source target : Context (OpaqueRelatorExtension.rules signature)}
    (native : Based.Admitted target) (substitution : source ⟶ target) :
    (nativeInput native).reindex reindexing section_square (project substitution) =
      nativeInput (native.reindex substitution) := by
  apply ContextualRetainedIdentityOperations.Input.ext
  · apply body_ext
    · exact QuotientIdentityNativeReindexing.canonical_motive_substitution native substitution
    · apply ((nativeInput native).reindexedBase_heq reindexing section_square
        (project substitution)).trans
      apply QuotientComprehensionSyntax.heq_of_value
      exact native.method_substitution substitution
  · exact heq_of_eq (QuotientIdentityNativeReindexing.motive_function_type_reindex
      native substitution).symm
  · apply QuotientComprehensionSyntax.heq_of_value
    exact (QuotientIdentityNativeReindexing.motive_function_reindex native substitution).symm

theorem native_substitution {source target : Context (OpaqueRelatorExtension.rules signature)}
    (native : Based.Admitted target) (admitted : Scope (nativeInput native))
    (substitution : source ⟶ target)
    (base : QuotientCwf.Tm ((quotientProjection _).obj source)
      (tySub (tySub (nativeInput native).body.motive
        (reindexing.map (project substitution) (nativeInput native).body.left))
        (QuotientIdentityGeometry.reflSection
          (tmSub (nativeInput native).body.left (project substitution)))))
    (sameBase : HEq (tmSub (nativeInput native).body.base (project substitution)) base) :
    ∃ reindexedAdmitted : Scope ((nativeInput native).reindexWithBase
        reindexing (project substitution) base),
      tmSub (run (nativeInput native) admitted)
          (reindexing.map (project substitution) (nativeInput native).body.left) =
        run ((nativeInput native).reindexWithBase reindexing (project substitution) base)
          reindexedAdmitted := by
  have inputs := ((nativeInput native).reindexWithBase_eq reindexing section_square
    (project substitution) base sameBase).trans (native_reindex native substitution)
  have admittedTarget : Scope ((nativeInput native).reindexWithBase
      reindexing (project substitution) base) :=
    inputs.symm ▸ native_admitted (native.reindex substitution)
  refine ⟨admittedTarget, ?_⟩
  apply eq_of_heq
  have actual : HEq
      (tmSub (run (nativeInput native) admitted)
        (reindexing.map (project substitution) (nativeInput native).body.left))
      (native.reindex substitution).chosenJ := by
    rw [run_native]
    exact QuotientComprehensionSyntax.heq_of_value
      (QuotientIdentityNativeReindexing.canonical_j_substitution_value native substitution)
  exact actual.trans ((run_heq inputs admittedTarget
    (native_admitted (native.reindex substitution))).trans
      (heq_of_eq (run_native (native.reindex substitution) _))).symm

/-- Every arrow in the quotient has an independently typed native
representative. The resulting law includes all semantic arrows and every
method satisfying the original heterogeneous transport premise. -/
theorem substitution : ContextualRetainedIdentityOperations.Substitution
    (run (signature := signature)) reindexing := by
  intro input admitted
  have admittedCopy := admitted
  obtain ⟨native, same⟩ := admittedCopy
  have nativeStable : ∀ (h : Scope (nativeInput native))
      (source : QContext (OpaqueRelatorExtension.rules signature))
      (sigma : source ⟶ (nativeInput native).body.context)
      (base : QuotientCwf.Tm source
        (tySub (tySub (nativeInput native).body.motive
          (reindexing.map sigma (nativeInput native).body.left))
          (QuotientIdentityGeometry.reflSection (tmSub (nativeInput native).body.left sigma)))),
      HEq (tmSub (nativeInput native).body.base sigma) base →
        ∃ h' : Scope ((nativeInput native).reindexWithBase reindexing sigma base),
          tmSub (run (nativeInput native) h)
              (reindexing.map sigma (nativeInput native).body.left) =
            run ((nativeInput native).reindexWithBase reindexing sigma base) h' := by
    intro h source sigma
    refine Quot.inductionOn sigma ?_
    intro raw
    exact native_substitution native h raw
  exact (same ▸ nativeStable) admitted

theorem beta_substitution (input : Input signature) (admitted : Scope input)
    {source : QContext (OpaqueRelatorExtension.rules signature)}
    (sigma : source ⟶ input.body.context) :
    HEq (tmSub (tmSub (run input admitted) (reindexing.map sigma input.body.left))
      (QuotientIdentityGeometry.reflSection (tmSub input.body.left sigma)))
      (tmSub input.body.base sigma) :=
  ContextualRetainedIdentityOperations.beta_substitution run reindexing section_square
    substitution beta input admitted sigma

#print axioms run_native
#print axioms beta
#print axioms native_reindex
#print axioms substitution
#print axioms beta_substitution

end FormationSensitiveContextual.QuotientRetainedIdentityInterface
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
