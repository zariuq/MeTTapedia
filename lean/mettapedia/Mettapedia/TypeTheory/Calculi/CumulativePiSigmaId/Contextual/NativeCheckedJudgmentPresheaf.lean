import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedSubstitutionCategory
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayFormation

/-!
# Native checked judgments as a proof-retaining presheaf

Substitution acts on actual accepted finite typing certificates. Its strict
identity and composition laws give a presheaf on checked contexts, whose
arrows also retain their image proofs. This is stronger than a family of
unrelated accepted checker results.

Observation maps into the existing conversion-valued formed-term presheaf,
pulled back along certificate erasure. Executable native regularity extracts
type formation from the checked tree. The formation witness is immaterial to the
observation, whose equality is exactly conversion of both subject and type.
Observation is natural but not injective: distinct checked derivations can
have the same subject and type. Neither presheaf is claimed to be initial.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedSubstitution

open Presentation NativeIndexedFamilies NativeJudgmentReplay
open _root_.CategoryTheory

structure JudgmentReceipt (context : Context) where
  subject : Tower.Tm context.arity
  type : Tower.Tm context.arity
  code : Code context.arity
  accepted : check context.raw subject type context.code code = true

@[ext] theorem JudgmentReceipt.ext {context : Context}
    {left right : JudgmentReceipt context}
    (subjects : left.subject = right.subject) (types : left.type = right.type)
    (codes : left.code = right.code) : left = right := by
  cases left
  cases right
  cases subjects
  cases types
  cases codes
  rfl

def JudgmentReceipt.reindex {source target : Context} (receipt : JudgmentReceipt target)
    (morphism : source ⟶ target) : JudgmentReceipt source where
  subject := subst morphism.substitution receipt.subject
  type := subst morphism.substitution receipt.type
  code := substitute morphism.substitution morphism.codes receipt.subject receipt.type receipt.code
  accepted := check_substitute receipt.accepted source.code source.accepted
    morphism.substitution morphism.codes morphism.accepted

theorem JudgmentReceipt.reindex_id {context : Context} (receipt : JudgmentReceipt context) :
    receipt.reindex (𝟙 context) = receipt := by
  apply JudgmentReceipt.ext (subst_ids receipt.subject) (subst_ids receipt.type)
  exact substitute_ids receipt.accepted

theorem JudgmentReceipt.reindex_comp {first middle last : Context}
    (receipt : JudgmentReceipt last) (earlier : first ⟶ middle) (later : middle ⟶ last) :
    receipt.reindex (earlier ≫ later) = (receipt.reindex later).reindex earlier := by
  apply JudgmentReceipt.ext (subst_subComp _ _ receipt.subject).symm
    (subst_subComp _ _ receipt.type).symm
  exact (substitute_comp receipt.accepted later.substitution later.codes
    earlier.substitution earlier.codes).symm

def judgmentReceipts : Contextᵒᵖ ⥤ Type where
  obj context := JudgmentReceipt context.unop
  map morphism := TypeCat.ofHom fun receipt => receipt.reindex morphism.unop
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact JudgmentReceipt.reindex_id receipt
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact JudgmentReceipt.reindex_comp receipt second.unop first.unop

def JudgmentReceipt.formedType {context : Context}
    (receipt : JudgmentReceipt context) : FormationSensitiveContextual.TypeOver context.toFormed := by
  let result := resultFormationValue receipt.accepted
  have specification := resultFormationValue_spec receipt.accepted
  exact ⟨receipt.type, result.1, specification.2.1, (sound specification.2.2).typing⟩

def JudgmentReceipt.formedTerm {context : Context}
    (receipt : JudgmentReceipt context) : FormationSensitiveContextual.Term context.toFormed receipt.formedType :=
  ⟨receipt.subject, (sound receipt.accepted).typing⟩

def JudgmentReceipt.observe {context : Context} (receipt : JudgmentReceipt context) :
    FormationSensitiveContextual.QTerm context.toFormed :=
  FormationSensitiveContextual.QTerm.mk receipt.formedTerm

/-- Replacing a formation witness by the extracted one preserves the
existing conversion-class observation, at the same subject and annotation. -/
theorem JudgmentReceipt.observe_eq_mk {context : Context} (receipt : JudgmentReceipt context)
    {type : FormationSensitiveContextual.TypeOver context.toFormed}
    (term : FormationSensitiveContextual.Term context.toFormed type)
    (sameType : type.code = receipt.type) (sameSubject : term.code = receipt.subject) :
    receipt.observe = FormationSensitiveContextual.QTerm.mk term := by
  apply (FormationSensitiveContextual.QTerm.mk_eq_iff _ _).mpr
  change Conv IntrinsicRelator.rules.headEq receipt.type type.code IntrinsicRelator.rules.computation ∧
    Conv IntrinsicRelator.rules.headEq receipt.subject term.code IntrinsicRelator.rules.computation
  rw [sameType, sameSubject]
  exact ⟨.refl _, .refl _⟩

/-- The formation witness does not add an equality test on universe choices. -/
theorem JudgmentReceipt.observe_eq_iff {context : Context} (left right : JudgmentReceipt context) :
    left.observe = right.observe ↔
      Conv IntrinsicRelator.rules.headEq left.type right.type IntrinsicRelator.rules.computation ∧
      Conv IntrinsicRelator.rules.headEq left.subject right.subject IntrinsicRelator.rules.computation :=
  FormationSensitiveContextual.QTerm.mk_eq_iff left.formedTerm right.formedTerm

/-- Directed checked computation at an unchanged displayed type preserves
conversion-class observation; the two retained certificates need not agree. -/
theorem JudgmentReceipt.observe_eq_of_checkedStep {context : Context}
    (left right : JudgmentReceipt context) (sameType : left.type = right.type)
    (step : NativeRelatorConversionChecking.StepCode context.arity)
    (checked : NativeRelatorConversionChecking.checkStep step left.subject right.subject = true) :
    left.observe = right.observe := by
  apply (JudgmentReceipt.observe_eq_iff _ _).mpr
  constructor
  · rw [sameType]
    exact .refl _
  · exact .rel _ _ (NativeRelatorConversionChecking.step_iff_checked.mpr ⟨step, checked⟩)

theorem JudgmentReceipt.observe_reindex {source target : Context} (receipt : JudgmentReceipt target)
    (morphism : source ⟶ target) :
    (receipt.reindex morphism).observe = receipt.observe.reindex (forget.map morphism) := by
  apply (FormationSensitiveContextual.QTerm.mk_eq_iff _ _).mpr
  exact ⟨.refl _, .refl _⟩

/-- Every existing formed conversion class at a checked context has finite
typing evidence. The replay completeness theorem supplies existence only. -/
theorem JudgmentReceipt.observe_surjective (context : Context) :
    Function.Surjective (JudgmentReceipt.observe (context := context)) := by
  intro value
  induction value using _root_.Quotient.inductionOn with
  | _ pair =>
      obtain ⟨code, accepted⟩ := StructuralTypingReplay.check_complete IntrinsicRelator.rules
        NativeRelatorConversionChecking.check
        (fun conversion => NativeRelatorConversionChecking.conversion_iff_checked.mp conversion)
        pair.2.typed
      let receipt : JudgmentReceipt context := ⟨pair.2.code, pair.1.code, code, by
        simp only [check, StructuralTypingReplay.checkJudgment, Bool.and_eq_true]
        exact ⟨context.accepted, accepted⟩⟩
      exact ⟨receipt, (FormationSensitiveContextual.QTerm.mk_eq_iff _ _).mpr ⟨.refl _, .refl _⟩⟩

def judgmentObservations : Contextᵒᵖ ⥤ Type :=
  forget.op ⋙ FormationSensitiveContextual.QTerm.rawPresheaf IntrinsicRelator.rules

/-- Checked certificate substitution and existing conversion observation commute. -/
def judgmentObservation : judgmentReceipts ⟶ judgmentObservations where
  app _ := TypeCat.ofHom JudgmentReceipt.observe
  naturality _ _ morphism := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact JudgmentReceipt.observe_reindex receipt morphism.unop

namespace Controls

def directReceipt : JudgmentReceipt groundContext :=
  ⟨.refl (.var (0 : Fin 1)), NativeJudgmentReplay.CoherenceControls.identityType,
    NativeJudgmentReplay.CoherenceControls.directProof,
    NativeJudgmentReplay.CoherenceControls.distinct_proofs_both_checked.1⟩

def convertedReceipt : JudgmentReceipt groundContext :=
  ⟨.refl (.var (0 : Fin 1)), NativeJudgmentReplay.CoherenceControls.identityType,
    NativeJudgmentReplay.CoherenceControls.explicitConversionProof,
    NativeJudgmentReplay.CoherenceControls.distinct_proofs_both_checked.2⟩

theorem distinct_receipts : directReceipt ≠ convertedReceipt := by
  intro equal
  have codes := congrArg JudgmentReceipt.code equal
  cases codes

theorem same_observation : directReceipt.observe = convertedReceipt.observe :=
  (JudgmentReceipt.observe_eq_iff _ _).mpr ⟨.refl _, .refl _⟩

theorem observation_not_injective :
    ¬ Function.Injective (judgmentObservation.app (Opposite.op groundContext)) := by
  intro injective
  exact distinct_receipts (injective same_observation)

/-- Image certificates genuinely act on retained derivations, even when
their underlying term substitution is the identity. -/
theorem converted_arrow_changes_receipt :
    directReceipt.reindex convertedIdentity ≠ directReceipt := by
  intro equal
  have codes := congrArg JudgmentReceipt.code equal
  cases codes

theorem converted_arrow_preserves_observation :
    (directReceipt.reindex convertedIdentity).observe = directReceipt.observe := by
  rw [JudgmentReceipt.observe_reindex, erased_arrows_equal]
  change directReceipt.observe.reindex (𝟙 groundContext.toFormed) = directReceipt.observe
  exact FormationSensitiveContextual.QTerm.reindex_id _

/-- An action depending only on the erased term substitution cannot recover
the proof-retaining action, even at this single inhabited context. -/
theorem retained_action_does_not_factor :
    ¬ ∃ action : (groundContext.toFormed ⟶ groundContext.toFormed) →
        JudgmentReceipt groundContext → JudgmentReceipt groundContext,
      ∀ (morphism : groundContext ⟶ groundContext) (receipt : JudgmentReceipt groundContext),
        receipt.reindex morphism = action (forget.map morphism) receipt := by
  rintro ⟨action, factors⟩
  apply converted_arrow_changes_receipt
  calc
    directReceipt.reindex convertedIdentity = action (forget.map convertedIdentity) directReceipt :=
      factors convertedIdentity directReceipt
    _ = action (forget.map (𝟙 groundContext)) directReceipt :=
      congrArg (fun arrow => action arrow directReceipt) erased_arrows_equal
    _ = directReceipt.reindex (𝟙 groundContext) := (factors _ _).symm
    _ = directReceipt := directReceipt.reindex_id

end Controls

#print axioms judgmentReceipts
#print axioms judgmentObservation
#print axioms JudgmentReceipt.observe_eq_iff
#print axioms JudgmentReceipt.observe_eq_of_checkedStep
#print axioms JudgmentReceipt.observe_eq_mk
#print axioms JudgmentReceipt.observe_reindex
#print axioms JudgmentReceipt.observe_surjective
#print axioms Controls.distinct_receipts
#print axioms Controls.observation_not_injective
#print axioms Controls.converted_arrow_changes_receipt
#print axioms Controls.converted_arrow_preserves_observation
#print axioms Controls.retained_action_does_not_factor

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedSubstitution
