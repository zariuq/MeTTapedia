import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllComputation

/-!
# Henkin interpretation and exact cons fibres of the actual All programme

The retained computation proofs are interpreted by independent HOL soundness.
General carriers retain admissibility and extensional equality. At a base
evidence carrier, the original pair projection laws give an actual value-fibre
equivalence with head and recursive evidence, including both inverse laws.
No source identity reflection or full universe interpretation is inferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Interpretation

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Reading
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Computation
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v w
section General
variable {Base : Type u} {Const : HOL.Ty Base → Type v} {evidence : HOL.Ty Base}
    (original : NativeVectorComputationRows.Operations Base Const)
    (pairs : HOL.PredicateSigma.Operations Const evidence) (witness : HOL.ClosedTerm Const evidence)
    (selection : HOL.ClosedTerm Const
      (HOL.SelectionProofs.Selection (original.number ⇒ original.vector ⇒ (evidence ⇒ .prop))))
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ evidence ⇒ .prop)))
    (model : HOL.HenkinModel.{u,v,w} Base Const) (values : model.Valuation Γ)
    (respects : model.FunctionsRespectEqv) (admissible : model.ValuationAdmissible values)
    (holds : HOL.Soundness.SatisfiesHyps model values Δ)

include choice recursion respects admissible holds

theorem nil_eqv : model.Eqv (evidence ⇒ .prop)
    (model.denote (allCode original pairs witness selection A predicate (HOL.weakenCtx Γ original.zero)
      (.app (HOL.weakenCtx Γ (operations original selection).nilCode) A)) values)
    (model.denote (StructuralProfile.identityPredicate witness (fullCode original.number)
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.zero)) values) :=
  HOL.Soundness.extDerivation_sound
    (nil_guard original pairs witness selection A predicate choice recursion).erase respects admissible holds

variable (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector)
    (headLaw : HOL.ProofSyntax Const Δ (operations original selection).headLaw)
    (tailLaw : HOL.ProofSyntax Const Δ (operations original selection).tailLaw)

include headLaw tailLaw

theorem cons_eqv : model.Eqv (evidence ⇒ .prop)
    (model.denote (allCode original pairs witness selection A predicate (.app (HOL.weakenCtx Γ original.successor) index)
      (.app (.app (.app (.app (HOL.weakenCtx Γ (operations original selection).consCode) A) index) head) tail)) values)
    (model.denote (HOL.PredicateSigma.sigma pairs (.app predicate head)
      (.lam (HOL.weaken (allCode original pairs witness selection A predicate index tail)))) values) :=
  HOL.Soundness.extDerivation_sound
    (cons_guard original pairs witness selection A predicate index head tail choice recursion headLaw tailLaw).erase
    respects admissible holds

theorem cons_denote (point : HOL.Ty.denote model.Carrier evidence) (pointAdmitted : model.adm evidence point) :
    (model.denote (allCode original pairs witness selection A predicate (.app (HOL.weakenCtx Γ original.successor) index)
      (.app (.app (.app (.app (HOL.weakenCtx Γ (operations original selection).consCode) A) index) head) tail)) values point).down ↔
    ∃ first, model.adm evidence first ∧ ∃ second, model.adm evidence second ∧
      model.Eqv evidence (HOL.PredicateSigma.pairValue model pairs first second) point ∧
      (model.denote (.app predicate head) values first).down ∧
      (model.denote (allCode original pairs witness selection A predicate index tail) values second).down := by
  have same := model.eqv_arr_apply
    (cons_eqv original pairs witness selection A predicate choice recursion model values respects admissible holds
      index head tail headLaw tailLaw) pointAdmitted
  have interpreted := HOL.PredicateSigma.sigma_apply_denote model pairs (.app predicate head)
    (.lam (HOL.weaken (allCode original pairs witness selection A predicate index tail))) point values
  exact same.trans (by simpa only [HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.Soundness.denote_weaken] using interpreted)

end General

section BaseEvidence
variable {Base : Type u} {Const : HOL.Ty Base → Type v} (base : Base)
    (original : NativeVectorComputationRows.Operations Base Const)
    (pairs : HOL.PredicateSigma.Operations Const (.base base)) (witness : HOL.ClosedTerm Const (.base base))
    (selection : HOL.ClosedTerm Const
      (HOL.SelectionProofs.Selection (original.number ⇒ original.vector ⇒ (.base base ⇒ .prop))))
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ .base base ⇒ .prop))
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ .base base ⇒ .prop)))
    (model : HOL.HenkinModel.{u,v,w} Base Const) (values : model.Valuation Γ)
    (respects : model.FunctionsRespectEqv) (admissible : model.ValuationAdmissible values)
    (holds : HOL.Soundness.SatisfiesHyps model values Δ)
    (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector)
    (headLaw : HOL.ProofSyntax Const Δ (operations original selection).headLaw)
    (tailLaw : HOL.ProofSyntax Const Δ (operations original selection).tailLaw)

/-- The actual cons-program fibre decodes into head and recursive witnesses.
Both inverse laws follow through the retained computation and existing pairing
equivalence; no ambient evidence-carrier induction or surjectivity is required. -/
def cons_fibreEquiv (firstValid : model.models (HOL.PredicateSigma.firstLaw pairs))
    (secondValid : model.models (HOL.PredicateSigma.secondLaw pairs)) :
    {code : model.Carrier base //
      (model.denote (allCode original pairs witness selection A predicate (.app (HOL.weakenCtx Γ original.successor) index)
        (.app (.app (.app (.app (HOL.weakenCtx Γ (operations original selection).consCode) A) index) head) tail)) values code).down} ≃
      TypeTheory.MaterialSets.Pairing.GuardedSigma
        (fun headEvidence => (model.denote (.app predicate head) values headEvidence).down)
        (fun _ tailEvidence => (model.denote (allCode original pairs witness selection A predicate index tail) values tailEvidence).down) := by
  let family : HOL.Term Const Γ (.base base ⇒ .base base ⇒ .prop) :=
    .lam (HOL.weaken (allCode original pairs witness selection A predicate index tail))
  let firstEquiv :
      {code : model.Carrier base //
        (model.denote (allCode original pairs witness selection A predicate (.app (HOL.weakenCtx Γ original.successor) index)
          (.app (.app (.app (.app (HOL.weakenCtx Γ (operations original selection).consCode) A) index) head) tail)) values code).down} ≃
      {code : model.Carrier base // (model.denote (HOL.PredicateSigma.sigma pairs (.app predicate head) family) values code).down} :=
    { toFun := fun code => ⟨code.val, (model.eqv_arr_apply
        (cons_eqv original pairs witness selection A predicate choice recursion model values respects admissible holds
          index head tail headLaw tailLaw) (model.base_mem base code.val)).mp code.property⟩
      invFun := fun code => ⟨code.val, (model.eqv_arr_apply
        (cons_eqv original pairs witness selection A predicate choice recursion model values respects admissible holds
          index head tail headLaw tailLaw) (model.base_mem base code.val)).mpr code.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  have familyMeaning (headEvidence tailEvidence : model.Carrier base) :
      (model.denote family values headEvidence tailEvidence).down ↔
        (model.denote (allCode original pairs witness selection A predicate index tail) values tailEvidence).down := by
    simp only [family, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.Soundness.denote_weaken]
  let lastEquiv : TypeTheory.MaterialSets.Pairing.GuardedSigma
      (fun headEvidence => (model.denote (.app predicate head) values headEvidence).down)
      (fun headEvidence tailEvidence => (model.denote family values headEvidence tailEvidence).down) ≃
      TypeTheory.MaterialSets.Pairing.GuardedSigma
        (fun headEvidence => (model.denote (.app predicate head) values headEvidence).down)
        (fun _ tailEvidence => (model.denote (allCode original pairs witness selection A predicate index tail) values tailEvidence).down) :=
    { toFun := fun value => ⟨value.1, ⟨value.2.val, (familyMeaning value.1.val value.2.val).mp value.2.property⟩⟩
      invFun := fun value => ⟨value.1, ⟨value.2.val, (familyMeaning value.1.val value.2.val).mpr value.2.property⟩⟩
      left_inv := fun value => by rcases value with ⟨first, second, valid⟩; rfl
      right_inv := fun value => by rcases value with ⟨first, second, valid⟩; rfl }
  exact firstEquiv.trans ((HOL.PredicateSigma.fibreEquiv model pairs firstValid secondValid
    (.app predicate head) family values).trans lastEquiv)

end BaseEvidence

#print axioms cons_denote
#print axioms cons_fibreEquiv

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Interpretation
