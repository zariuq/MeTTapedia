import Mettapedia.Languages.HOLLight.AdmittedMembershipCompilation
import Mettapedia.Logic.HOL.TermInterpretationLaws

/-!
# Exact premise framing for membership-schema composition

Three native hypothesis discharges keep the complete child-condition premise.
Its quantified syntax is distinct from both two-argument parent queries,
independently of variable names and carrier identifications. The distinction
concerns unreduced canonical syntax, not logical inequivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.AdmittedMembershipFraming
open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ReverseTranslation AdmittedMembershipCompilation
open Mettapedia.GSLT.LanguageDef
universe u v

theorem universal_ne_two_app {Γ : HOL.Ctx AtomicTy} {domain first second : HOL.Ty AtomicTy}
    (names : Naming Γ) (body : HOL.Formula Symbol (domain :: Γ))
    (function : HOL.Term Symbol Γ (.arr first (.arr second .prop)))
    (a : HOL.Term Symbol Γ first) (b : HOL.Term Symbol Γ second) :
    reverseCanonical names (HOL.ImpredicativeConnectives.expand (.all body)) ≠
      reverseCanonical names (HOL.ImpredicativeConnectives.expand (.app (.app function a) b)) := by
  intro same
  have raw := congrArg CanonicalTerm.term same
  simp only [reverseCanonical_term, HOL.ImpredicativeConnectives.expand,
    reverseTerm, reverseTermWith, ExcludedMiddle.forallDB] at raw
  cases (DBTerm.app.inj raw).1

theorem childConditions_ne_two_app {Base : Type u} {Const : HOL.Ty Base → Type v}
    {Γ : HOL.Ctx Base} (interp : HOL.TermInterpretation Base Const AtomicTy Symbol)
    (names : Naming (Γ.map (HOL.Ty.substitute interp.types)))
    (signature : HOL.RecursiveSpacePredicate.Contextual Const Γ)
    (predicate : HOL.Term Const Γ (.arr signature.space .prop))
    (payload : HOL.Term Const Γ signature.payload)
    (ch : HOL.Term Const Γ (.arr signature.number signature.space))
    {first second : HOL.Ty Base} (function : HOL.Term Const Γ (.arr first (.arr second .prop)))
    (a : HOL.Term Const Γ first) (b : HOL.Term Const Γ second) :
    reverseCanonical (τ := .prop) names (HOL.ImpredicativeConnectives.expand
      (interp.term (signature.childConditions predicate payload ch))) ≠
    reverseCanonical (τ := .prop) names (HOL.ImpredicativeConnectives.expand
      (interp.term (.app (.app function a) b))) := by
  unfold HOL.RecursiveSpacePredicate.Contextual.childConditions
  rw [HOL.TermInterpretation.term_all, HOL.TermInterpretation.term_app, HOL.TermInterpretation.term_app]
  exact universal_ne_two_app names _ _ _ _

theorem childConditions_ne_shapeAt {Base : Type u} {Const : HOL.Ty Base → Type v}
    {Γ : HOL.Ctx Base} (interp : HOL.TermInterpretation Base Const AtomicTy Symbol)
    (names : Naming (Γ.map (HOL.Ty.substitute interp.types)))
    (signature : HOL.RecursiveSpacePredicate.Contextual Const Γ)
    (predicate : HOL.Term Const Γ (.arr signature.space .prop))
    (t : HOL.Term Const Γ signature.number) (payload : HOL.Term Const Γ signature.payload)
    (ch : HOL.Term Const Γ (.arr signature.number signature.space)) :
    reverseCanonical (τ := .prop) names (HOL.ImpredicativeConnectives.expand
      (interp.term (signature.childConditions predicate payload ch))) ≠
    reverseCanonical (τ := .prop) names (HOL.ImpredicativeConnectives.expand
      (interp.term (signature.shapeAt t payload))) := by
  unfold HOL.RecursiveSpacePredicate.Contextual.shapeAt
  exact childConditions_ne_two_app interp names signature predicate payload ch
    signature.validShape t payload

theorem three_discharge_hypotheses
    (shape constructor joined root : Theorem) (condition : CanonicalTerm)
    (shapeEmpty : shape.sequent.hyp = ∅)
    (constructorHyps : constructor.sequent.hyp = {shape.sequent.concl, condition})
    (joinedHyps : joined.sequent.hyp = {constructor.sequent.concl, root.sequent.concl})
    (rootEmpty : root.sequent.hyp = ∅)
    (conditionShape : condition ≠ shape.sequent.concl)
    (conditionRoot : condition ≠ root.sequent.concl) :
    (HypothesisExpansion.proveHypResult root
      (HypothesisExpansion.proveHypResult (HypothesisExpansion.proveHypResult shape constructor) joined)).sequent.hyp =
        {condition} := by
  simp only [HypothesisExpansion.proveHypResult, Theorem.unionResult]
  rw [shapeEmpty, constructorHyps, joinedHyps, rootEmpty]
  simp only [Finset.empty_union]
  ext hypothesis
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨differentRoot, first | second⟩
    · exact (first.2.resolve_left first.1)
    · exact False.elim (differentRoot (second.2.resolve_left second.1))
  · intro same
    subst hypothesis
    exact ⟨conditionRoot, Or.inl ⟨conditionShape, Or.inr rfl⟩⟩

def applicationSpine : DBTerm → Nat
  | .app (.abs _ _) _ => 0
  | .app (.app _ _) _ => 1
  | _ => 2

def canonicalSpine (term : CanonicalTerm) : Nat := applicationSpine term.term

theorem interpreted_all_spine {Base : Type u} {Const : HOL.Ty Base → Type v}
    {Γ : HOL.Ctx Base} {domain : HOL.Ty Base}
    (interp : HOL.TermInterpretation Base Const AtomicTy Symbol)
    (names : Naming (Γ.map (HOL.Ty.substitute interp.types)))
    (body : HOL.Formula Const (domain :: Γ)) :
    canonicalSpine (reverseCanonical (τ := .prop) names
      (HOL.ImpredicativeConnectives.expand (interp.term (.all body)))) = 0 := by
  rw [HOL.TermInterpretation.term_all]
  rfl

theorem interpreted_childConditions_spine {Base : Type u} {Const : HOL.Ty Base → Type v}
    {Γ : HOL.Ctx Base}
    (interp : HOL.TermInterpretation Base Const AtomicTy Symbol)
    (names : Naming (Γ.map (HOL.Ty.substitute interp.types)))
    (sig : HOL.RecursiveSpacePredicate.Contextual Const Γ)
    (pred : HOL.Term Const Γ (.arr sig.space .prop))
    (payload : HOL.Term Const Γ sig.payload)
    (ch : HOL.Term Const Γ (.arr sig.number sig.space)) :
    canonicalSpine (reverseCanonical (τ := .prop) names
      (HOL.ImpredicativeConnectives.expand (interp.term (sig.childConditions pred payload ch)))) = 0 := by
  unfold HOL.RecursiveSpacePredicate.Contextual.childConditions
  exact interpreted_all_spine interp names _

theorem interpreted_two_app_spine {Base : Type u} {Const : HOL.Ty Base → Type v}
    {Γ : HOL.Ctx Base} (interp : HOL.TermInterpretation Base Const AtomicTy Symbol)
    (names : Naming (Γ.map (HOL.Ty.substitute interp.types)))
    {first second : HOL.Ty Base} (fn : HOL.Term Const Γ (.arr first (.arr second .prop)))
    (a : HOL.Term Const Γ first) (b : HOL.Term Const Γ second) :
    canonicalSpine (reverseCanonical (τ := .prop) names
      (HOL.ImpredicativeConnectives.expand (interp.term (.app (.app fn a) b)))) = 1 := by
  rw [HOL.TermInterpretation.term_app, HOL.TermInterpretation.term_app]
  rfl

theorem interpreted_shapeAt_spine {Base : Type u} {Const : HOL.Ty Base → Type v}
    {Γ : HOL.Ctx Base} (interp : HOL.TermInterpretation Base Const AtomicTy Symbol)
    (names : Naming (Γ.map (HOL.Ty.substitute interp.types)))
    (sig : HOL.RecursiveSpacePredicate.Contextual Const Γ)
    (t : HOL.Term Const Γ sig.number) (payload : HOL.Term Const Γ sig.payload) :
    canonicalSpine (reverseCanonical (τ := .prop) names
      (HOL.ImpredicativeConnectives.expand (interp.term (sig.shapeAt t payload)))) = 1 := by
  unfold HOL.RecursiveSpacePredicate.Contextual.shapeAt
  exact interpreted_two_app_spine interp names sig.validShape t payload

variable (operations : Operations) (callerNames : Naming (NativeContext operations))

private theorem naming_eta : (fun {τ} => @callerNames τ) = @callerNames := rfl

private theorem parentShape_eta :
    parentShape operations callerNames = parentShape operations @callerNames :=
  congrArg (parentShape operations) (naming_eta operations @callerNames)

private theorem parentRoot_eta :
    parentRoot operations callerNames = parentRoot operations @callerNames :=
  congrArg (parentRoot operations) (naming_eta operations @callerNames)

private theorem parentShape_at_eq :
    parentShape operations @callerNames = (compiledParentShape operations callerNames).proof := rfl

private theorem parentRoot_at_eq :
    parentRoot operations @callerNames = (compiledParentRoot operations callerNames).proof := rfl

theorem parentShape_eq_compiled :
    parentShape operations callerNames = (compiledParentShape operations callerNames).proof :=
  (parentShape_eta operations @callerNames).trans (parentShape_at_eq operations @callerNames)

theorem parentRoot_eq_compiled :
    parentRoot operations callerNames = (compiledParentRoot operations callerNames).proof :=
  (parentRoot_eta operations @callerNames).trans (parentRoot_at_eq operations @callerNames)

theorem reverseHypotheses_nil :
    reverseHypotheses (Γ := NativeContext operations) callerNames [] = ∅ := rfl

theorem parentShape_hypotheses : (parentShape operations callerNames).result.sequent.hyp = ∅ :=
  (congrArg (fun p => p.result.sequent.hyp) (parentShape_eq_compiled operations @callerNames)).trans
    ((compiledParentShape operations callerNames).hypotheses_exact.trans
      (reverseHypotheses_nil operations @callerNames))

theorem parentRoot_hypotheses : (parentRoot operations callerNames).result.sequent.hyp = ∅ :=
  (congrArg (fun p => p.result.sequent.hyp) (parentRoot_eq_compiled operations @callerNames)).trans
    ((compiledParentRoot operations callerNames).hypotheses_exact.trans
      (reverseHypotheses_nil operations @callerNames))

def conditionCode : CanonicalTerm := reverseCanonical (Γ := NativeContext operations) (τ := .prop) callerNames
  (HOL.ImpredicativeConnectives.expand (Γ := NativeContext operations) (τ := .prop) ((interpretation operations).term
    (Γ := AdmittedContainerProofControls.Open.context) (type := .prop) conditions))

theorem condition_spine : canonicalSpine (conditionCode operations callerNames) = 0 := by
  unfold conditionCode AdmittedMembershipCompilation.conditions
  exact interpreted_childConditions_spine (Γ := AdmittedContainerProofControls.Open.context)
    (interpretation operations) callerNames descriptor descriptor.least data children

theorem parentShape_spine : canonicalSpine (parentShape operations callerNames).result.sequent.concl = 1 :=
  (congrArg (fun p => canonicalSpine p.result.sequent.concl) (parentShape_eq_compiled operations @callerNames)).trans
    ((congrArg canonicalSpine (compiledParentShape operations callerNames).conclusion_exact).trans
      (interpreted_shapeAt_spine (Γ := AdmittedContainerProofControls.Open.context)
        (interpretation operations) callerNames descriptor tag data))

theorem parentRoot_spine : canonicalSpine (parentRoot operations callerNames).result.sequent.concl = 1 :=
  (congrArg (fun p => canonicalSpine p.result.sequent.concl) (parentRoot_eq_compiled operations @callerNames)).trans
    ((congrArg canonicalSpine (compiledParentRoot operations callerNames).conclusion_exact).trans
      (interpreted_two_app_spine (Γ := AdmittedContainerProofControls.Open.context)
        (interpretation operations) callerNames
        rootTerm (descriptor.constructValue tag data children) target))

theorem condition_ne_parentShape : conditionCode operations callerNames ≠
    (parentShape operations callerNames).result.sequent.concl := by
  intro same
  have impossible := (condition_spine operations @callerNames).symm.trans
    ((congrArg canonicalSpine same).trans (parentShape_spine operations @callerNames))
  exact Nat.zero_ne_one impossible

theorem condition_ne_parentRoot : conditionCode operations callerNames ≠
    (parentRoot operations callerNames).result.sequent.concl := by
  intro same
  have impossible := (condition_spine operations @callerNames).symm.trans
    ((congrArg canonicalSpine same).trans (parentRoot_spine operations @callerNames))
  exact Nat.zero_ne_one impossible

#print axioms universal_ne_two_app
#print axioms three_discharge_hypotheses
#print axioms condition_ne_parentShape
#print axioms condition_ne_parentRoot
#print axioms parentShape_hypotheses
#print axioms parentRoot_hypotheses

end Mettapedia.Languages.HOLLight.AdmittedMembershipFraming
