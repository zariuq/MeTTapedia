import Mettapedia.OSLF.Syntax.FiniteRulePremiseLists
import Mettapedia.OSLF.Syntax.LambdaRuleLocalPremiseComparison

/-!
# Chapter 7 lambda premises as an exact finite rule list

The four authored lambda constructors have zero or one recursive premise.
The list used here is exactly the list of binder-local premises previously
identified for each constructor. The finite-list polynomial and the existing
intrinsic polynomial have equivalent complete derivation trees; in particular,
the LamCong child remains in the context extended by its term binder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaFiniteRulePremiseComparison

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial
open Mettapedia.OSLF.Binding.LambdaRuleLocalPremiseComparison
open Mettapedia.OSLF.Binding.BinderLocalPremise
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

/-- The ordered recursive child judgments of each displayed lambda rule. -/
def premises : {j : Judgment} → RuleShape j → List Judgment
  | _, .beta _ _ => []
  | _, .appCongL source target _ => [judgment source target]
  | _, .appCongR _ source target => [judgment source target]
  | _, .lamCong source target => [judgment source target]

private def emptyPositions : Empty ≃ Fin 0 where
  toFun := fun impossible => impossible.elim
  invFun := fun impossible => impossible.elim0
  left_inv := fun impossible => impossible.elim
  right_inv := fun impossible => impossible.elim0

private def onePosition : Unit ≃ Fin 1 where
  toFun := fun _ => ⟨0, by decide⟩
  invFun := fun _ => ()
  left_inv := by
    intro value
    cases value
    rfl
  right_inv := by
    intro value
    fin_cases value
    rfl

/-- Beta has no recursive position; each congruence constructor has the
single listed position, including abstraction congruence below a binder. -/
def positionEquiv : {j : Judgment} → (shape : RuleShape j) →
    premisePosition shape ≃ Fin (premises shape).length
  | _, .beta _ _ => emptyPositions
  | _, .appCongL _ _ _ => onePosition
  | _, .appCongR _ _ _ => onePosition
  | _, .lamCong _ _ => onePosition

/-- The existing polynomial's child index is exactly the entry addressed
in the authored finite premise list. -/
def listing : FiniteRulePremiseLists.Listing rules where
  premises := fun _ _ shape => premises shape
  positions := fun _ _ shape => positionEquiv shape
  next_eq := by
    intro b i shape position
    cases shape with
    | beta body arg => exact position.elim
    | appCongL source target arg =>
        cases position
        rfl
    | appCongR funTerm source target =>
        cases position
        rfl
    | lamCong source target =>
        cases position
        rfl

/-- Read the context extension and term pair from a binder-local premise. -/
def localIndex {Γ : Ctx sig} (premise : LocalStepPremise sig Γ) : Judgment :=
  match premise with
  | ⟨_binders, .term, source, target⟩ => judgment source target

theorem localIndex_context {Γ : Ctx sig}
    (premise : LocalStepPremise sig Γ) :
    (localIndex premise).1 = premise.binders ++ Γ := by
  cases premise with
  | mk binders sort source target =>
      cases sort
      rfl

/-- The finite list is not a second choice of premises: it is the image of
the already checked local-premise assignment, in source order. -/
theorem premises_are_local {j : Judgment} (shape : RuleShape j) :
    premises shape =
      (localPremise shape).toList.map localIndex := by
  cases shape <;> rfl

/-- Every lambda derivation has a uniquely corresponding derivation in the
finite premise-list polynomial, and conversely. -/
noncomputable def treeEquiv (j : Judgment) :
    rules.Fix () j ≃ listing.polynomial.Fix () j :=
  listing.treeEquiv () j

/-- The list polynomial generates exactly the original four-rule reduction
relation, for open as well as closed contexts. -/
theorem step_iff_listed {Γ : Ctx sig}
    {source target : Term sig Γ .term} :
    LambdaContextualRung.Step Γ source target ↔
      Nonempty (listing.polynomial.Fix () (judgment source target)) :=
  step_iff_derivation.trans (listing.nonempty_iff () (judgment source target))

/-- The actual lambda reduction relation interprets each finite premise
list, including the child indexed by LamCong's extended context. -/
theorem contextualStep_listed_closed :
    FiniteRulePremiseLists.RuleClosed listing.polynomial
      (fun _ j => LambdaContextualRung.Step j.1 j.2.1 j.2.2) := by
  apply (listing.ruleClosed_iff
    (fun _ j => LambdaContextualRung.Step j.1 j.2.1 j.2.2)).mp
  intro b j shape children
  exact contextualStep_closed j shape (fun position => children position)

/-- The source lambda relation is least among predicate interpretations
closed under these actual ordered premise lists. -/
theorem contextualStep_listed_least
    (relation : Judgment → Prop)
    (closed : FiniteRulePremiseLists.RuleClosed listing.polynomial
      (fun _ j => relation j))
    {Γ : Ctx sig} {source target : Term sig Γ .term}
    (step : LambdaContextualRung.Step Γ source target) :
    relation (judgment source target) := by
  apply contextualStep_least relation
  · intro j shape children
    exact (listing.ruleClosed_iff (fun _ j => relation j)).mpr
      closed () j shape children
  · exact step

/-- A false predicate cannot be a model of the list rules: beta has no
premise and has a concrete conclusion. -/
theorem false_not_listed_closed :
    ¬ FiniteRulePremiseLists.RuleClosed listing.polynomial
      (fun _ _ => False) := by
  intro closed
  apply false_not_closed
  intro j shape children
  exact (listing.ruleClosed_iff (fun _ _ => False)).mpr
    closed () j shape children

/-- The concrete closed LamCong tree translates to a list derivation whose
single child remains the open beta firing below one term binder. -/
noncomputable def listedClosedLamTree :
    listing.polynomial.Fix ()
      (judgment
        (lamT (appT
          (lamT (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term)))
          (Term.var (Var.zero : Var [Srt.term] Srt.term))))
        (lamT (inst
          (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term))
          (Term.var (Var.zero : Var [Srt.term] Srt.term))))) :=
  treeEquiv _ closedLamTree

/-- No finite-list derivation starts from a lone variable. -/
theorem variable_has_no_listed_derivation {Γ : Ctx sig}
    (v : Var Γ .term) {target : Term sig Γ .term} :
    ¬ Nonempty (listing.polynomial.Fix ()
      (judgment (.var v) target)) := by
  intro inhabited
  exact variable_has_no_derivation v
    ((listing.nonempty_iff () (judgment (.var v) target)).mpr inhabited)

#print axioms listing
#print axioms treeEquiv
#print axioms step_iff_listed
#print axioms contextualStep_listed_closed
#print axioms contextualStep_listed_least
#print axioms false_not_listed_closed
#print axioms listedClosedLamTree
#print axioms variable_has_no_listed_derivation

end Mettapedia.OSLF.Binding.LambdaFiniteRulePremiseComparison
