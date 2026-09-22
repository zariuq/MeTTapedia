import Mettapedia.Languages.OpenTheory.DerivedRulesConnectives
import Mettapedia.Languages.OpenTheory.EtaNotDerivable

/-!
# Eta and function extensionality from one axiom

OpenTheory's standard axiom `axiomOfExtensionality` is
`⊢ ∀d. (λe. d e) = d` for `d : A → B`, with type variables `A` and `B`.  The
policy `etaAxiomPolicy` admits exactly its free-variable form
`EtaAxiom.sequent`, `⊢ (λx. d x) = d` with `d` a free variable (the sequent
`Eta.equation` of `EtaNotDerivable.lean`).  From it:

* `etaVar`: the primitive `subst` rule instantiates the type variables, giving
  eta for the variable `d` at every function type;
* `eta`: abstraction over `d`, `apThm` and two beta conversions give
  `⊢ (λx. t x) = t` for every closed term `t` of function type; in de Bruijn
  form `x` cannot occur in `t`, and `etaNamed` states the named form with the
  side condition that `x` is not free in `t`;
* `ext`: from `A ⊢ ∀x. f x = g x`, with `x` not free in `f` or `g`, derive
  `A ⊢ f = g`, by SPEC at a fresh variable, ABS, and `eta` on both sides
  (HOL Light's `EQ_EXT`); `extNamed` states the named form.

Every statement holds for any policy that admits the eta sequent.

Controls: eta for a free variable `f` is provable under `etaAxiomPolicy`
(`etaVariable_provable`) and not under the empty policy
(`etaVariable_not_provable_without_axiom`); the side condition of `etaNamed`
carries weight (`etaNamed_side_condition_needed`), and so does the freshness
condition of GEN under the eta policy (`gen_freshness_needed_with_eta`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic
open CanonicalTerm (equalityDB)
open DBTerm (instantiateAt closeFreeAt FreeOccurrence inferType_app_of inferType_abs_of
  instantiateAt_closed)
open DerivedRules

namespace EtaAxiom

/-- The type variable `A` of the axiom of extensionality. -/
def domainName : Name := Name.global "A"

/-- The type variable `B` of the axiom of extensionality. -/
def codomainName : Name := Name.global "B"

/-- The variable `d : A → B` of the axiom of extensionality. -/
def functionName : Name := Name.global "d"

/-- The free-variable form `⊢ (λx. d x) = d` of the axiom of extensionality. -/
def sequent : Sequent :=
  ⟨∅, Eta.equation functionName (.var domainName) (.var codomainName)⟩

theorem sequent_isBool : sequent.IsBool :=
  ⟨rfl, fun _ hterm => absurd hterm (Finset.notMem_empty _)⟩

/-- The type substitution `A ↦ domain, B ↦ codomain`, with no term maplets. -/
def instantiateTypes (domain codomain : Ty) : TypeCorrectTermSubstitution :=
  ⟨⟨⟨[(domainName, domain), (codomainName, codomain)]⟩, []⟩,
    fun _ hentry => absurd hentry List.not_mem_nil⟩

theorem applyDB_equationDB (domain codomain : Ty) :
    (instantiateTypes domain codomain).raw.applyDB
        (Eta.equationDB functionName (.var domainName) (.var codomainName)) =
      Eta.equationDB functionName domain codomain := by
  have distinct : (codomainName == domainName) = false := by decide
  simp [instantiateTypes, Eta.equationDB, Eta.expansionDB, Eta.functionVar, equalityDB,
    TermSubst.applyDB, TermSubst.lookup, TypeSubst.applyVar, TypeSubst.lookup, List.lookup,
    distinct]

end EtaAxiom

/-- The axiom policy admitting exactly the eta sequent `⊢ (λx. d x) = d`. -/
def etaAxiomPolicy : AxiomPolicy := fun sequent => sequent = EtaAxiom.sequent

theorem etaAxiomPolicy_translatedProvable :
    ∀ sequent, etaAxiomPolicy sequent → TranslatedProvable ∅ sequent := by
  rintro sequent rfl
  exact Eta.equation_translatedProvable _ _ _

namespace KernelProvable

variable {policy : AxiomPolicy}

/-- The eta axiom: `⊢ (λx. d x) = d` for `d : A → B`. -/
theorem etaAxiom (admitted : policy EtaAxiom.sequent) :
    KernelProvable policy ∅
      (Eta.equationDB EtaAxiom.functionName (.var EtaAxiom.domainName)
        (.var EtaAxiom.codomainName)) :=
  «axiom» _ admitted EtaAxiom.sequent_isBool

/-- Eta for the variable `d` at every function type, by type instantiation. -/
theorem etaVar (admitted : policy EtaAxiom.sequent) (domain codomain : Ty) :
    KernelProvable policy ∅ (Eta.equationDB EtaAxiom.functionName domain codomain) := by
  have h := (etaAxiom admitted).subst (EtaAxiom.instantiateTypes domain codomain)
  rw [EtaAxiom.applyDB_equationDB] at h
  exact h.congr_hyp (by simp [TypeCorrectTermSubstitution.applyHypotheses])

/-- ETA: `⊢ (λx. t x) = t` for every closed term `t` of function type. -/
theorem eta (admitted : policy EtaAxiom.sequent) {domain codomain : Ty} {function : DBTerm}
    (hfunction : function.inferType [] = some (.function domain codomain)) :
    KernelProvable policy ∅
      (equalityDB (.function domain codomain) (.abs domain (.app function (.bound 0)))
        function) := by
  have habs := abs (Eta.functionVar EtaAxiom.functionName domain codomain)
    (etaVar admitted domain codomain) fun ⟨_, hterm, _⟩ => absurd hterm (Finset.notMem_empty _)
  simp only [Eta.expansionDB, closeFreeAt, sourceVarSame_eq_true_iff, if_true] at habs
  have happ := apThm habs hfunction
  obtain ⟨hredexLeft, hredexRight⟩ := inferType_equality_operands happ
  have hleft := betaConv_of_instantiateAt_eq (policy := policy) hredexLeft
    (result := .abs domain (.app function (.bound 0)))
    (by simp [instantiateAt])
  have hright := betaConv_of_instantiateAt_eq (policy := policy) hredexRight (result := function)
    (by simp)
  exact (trans (trans (sym hleft) happ) hright).congr_hyp (by simp)

/-- ETA in named form: `⊢ (λx. t x) = t` when `x` is not free in `t`. -/
theorem etaNamed (admitted : policy EtaAxiom.sequent) (sourceVar : SourceVar)
    {codomain : Ty} {function : DBTerm}
    (hfunction : function.inferType [] = some (.function sourceVar.ty codomain))
    (absent : ¬ FreeOccurrence sourceVar function) :
    KernelProvable policy ∅
      (equalityDB (.function sourceVar.ty codomain)
        (.abs sourceVar.ty (closeFreeAt sourceVar 0 (.app function (.free sourceVar))))
        function) := by
  have hclose : closeFreeAt sourceVar 0 (.app function (.free sourceVar)) =
      .app function (.bound 0) := by
    simp [closeFreeAt, DBTerm.closeFreeAt_of_not_freeOccurrence absent]
  rw [hclose]
  exact eta admitted hfunction

/-- EXT: from `A ⊢ ∀x. f x = g x`, with `f` and `g` closed (so `x` is free in
neither), derive `A ⊢ f = g`. -/
theorem ext (admitted : policy EtaAxiom.sequent) {hyp : Finset CanonicalTerm}
    {domain codomain : Ty} {left right : DBTerm}
    (closedLeft : left.LooseBelow 0) (closedRight : right.LooseBelow 0)
    (h : KernelProvable policy hyp (forallAppDB domain (.abs domain
      (equalityDB codomain (.app left (.bound 0)) (.app right (.bound 0)))))) :
    KernelProvable policy hyp (equalityDB (.function domain codomain) left right) := by
  obtain ⟨hpredicate, -⟩ := inferType_forallAppDB_iff.mp h.inferType
  obtain ⟨_, hbody, hfunction⟩ := DBTerm.inferType_abs_eq_some_iff.mp hpredicate
  obtain ⟨-, rfl⟩ := Ty.function_inj hfunction
  obtain ⟨happLeft, happRight, -⟩ := DBTerm.inferType_equalityDB_iff.mp hbody
  have closedType : ∀ {term : DBTerm}, term.LooseBelow 0 →
      (DBTerm.app term (.bound 0)).inferType [domain] = some codomain →
        term.inferType [] = some (.function domain codomain) := by
    intro term closed happ
    obtain ⟨domain', hterm, hbound⟩ := DBTerm.inferType_app_eq_some_iff.mp happ
    obtain rfl : domain' = domain := by simpa using hbound.symm
    rwa [DBTerm.inferType_of_looseBelow_zero closed] at hterm
  have hleft := closedType closedLeft happLeft
  have hright := closedType closedRight happRight
  obtain ⟨sourceVar, hsourceVar, fresh, freshTerms⟩ :=
    exists_fresh_var domain hyp [left, right]
  have hspec := spec h (argument := .free sourceVar) (by simp [hsourceVar])
  have hinstance : instantiateAt (.free sourceVar) 0
      (equalityDB codomain (.app left (.bound 0)) (.app right (.bound 0))) =
      equalityDB codomain (.app left (.free sourceVar)) (.app right (.free sourceVar)) := by
    simp [equalityDB, instantiateAt, instantiateAt_closed hleft, instantiateAt_closed hright]
  rw [hinstance] at hspec
  have habs := abs sourceVar hspec fresh
  have hclose : ∀ {term : DBTerm}, ¬ FreeOccurrence sourceVar term →
      closeFreeAt sourceVar 0 (.app term (.free sourceVar)) = .app term (.bound 0) := by
    intro term absent
    simp [closeFreeAt, DBTerm.closeFreeAt_of_not_freeOccurrence absent]
  rw [hclose (freshTerms left (by simp)), hclose (freshTerms right (by simp)), hsourceVar] at habs
  exact (trans (trans (sym (eta admitted hleft)) habs) (eta admitted hright)).congr_hyp
    (by simp)

/-- EXT in named form: from `A ⊢ ∀x. f x = g x`, with `x` not free in the
closed terms `f` and `g`, derive `A ⊢ f = g`. -/
theorem extNamed (admitted : policy EtaAxiom.sequent) {hyp : Finset CanonicalTerm}
    (sourceVar : SourceVar) {codomain : Ty} {left right : DBTerm}
    (closedLeft : left.LooseBelow 0) (closedRight : right.LooseBelow 0)
    (absentLeft : ¬ FreeOccurrence sourceVar left)
    (absentRight : ¬ FreeOccurrence sourceVar right)
    (h : KernelProvable policy hyp (forallAppDB sourceVar.ty (.abs sourceVar.ty
      (closeFreeAt sourceVar 0 (equalityDB codomain (.app left (.free sourceVar))
        (.app right (.free sourceVar))))))) :
    KernelProvable policy hyp (equalityDB (.function sourceVar.ty codomain) left right) := by
  simp only [equalityDB, closeFreeAt, sourceVarSame_eq_true_iff, if_true,
    DBTerm.closeFreeAt_of_not_freeOccurrence absentLeft,
    DBTerm.closeFreeAt_of_not_freeOccurrence absentRight] at h
  exact ext admitted closedLeft closedRight h

end KernelProvable

/-! ## Controls -/

namespace DerivedRulesEtaExamples

open KernelProvable BindingExamples DerivedRulesExamples

/-- The free variable `f : ind → bool`. -/
def fVar : SourceVar := ⟨Name.global "f", .function Examples.individual Ty.bool⟩

/-- Positive control: `⊢ (λx. f x) = f` under the eta policy. -/
theorem etaVariable_provable :
    KernelProvable etaAxiomPolicy ∅
      (Eta.equationDB (Name.global "f") Examples.individual Ty.bool) :=
  eta (policy := etaAxiomPolicy) rfl (domain := Examples.individual) (codomain := Ty.bool)
    (function := .free fVar) (by simp [fVar])

/-- The eta policy is needed: the axiom-free kernel does not prove
`⊢ (λx. f x) = f`. -/
theorem etaVariable_not_provable_without_axiom :
    ¬ KernelProvable emptyAxiomPolicy ∅
      (Eta.equationDB (Name.global "f") Examples.individual Ty.bool) := by
  rintro ⟨out, hout, hhyp, hconcl⟩
  exact Eta.eta_not_derivable (Name.global "f") Examples.individual Ty.bool hout
    (Sequent.ext hhyp (CanonicalTerm.ext_term hconcl))

/-- `λy. x`, a term in which `x` is free. -/
def constantXDB : DBTerm := .abs Examples.individual (.free xIndividual)

/-- `(λx. (λy. x) x) = (λy. x)`: ETA in named form at a term in which the bound
variable is free. -/
def capturedEtaDB : DBTerm :=
  equalityDB (.function Examples.individual Examples.individual)
    (.abs xIndividual.ty (closeFreeAt xIndividual 0 (.app constantXDB (.free xIndividual))))
    constantXDB

theorem capturedEtaDB_eq :
    capturedEtaDB = equalityDB (.function Examples.individual Examples.individual)
      (.abs Examples.individual (.app (.abs Examples.individual (.bound 1)) (.bound 0)))
      constantXDB := by
  have hty : xIndividual.ty = Examples.individual := rfl
  simp [capturedEtaDB, constantXDB, closeFreeAt, hty]

/-- The target formula `(λx. (λy. x) x) = (λy. x)`. -/
def capturedEtaFormula : HOL.ClosedFormula Symbol :=
  .eq (.lam (.app (.lam (.var (.vs .vz))) (.var .vz)))
    (.lam (.const (Symbol.ofVar xIndividual)))

theorem capturedEtaDB_translates : Translates [] capturedEtaDB .prop capturedEtaFormula := by
  rw [capturedEtaDB_eq]
  exact .equalityApp (equalityOperand?_equality _) (Ty.toHOL_function _ _)
    (.abs rfl (.app rfl (.abs rfl (.bound (.vs .vz))) (.bound .vz))) (.abs rfl (.free rfl))

/-- In the two-point model, `λx. (λy. x) x` is the identity and `λy. x` is
constant. -/
theorem twoPointModel_not_models_captured_eta {τ : HOL.Ty AtomicTy} (symbol : Symbol τ)
    (base : ∃ b, τ = .base b) :
    ¬ twoPointModel.models
      (.eq (.lam (.app (.lam (.var (.vs .vz))) (.var .vz)) : HOL.ClosedTerm Symbol (.arr τ τ))
        (.lam (.const symbol))) := by
  obtain ⟨b, rfl⟩ := base
  intro holds
  exact Bool.noConfusion (congrArg ULift.down (holds (ULift.up true) trivial))

/-- **Negative control: the side condition of `etaNamed` carries weight.**  At
`t = λy. x`, where `x` is free, the named eta equation
`(λx. (λy. x) x) = (λy. x)` is not provable under the eta policy: in the
two-point model its left side is the identity and its right side is
constant. -/
theorem etaNamed_side_condition_needed :
    FreeOccurrence xIndividual constantXDB ∧
      ¬ KernelProvable etaAxiomPolicy ∅ capturedEtaDB := by
  refine ⟨.absBody .here, fun h => ?_⟩
  obtain ⟨φ, hφ, holds⟩ :=
    twoPointModel_of_kernelProvable etaAxiomPolicy_translatedProvable h
  rw [hφ.unique_eq capturedEtaDB_translates] at holds
  exact twoPointModel_not_models_captured_eta (Symbol.ofVar xIndividual)
    individual_toHOL_base (holds fun _ ⟨_, hterm, _⟩ => absurd hterm (Finset.notMem_empty _))

/-- The freshness condition of GEN carries weight under the eta policy too. -/
theorem gen_freshness_needed_with_eta :
    KernelProvable etaAxiomPolicy {xEqYTerm} xEqYTerm.term ∧
      FreeInHypotheses xIndividual {xEqYTerm} ∧
      ¬ KernelProvable etaAxiomPolicy {xEqYTerm} forallXEqYDB :=
  gen_freshness_needed etaAxiomPolicy_translatedProvable

end DerivedRulesEtaExamples

end Mettapedia.Languages.OpenTheory
