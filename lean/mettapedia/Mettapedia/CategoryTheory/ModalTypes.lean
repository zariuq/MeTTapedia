import Mettapedia.CategoryTheory.LambdaTheory
import Mettapedia.CategoryTheory.PLNInstance
import Mettapedia.CategoryTheory.PLNTerms
import Mettapedia.Logic.EvidenceQuantale

/-!
# Modal Types: Predicate-First Semantics

Canonical modal semantics are defined here as explicit predicates/comprehensions
on hole fillers (`PLNTerm → Prop`), with context instantiation and one-step
reduction witnesses.

No meet-fold/scalar modal summary is used as a semantic source of truth in this
module.
-/

namespace Mettapedia.CategoryTheory.ModalTypes

open Mettapedia.CategoryTheory.LambdaTheories
open Mettapedia.CategoryTheory.PLNInstance
open Mettapedia.CategoryTheory.PLNTerms
open Mettapedia.Logic.EvidenceQuantale

/-! ## Predicate-First Modal Semantics -/

/-- Environments assign concrete terms to parameter names. -/
abbrev Env := String → PLNTerm

/-- Rely conditions in the predicate layer. -/
abbrev RelyCondition := String × (PLNTerm → Prop)

/-- Identity-like environment used in concrete fixtures. -/
def idEnv : Env := fun x => PLNTerm.atom x

/-- Instantiate a term under an environment (variable replacement on atoms). -/
def instantiateTerm (ρ : Env) : PLNTerm → PLNTerm
  | PLNTerm.atom x => ρ x
  | PLNTerm.impl A B => PLNTerm.impl (instantiateTerm ρ A) (instantiateTerm ρ B)
  | PLNTerm.conj A B => PLNTerm.conj (instantiateTerm ρ A) (instantiateTerm ρ B)
  | PLNTerm.disj A B => PLNTerm.disj (instantiateTerm ρ A) (instantiateTerm ρ B)
  | PLNTerm.neg A => PLNTerm.neg (instantiateTerm ρ A)
  | PLNTerm.truth e => PLNTerm.truth e

/-- Instantiate all embedded terms in a one-hole context. -/
def instantiateContext (ρ : Env) : Context → Context
  | Context.hole => Context.hole
  | Context.implLeft C B => Context.implLeft (instantiateContext ρ C) (instantiateTerm ρ B)
  | Context.implRight A C => Context.implRight (instantiateTerm ρ A) (instantiateContext ρ C)
  | Context.conjLeft C B => Context.conjLeft (instantiateContext ρ C) (instantiateTerm ρ B)
  | Context.conjRight A C => Context.conjRight (instantiateTerm ρ A) (instantiateContext ρ C)
  | Context.disjLeft C B => Context.disjLeft (instantiateContext ρ C) (instantiateTerm ρ B)
  | Context.disjRight A C => Context.disjRight (instantiateTerm ρ A) (instantiateContext ρ C)
  | Context.negCtx C => Context.negCtx (instantiateContext ρ C)

/-- Instantiating then filling equals filling in the instantiated context. -/
theorem instantiateContext_fill (ρ : Env) (C : Context) (t : PLNTerm) :
    instantiateTerm ρ (C.fill t) =
      (instantiateContext ρ C).fill (instantiateTerm ρ t) := by
  induction C with
  | hole =>
      simp [Context.fill, instantiateContext]
  | implLeft C B ih =>
      simp [Context.fill, instantiateContext, instantiateTerm, ih]
  | implRight A C ih =>
      simp [Context.fill, instantiateContext, instantiateTerm, ih]
  | conjLeft C B ih =>
      simp [Context.fill, instantiateContext, instantiateTerm, ih]
  | conjRight A C ih =>
      simp [Context.fill, instantiateContext, instantiateTerm, ih]
  | disjLeft C B ih =>
      simp [Context.fill, instantiateContext, instantiateTerm, ih]
  | disjRight A C ih =>
      simp [Context.fill, instantiateContext, instantiateTerm, ih]
  | negCtx C ih =>
      simp [Context.fill, instantiateContext, instantiateTerm, ih]

/-- Environment `ρ` satisfies all listed rely predicates. -/
def satisfiesRelies (ρ : Env) (relies : List RelyCondition) : Prop :=
  ∀ x A, (x, A) ∈ relies → A (ρ x)

/-- One-step reachability obligation for a fixed environment and filler term. -/
def reachesResultInOneStep {rule : RewriteRule}
    (rwCtx : RewriteContext rule)
    (B : PLNTerm → Prop)
    (ρ : Env)
    (t : PLNTerm) : Prop :=
  ∃ p,
    Reduces ((instantiateContext ρ rwCtx.ctx).fill (instantiateTerm ρ t)) p ∧
      B p

/-- Canonical rely-possibly predicate:
`t` is admissible when every rely-satisfying environment admits a one-step reduct
in the result predicate `B`. -/
def relyPossiblyPred {rule : RewriteRule}
    (rwCtx : RewriteContext rule)
    (relies : List RelyCondition)
    (B : PLNTerm → Prop) : PLNTerm → Prop :=
  fun t => ∀ ρ, satisfiesRelies ρ relies → reachesResultInOneStep rwCtx B ρ t

/-- Predicate monotonicity in the result postcondition. -/
theorem relyPossiblyPred_mono_result {rule : RewriteRule}
    (rwCtx : RewriteContext rule)
    (relies : List RelyCondition)
    {B₁ B₂ : PLNTerm → Prop}
    (hMono : ∀ p, B₁ p → B₂ p)
    {t : PLNTerm} :
    relyPossiblyPred rwCtx relies B₁ t →
      relyPossiblyPred rwCtx relies B₂ t := by
  intro h ρ hRel
  rcases h ρ hRel with ⟨p, hRed, hB⟩
  exact ⟨p, hRed, hMono p hB⟩

/-- The modal type as an explicit comprehension (set of fillers). -/
def modalComprehension {rule : RewriteRule}
    (rwCtx : RewriteContext rule)
    (relies : List RelyCondition)
    (B : PLNTerm → Prop) : Set PLNTerm :=
  { t | relyPossiblyPred rwCtx relies B t }

theorem modalComprehension_mem_iff {rule : RewriteRule}
    (rwCtx : RewriteContext rule)
    (relies : List RelyCondition)
    (B : PLNTerm → Prop)
    (t : PLNTerm) :
    t ∈ modalComprehension rwCtx relies B ↔ relyPossiblyPred rwCtx relies B t := by
  rfl

/-- Subtype form of modal comprehension (set-theoretic subobject at term level). -/
def modalSubtype {rule : RewriteRule}
    (rwCtx : RewriteContext rule)
    (relies : List RelyCondition)
    (B : PLNTerm → Prop) : Type :=
  { t : PLNTerm // t ∈ modalComprehension rwCtx relies B }

theorem reachesResultInOneStep_false_result_not {rule : RewriteRule}
    (rwCtx : RewriteContext rule)
    (ρ : Env)
    (t : PLNTerm) :
    ¬ reachesResultInOneStep rwCtx (fun _ => False) ρ t := by
  intro h
  rcases h with ⟨p, _hRed, hFalse⟩
  exact hFalse

/-! ### Concrete Positive/Negative Fixtures -/

/-- Concrete positive fixture: deduction context reaches its canonical RHS under
the identity-like environment. -/
theorem deduction_reaches_rhs_identity :
    reachesResultInOneStep deductionRewriteContext
      (fun p => p = deductionRule.rhs) idEnv (PLNTerm.atom "A") := by
  refine ⟨deductionRule.rhs, ?_, rfl⟩
  simpa [reachesResultInOneStep, idEnv, deductionRewriteContext, deductionRule,
    deductionContext, instantiateContext, instantiateTerm, Context.fill]
    using (Reduces.deduction
      (A := PLNTerm.atom "A")
      (B := PLNTerm.atom "B")
      (C := PLNTerm.atom "C"))

/-- Concrete negative fixture: with the false result predicate, no one-step
modal witness exists. -/
theorem deduction_not_reach_false_identity :
    ¬ reachesResultInOneStep deductionRewriteContext
        (fun _ => False) idEnv (PLNTerm.atom "A") := by
  exact reachesResultInOneStep_false_result_not deductionRewriteContext idEnv (PLNTerm.atom "A")

/-! ## Existing Quantale-Modal Bridge Endpoints -/

/-- Modal composition is meet in the frame fibers. -/
theorem modalCompose_is_meet
    (m1 m2 : PLNFiber PLNLambdaTheory.Pr) :
    modalCompose PLNLambdaTheory m1 m2 = m1 ⊓ m2 := by
  unfold modalCompose
  rfl

/-- Structural decomposition of PLN deduction strength into direct+indirect paths. -/
theorem pln_deduction_structural_decomposition
    (sAB sBC pB pC : ENNReal) :
    BinaryEvidence.deductionStrength sAB sBC pB pC =
      BinaryEvidence.directPathStrength sAB sBC +
      BinaryEvidence.indirectPathStrength sAB pB pC sBC := by
  unfold BinaryEvidence.deductionStrength
  rfl

end Mettapedia.CategoryTheory.ModalTypes
