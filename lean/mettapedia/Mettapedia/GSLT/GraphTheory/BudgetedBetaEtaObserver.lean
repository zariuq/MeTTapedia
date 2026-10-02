import Mettapedia.GSLT.GraphTheory.BetaEtaConfluence
import Mettapedia.GSLT.GraphTheory.BudgetedBetaObserver

/-!
# The default observer with η: budgeted βη-normalisation

The strong judgment is βη-conversion on all λ-terms, `BetaEtaConv`.  The
default observer reaches a β-normal form by budgeted leftmost-outermost
reduction and then contracts every η-redex, innermost first
(`etaNormalize`).  This module proves:

* `etaNormalize` reaches an η-normal form by η-steps and preserves β-normal
  forms, so the observer returns βη-normal forms (`betaEtaNormalize_sound`);
* **exactness** (`betaEtaConv_iff_of_normalize`): two terms whose normal forms
  are reached are βη-convertible exactly when the normal forms are equal, by
  the confluence of βη-reduction;
* **decidability on a normalising fragment** (`certifiedDecision`,
  `decidableCertified`), and a budgeted verdict packaged as a bubble
  (`betaEtaBubble`).

η is the extensionality rule of the λ-calculus, and the βη-bubble records the
commitment `functionExtensionality`.  The control `extensionality_is_observed`
shows the observer choice at work: on `λx. y x` against `y`, the β-observer
refutes and the βη-observer establishes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.GraphTheory.BetaEta

open Mettapedia.GSLT
open Mettapedia.GSLT.GraphTheory
open Mettapedia.GSLT.GraphTheory.BudgetedBeta
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.ObserverBubble
open Mettapedia.TypeTheory.AuthorityTheory
open LambdaTerm

/-! ## Normal forms -/

/-- No β-step leaves the term. -/
def BetaNormal (term : LambdaTerm) : Prop := ∀ next, ¬ BetaStep term next

/-- No η-step leaves the term. -/
def EtaNormal (term : LambdaTerm) : Prop := ∀ next, ¬ EtaStep term next

theorem betaNormal_of_step_none {term : LambdaTerm} (stopped : LambdaTerm.step term = none) :
    BetaNormal term := by
  intro next step
  induction step with
  | beta body argument => simp [LambdaTerm.step] at stopped
  | @lam body body' _ ih =>
      apply ih
      cases bodyStep : LambdaTerm.step body with
      | none => rfl
      | some _ => simp [LambdaTerm.step, bodyStep] at stopped
  | @appL function function' argument _ ih =>
      apply ih
      cases function with
      | var index => rfl
      | lam body => simp [LambdaTerm.step] at stopped
      | app first second =>
          cases functionStep : LambdaTerm.step (.app first second) with
          | none => rfl
          | some _ =>
              simp only [LambdaTerm.step] at stopped
              rw [functionStep] at stopped
              simp at stopped
  | @appR function argument argument' _ ih =>
      apply ih
      cases function with
      | var index =>
          cases argumentStep : LambdaTerm.step argument with
          | none => rfl
          | some _ => simp [LambdaTerm.step, argumentStep] at stopped
      | lam body => simp [LambdaTerm.step] at stopped
      | app first second =>
          have functionStopped : LambdaTerm.step (.app first second) = none := by
            cases functionStep : LambdaTerm.step (.app first second) with
            | none => rfl
            | some _ =>
                simp only [LambdaTerm.step] at stopped
                rw [functionStep] at stopped
                simp at stopped
          cases argumentStep : LambdaTerm.step argument with
          | none => rfl
          | some _ =>
              simp only [LambdaTerm.step] at stopped
              rw [functionStopped] at stopped
              simp [argumentStep] at stopped

/-! ## Removing a variable -/

/-- Remove the variable `cutoff`, lowering those above it; `none` if it occurs. -/
def unshift (cutoff : ℕ) : LambdaTerm → Option LambdaTerm
  | .var n => if n < cutoff then some (.var n) else if n = cutoff then none else some (.var (n - 1))
  | .lam body => (unshift (cutoff + 1) body).map LambdaTerm.lam
  | .app function argument =>
      match unshift cutoff function, unshift cutoff argument with
      | some function', some argument' => some (.app function' argument')
      | _, _ => none

theorem eq_shift_of_unshift : ∀ {term result : LambdaTerm} {cutoff : ℕ},
    unshift cutoff term = some result → term = shift 1 cutoff result
  | .var n, result, cutoff, found => by
      simp only [unshift] at found
      by_cases below : n < cutoff
      · rw [if_pos below] at found
        injection found with found
        subst found
        exact (shift_var_lt n 1 cutoff below).symm
      · rw [if_neg below] at found
        by_cases same : n = cutoff
        · rw [if_pos same] at found
          cases found
        · rw [if_neg same] at found
          injection found with found
          subst found
          rw [shift_var_ge (n - 1) 1 cutoff (by omega)]
          congr 1
          omega
  | .lam body, result, cutoff, found => by
      simp only [unshift] at found
      cases bodyFound : unshift (cutoff + 1) body with
      | none => simp [bodyFound] at found
      | some body' =>
          simp only [bodyFound, Option.map_some, Option.some.injEq] at found
          subst found
          rw [eq_shift_of_unshift bodyFound]
          rfl
  | .app function argument, result, cutoff, found => by
      simp only [unshift] at found
      cases functionFound : unshift cutoff function with
      | none => simp [functionFound] at found
      | some function' =>
          cases argumentFound : unshift cutoff argument with
          | none => simp [functionFound, argumentFound] at found
          | some argument' =>
              simp only [functionFound, argumentFound, Option.some.injEq] at found
              subst found
              rw [eq_shift_of_unshift functionFound, eq_shift_of_unshift argumentFound]
              rfl

theorem unshift_shift : ∀ (term : LambdaTerm) (cutoff : ℕ),
    unshift cutoff (shift 1 cutoff term) = some term
  | .var n, cutoff => by
      by_cases below : n < cutoff
      · rw [shift_var_lt n 1 cutoff below]
        simp only [unshift, if_pos below]
      · rw [shift_var_ge n 1 cutoff (by omega)]
        simp only [unshift]
        rw [if_neg (by omega), if_neg (by omega)]
        rfl
  | .lam body, cutoff => by
      rw [shift_lam]
      simp only [unshift, unshift_shift body (cutoff + 1), Option.map_some]
  | .app function argument, cutoff => by
      rw [shift_app]
      simp only [unshift, unshift_shift function cutoff, unshift_shift argument cutoff]

/-! ## The η-normaliser -/

/-- Contract `λ. body` at the root if it is an η-redex. -/
def etaRoot (body : LambdaTerm) : LambdaTerm :=
  match body with
  | .app function (.var 0) =>
      match unshift 0 function with
      | some function' => function'
      | none => .lam body
  | _ => .lam body

/-- Contract every η-redex, innermost first. -/
def etaNormalize : LambdaTerm → LambdaTerm
  | .var n => .var n
  | .lam body => etaRoot (etaNormalize body)
  | .app function argument => .app (etaNormalize function) (etaNormalize argument)

/-- What `etaRoot` does: contract an η-redex, or leave a non-redex under a
binder. -/
theorem etaRoot_cases (body : LambdaTerm) :
    (∃ function', body = .app (shift 1 0 function') (.var 0) ∧ etaRoot body = function') ∨
      (etaRoot body = .lam body ∧ ∀ function', body ≠ .app (shift 1 0 function') (.var 0)) := by
  cases body with
  | var n => exact Or.inr ⟨rfl, fun _ => nofun⟩
  | lam inner => exact Or.inr ⟨rfl, fun _ => nofun⟩
  | app function argument =>
      cases argument with
      | var index =>
          cases index with
          | zero =>
              cases found : unshift 0 function with
              | some function' =>
                  refine Or.inl ⟨function', ?_, ?_⟩
                  · rw [eq_shift_of_unshift found]
                  · simp only [etaRoot, found]
              | none =>
                  refine Or.inr ⟨by simp only [etaRoot, found], ?_⟩
                  intro function' equal
                  injection equal with functionEq _
                  rw [functionEq, unshift_shift] at found
                  cases found
          | succ index => exact Or.inr ⟨rfl, fun _ equal => by injection equal with _ zeroEq; cases zeroEq⟩
      | lam _ => exact Or.inr ⟨rfl, fun _ equal => by injection equal with _ zeroEq; cases zeroEq⟩
      | app _ _ => exact Or.inr ⟨rfl, fun _ equal => by injection equal with _ zeroEq; cases zeroEq⟩

theorem etaStar_etaNormalize : ∀ term : LambdaTerm, EtaStar term (etaNormalize term)
  | .var _ => .refl
  | .lam body => by
      have inner := etaStar_lam (etaStar_etaNormalize body)
      change EtaStar (.lam body) (etaRoot (etaNormalize body))
      rcases etaRoot_cases (etaNormalize body) with ⟨function', bodyEq, rootEq⟩ | ⟨rootEq, _⟩
      · rw [rootEq]
        rw [bodyEq] at inner
        exact inner.tail (.eta function')
      · rw [rootEq]
        exact inner
  | .app function argument =>
      (etaStar_appL _ (etaStar_etaNormalize function)).trans
        (etaStar_appR _ (etaStar_etaNormalize argument))

theorem etaNormal_etaNormalize : ∀ term : LambdaTerm, EtaNormal (etaNormalize term)
  | .var _ => fun _ step => nomatch step
  | .lam body => by
      have inner := etaNormal_etaNormalize body
      change EtaNormal (etaRoot (etaNormalize body))
      generalize etaNormalize body = body' at inner ⊢
      rcases etaRoot_cases body' with ⟨function', bodyEq, rootEq⟩ | ⟨rootEq, notRedex⟩
      · rw [rootEq]
        intro next step
        subst bodyEq
        exact inner _ (.appL _ (etaStep_shift step 1 0))
      · rw [rootEq]
        intro next step
        cases step with
        | eta _ => exact notRedex next rfl
        | lam bodyStep => exact inner _ bodyStep
  | .app function argument => by
      have functionNormal := etaNormal_etaNormalize function
      have argumentNormal := etaNormal_etaNormalize argument
      change EtaNormal (.app (etaNormalize function) (etaNormalize argument))
      generalize etaNormalize function = function' at functionNormal ⊢
      generalize etaNormalize argument = argument' at argumentNormal ⊢
      intro next step
      cases step with
      | appL _ functionStep => exact functionNormal _ functionStep
      | appR _ argumentStep => exact argumentNormal _ argumentStep

theorem etaNormalize_not_lam : ∀ {term : LambdaTerm}, (∀ body, term ≠ .lam body) →
    ∀ body, etaNormalize term ≠ .lam body
  | .var _, _ => fun _ => nofun
  | .lam body, notLam => absurd rfl (notLam body)
  | .app _ _, _ => fun _ => nofun

theorem betaNormal_etaNormalize : ∀ {term : LambdaTerm}, BetaNormal term →
    BetaNormal (etaNormalize term)
  | .var _, _ => fun _ step => nomatch step
  | .lam body, normal => by
      have bodyNormal : BetaNormal body := fun next step => normal _ (.lam step)
      have inner := betaNormal_etaNormalize bodyNormal
      change BetaNormal (etaRoot (etaNormalize body))
      generalize etaNormalize body = body' at inner ⊢
      rcases etaRoot_cases body' with ⟨function', bodyEq, rootEq⟩ | ⟨rootEq, _⟩
      · rw [rootEq]
        intro next step
        subst bodyEq
        exact inner _ (.appL _ (betaStep_shift step 1 0))
      · rw [rootEq]
        intro next step
        cases step with
        | lam bodyStep => exact inner _ bodyStep
  | .app function argument, normal => by
      have functionNormal : BetaNormal function := fun next step => normal _ (.appL _ step)
      have argumentNormal : BetaNormal argument := fun next step => normal _ (.appR _ step)
      have notLam : ∀ body, function ≠ .lam body := by
        rintro body rfl
        exact normal _ (.beta body argument)
      have functionInner := betaNormal_etaNormalize functionNormal
      have argumentInner := betaNormal_etaNormalize argumentNormal
      have innerNotLam := etaNormalize_not_lam notLam
      change BetaNormal (.app (etaNormalize function) (etaNormalize argument))
      generalize etaNormalize function = function' at functionInner innerNotLam ⊢
      generalize etaNormalize argument = argument' at argumentInner ⊢
      intro next step
      cases step with
      | beta body _ => exact innerNotLam body rfl
      | appL _ functionStep => exact functionInner _ functionStep
      | appR _ argumentStep => exact argumentInner _ argumentStep

/-! ## Exactness -/

theorem betaEtaConv_of_betaEtaStar {source target : LambdaTerm}
    (reduces : BetaEtaStar source target) : BetaEtaConv source target := by
  induction reduces with
  | refl => exact Relation.EqvGen.refl _
  | tail _ step ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ step)

theorem betaEtaConv_equivalence : Equivalence BetaEtaConv :=
  Relation.EqvGen.is_equivalence BetaEtaStep

/-- A βη-normal term reduces only to itself. -/
theorem eq_of_betaEtaStar_of_normal {term result : LambdaTerm} (betaNormal : BetaNormal term)
    (etaNormal : EtaNormal term) (reduces : BetaEtaStar term result) : result = term := by
  induction reduces using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ _ =>
      rcases step with beta | eta
      · exact absurd beta (betaNormal _)
      · exact absurd eta (etaNormal _)

/-- The βη-observer: β-normalise within the budget, then η-normalise. -/
def betaEtaNormalize (fuel : ℕ) (term : LambdaTerm) : Option LambdaTerm :=
  (normalize fuel term).map etaNormalize

theorem betaEtaNormalize_sound {fuel : ℕ} {term result : LambdaTerm}
    (found : betaEtaNormalize fuel term = some result) :
    BetaEtaStar term result ∧ BetaNormal result ∧ EtaNormal result := by
  unfold betaEtaNormalize at found
  cases betaFound : normalize fuel term with
  | none => simp [betaFound] at found
  | some betaNormalForm =>
      simp only [betaFound, Option.map_some, Option.some.injEq] at found
      subst found
      obtain ⟨parallel, stopped⟩ := normalize_sound betaFound
      refine ⟨(betaEtaStar_of_betaStar (betaStar_iff_parRedStar.mpr parallel)).trans
        (betaEtaStar_of_etaStar (etaStar_etaNormalize betaNormalForm)),
        betaNormal_etaNormalize (betaNormal_of_step_none stopped),
        etaNormal_etaNormalize betaNormalForm⟩

theorem betaEtaNormalize_mono {fuel fuel' : ℕ} (le : fuel ≤ fuel') {term result : LambdaTerm}
    (found : betaEtaNormalize fuel term = some result) :
    betaEtaNormalize fuel' term = some result := by
  unfold betaEtaNormalize at found ⊢
  cases betaFound : normalize fuel term with
  | none => simp [betaFound] at found
  | some betaNormalForm =>
      rw [normalize_mono le betaFound]
      simpa [betaFound] using found

/-- **Exactness.**  Where both normal forms are reached, βη-convertibility is
their equality. -/
theorem betaEtaConv_iff_of_normalize {fuel fuel' : ℕ}
    {left right leftNormal rightNormal : LambdaTerm}
    (leftFound : betaEtaNormalize fuel left = some leftNormal)
    (rightFound : betaEtaNormalize fuel' right = some rightNormal) :
    BetaEtaConv left right ↔ leftNormal = rightNormal := by
  obtain ⟨leftReduces, leftBeta, leftEta⟩ := betaEtaNormalize_sound leftFound
  obtain ⟨rightReduces, rightBeta, rightEta⟩ := betaEtaNormalize_sound rightFound
  constructor
  · intro convertible
    obtain ⟨meet, leftMeet, rightMeet⟩ := join_of_betaEtaConv convertible
    obtain ⟨leftCommon, leftNormalCommon, meetLeftCommon⟩ :=
      betaEtaStar_confluent leftReduces leftMeet
    obtain ⟨rightCommon, rightNormalCommon, meetRightCommon⟩ :=
      betaEtaStar_confluent rightReduces rightMeet
    have leftEq := eq_of_betaEtaStar_of_normal leftBeta leftEta leftNormalCommon
    have rightEq := eq_of_betaEtaStar_of_normal rightBeta rightEta rightNormalCommon
    subst leftEq
    subst rightEq
    obtain ⟨last, leftLast, rightLast⟩ := betaEtaStar_confluent meetLeftCommon meetRightCommon
    rw [← eq_of_betaEtaStar_of_normal leftBeta leftEta leftLast,
      eq_of_betaEtaStar_of_normal rightBeta rightEta rightLast]
  · intro same
    subst same
    exact betaEtaConv_equivalence.trans (betaEtaConv_of_betaEtaStar leftReduces)
      (betaEtaConv_equivalence.symm (betaEtaConv_of_betaEtaStar rightReduces))

/-- **The default βη-observer.** -/
def betaEtaObserver : NormalFormObserver BetaEtaConv where
  normalForm := betaEtaNormalize
  normalForm_mono := fun le found => betaEtaNormalize_mono le found
  normalForm_exact := betaEtaConv_iff_of_normalize

/-- **Carve-out.**  βη-conversion restricted to the fragment certified by a
budget function. -/
def certifiedDecision (budget : LambdaTerm → ℕ) : FragmentDecision BetaEtaConv :=
  betaEtaObserver.certifiedDecision budget

/-- **βη-conversion is decidable on the certified fragment.** -/
@[instance_reducible]
def decidableCertified (budget : LambdaTerm → ℕ) :
    DecidableRel (fun left right : {term // betaEtaObserver.Certified budget term} =>
      BetaEtaConv left.1 right.1) :=
  (certifiedDecision budget).decidableRestriction

/-! ## The βη-observer as a bubble -/

theorem betaEtaConv_app_left {function function' : LambdaTerm} (argument : LambdaTerm)
    (convertible : BetaEtaConv function function') :
    BetaEtaConv (.app function argument) (.app function' argument) := by
  induction convertible with
  | rel first second step =>
      refine Relation.EqvGen.rel _ _ ?_
      rcases step with beta | eta
      · exact Or.inl (.appL argument beta)
      · exact Or.inr (.appL argument eta)
  | refl term => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ firstIh secondIh => exact Relation.EqvGen.trans _ _ _ firstIh secondIh

/-- λ-terms with βη-conversion as their equations and no reduction. -/
abbrev betaEtaGSLT : GSLT where
  Term := LambdaTerm
  equations := ⟨BetaEtaConv, betaEtaConv_equivalence⟩
  rewrites _ _ := False
  rewrites_resp_left := fun _ impossible => impossible.elim
  rewrites_resp_right := fun impossible _ => impossible.elim

/-- Applicative contexts over βη-conversion. -/
abbrev betaEtaApplicativeRules : ContextualRules betaEtaGSLT where
  Context := List LambdaTerm
  identity := []
  compose outer inner := inner ++ outer
  plug arguments term := arguments.foldl LambdaTerm.app term
  plug_identity term := betaEtaConv_equivalence.refl term
  plug_compose outer inner term := by
    change BetaEtaConv ((inner ++ outer).foldl LambdaTerm.app term)
      (outer.foldl LambdaTerm.app (inner.foldl LambdaTerm.app term))
    rw [List.foldl_append]
    exact betaEtaConv_equivalence.refl _
  plug_resp arguments := by
    intro left right convertible
    induction arguments generalizing left right with
    | nil => exact convertible
    | cons argument arguments ih => exact ih (betaEtaConv_app_left argument convertible)
  Rule := Empty
  fires _ _ _ := False
  fires_resp_left := fun _ impossible => impossible.elim
  fires_resp_right := fun impossible _ => impossible.elim
  fires_step := fun impossible => impossible.elim

theorem relEquiv_betaEta_iff (A : AdmissibleClass betaEtaApplicativeRules)
    (left right : LambdaTerm) :
    A.RelEquiv (classObservations betaEtaGSLT) left right ↔ BetaEtaConv left right :=
  relEquiv_classObservations_iff (S := betaEtaGSLT) (fun _ _ impossible => impossible) A left right

/-- The authority of βη-conversion judgments. -/
def betaEtaAuthority : Authority (LambdaTerm × LambdaTerm) where
  Holds judgment := BetaEtaConv judgment.1 judgment.2
  Evidence judgment := BetaEtaConv judgment.1 judgment.2
  Obstruction judgment := ¬ BetaEtaConv judgment.1 judgment.2
  evidenceSound _ evidence := evidence
  obstructionSound _ obstruction := obstruction

/-- **The default βη-observer as a bubble**: applicative observers reading the
βη-class, the extensionality commitment, and the budgeted verdict on the
fragment certified by term size. -/
def betaEtaBubble : Bubble betaEtaGSLT betaEtaApplicativeRules ℕ where
  observers := ⊤
  observations := classObservations betaEtaGSLT
  commitments := {Principle.functionExtensionality}
  Judgment := LambdaTerm × LambdaTerm
  authority := betaEtaAuthority
  Boundary := Unit
  Receipt := Unit
  verdict judgment fuel :=
    betaEtaObserver.verdict (betaEtaObserver.Certified size) judgment.1 judgment.2 fuel
  verdict_budget_mono judgment _ _ le :=
    betaEtaObserver.verdict_budget_mono (betaEtaObserver.Certified size) judgment.1 judgment.2 le
  equality left right := (left, right)
  equality_holds left right := (relEquiv_betaEta_iff ⊤ left right).symm

/-! ## Controls -/

/-- `λx. y x`, with `y` the free variable `0`. -/
def etaExpandedVar : LambdaTerm := .lam (.app (.var 1) (.var 0))

/-- **Extensionality is observed.**  The β-observer refutes `λx. y x = y`; the
βη-observer establishes it. -/
theorem extensionality_is_observed :
    (betaObserver.verdict (betaObserver.Certified size) etaExpandedVar (.var 0) 0).asBool =
        some false ∧
      (betaEtaObserver.verdict (betaEtaObserver.Certified size) etaExpandedVar (.var 0) 0).asBool =
        some true := by
  constructor <;> decide

/-- The η-redex and its contractum are βη-convertible but not β-convertible. -/
theorem etaExpandedVar_conversions :
    BetaEtaConv etaExpandedVar (.var 0) ∧ ¬ BetaConv etaExpandedVar (.var 0) := by
  refine ⟨Relation.EqvGen.rel _ _ (Or.inr (EtaStep.eta (.var 0))), fun convertible => ?_⟩
  have normalLeft : normalize 0 etaExpandedVar = some etaExpandedVar := by decide
  have normalRight : normalize 0 (.var 0) = some (.var 0) := by decide
  exact absurd ((betaConv_iff_of_normalize normalLeft normalRight).mp convertible) (by decide)

/-- `Ω` stays incomplete for the βη-observer at every budget. -/
theorem unrestricted_omega_incomplete (fuel : ℕ) :
    betaEtaObserver.verdict (fun _ => True) LambdaTerm.Omega LambdaTerm.Omega fuel =
      .incomplete () := by
  have noPair : betaEtaObserver.pair fuel LambdaTerm.Omega LambdaTerm.Omega = none := by
    simp [NormalFormObserver.pair, betaEtaObserver, betaEtaNormalize, normalize_Omega]
  have notFound : ¬ (betaEtaObserver.pair fuel LambdaTerm.Omega LambdaTerm.Omega).isSome = true := by
    rw [noPair]
    decide
  unfold NormalFormObserver.verdict
  rw [if_pos ⟨trivial, trivial⟩, dif_neg notFound]

end Mettapedia.GSLT.GraphTheory.BetaEta
