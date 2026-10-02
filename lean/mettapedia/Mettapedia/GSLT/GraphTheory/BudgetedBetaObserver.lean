import Mettapedia.GSLT.GraphTheory.ParallelReduction
import Mettapedia.GSLT.Logic.ObserverBubble

/-!
# A default observer: budgeted β-normalisation, and its carve-out

The strong judgment is β-conversion on all λ-terms, `BetaConv`, the
equivalence closure of parallel β-reduction.  It is never redefined.

The default observer reduces a term by the leftmost-outermost stepper for a
bounded number of steps and reads the normal form it reaches, if any.  This
module proves:

* **uniqueness of normal forms** (`normalForm_eq_of_betaConv`), from the
  confluence of parallel reduction;
* **exactness where the observer succeeds** (`betaConv_iff_of_normalize`): two
  terms whose normal forms are reached are convertible exactly when the
  normal forms are equal;
* **decidability on a normalising fragment** (`certifiedDecision`,
  `decidableCertified`): on the terms whose normal form is reached within a
  given budget function, β-conversion is decidable, as the restriction of the
  strong judgment to that fragment;
* a **budgeted verdict** (`betaObserver.verdict`) returning `established`,
  `refuted`, `incomplete` or `outsideFragment`, whose outcomes refine as the
  budget grows, packaged as a bubble (`betaBubble`) whose equality means the
  class-observation equivalence.

Controls:

* positive: `(λx.x) y` and `y` are established equal, and the combinators
  `I` and `K` are refuted equal, by evaluation;
* the decision does not extend by running longer: the verdict on the true
  equation `Ω = Ω`, with no fragment restriction, is `incomplete` at every
  budget (`unrestricted_omega_incomplete`);
* a naive decision that compares syntax when no normal form is found is
  unsound: it refutes the true equation `Ω = (λx.x) Ω` at every budget
  (`naive_unsound`).

`BudgetedBetaEtaObserver` adds η.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.GraphTheory.BudgetedBeta

open Mettapedia.GSLT
open Mettapedia.GSLT.GraphTheory
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.ObserverBubble
open Mettapedia.TypeTheory.AuthorityTheory

/-! ## β-conversion -/

/-- **The strong judgment**: β-conversion, the equivalence closure of parallel
β-reduction. -/
def BetaConv (left right : LambdaTerm) : Prop := Relation.EqvGen ParRed left right

theorem betaConv_equivalence : Equivalence BetaConv := Relation.EqvGen.is_equivalence ParRed

theorem betaConv_of_parRedStar {left right : LambdaTerm} (reduces : left ⇛* right) :
    BetaConv left right := by
  induction reduces with
  | refl => exact Relation.EqvGen.refl _
  | tail _ step ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ step)

/-- Convertible terms have a common reduct. -/
theorem join_of_betaConv {left right : LambdaTerm} (convertible : BetaConv left right) :
    Relation.Join ParRedStar left right := by
  induction convertible with
  | rel first second step => exact ⟨second, Relation.ReflTransGen.single step, .refl⟩
  | refl term => exact ⟨term, .refl, .refl⟩
  | symm _ _ _ ih =>
      obtain ⟨meet, firstMeet, secondMeet⟩ := ih
      exact ⟨meet, secondMeet, firstMeet⟩
  | trans _ _ _ _ _ firstIh secondIh =>
      obtain ⟨meet, firstMeet, middleMeet⟩ := firstIh
      obtain ⟨meet', middleMeet', lastMeet⟩ := secondIh
      obtain ⟨common, meetCommon, meetCommon'⟩ := confluence middleMeet middleMeet'
      exact ⟨common, Relation.ReflTransGen.trans firstMeet meetCommon,
        Relation.ReflTransGen.trans lastMeet meetCommon'⟩

/-- β-conversion is a congruence for application on the left. -/
theorem betaConv_app_left {function function' : LambdaTerm} (argument : LambdaTerm)
    (convertible : BetaConv function function') :
    BetaConv (.app function argument) (.app function' argument) := by
  induction convertible with
  | rel first second step => exact Relation.EqvGen.rel _ _ (.app step (ParRed.refl argument))
  | refl term => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ firstIh secondIh => exact Relation.EqvGen.trans _ _ _ firstIh secondIh

/-! ## The leftmost-outermost stepper and normal forms -/

/-- One leftmost-outermost step is a parallel step. -/
theorem parRed_of_step : ∀ {term next : LambdaTerm}, LambdaTerm.step term = some next →
    term ⇛ next
  | .var _, _, stepped => by simp [LambdaTerm.step] at stepped
  | .lam body, next, stepped => by
      cases bodyStep : LambdaTerm.step body with
      | none => simp [LambdaTerm.step, bodyStep] at stepped
      | some body' =>
          simp only [LambdaTerm.step, bodyStep, Option.some.injEq] at stepped
          subst stepped
          exact .lam (parRed_of_step bodyStep)
  | .app (.lam body) argument, next, stepped => by
      simp only [LambdaTerm.step, Option.some.injEq] at stepped
      subst stepped
      exact beta_to_parRed body argument
  | .app (.var index) argument, next, stepped => by
      cases argumentStep : LambdaTerm.step argument with
      | none => simp [LambdaTerm.step, argumentStep] at stepped
      | some argument' =>
          simp only [LambdaTerm.step, argumentStep, Option.some.injEq] at stepped
          subst stepped
          exact .app (ParRed.refl _) (parRed_of_step argumentStep)
  | .app (.app first second) argument, next, stepped => by
      cases functionStep : LambdaTerm.step (.app first second) with
      | some function' =>
          simp only [LambdaTerm.step] at stepped
          rw [functionStep] at stepped
          simp only [Option.some.injEq] at stepped
          subst stepped
          exact .app (parRed_of_step functionStep) (ParRed.refl _)
      | none =>
          cases argumentStep : LambdaTerm.step argument with
          | none =>
              simp only [LambdaTerm.step] at stepped
              rw [functionStep] at stepped
              simp [argumentStep] at stepped
          | some argument' =>
              simp only [LambdaTerm.step] at stepped
              rw [functionStep] at stepped
              simp only [argumentStep, Option.some.injEq] at stepped
              subst stepped
              exact .app (ParRed.refl _) (parRed_of_step argumentStep)

/-- A term on which the stepper stops parallel-reduces only to itself. -/
theorem eq_of_parRed_of_step_none {term result : LambdaTerm}
    (stopped : LambdaTerm.step term = none) (reduces : term ⇛ result) : result = term := by
  induction reduces with
  | var _ => rfl
  | @lam body body' _ ih =>
      have bodyStopped : LambdaTerm.step body = none := by
        cases bodyStep : LambdaTerm.step body with
        | none => rfl
        | some _ => simp [LambdaTerm.step, bodyStep] at stopped
      rw [ih bodyStopped]
  | @app function function' argument argument' _ _ functionIh argumentIh =>
      cases function with
      | lam body => simp [LambdaTerm.step] at stopped
      | var index =>
          have argumentStopped : LambdaTerm.step argument = none := by
            cases argumentStep : LambdaTerm.step argument with
            | none => rfl
            | some _ => simp [LambdaTerm.step, argumentStep] at stopped
          have functionStopped : LambdaTerm.step (.var index) = none := rfl
          rw [functionIh functionStopped, argumentIh argumentStopped]
      | app first second =>
          have functionStopped : LambdaTerm.step (.app first second) = none := by
            cases functionStep : LambdaTerm.step (.app first second) with
            | none => rfl
            | some _ =>
                simp only [LambdaTerm.step] at stopped
                rw [functionStep] at stopped
                simp at stopped
          have argumentStopped : LambdaTerm.step argument = none := by
            cases argumentStep : LambdaTerm.step argument with
            | none => rfl
            | some _ =>
                simp only [LambdaTerm.step] at stopped
                rw [functionStopped] at stopped
                simp [argumentStep] at stopped
          rw [functionIh functionStopped, argumentIh argumentStopped]
  | beta _ _ _ _ => simp [LambdaTerm.step] at stopped

theorem eq_of_parRedStar_of_step_none {term result : LambdaTerm}
    (stopped : LambdaTerm.step term = none) (reduces : term ⇛* result) : result = term := by
  induction reduces with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      exact eq_of_parRed_of_step_none stopped step

/-- **Uniqueness of normal forms.**  Two convertible terms on which the stepper
stops are equal. -/
theorem normalForm_eq_of_betaConv {first second : LambdaTerm}
    (firstStopped : LambdaTerm.step first = none) (secondStopped : LambdaTerm.step second = none)
    (convertible : BetaConv first second) : first = second := by
  obtain ⟨meet, firstMeet, secondMeet⟩ := join_of_betaConv convertible
  rw [← eq_of_parRedStar_of_step_none firstStopped firstMeet,
    eq_of_parRedStar_of_step_none secondStopped secondMeet]

/-! ## The budgeted normaliser -/

/-- Run the stepper for at most `fuel` further steps; return the term it stops
on, if it stops. -/
def normalize : ℕ → LambdaTerm → Option LambdaTerm
  | 0, term =>
      match LambdaTerm.step term with
      | none => some term
      | some _ => none
  | fuel + 1, term =>
      match LambdaTerm.step term with
      | none => some term
      | some next => normalize fuel next

theorem normalize_sound : ∀ {fuel : ℕ} {term result : LambdaTerm},
    normalize fuel term = some result → (term ⇛* result) ∧ LambdaTerm.step result = none
  | 0, term, result, found => by
      cases stepped : LambdaTerm.step term with
      | none =>
          simp only [normalize, stepped, Option.some.injEq] at found
          subst found
          exact ⟨.refl, stepped⟩
      | some _ => simp [normalize, stepped] at found
  | fuel + 1, term, result, found => by
      cases stepped : LambdaTerm.step term with
      | none =>
          simp only [normalize, stepped, Option.some.injEq] at found
          subst found
          exact ⟨.refl, stepped⟩
      | some next =>
          simp only [normalize, stepped] at found
          obtain ⟨reduces, stops⟩ := normalize_sound found
          exact ⟨Relation.ReflTransGen.head (parRed_of_step stepped) reduces, stops⟩

theorem normalize_succ : ∀ {fuel : ℕ} {term result : LambdaTerm},
    normalize fuel term = some result → normalize (fuel + 1) term = some result
  | 0, term, result, found => by
      cases stepped : LambdaTerm.step term with
      | none => simpa [normalize, stepped] using found
      | some _ => simp [normalize, stepped] at found
  | fuel + 1, term, result, found => by
      cases stepped : LambdaTerm.step term with
      | none => simpa [normalize, stepped] using found
      | some next =>
          simp only [normalize, stepped] at found ⊢
          exact normalize_succ found

theorem normalize_mono {fuel fuel' : ℕ} (le : fuel ≤ fuel') {term result : LambdaTerm}
    (found : normalize fuel term = some result) : normalize fuel' term = some result := by
  induction le with
  | refl => exact found
  | step _ ih => exact normalize_succ ih

/-- **Exactness where the observer succeeds.** -/
theorem betaConv_iff_of_normalize {fuel fuel' : ℕ} {left right leftNormal rightNormal : LambdaTerm}
    (leftFound : normalize fuel left = some leftNormal)
    (rightFound : normalize fuel' right = some rightNormal) :
    BetaConv left right ↔ leftNormal = rightNormal := by
  obtain ⟨leftReduces, leftStops⟩ := normalize_sound leftFound
  obtain ⟨rightReduces, rightStops⟩ := normalize_sound rightFound
  have leftConv := betaConv_of_parRedStar leftReduces
  have rightConv := betaConv_of_parRedStar rightReduces
  constructor
  · intro convertible
    exact normalForm_eq_of_betaConv leftStops rightStops
      (betaConv_equivalence.trans (betaConv_equivalence.symm leftConv)
        (betaConv_equivalence.trans convertible rightConv))
  · intro same
    subst same
    exact betaConv_equivalence.trans leftConv (betaConv_equivalence.symm rightConv)

/-! ## Decidability on a normalising fragment -/

/-- The size of a term. -/
def size : LambdaTerm → ℕ
  | .var _ => 1
  | .lam body => size body + 1
  | .app function argument => size function + size argument + 1

/-- **The default β-observer**: leftmost-outermost normalisation within a
budget, read off syntactically. -/
def betaObserver : NormalFormObserver BetaConv where
  normalForm := normalize
  normalForm_mono := fun le found => normalize_mono le found
  normalForm_exact := betaConv_iff_of_normalize

/-- **Carve-out.**  β-conversion restricted to the fragment certified by a
budget function, decided by comparing normal forms. -/
def certifiedDecision (budget : LambdaTerm → ℕ) : FragmentDecision BetaConv :=
  betaObserver.certifiedDecision budget

/-- **β-conversion is decidable on the certified fragment.** -/
@[instance_reducible]
def decidableCertified (budget : LambdaTerm → ℕ) :
    DecidableRel (fun left right : {term // betaObserver.Certified budget term} =>
      BetaConv left.1 right.1) :=
  (certifiedDecision budget).decidableRestriction

/-! ## The default observer as a bubble -/

/-- λ-terms with β-conversion as their equations and no reduction: the
equational theory, observed. -/
abbrev betaGSLT : GSLT where
  Term := LambdaTerm
  equations := ⟨BetaConv, betaConv_equivalence⟩
  rewrites _ _ := False
  rewrites_resp_left := fun _ impossible => impossible.elim
  rewrites_resp_right := fun impossible _ => impossible.elim

/-- Applicative contexts: a term applied to a list of arguments. -/
abbrev applicativeRules : ContextualRules betaGSLT where
  Context := List LambdaTerm
  identity := []
  compose outer inner := inner ++ outer
  plug arguments term := arguments.foldl LambdaTerm.app term
  plug_identity term := betaConv_equivalence.refl term
  plug_compose outer inner term := by
    change BetaConv ((inner ++ outer).foldl LambdaTerm.app term)
      (outer.foldl LambdaTerm.app (inner.foldl LambdaTerm.app term))
    rw [List.foldl_append]
    exact betaConv_equivalence.refl _
  plug_resp arguments := by
    intro left right convertible
    induction arguments generalizing left right with
    | nil => exact convertible
    | cons argument arguments ih => exact ih (betaConv_app_left argument convertible)
  Rule := Empty
  fires _ _ _ := False
  fires_resp_left := fun _ impossible => impossible.elim
  fires_resp_right := fun impossible _ => impossible.elim
  fires_step := fun impossible => impossible.elim

/-- With class observations, every applicative observer class sees exactly
β-conversion. -/
theorem relEquiv_beta_iff (A : AdmissibleClass applicativeRules) (left right : LambdaTerm) :
    A.RelEquiv (classObservations betaGSLT) left right ↔ BetaConv left right :=
  relEquiv_classObservations_iff (S := betaGSLT) (fun _ _ impossible => impossible) A left right

/-- The authority of β-conversion judgments: evidence is a proof, an
obstruction a refutation. -/
def betaAuthority : Authority (LambdaTerm × LambdaTerm) where
  Holds judgment := BetaConv judgment.1 judgment.2
  Evidence judgment := BetaConv judgment.1 judgment.2
  Obstruction judgment := ¬ BetaConv judgment.1 judgment.2
  evidenceSound _ evidence := evidence
  obstructionSound _ obstruction := obstruction

/-- **The default observer as a bubble**: applicative observers reading the
β-class, no commitments from the inventory, and the budgeted verdict on the
fragment certified by term size. -/
def betaBubble : Bubble betaGSLT applicativeRules ℕ where
  observers := ⊤
  observations := classObservations betaGSLT
  commitments := ∅
  Judgment := LambdaTerm × LambdaTerm
  authority := betaAuthority
  Boundary := Unit
  Receipt := Unit
  verdict judgment fuel :=
    betaObserver.verdict (betaObserver.Certified size) judgment.1 judgment.2 fuel
  verdict_budget_mono judgment _ _ le :=
    betaObserver.verdict_budget_mono (betaObserver.Certified size) judgment.1 judgment.2 le
  equality left right := (left, right)
  equality_holds left right := (relEquiv_beta_iff ⊤ left right).symm

/-! ## Controls -/

/-- `(λx.x) y` and `y`: established equal. -/
theorem identity_application_established :
    (betaObserver.verdict (betaObserver.Certified size) (.app LambdaTerm.I (.var 0)) (.var 0)
      1).asBool = some true := by
  decide

/-- The combinators `I` and `K`: refuted equal. -/
theorem identity_ne_constant_refuted :
    (betaObserver.verdict (betaObserver.Certified size) LambdaTerm.I LambdaTerm.K 0).asBool =
      some false := by
  decide

/-- The stepper maps `Ω` to itself. -/
theorem step_Omega : LambdaTerm.step LambdaTerm.Omega = some LambdaTerm.Omega := by decide

theorem normalize_Omega : ∀ fuel, normalize fuel LambdaTerm.Omega = none
  | 0 => by simp [normalize, step_Omega]
  | fuel + 1 => by simp only [normalize, step_Omega]; exact normalize_Omega fuel

/-- `Ω` lies outside the certified fragment. -/
theorem Omega_not_certified (budget : LambdaTerm → ℕ) :
    ¬ betaObserver.Certified budget LambdaTerm.Omega := by
  simp [NormalFormObserver.Certified, betaObserver, normalize_Omega]

/-- **The decision does not extend by running longer.**  With no fragment
restriction, the verdict on the true equation `Ω = Ω` is incomplete at every
budget. -/
theorem unrestricted_omega_incomplete (fuel : ℕ) :
    betaObserver.verdict (fun _ => True) LambdaTerm.Omega LambdaTerm.Omega fuel =
      .incomplete () := by
  have noPair : betaObserver.pair fuel LambdaTerm.Omega LambdaTerm.Omega = none := by
    simp [NormalFormObserver.pair, betaObserver, normalize_Omega]
  have notFound : ¬ (betaObserver.pair fuel LambdaTerm.Omega LambdaTerm.Omega).isSome = true := by
    rw [noPair]
    decide
  unfold NormalFormObserver.verdict
  rw [if_pos ⟨trivial, trivial⟩, dif_neg notFound]

theorem Omega_betaConv_self : BetaConv LambdaTerm.Omega LambdaTerm.Omega :=
  betaConv_equivalence.refl _

/-- A naive decision: compare normal forms when both are reached, and compare
syntax otherwise. -/
def naiveDecide (fuel : ℕ) (left right : LambdaTerm) : Bool :=
  match betaObserver.pair fuel left right with
  | some (leftNormal, rightNormal) => decide (leftNormal = rightNormal)
  | none => decide (left = right)

theorem step_identity_Omega :
    LambdaTerm.step (.app LambdaTerm.I LambdaTerm.Omega) = some LambdaTerm.Omega := by decide

theorem normalize_identity_Omega (fuel : ℕ) :
    normalize fuel (.app LambdaTerm.I LambdaTerm.Omega) = none := by
  cases fuel with
  | zero => simp [normalize, step_identity_Omega]
  | succ fuel =>
      simp only [normalize, step_identity_Omega]
      exact normalize_Omega fuel

/-- **The naive decision is unsound**: it refutes the true equation
`Ω = (λx.x) Ω` at every budget. -/
theorem naive_unsound :
    BetaConv LambdaTerm.Omega (.app LambdaTerm.I LambdaTerm.Omega) ∧
      ∀ fuel, naiveDecide fuel LambdaTerm.Omega (.app LambdaTerm.I LambdaTerm.Omega) = false := by
  refine ⟨Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ?_), fun fuel => ?_⟩
  · exact beta_to_parRed (.var 0) LambdaTerm.Omega
  · have noPair :
        betaObserver.pair fuel LambdaTerm.Omega (.app LambdaTerm.I LambdaTerm.Omega) = none := by
      simp [NormalFormObserver.pair, betaObserver, normalize_Omega]
    unfold naiveDecide
    rw [noPair]
    decide

end Mettapedia.GSLT.GraphTheory.BudgetedBeta
