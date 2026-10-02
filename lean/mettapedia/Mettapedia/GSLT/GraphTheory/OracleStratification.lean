import Mettapedia.GSLT.GraphTheory.ReflectiveBetaBubble
import Mettapedia.GSLT.Logic.ObserverDetermination

/-!
# The stratified escape: the next stage decides, and changes nothing it decides

No λ-term decides β-conversion (`no_lambda_decides_betaConv`, the diagonal).
The escape by stratification adds an *oracle observer* one stage up and uses
the oracle-stage criterion (`relEquiv_sup_generatedBy_iff`) to check that the
equivalence does not move.

**The calculus.**  λ-terms with syntactic equations and no reduction; an
observation reads the β-class of a term (`betaClass`).  Contexts are lists of
actions: apply to an argument, ask the β-oracle whether the term is
β-convertible to a target (answer: a Church Boolean), or ask the syntactic
oracle whether the term *is* the target.

* **Stage 0** (`applicative`): applicative contexts only.  Its relative
  equivalence is β-conversion (`applicative_relEquiv_iff`).
* **Stage 1** (`applicative ⊔ generatedBy betaOracles`): the β-oracle preserves
  stage-0 equivalence, so by the criterion the extension is conservative
  (`stageOne_relEquiv_iff`), and one stage-1 observation decides every stage-0
  equation (`betaOracle_decides_true`, `betaOracle_decides_false`).
* **Control, strict stage**: the syntactic oracle does not preserve stage-0
  equivalence; `I I` and `I` are β-convertible yet separated once it is added
  (`syntacticOracle_separates`).  Deciding is not distinguishing: the
  admissible oracle adds verdicts, the inadmissible one adds distinctions.

`stratified_escape` packages the three facts: stage 0 has no internal decider,
stage 1 has the same equivalence, and a stage-1 observer decides it.  The
diagonal recurs at any stage that is itself presented as a reflexive
structure: `Mettapedia.Logic.Diagonal.Reflexive.trivial_of_decidesEquiv` says a
reflexive structure deciding its own equivalence internally is trivial.

The β-oracle is a parameter: any decision of β-conversion (an instance of
`Decidable (BetaConv term target)` for every pair) gives the same stage.  One
exists classically (`classicalOracle`); no λ-term implements one
(`no_lambda_decides_betaConv`).  The theorems hold for every oracle.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.GraphTheory.OracleStratification

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.GraphTheory
open Mettapedia.GSLT.GraphTheory.BudgetedBeta
open Mettapedia.GSLT.GraphTheory.ReflectiveBeta
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass

universe uS uContext uRule uAtom

/-! ## Relative equivalence of an inert calculus -/

/-- **In a calculus with no reduction, the relative equivalence is agreement of
every observation through every admissible context.** -/
theorem relEquiv_iff_of_inert {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
    (inert : ∀ source target : S.Term, ¬ S.Step source target) (A : AdmissibleClass rules)
    (observations : ContextualRules.Observations.{uAtom} S) (left right : S.Term) :
    A.RelEquiv observations left right ↔
      ∀ context, A.Admissible context → ∀ atom,
        observations.observes atom (rules.plug context left) ↔
          observations.observes atom (rules.plug context right) := by
  constructor
  · intro related context admissible atom
    exact AdmissibleContextCongruence.bisimilar_observes related (atom, ⟨context, admissible⟩)
  · intro agree
    refine ⟨fun first second => ∀ context, A.Admissible context → ∀ atom,
        observations.observes atom (rules.plug context first) ↔
          observations.observes atom (rules.plug context second), ⟨?_, ?_, ?_⟩, agree⟩
    · intro _ _ _ label _ step
      exact absurd step (inert _ _)
    · intro _ _ _ label _ step
      exact absurd step (inert _ _)
    · intro first second held atom
      exact held atom.2.1 atom.2.2 atom.1

/-! ## The calculus -/

/-- λ-terms with syntactic equations and no reduction. -/
abbrev syntacticLambdaGSLT : GSLT where
  Term := LambdaTerm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites _ _ := False
  rewrites_resp_left := fun _ impossible => impossible.elim
  rewrites_resp_right := fun impossible _ => impossible.elim

/-- Church truth, `λx y. x`. -/
def churchTrue : LambdaTerm := .lam (.lam (.var 1))

/-- Church falsity, `λx y. y`. -/
def churchFalse : LambdaTerm := .lam (.lam (.var 0))

theorem churchTrue_not_betaConv_churchFalse : ¬ BetaConv churchTrue churchFalse := by
  intro convertible
  exact absurd (normalForm_eq_of_betaConv (by decide) (by decide) convertible) (by decide)

/-- Observer actions. -/
inductive Action where
  /-- Apply the term to an argument. -/
  | apply (argument : LambdaTerm)
  /-- Ask whether the term is β-convertible to the target. -/
  | betaOracle (target : LambdaTerm)
  /-- Ask whether the term is syntactically the target. -/
  | syntacticOracle (target : LambdaTerm)

/-- A β-oracle: a decision of β-conversion for every pair. -/
abbrev BetaOracle : Type := ∀ term target : LambdaTerm, Decidable (BetaConv term target)

/-- **An oracle exists classically.** -/
@[instance_reducible]
noncomputable def classicalOracle : BetaOracle := fun _ _ => Classical.propDecidable _

variable (oracle : BetaOracle)

/-- The effect of an action on a term, with the β-oracle's answers read off
`oracle`. -/
def Action.act : Action → LambdaTerm → LambdaTerm
  | .apply argument, term => .app term argument
  | .betaOracle target, term =>
      @ite _ (BetaConv term target) (oracle term target) churchTrue churchFalse
  | .syntacticOracle target, term => if term = target then churchTrue else churchFalse

/-- Contexts are action lists, applied first to last. -/
abbrev oracleRules : ContextualRules syntacticLambdaGSLT where
  Context := List Action
  identity := []
  compose outer inner := inner ++ outer
  plug actions term := actions.foldl (fun current action => action.act oracle current) term
  plug_identity _ := rfl
  plug_compose outer inner term := by
    change (inner ++ outer).foldl _ term = outer.foldl _ (inner.foldl _ term)
    rw [List.foldl_append]
  plug_resp _ := by
    intro left right equal
    change left = right at equal
    subst equal
    rfl
  Rule := Empty
  fires _ _ _ := False
  fires_resp_left := fun _ impossible => impossible.elim
  fires_resp_right := fun impossible _ => impossible.elim
  fires_step := fun impossible => impossible.elim

/-- Observations read the β-class. -/
def betaClass : ContextualRules.Observations syntacticLambdaGSLT where
  Atom := LambdaTerm
  observes atom term := BetaConv term atom
  observes_resp := by
    intro _ left right equal
    change left = right at equal
    subst equal
    exact Iff.rfl

/-- Agreement on every β-class observation is β-conversion. -/
theorem observations_agree_iff (first second : LambdaTerm) :
    (∀ atom, betaClass.observes atom first ↔ betaClass.observes atom second) ↔
      BetaConv first second := by
  constructor
  · intro agree
    exact betaConv_equivalence.symm ((agree first).mp (betaConv_equivalence.refl first))
  · intro convertible atom
    exact ⟨fun held => betaConv_equivalence.trans (betaConv_equivalence.symm convertible) held,
      fun held => betaConv_equivalence.trans convertible held⟩

/-! ## Stage 0: applicative observers -/

/-- Only applications. -/
def IsApplicative (actions : List Action) : Prop :=
  ∀ action ∈ actions, ∃ argument, action = .apply argument

/-- **Stage 0**: the applicative contexts. -/
def applicative : AdmissibleClass (oracleRules oracle) where
  Admissible := IsApplicative
  identity_mem := fun _ member => absurd member (List.not_mem_nil)
  compose_mem := fun {outer inner} outerApplicative innerApplicative action member => by
    rcases List.mem_append.mp member with inInner | inOuter
    · exact innerApplicative action inInner
    · exact outerApplicative action inOuter

theorem plug_applicative_betaConv {actions : List Action}
    (applicativeActions : IsApplicative actions)
    {left right : LambdaTerm} (convertible : BetaConv left right) :
    BetaConv ((oracleRules oracle).plug actions left)
      ((oracleRules oracle).plug actions right) := by
  induction actions generalizing left right with
  | nil => exact convertible
  | cons action rest ih =>
      obtain ⟨argument, rfl⟩ := applicativeActions action List.mem_cons_self
      exact ih (fun action' member => applicativeActions action' (List.mem_cons_of_mem _ member))
        (betaConv_app_left argument convertible)

/-- **Stage 0 equivalence is β-conversion.** -/
theorem applicative_relEquiv_iff (left right : LambdaTerm) :
    (applicative oracle).RelEquiv betaClass left right ↔ BetaConv left right := by
  rw [relEquiv_iff_of_inert (S := syntacticLambdaGSLT) (rules := oracleRules oracle)
    (fun _ _ impossible => impossible)]
  constructor
  · intro agree
    exact (observations_agree_iff left right).mp (agree [] (applicative oracle).identity_mem)
  · intro convertible context admissible
    exact (observations_agree_iff _ _).mpr
      (plug_applicative_betaConv oracle admissible convertible)

/-! ## Stage 1: the β-oracle -/

/-- The single-action β-oracle contexts. -/
def betaOracles : Set (List Action) := {context | ∃ target, context = [.betaOracle target]}

/-- The single-action syntactic-oracle contexts. -/
def syntacticOracles : Set (List Action) :=
  {context | ∃ target, context = [.syntacticOracle target]}

theorem plug_betaOracle (target term : LambdaTerm) :
    (oracleRules oracle).plug [.betaOracle target] term =
      Action.act oracle (.betaOracle target) term := rfl

theorem act_betaOracle_of_betaConv {target term : LambdaTerm} (convertible : BetaConv term target) :
    Action.act oracle (.betaOracle target) term = churchTrue :=
  @if_pos _ (oracle term target) convertible _ _ _

theorem act_betaOracle_of_not_betaConv {target term : LambdaTerm}
    (distinct : ¬ BetaConv term target) :
    Action.act oracle (.betaOracle target) term = churchFalse :=
  @if_neg _ (oracle term target) distinct _ _ _

/-- **The β-oracle preserves stage-0 equivalence**: its answer depends only on
the β-class. -/
theorem betaOracle_preserves :
    ∀ context ∈ betaOracles,
      Preserves (rules := oracleRules oracle) context
        ((applicative oracle).RelEquiv betaClass) := by
  rintro _ ⟨target, rfl⟩ left right related
  have convertible := (applicative_relEquiv_iff oracle left right).mp related
  rw [applicative_relEquiv_iff]
  change BetaConv (Action.act oracle (.betaOracle target) left)
    (Action.act oracle (.betaOracle target) right)
  cases oracle left target with
  | isTrue leftTarget =>
      have rightTarget : BetaConv right target :=
        betaConv_equivalence.trans (betaConv_equivalence.symm convertible) leftTarget
      rw [act_betaOracle_of_betaConv oracle leftTarget,
        act_betaOracle_of_betaConv oracle rightTarget]
      exact betaConv_equivalence.refl _
  | isFalse leftTarget =>
      have rightTarget : ¬ BetaConv right target := fun held =>
        leftTarget (betaConv_equivalence.trans convertible held)
      rw [act_betaOracle_of_not_betaConv oracle leftTarget,
        act_betaOracle_of_not_betaConv oracle rightTarget]
      exact betaConv_equivalence.refl _

/-- **Stage 1 is conservative** over stage 0, by the oracle-stage criterion. -/
theorem stageOne_conservative (left right : LambdaTerm) :
    (applicative oracle ⊔ generatedBy betaOracles).RelEquiv betaClass left right ↔
      (applicative oracle).RelEquiv betaClass left right :=
  ((applicative oracle).relEquiv_sup_generatedBy_iff betaClass betaOracles).mpr
    (betaOracle_preserves oracle) left right

theorem stageOne_relEquiv_iff (left right : LambdaTerm) :
    (applicative oracle ⊔ generatedBy betaOracles).RelEquiv betaClass left right ↔
      BetaConv left right :=
  (stageOne_conservative oracle left right).trans (applicative_relEquiv_iff oracle left right)

/-- **One stage-1 observation decides a stage-0 equation**: the β-oracle's
answer is β-convertible to truth exactly when the equation holds. -/
theorem betaOracle_decides_true (target term : LambdaTerm) :
    betaClass.observes churchTrue ((oracleRules oracle).plug [.betaOracle target] term) ↔
      BetaConv term target := by
  change BetaConv (Action.act oracle (.betaOracle target) term) churchTrue ↔ BetaConv term target
  cases oracle term target with
  | isTrue convertible =>
      rw [act_betaOracle_of_betaConv oracle convertible]
      exact ⟨fun _ => convertible, fun _ => betaConv_equivalence.refl _⟩
  | isFalse convertible =>
      rw [act_betaOracle_of_not_betaConv oracle convertible]
      exact ⟨fun wrong =>
          absurd (betaConv_equivalence.symm wrong) churchTrue_not_betaConv_churchFalse,
        fun held => absurd held convertible⟩

/-- … and to falsity exactly when it fails. -/
theorem betaOracle_decides_false (target term : LambdaTerm) :
    betaClass.observes churchFalse ((oracleRules oracle).plug [.betaOracle target] term) ↔
      ¬ BetaConv term target := by
  change BetaConv (Action.act oracle (.betaOracle target) term) churchFalse ↔
    ¬ BetaConv term target
  cases oracle term target with
  | isTrue convertible =>
      rw [act_betaOracle_of_betaConv oracle convertible]
      exact ⟨fun wrong => absurd wrong churchTrue_not_betaConv_churchFalse,
        fun fails => absurd convertible fails⟩
  | isFalse convertible =>
      rw [act_betaOracle_of_not_betaConv oracle convertible]
      exact ⟨fun _ => convertible, fun _ => betaConv_equivalence.refl _⟩

/-! ## Control: an inadmissible oracle is strict -/

/-- `I I` β-converts to `I`. -/
theorem identity_application_betaConv :
    BetaConv (.app LambdaTerm.I LambdaTerm.I) LambdaTerm.I :=
  betaConv_beta (.var 0) LambdaTerm.I

/-- **The syntactic oracle separates β-convertible terms**: adding it refines
the equivalence (the strict case of the oracle-stage criterion). -/
theorem syntacticOracle_separates :
    (applicative oracle).RelEquiv betaClass (.app LambdaTerm.I LambdaTerm.I) LambdaTerm.I ∧
      ¬ (applicative oracle ⊔ generatedBy syntacticOracles).RelEquiv betaClass
        (.app LambdaTerm.I LambdaTerm.I) LambdaTerm.I := by
  refine ⟨(applicative_relEquiv_iff oracle _ _).mpr identity_application_betaConv, ?_⟩
  refine (applicative oracle).not_relEquiv_sup_of_not_preserved betaClass
    (added := syntacticOracles)
    (context := [.syntacticOracle LambdaTerm.I]) ⟨LambdaTerm.I, rfl⟩ ?_
  rw [applicative_relEquiv_iff]
  change ¬ BetaConv (if LambdaTerm.app LambdaTerm.I LambdaTerm.I = LambdaTerm.I then churchTrue
    else churchFalse) (if LambdaTerm.I = LambdaTerm.I then churchTrue else churchFalse)
  rw [if_neg (by decide), if_pos rfl]
  exact fun convertible =>
    churchTrue_not_betaConv_churchFalse (betaConv_equivalence.symm convertible)

/-! ## The stratified escape -/

/-- **The stratified escape.**  No λ-term decides β-conversion; the stage with
the β-oracle has the same equivalence; and one of its observers decides every
equation. -/
theorem stratified_escape :
    (∀ decider : LambdaTerm, ¬ lambdaReflexive.DecidesEquiv decider) ∧
      (∀ left right,
        (applicative oracle ⊔ generatedBy betaOracles).RelEquiv betaClass left right ↔
          (applicative oracle).RelEquiv betaClass left right) ∧
      (∀ term target, (betaClass.observes churchTrue
          ((oracleRules oracle).plug [.betaOracle target] term) ↔ BetaConv term target) ∧
        (betaClass.observes churchFalse
          ((oracleRules oracle).plug [.betaOracle target] term) ↔ ¬ BetaConv term target)) :=
  ⟨no_lambda_decides_betaConv, stageOne_conservative oracle,
    fun term target =>
      ⟨betaOracle_decides_true oracle target term, betaOracle_decides_false oracle target term⟩⟩

end Mettapedia.GSLT.GraphTheory.OracleStratification
