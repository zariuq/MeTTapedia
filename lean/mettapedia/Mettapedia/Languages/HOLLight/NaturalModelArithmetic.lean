import Mettapedia.Languages.HOLLight.NaturalModelCategoricity
import Mettapedia.Languages.HOLLight.ExactFormulaReadback

/-!
# Addition interpreted from retained source equations

The two recursion equations concern the actual supplied addition term.
Together with the received Peano facts they determine its action through the
existing natural-carrier equivalence. No correctness law for an entire source
expression evaluator is assumed.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.NaturalModelArithmetic
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReferenceBooleanSemantics
universe w

variable (natural : NaturalModelCategoricity.Signature)
  (addition : HOL.ClosedTerm Symbol (natural.number.arr (natural.number.arr natural.number)))

def zeroEquation : HOL.ClosedFormula Symbol :=
  universal (.eq
    (.app (.app (HOL.weakenCtx _ addition) (HOL.weakenCtx _ natural.zero)) (.var .vz))
    (.var .vz))

def successorEquation : HOL.ClosedFormula Symbol :=
  universal (universal (.eq
    (.app (.app (HOL.weakenCtx _ addition)
      (.app (HOL.weakenCtx _ natural.successor) (.var (.vs .vz)))) (.var .vz))
    (.app (HOL.weakenCtx _ natural.successor)
      (.app (.app (HOL.weakenCtx _ addition) (.var (.vs .vz))) (.var .vz)))))

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

def add : natural.Carrier model → natural.Carrier model → natural.Carrier model :=
  model.denote addition (fun impossible => nomatch impossible)

theorem denote_add (values : model.Valuation []) :
    model.denote addition values = add natural addition model := by
  apply congrArg (model.denote addition)
  funext type impossible
  exact nomatch impossible

variable (full : model.FullDomains) (meanings : Meanings model)
include full meanings

theorem zeroEquation_meaning : model.models (zeroEquation natural addition) ↔
    ∀ value, add natural addition model (natural.origin model) value = value := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [zeroEquation, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote, HOL.PreModel.denote,
    HOL.PreModel.extend, HOL.HenkinModel.denote_weakenCtx, natural.denote_zero model,
    denote_add natural addition model, model.eqv_iff_eq_of_fullDomains full,
    admitted, forall_true_left]

theorem successorEquation_meaning : model.models (successorEquation natural addition) ↔
    ∀ first second,
      add natural addition model (natural.next model first) second =
        natural.next model (add natural addition model first second) := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [successorEquation, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote, HOL.PreModel.denote,
    HOL.PreModel.extend, HOL.HenkinModel.denote_weakenCtx, natural.denote_successor model,
    denote_add natural addition model, model.eqv_iff_eq_of_fullDomains full,
    admitted, forall_true_left]

/-- Addition follows from its primitive source equations and the previously
constructed zero/successor comparison. -/
theorem add_naturalEquivalence
    (separation : model.models natural.successorSeparation)
    (injectivity : model.models natural.successorInjective)
    (induction : model.models natural.induction)
    (atZero : model.models (zeroEquation natural addition))
    (atSuccessor : model.models (successorEquation natural addition)) (first second : Nat) :
    add natural addition model
      (natural.naturalEquivalence model full meanings separation injectivity induction first)
      (natural.naturalEquivalence model full meanings separation injectivity induction second) =
    natural.naturalEquivalence model full meanings separation injectivity induction (first + second) := by
  have zero := (zeroEquation_meaning natural addition model full meanings).mp atZero
  have successor := (successorEquation_meaning natural addition model full meanings).mp atSuccessor
  induction first with
  | zero =>
      rw [natural.naturalEquivalence_zero, zero, Nat.zero_add]
  | succ first previous =>
      rw [natural.naturalEquivalence_succ, successor, previous, Nat.succ_add,
        natural.naturalEquivalence_succ]

def constantZero : HOL.ClosedTerm Symbol (natural.number.arr (natural.number.arr natural.number)) :=
  .lam (.lam (HOL.weakenCtx _ natural.zero))

/-- Correct zero/successor operations do not justify substituting a constant
function for addition. Its zero clause already fails at successor zero. -/
theorem constantZero_refused (separation : model.models natural.successorSeparation) :
    ¬ model.models (zeroEquation natural (constantZero natural)) := by
  intro valid
  have equation := (zeroEquation_meaning natural (constantZero natural) model full meanings).mp valid
    (natural.next model (natural.origin model))
  have computed : add natural (constantZero natural) model (natural.origin model)
      (natural.next model (natural.origin model)) = natural.origin model := by
    simp only [add, constantZero, HOL.HenkinModel.denote, HOL.PreModel.denote,
      HOL.HenkinModel.denote_weakenCtx, natural.denote_zero model]
  rw [computed] at equation
  exact (natural.successorSeparation_meaning model full meanings).mp separation _ equation.symm

structure CachedFacts (state : ProofExecution.Registered.State) where
  zero : Theorem
  successor : Theorem
  zero_known : zero ∈ state.cache
  successor_known : successor ∈ state.cache
  zero_closed : zero.sequent.hyp = ∅
  successor_closed : successor.sequent.hyp = ∅
  zero_read : Translates [] zero.sequent.concl.term .prop (zeroEquation natural addition)
  successor_read : Translates [] successor.sequent.concl.term .prop (successorEquation natural addition)

def read? (state : ProofExecution.Registered.State) (zeroIndex successorIndex : Nat) :
    Option (CachedFacts natural addition state) := do
  let zero ← ExactFormulaReadback.read? state zeroIndex (zeroEquation natural addition)
  let successor ← ExactFormulaReadback.read? state successorIndex (successorEquation natural addition)
  return ⟨zero.fact, successor.fact, zero.known, successor.known,
    zero.closed, successor.closed, zero.translated, successor.translated⟩

open SourceProfileModels TypeFamilySemantics
omit full meanings

/-- Exact retained readings turn accepted source commands into the two
arithmetic laws in their receiving model. -/
theorem replay_equations (commands : List ProofExecution.Registered.Command)
    (after : ProofExecution.Registered.State)
    (accepted : ProofExecution.Registered.replayFrom policy
      (ProofExecution.Registered.empty SourceProfile.primitiveContext) commands = some after)
    (facts : CachedFacts natural addition after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (sourceReplayFrame commands after accepted).frame.model other assignment
    model.models (zeroEquation natural addition) ∧ model.models (successorEquation natural addition) := by
  let frame := (sourceReplayFrame commands after accepted).frame
  constructor
  · apply frame.cached_models_of_translation other assignment facts.zero_known facts.zero_read
    intro hypothesis member
    simp [facts.zero_closed, translatedHypotheses] at member
  · apply frame.cached_models_of_translation other assignment facts.successor_known facts.successor_read
    intro hypothesis member
    simp [facts.successor_closed, translatedHypotheses] at member

#print axioms add_naturalEquivalence
#print axioms replay_equations
end Mettapedia.Languages.HOLLight.NaturalModelArithmetic
