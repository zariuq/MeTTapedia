import Mettapedia.GSLT.Core.ComputationQuotient
import Mettapedia.GSLT.Dedukti.PeanoFiber
import Mettapedia.GSLT.Dedukti.Separation

/-! A Dedukti reduction is computational; publishing a numeral is observable.
Promotion preserves which numeral is published and every finite trace of
publication labels. A literal-match census changes on exactly the same two
input occurrences. -/

set_option autoImplicit false
namespace Mettapedia.GSLT.Dedukti.PeanoComputationQuotient

open Mettapedia.GSLT.LanguageDef.LF (Term)
open PeanoFiber
open ComputationQuotient
open _root_.Relation (EqvGen ReflTransGen)

inductive State where
  | pending (t : Term)
  | reported (n : Nat)
  deriving DecidableEq

inductive Compute (theory : Theory) : State → State → Prop where
  | reduce {t u} : Step theory t u → Compute theory (.pending t) (.pending u)

inductive Emit : Nat → State → State → Prop where
  | numeral (n) : Emit n (.pending (PeanoFiber.numeral n)) (.reported n)

def reference (theory : Theory) := Mettapedia.OSLF.Framework.GSLTTypeSynthesis.equalityGSLT State
  (fun x y => Compute theory x y ∨ ∃ n, Emit n x y)

def presentation (theory : Theory) : Split (reference theory) Nat := ⟨Compute theory, Emit, fun _ _ => Iff.rfl⟩

abbrev split := presentation peanoTheory

private def termSetoid : Setoid Term :=
  ⟨Conv peanoTheory, EqvGen.is_equivalence _⟩

private def code : State → Sum (Quotient termSetoid) Nat
  | .pending t => .inl (Quotient.mk termSetoid t)
  | .reported n => .inr n

private theorem code_eq {x y : State} (same : split.project x = split.project y) : code x = code y := by
  have comp : ∀ x y, Compute peanoTheory x y → code x = code y := by
    intro x y step
    cases step with
    | reduce h => exact congrArg Sum.inl (Quotient.sound (EqvGen.rel _ _ h : Conv peanoTheory _ _))
  obtain ⟨read, observes⟩ := (split.observer_iff code).2 ⟨fun _ _ h => congrArg code h, comp⟩
  exact (observes x).symm.trans ((congrArg read same).trans (observes y))

private theorem pending_reduces {t u : Term} (r : Reduces peanoTheory t u) :
    ReflTransGen split.compute (.pending t) (.pending u) := by
  induction r with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (Compute.reduce h)

/-- Dedukti confluence supplies a common reduct for any two representatives,
even outside the closed arithmetic fragment. Numerals are normal, so a
publication can never lose a race with further computation from its source. -/
theorem lifts : split.Lifts := by
  apply split.lifts_of_join_postponement
  · intro x u same
    have h := code_eq same
    cases x with
    | pending t =>
      cases u with
      | reported => cases h
      | pending v =>
        have converted : Conv peanoTheory t v := Quotient.exact (Sum.inl.inj h)
        obtain ⟨z, first, second⟩ := peano_confluent.eqvGen_iff_join.mp converted
        exact ⟨.pending z, pending_reduces first, pending_reduces second⟩
    | reported n =>
      cases u with
      | pending => cases h
      | reported m => obtain rfl := Sum.inr.inj h; exact ⟨_, .refl, .refl⟩
  · intro l u v z event computation
    cases event
    cases computation with
    | reduce h => exact (numeral_normal _ _ h).elim

theorem finite_publications (s : State) (events : List Nat) (out : split.Class) :
    Split.Trace split.visible (split.project s) events out ↔
      ∃ t, Split.Trace split.weak s events t ∧ split.project t = out :=
  split.trace_iff lifts s events out

/-- An entire recursive addition can precede one publication. Only the
sum can be reported from this input, and the label identifies the receipt. -/
theorem addition_publishes (a b label result : Nat) :
    split.visible label (split.project (.pending (plus (numeral a) (numeral b))))
      (split.project (.reported result)) ↔ a + b = label ∧ label = result := by
  constructor
  · rintro ⟨u,v,input,output,event⟩
    cases event
    have first := Sum.inl.inj (code_eq input.symm)
    have converted : Conv peanoTheory _ _ := Quotient.exact first
    exact ⟨(conv_iff_numeral_eq (reduces_plus_numerals a b) .refl).mp converted, Sum.inr.inj (code_eq output)⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, _, (split.reductions_equal (pending_reduces (reduces_plus_numerals a b))).symm,
      rfl, Emit.numeral _⟩

/-- The source needs one arithmetic step before it can publish this answer.
The quotient can issue the same label immediately. -/
theorem plus_zero_needs_work (n : Nat) :
    let input := State.pending (plus (numeral n) zero)
    ¬ Emit n input (.reported n) ∧
      Compute peanoTheory input (.pending (numeral n)) ∧
      split.visible n (split.project input) (split.project (.reported n)) := by
  dsimp only
  refine ⟨?_, Compute.reduce ?_, (addition_publishes n 0 n n).2 ⟨Nat.add_zero _, rfl⟩⟩
  · intro issued
    have neq : plus (numeral n) zero ≠ numeral n := by cases n <;> simp [plus, numeral, zero, succ]
    have origin {a b k} (event : Emit k a b) : a = .pending (numeral k) := by cases event; rfl
    exact neq (State.pending.inj (origin issued))
  · have root := RootStep.rule (theory := peanoTheory) (rule := plusZero) (fun _ => numeral n)
      (by simp [peanoTheory, Theory.ofSig, peanoRules])
    simpa [plusZero, plus, zero] using Step.root root

private def add23 := State.pending (plus (numeral 2) (numeral 3))
private def five := State.pending (numeral 5)

theorem literal_census_changes :
    [add23, five].countP (· == five) = 1 ∧
    ∀ test : split.Class → Bool, test (split.project five) = true →
      [add23, five].countP (fun (s : State) => test (split.project s)) = 2 := by
  refine ⟨by decide +kernel, ?_⟩
  intro test accepts
  have same : split.project add23 = split.project five :=
    split.reductions_equal (pending_reduces (reduces_plus_numerals 2 3))
  simp [same, accepts]

/-- Hiding both arms of Dedukti's choice turns a stuck variable into a
state that can publish zero in the quotient. The single-event observer
detects the extra behavior. -/
theorem hiding_choice_loses_lifting : ¬ (presentation (withChoice Theory.empty)).Lifts := by
  let p := presentation (withChoice Theory.empty)
  intro liftsChoice
  have left : p.project (.pending (choose (.var 0) (numeral 0))) = p.project (.pending (.var 0)) :=
    p.compute_equal (Compute.reduce (step_choose_left _ _ _))
  have right : p.project (.pending (choose (.var 0) (numeral 0))) = p.project (.pending (numeral 0)) :=
    p.compute_equal (Compute.reduce (step_choose_right _ _ _))
  obtain ⟨_, ⟨_, work, issued⟩, _⟩ := liftsChoice (left.symm.trans right) (Emit.numeral 0)
  cases issued
  have stuck : Mettapedia.Logic.Relation.IsNormal p.compute (.pending (.var 0)) := by
    intro y step
    cases step with
    | reduce h => exact var_normal (withChoice_headed Theory.empty_headed) 0 _ h
  have impossible := stuck.reflTransGen_eq work
  exact Term.noConfusion (show Term.con "zero" = Term.var 0 from State.pending.inj impossible)

end Mettapedia.GSLT.Dedukti.PeanoComputationQuotient
