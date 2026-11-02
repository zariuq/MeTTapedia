import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Information required by future region observers

A question may run an entire continuation before returning its answer.
Answers may depend on the question. Equality of all these answers defines
the semantic information which a region boundary must retain.

The canonical class map factors through every sufficient summary, on that
summary's reachable image. The converse is false: sufficient summaries may
retain extra information. No arbitrary value is chosen for unreachable codes.
Finite cardinality is an information bound, not a byte or instruction bound.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RegionObservations

universe u v w x

-- Questions and their answer families have independent universe levels.
-- Neither is a type parameter; their maximum appears in the bundle's type.
set_option linter.checkUnivs false in
structure Family (State : Type u) where
  Question : Type v
  Answer : Question → Type w
  read : (question : Question) → State → Answer question

namespace Family

variable {State : Type u} (family : Family.{u, v, w} State)

def Equivalent (left right : State) : Prop :=
  ∀ question, family.read question left = family.read question right

def setoid : Setoid State where
  r := family.Equivalent
  iseqv := ⟨fun _ _ => rfl, fun same question => (same question).symm,
    fun first second question => (first question).trans (second question)⟩

abbrev Classes := Quotient family.setoid

def classOf (state : State) : family.Classes := Quotient.mk family.setoid state

theorem classOf_eq_iff (left right : State) :
    family.classOf left = family.classOf right ↔ family.Equivalent left right :=
  Quotient.eq

def readClass (question : family.Question) : family.Classes → family.Answer question :=
  Quotient.lift (family.read question) (fun _ _ same => same question)

@[simp] theorem readClass_classOf (question : family.Question) (state : State) :
    family.readClass question (family.classOf state) = family.read question state := rfl

/-- Summary equality must preserve all admitted future questions, not just
the latest returned value. -/
def Sufficient {Code : Type x} (summary : State → Code) : Prop :=
  ∀ left right, summary left = summary right → family.Equivalent left right

/-- An exact summary forgets every distinction that these questions cannot
detect, as well as retaining every distinction they can detect. -/
def Exact {Code : Type x} (summary : State → Code) : Prop :=
  ∀ left right, summary left = summary right ↔ family.Equivalent left right

theorem classOf_exact : family.Exact family.classOf := family.classOf_eq_iff

theorem classOf_sufficient : family.Sufficient family.classOf :=
  fun left right => (family.classOf_eq_iff left right).mp

/-- Recover the least semantic state from a reachable sufficient code.
Classical choice supplies a representative, but sufficiency makes its class
independent of that choice. This is a specification, not a native decoder. -/
noncomputable def recover {Code : Type x} (summary : State → Code) :
    Set.range summary → family.Classes :=
  fun code => family.classOf (Classical.choose code.property)

theorem recover_summary {Code : Type x} (summary : State → Code)
    (sufficient : family.Sufficient summary) (state : State) :
    family.recover summary (Set.rangeFactorization summary state) = family.classOf state := by
  apply (family.classOf_eq_iff _ _).mpr
  apply sufficient
  exact Classical.choose_spec (Set.rangeFactorization summary state).property

/-- The universal property points from a sufficient summary to the minimal
quotient. It does not require an inhabited result for unreachable codes. -/
theorem sufficient_iff_factors {Code : Type x} (summary : State → Code) :
    family.Sufficient summary ↔
      Core.NonFactorization.Factors (Set.rangeFactorization summary) family.classOf := by
  constructor
  · intro sufficient
    exact ⟨family.recover summary, family.recover_summary summary sufficient⟩
  · rintro ⟨decode, sound⟩ left right same
    apply (family.classOf_eq_iff left right).mp
    rw [← sound left, ← sound right]
    congr 1
    exact Subtype.ext same

theorem recover_surjective {Code : Type x} (summary : State → Code)
    (sufficient : family.Sufficient summary) : Function.Surjective (family.recover summary) := by
  intro target
  induction target using Quotient.inductionOn with
  | h state => exact ⟨Set.rangeFactorization summary state,
      family.recover_summary summary sufficient state⟩

/-- For a finite state space, every sufficient encoding uses at least as
many reachable codes as the future-observation quotient has classes. -/
theorem classes_card_le [Finite State] {Code : Type x} (summary : State → Code)
    (sufficient : family.Sufficient summary) :
    Nat.card family.Classes ≤ Nat.card (Set.range summary) := by
  let : Finite (Set.range summary) := Finite.of_surjective
    (Set.rangeFactorization summary) (fun ⟨_, state, equal⟩ => ⟨state, Subtype.ext equal⟩)
  exact Nat.card_le_card_of_surjective _ (family.recover_surjective summary sufficient)

theorem recover_injective_of_exact {Code : Type x} (summary : State → Code)
    (exactSummary : family.Exact summary) : Function.Injective (family.recover summary) := by
  intro left right same
  apply Subtype.ext
  have equivalent := (family.classOf_eq_iff _ _).mp same
  have codes := (exactSummary _ _).mpr equivalent
  exact (Classical.choose_spec left.property).symm.trans
    (codes.trans (Classical.choose_spec right.property))

/-- An exact summary's reachable codes are equivalent to the canonical
classes; the property is stronger than mere sufficiency. -/
noncomputable def exactEquiv {Code : Type x} (summary : State → Code)
    (exactSummary : family.Exact summary) : Set.range summary ≃ family.Classes :=
  Equiv.ofBijective (family.recover summary)
    ⟨family.recover_injective_of_exact summary exactSummary,
      family.recover_surjective summary (fun a b => (exactSummary a b).mp)⟩

theorem recover_unique {Code : Type x} (summary : State → Code)
    (sufficient : family.Sufficient summary) (other : Set.range summary → family.Classes)
    (sound : ∀ state, other (Set.rangeFactorization summary state) = family.classOf state) :
    other = family.recover summary := by
  funext code
  obtain ⟨state, equal⟩ := code.property
  have codeEq : code = Set.rangeFactorization summary state := Subtype.ext equal.symm
  rw [codeEq, sound, family.recover_summary summary sufficient]

end Family

variable {State : Type u}

/-- Fine questions can answer every coarse question, possibly by a readout
which discards answer detail. It follows that fine equivalence implies coarse
equivalence, not conversely. -/
structure Refinement (coarse : Family.{u, v, w} State) (fine : Family.{u, v, w} State) where
  question : coarse.Question → fine.Question
  answer : (q : coarse.Question) → fine.Answer (question q) → coarse.Answer q
  preserves : ∀ q state, answer q (fine.read (question q) state) = coarse.read q state

namespace Refinement

variable {coarse fine : Family.{u, v, w} State}

theorem equivalent (refinement : Refinement coarse fine) {left right : State}
    (same : fine.Equivalent left right) : coarse.Equivalent left right := by
  intro question
  rw [← refinement.preserves question left, ← refinement.preserves question right,
    same (refinement.question question)]

def classes (refinement : Refinement coarse fine) : fine.Classes → coarse.Classes :=
  Quotient.lift coarse.classOf (fun _ _ same =>
    (coarse.classOf_eq_iff _ _).mpr (refinement.equivalent same))

@[simp] theorem classes_classOf (refinement : Refinement coarse fine) (state : State) :
    refinement.classes (fine.classOf state) = coarse.classOf state := rfl

theorem classes_surjective (refinement : Refinement coarse fine) :
    Function.Surjective refinement.classes := by
  intro target
  induction target using Quotient.inductionOn with
  | h state => exact ⟨fine.classOf state, rfl⟩

theorem cardinal_mono [Finite State] (refinement : Refinement coarse fine) :
    Nat.card coarse.Classes ≤ Nat.card fine.Classes :=
  Nat.card_le_card_of_surjective _ refinement.classes_surjective

def comp {finest : Family.{u, v, w} State}
    (first : Refinement coarse fine) (second : Refinement fine finest) :
    Refinement coarse finest where
  question q := second.question (first.question q)
  answer q value := first.answer q (second.answer (first.question q) value)
  preserves q state := by rw [second.preserves, first.preserves]

theorem classes_comp {finest : Family.{u, v, w} State}
    (first : Refinement coarse fine) (second : Refinement fine finest)
    (value : finest.Classes) :
    (first.comp second).classes value = first.classes (second.classes value) := by
  induction value using Quotient.inductionOn with
  | h state => rfl

end Refinement

namespace Controls

/-- Future additions can change absence to presence, but cannot distinguish
two already positive counts under this observation. -/
def existence : Family Nat where
  Question := Nat
  Answer _ := Bool
  read added count := decide (0 < count + added)

theorem existence_exact : existence.Exact (fun count => decide (0 < count)) := by
  intro left right
  constructor
  · intro same
    change ∀ added : Nat, decide (0 < left + added) = decide (0 < right + added)
    intro added
    have positivity : (0 < left) ↔ (0 < right) := by simpa using congrArg (· = true) same
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  · intro same
    change ∀ added : Nat, decide (0 < left + added) = decide (0 < right + added) at same
    simpa using same 0

theorem counts_are_sufficient : existence.Sufficient (id : Nat → Nat) := by
  intro left right same
  cases same
  intro _
  rfl

theorem minimal_summary_does_not_recover_every_sufficient_summary :
    ¬ Core.NonFactorization.Factors existence.classOf (id : Nat → Nat) := by
  intro factors
  have same : existence.classOf 1 = existence.classOf 2 :=
    (existence.classOf_eq_iff 1 2).mpr ((existence_exact 1 2).mp (by decide))
  have impossible := factors.constantOnFibers 1 2 same
  exact (by decide : (1 : Nat) ≠ 2) impossible

def stateAndHidden : Family (Bool × Bool) where
  Question := Unit
  Answer _ := Bool
  read _ state := state.1

def bothBits : Family (Bool × Bool) where
  Question := Bool
  Answer _ := Bool
  read question state := if question then state.2 else state.1

def moreQuestions : Refinement stateAndHidden bothBits where
  question _ := false
  answer _ value := value
  preserves _ _ := rfl

theorem observer_refinement_splits_classes :
    stateAndHidden.classOf (false, false) = stateAndHidden.classOf (false, true) ∧
      bothBits.classOf (false, false) ≠ bothBits.classOf (false, true) := by
  constructor
  · apply (stateAndHidden.classOf_eq_iff _ _).mpr
    intro _
    rfl
  · intro same
    have impossible := (bothBits.classOf_eq_iff _ _).mp same true
    exact Bool.false_ne_true impossible

end Controls

#print axioms Family.sufficient_iff_factors
#print axioms Family.classes_card_le
#print axioms Family.exactEquiv
#print axioms Refinement.cardinal_mono
#print axioms Controls.minimal_summary_does_not_recover_every_sufficient_summary

end Mettapedia.GSLT.Dynamics.RegionObservations
