import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Defs

/-!
# Event-indexed behavioural comparison

Choice fibres retain distinct events with the same label and successor. They
may be empty or infinite. A bisimulation supplies a bijection of the fibres,
preserves labels and relates successors. No enumeration is required.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventMultiplicity

universe uS uT uU uV uA uC uD uE uF

structure System (State : Type uS) (Action : Type uA) where
  Choice : State → Type uC
  next : (state : State) → Choice state → State
  action : (state : State) → Choice state → Action

variable {S : Type uS} {T : Type uT} {U : Type uU} {V : Type uV} {A : Type uA}

structure Bisimulation (left : System.{uS,uA,uC} S A) (right : System.{uT,uA,uD} T A)
    (related : S → T → Prop) where
  choices : ∀ {s t}, related s t → left.Choice s ≃ right.Choice t
  actions : ∀ {s t} (same : related s t) (choice : left.Choice s),
    left.action s choice = right.action t (choices same choice)
  successors : ∀ {s t} (same : related s t) (choice : left.Choice s),
    related (left.next s choice) (right.next t (choices same choice))

def Bisimilar (left : System.{uS,uA,uC} S A) (s : S)
    (right : System.{uT,uA,uD} T A) (t : T) : Prop :=
  ∃ related : S → T → Prop, Nonempty (Bisimulation left right related) ∧ related s t

namespace Bisimulation

variable {left : System.{uS,uA,uC} S A} {middle : System.{uT,uA,uD} T A}
  {right : System.{uU,uA,uE} U A} {R : S → T → Prop} {Q : T → U → Prop}

def refl (sys : System.{uS,uA,uC} S A) : Bisimulation sys sys Eq where
  choices same := same ▸ Equiv.refl _
  actions same choice := by cases same; rfl
  successors same choice := by cases same; rfl

def symm (b : Bisimulation left middle R) :
    Bisimulation middle left (fun t s => R s t) where
  choices same := (b.choices same).symm
  actions same choice := by
    have equation := b.actions same ((b.choices same).symm choice)
    simpa only [Equiv.apply_symm_apply] using equation.symm
  successors same choice := by
    have next := b.successors same ((b.choices same).symm choice)
    simpa only [Equiv.apply_symm_apply] using next

noncomputable def trans (b : Bisimulation left middle R) (c : Bisimulation middle right Q) :
    Bisimulation left right (fun s u => ∃ t, R s t ∧ Q t u) where
  choices same := (b.choices (Classical.choose_spec same).1).trans
    (c.choices (Classical.choose_spec same).2)
  actions same choice := (b.actions (Classical.choose_spec same).1 choice).trans
    (c.actions (Classical.choose_spec same).2 _)
  successors same choice := ⟨_, b.successors (Classical.choose_spec same).1 choice,
    c.successors (Classical.choose_spec same).2 _⟩

end Bisimulation

namespace Bisimilar

variable {left : System.{uS,uA,uC} S A} {middle : System.{uT,uA,uD} T A}
  {right : System.{uU,uA,uE} U A} {s : S} {t : T} {u : U}

theorem refl (sys : System.{uS,uA,uC} S A) (state : S) : Bisimilar sys state sys state :=
  ⟨Eq, ⟨Bisimulation.refl sys⟩, rfl⟩

theorem symm (same : Bisimilar left s middle t) : Bisimilar middle t left s := by
  obtain ⟨related, ⟨b⟩, holds⟩ := same
  exact ⟨fun t s => related s t, ⟨b.symm⟩, holds⟩

theorem trans (first : Bisimilar left s middle t) (second : Bisimilar middle t right u) :
    Bisimilar left s right u := by
  obtain ⟨R, ⟨b⟩, one⟩ := first
  obtain ⟨Q, ⟨c⟩, two⟩ := second
  exact ⟨fun s u => ∃ t, R s t ∧ Q t u, ⟨b.trans c⟩, ⟨t, one, two⟩⟩

end Bisimilar

namespace System

variable (sys : System.{uS,uA,uC} S A)

def Execution : Nat → S → Type (max uS uC)
  | 0, _ => PUnit
  | count + 1, state => (choice : sys.Choice state) × Execution count (sys.next state choice)

def word : {count : Nat} → {state : S} → sys.Execution count state → List A
  | 0, _, _ => []
  | _ + 1, state, ⟨choice, rest⟩ => sys.action state choice :: word rest

def last : {count : Nat} → {state : S} → sys.Execution count state → S
  | 0, state, _ => state
  | _ + 1, _, ⟨_, rest⟩ => last rest

theorem word_length : ∀ {count : Nat} {state : S} (run : sys.Execution count state),
    (sys.word run).length = count
  | 0, _, _ => rfl
  | count + 1, _, ⟨_, rest⟩ => by simp [word, word_length rest]

end System

namespace Bisimulation

variable {left : System.{uS,uA,uC} S A} {right : System.{uT,uA,uD} T A}
  {related : S → T → Prop} (b : Bisimulation left right related)

def executions : (count : Nat) → {s : S} → {t : T} → related s t →
    left.Execution count s ≃ right.Execution count t
  | 0, _, _, _ => Equiv.punitEquivPUnit
  | count + 1, _, _, same => Equiv.sigmaCongr (b.choices same)
      (fun choice => executions count (b.successors same choice))

theorem execution_word : ∀ {count : Nat} {s : S} {t : T} (same : related s t)
    (run : left.Execution count s), right.word (b.executions count same run) = left.word run
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, same, ⟨choice, rest⟩ => by
      change right.action _ (b.choices same choice) ::
        right.word (b.executions _ (b.successors same choice) rest) = _
      rw [execution_word, ← b.actions]
      rfl

theorem execution_last : ∀ {count : Nat} {s : S} {t : T} (same : related s t)
    (run : left.Execution count s), related (left.last run) (right.last (b.executions count same run))
  | 0, _, _, same, _ => same
  | _ + 1, _, _, same, ⟨choice, rest⟩ => execution_last (b.successors same choice) rest

end Bisimulation

/-- Independent asynchronous composition: origins remain distinct sum injections. -/
def asynchronous (left : System.{uS,uA,uC} S A) (right : System.{uT,uA,uD} T A) :
    System (S × T) A where
  Choice state := left.Choice state.1 ⊕ right.Choice state.2
  next state
    | .inl choice => (left.next state.1 choice, state.2)
    | .inr choice => (state.1, right.next state.2 choice)
  action state
    | .inl choice => left.action state.1 choice
    | .inr choice => right.action state.2 choice

def Bisimulation.asynchronous {left : System.{uS,uA,uC} S A} {left' : System.{uT,uA,uD} T A}
    {right : System.{uU,uA,uE} U A} {right' : System.{uV,uA,uF} V A}
    {R : S → T → Prop} {Q : U → V → Prop}
    (b : Bisimulation left left' R) (c : Bisimulation right right' Q) :
    Bisimulation (asynchronous left right) (asynchronous left' right')
      (fun state state' => R state.1 state'.1 ∧ Q state.2 state'.2) where
  choices same := Equiv.sumCongr (b.choices same.1) (c.choices same.2)
  actions same choice := by
    cases choice with
    | inl choice => exact b.actions same.1 choice
    | inr choice => exact c.actions same.2 choice
  successors same choice := by
    cases choice with
    | inl choice => exact ⟨b.successors same.1 choice, same.2⟩
    | inr choice => exact ⟨same.1, c.successors same.2 choice⟩

theorem Bisimilar.asynchronous {left : System.{uS,uA,uC} S A} {left' : System.{uT,uA,uD} T A}
    {right : System.{uU,uA,uE} U A} {right' : System.{uV,uA,uF} V A}
    {s : S} {t : T} {u : U} {v : V}
    (one : Bisimilar left s left' t) (two : Bisimilar right u right' v) :
    Bisimilar (asynchronous left right) (s, u) (asynchronous left' right') (t, v) := by
  obtain ⟨R, ⟨b⟩, first⟩ := one
  obtain ⟨Q, ⟨c⟩, second⟩ := two
  exact ⟨_, ⟨b.asynchronous c⟩, first, second⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventMultiplicity
