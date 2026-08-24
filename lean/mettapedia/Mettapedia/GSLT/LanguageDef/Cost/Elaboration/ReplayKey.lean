import Mathlib.Logic.Function.Basic

/-!
# Replay keys for proof-relevant cost elaborations

A replay key may support an observation in two related senses.  Fibre
invariance is the proposition `Function.FactorsThrough observation key`.
Executable use retains a particular function on keys together with the
commuting equation.  The distinction matters when a key is not surjective or
when the observation codomain has no chosen default value.

The same distinction is retained for exact replay and key refinement: the
predicate records existence, while the corresponding structure retains the
decoder or forgetting map used by an implementation.
-/

namespace Mettapedia.GSLT.LanguageDef.Cost.Elaboration

universe uState uKey uValue uFine uCoarse uOther

namespace ReplayKey

/-- An observation is constant on every fibre of a replay key. -/
abbrev Supports {State : Type uState} {Key : Type uKey} {Value : Type uValue}
    (key : State → Key) (observation : State → Value) : Prop :=
  Function.FactorsThrough observation key

/-- A fine key refines a coarse key when every fine-key fibre is contained in
a coarse-key fibre. -/
abbrev Refines {State : Type uState} {Fine : Type uFine}
    {Coarse : Type uCoarse} (fine : State → Fine) (coarse : State → Coarse) :
    Prop :=
  Function.FactorsThrough coarse fine

/-- Strict refinement retains every distinction of the coarse key and at
least one additional distinction. -/
def StrictlyRefines {State : Type uState} {Fine : Type uFine}
    {Coarse : Type uCoarse} (fine : State → Fine) (coarse : State → Coarse) :
    Prop :=
  Refines fine coarse ∧ ¬ Refines coarse fine

theorem Refines.refl {State : Type uState} {Key : Type uKey}
    (key : State → Key) : Refines key key :=
  Function.FactorsThrough.rfl

theorem Refines.trans {State : Type uState} {Fine : Type uFine}
    {Middle : Type uCoarse} {Coarse : Type uOther}
    {fine : State → Fine} {middle : State → Middle}
    {coarse : State → Coarse} (fineMiddle : Refines fine middle)
    (middleCoarse : Refines middle coarse) : Refines fine coarse := by
  intro left right sameFine
  exact middleCoarse (fineMiddle sameFine)

/-- Observation support is monotone in retained information. -/
theorem Refines.supports {State : Type uState} {Fine : Type uFine}
    {Coarse : Type uCoarse} {Value : Type uValue}
    {fine : State → Fine} {coarse : State → Coarse}
    (refines : Refines fine coarse) {observation : State → Value}
    (supported : Supports coarse observation) : Supports fine observation := by
  intro left right sameFine
  exact supported (refines sameFine)

end ReplayKey

/-- A chosen implementation of an observation on replay keys. -/
structure ObservationRealization {State : Type uState} {Key : Type uKey}
    (key : State → Key) {Value : Type uValue}
    (observation : State → Value) where
  run : Key → Value
  agrees : observation = run ∘ key

namespace ObservationRealization

/-- Forget executable realization data to fibre invariance. -/
theorem supports {State : Type uState} {Key : Type uKey}
    {key : State → Key} {Value : Type uValue}
    {observation : State → Value}
    (realization : ObservationRealization key observation) :
    ReplayKey.Supports key observation := by
  intro left right sameKey
  rw [realization.agrees]
  exact congrArg realization.run sameKey

@[simp] theorem run_key {State : Type uState} {Key : Type uKey}
    {key : State → Key} {Value : Type uValue}
    {observation : State → Value}
    (realization : ObservationRealization key observation) (state : State) :
    realization.run (key state) = observation state := by
  exact (congrFun realization.agrees state).symm

/-- A split key turns fibre invariance into a chosen executable realization
without requiring a default value outside the image. -/
def ofSplit {State : Type uState} {Key : Type uKey} {Value : Type uValue}
    (key : State → Key) (select : Key → State)
    (splits : Function.RightInverse select key) (observation : State → Value)
    (supported : ReplayKey.Supports key observation) :
    ObservationRealization key observation where
  run := observation ∘ select
  agrees := by
    funext state
    exact supported (splits (key state)).symm

end ObservationRealization

/-- A replay key has a chosen realization for an observation. -/
def ReplayKey.HasRealization {State : Type uState} {Key : Type uKey}
    (key : State → Key) {Value : Type uValue}
    (observation : State → Value) : Prop :=
  Nonempty (ObservationRealization key observation)

/-- For a split key, fibre invariance is equivalent to existence of an
executable realization. -/
theorem ReplayKey.hasRealization_iff_supports_of_split
    {State : Type uState} {Key : Type uKey} {Value : Type uValue}
    (key : State → Key) (select : Key → State)
    (splits : Function.RightInverse select key) (observation : State → Value) :
    ReplayKey.HasRealization key observation ↔
      ReplayKey.Supports key observation := by
  constructor
  · rintro ⟨realization⟩
    exact realization.supports
  · intro supported
    exact ⟨ObservationRealization.ofSplit key select splits observation supported⟩

/-- An executable decoder paired with exact recovery. -/
structure ReplayRealization {State : Type uState} {Key : Type uKey}
    (key : State → Key) where
  decode : Key → State
  recovers : Function.LeftInverse decode key

/-- A key admits exact replay when a recovering decoder exists. -/
def ReplayKey.IsExact {State : Type uState} {Key : Type uKey}
    (key : State → Key) : Prop :=
  Nonempty (ReplayRealization key)

namespace ReplayRealization

theorem isExact {State : Type uState} {Key : Type uKey}
    {key : State → Key} (replay : ReplayRealization key) :
    ReplayKey.IsExact key :=
  ⟨replay⟩

/-- Exact replay realizes every observation. -/
def observation {State : Type uState} {Key : Type uKey}
    {key : State → Key} (replay : ReplayRealization key)
    {Value : Type uValue} (observe : State → Value) :
    ObservationRealization key observe where
  run := observe ∘ replay.decode
  agrees := by
    funext state
    simp only [Function.comp_apply, replay.recovers state]

end ReplayRealization

theorem ReplayKey.IsExact.supports
    {State : Type uState} {Key : Type uKey} {Value : Type uValue}
    {key : State → Key} (exact : ReplayKey.IsExact key)
    (observation : State → Value) : ReplayKey.Supports key observation := by
  rcases exact with ⟨replay⟩
  exact (replay.observation observation).supports

/-- Exact replay retains every distinction made by any other key. -/
theorem ReplayKey.IsExact.refines
    {State : Type uState} {Fine : Type uFine} {Coarse : Type uCoarse}
    {fine : State → Fine} (exact : ReplayKey.IsExact fine)
    (coarse : State → Coarse) : ReplayKey.Refines fine coarse :=
  exact.supports coarse

/-- Any two exact keys are equivalent in the information preorder. -/
theorem ReplayKey.exactKeys_mutuallyRefine
    {State : Type uState} {LeftKey : Type uFine} {RightKey : Type uCoarse}
    {left : State → LeftKey} {right : State → RightKey}
    (leftExact : ReplayKey.IsExact left) (rightExact : ReplayKey.IsExact right) :
    ReplayKey.Refines left right ∧ ReplayKey.Refines right left :=
  ⟨leftExact.refines right, rightExact.refines left⟩

theorem ReplayKey.isExact_iff_hasIdentityRealization
    {State : Type uState} {Key : Type uKey} (key : State → Key) :
    ReplayKey.IsExact key ↔ ReplayKey.HasRealization key (id : State → State) := by
  constructor
  · rintro ⟨replay⟩
    exact ⟨replay.observation id⟩
  · rintro ⟨realization⟩
    exact ⟨{
      decode := realization.run
      recovers := fun state => (congrFun realization.agrees state).symm
    }⟩

/-- A collision between distinct states prevents exact replay. -/
theorem ReplayKey.collision_prevents_exact
    {State : Type uState} {Key : Type uKey} {key : State → Key}
    {left right : State} (different : left ≠ right)
    (collision : key left = key right) : ¬ ReplayKey.IsExact key := by
  rintro ⟨replay⟩
  apply different
  calc
    left = replay.decode (key left) := (replay.recovers left).symm
    _ = replay.decode (key right) := congrArg replay.decode collision
    _ = right := replay.recovers right

/-- Every decoder for a collided key is wrong on at least one member of the
collided pair. -/
theorem ReplayKey.collision_forces_decode_failure
    {State : Type uState} {Key : Type uKey} {key : State → Key}
    {left right : State} (different : left ≠ right)
    (collision : key left = key right) (decode : Key → State) :
    decode (key left) ≠ left ∨ decode (key right) ≠ right := by
  by_cases recoversLeft : decode (key left) = left
  · right
    intro recoversRight
    apply different
    calc
      left = decode (key left) := recoversLeft.symm
      _ = decode (key right) := congrArg decode collision
      _ = right := recoversRight
  · exact Or.inl recoversLeft

/-- A nonconstant Boolean observation distinguishes a pair of states. -/
theorem ReplayKey.exists_bool_distinguished_pair
    {State : Type uState} (observation : State → Bool)
    (nonconstant : ¬ ∃ value : Bool, ∀ state, observation state = value) :
    ∃ left right, observation left ≠ observation right := by
  classical
  by_contra noPair
  have allEqual : ∀ left right, observation left = observation right := by
    intro left right
    by_contra different
    exact noPair ⟨left, right, different⟩
  by_cases inhabited : Nonempty State
  · rcases inhabited with ⟨seed⟩
    exact nonconstant ⟨observation seed, fun state => allEqual state seed⟩
  · exact nonconstant ⟨false, fun state => False.elim (inhabited ⟨state⟩)⟩

/-- A chosen map recovering a coarse key from a fine key. -/
structure KeyRefinement {State : Type uState} {Fine : Type uFine}
    {Coarse : Type uCoarse} (fine : State → Fine) (coarse : State → Coarse)
    where
  forget : Fine → Coarse
  commutes : coarse = forget ∘ fine

namespace KeyRefinement

theorem refines {State : Type uState} {Fine : Type uFine}
    {Coarse : Type uCoarse} {fine : State → Fine} {coarse : State → Coarse}
    (refinement : KeyRefinement fine coarse) :
    ReplayKey.Refines fine coarse := by
  intro left right sameFine
  rw [refinement.commutes]
  exact congrArg refinement.forget sameFine

def refl {State : Type uState} {Key : Type uKey} (key : State → Key) :
    KeyRefinement key key where
  forget := id
  commutes := rfl

def trans {State : Type uState} {Fine : Type uFine}
    {Middle : Type uCoarse} {Coarse : Type uOther}
    {fine : State → Fine} {middle : State → Middle}
    {coarse : State → Coarse} (fineMiddle : KeyRefinement fine middle)
    (middleCoarse : KeyRefinement middle coarse) :
    KeyRefinement fine coarse where
  forget := middleCoarse.forget ∘ fineMiddle.forget
  commutes := by
    funext state
    calc
      coarse state = middleCoarse.forget (middle state) :=
        congrFun middleCoarse.commutes state
      _ = middleCoarse.forget (fineMiddle.forget (fine state)) :=
        congrArg middleCoarse.forget (congrFun fineMiddle.commutes state)
      _ = ((middleCoarse.forget ∘ fineMiddle.forget) ∘ fine) state := rfl

end KeyRefinement

/-- A fine key admits a chosen forgetting map to a coarse key. -/
def ReplayKey.HasRefinement {State : Type uState} {Fine : Type uFine}
    {Coarse : Type uCoarse} (fine : State → Fine) (coarse : State → Coarse) :
    Prop :=
  Nonempty (KeyRefinement fine coarse)

/-! ## Positive and negative controls -/

namespace ReplayKey.Examples

def retained : Bool → Bool := id

def collapsed : Bool → Unit := fun _ => ()

theorem retained_isExact : ReplayKey.IsExact retained :=
  ⟨{ decode := id, recovers := fun _ => rfl }⟩

theorem collapsed_not_exact : ¬ ReplayKey.IsExact collapsed := by
  exact ReplayKey.collision_prevents_exact
    (key := collapsed) (left := false) (right := true) (by decide) rfl

theorem retained_strictlyRefines_collapsed :
    ReplayKey.StrictlyRefines retained collapsed := by
  constructor
  · intro _ _ _
    rfl
  · intro refines
    exact Bool.false_ne_true (refines rfl)

end ReplayKey.Examples

#print axioms ReplayKey.hasRealization_iff_supports_of_split
#print axioms ReplayKey.isExact_iff_hasIdentityRealization
#print axioms ReplayKey.Examples.collapsed_not_exact
#print axioms ReplayKey.Examples.retained_strictlyRefines_collapsed

end Mettapedia.GSLT.LanguageDef.Cost.Elaboration
