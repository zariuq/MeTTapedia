import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeStepBisim

/-!
# Controls for agreement up to dead names

Over the one-name state `NativeResidualExample.initial` (one shared name `X`, no occurrences, no
knowledge) and the closed maker, which makes occurrence `0` publishing `false` and mentions no name.

* **Positive** (`initial_extended`, `extended_not_renaming`, `closed_maker_moves`,
  `initial_bisimilar_extended`): `initial` and the same state with one extra dead name are a
  dead-name extension; their frames have different sizes, so no renaming of names relates them; the
  closed maker is admitted at `initial`; and the two states are bisimilar for every closed program.
* **Negative: a mentioned name** (`contradicted_no_firing`, `contradicted_not_deadEquiv`,
  `contradicted_not_bisimilar`): `initial` with knowledge `X = true` and `X = false` has the same
  frame and rows, and its knowledge mentions its one name. No live firing is admitted there, while the
  closed maker is admitted at `initial`; the two neither agree up to dead names nor are bisimilar.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidualExample

namespace NativeDead

namespace Controls

/-- Two parameterless shared names. -/
def twoNames : Unit ⊕ Unit → MetaArity tiny := fun _ => ([], ())

/-- **`initial` with one extra dead name.** -/
def extended : NativeState tiny ℕ ([] : Ctx tiny) () :=
  ⟨Empty, inferInstance, noLocals,
    { Names := Unit ⊕ Unit
      equality := inferInstance
      declarations := twoNames
      occupied := ∅
      equations := []
      present := ∅
      rows := fun _ => ContextualConditionalRows.ofStored noLocals twoNames (.shared (bit twoNames true)) }⟩

/-- **The extra name is dead**: `extended` is a dead-name extension of `initial`. -/
def initial_extended : DeadExtension initial extended where
  locals := id
  locals_injective := Function.injective_id
  locals_preserves _ := rfl
  names := Sum.inl
  names_injective := Sum.inl_injective
  names_preserves _ := rfl
  rows _ := rfl
  equations := List.Perm.nil
  present := rfl
  occupied := rfl

/-- **No renaming of names relates the two frames**: they have different sizes. -/
theorem extended_not_renaming : ¬ Nonempty (initial.state.Names ≃ extended.state.Names) := by
  show ¬ Nonempty (Unit ≃ Unit ⊕ Unit)
  rintro ⟨bijection⟩
  have sizes := Fintype.card_congr bijection
  simp at sizes

/-- The native step over the one-name signature. -/
noncomputable abbrev tinyNative :=
  (native (S := tiny) (O := ℕ) (Γ := ([] : Ctx tiny)) (sort := ())).toStep

/-- The closed maker: makes occurrence `0`, publishing `false`. -/
def closedMaker : ClosedFiring tiny ℕ ([] : Ctx tiny) () where
  rule := ⟨[], [], [], [], [bit noNames false]⟩
  selection := ⟨[], [], [0]⟩
  outputs _ := bit noNames false
  patterns := []
  fuel := 0

/-- The program offering the closed maker. -/
def makerProgram : Unit → ClosedFiring tiny ℕ ([] : Ctx tiny) () → Prop := fun _ k => k = closedMaker

theorem closedMaker_at_initial : closedMaker.atState initial = maker 0 none := rfl

/-- **The closed maker moves `initial`.** -/
theorem closed_maker_moves :
    ∃ t, Race.Generic.Moves tinyNative (liveOffers (closedOffers makerProgram)) initial () t :=
  ⟨_, (maker 0 none).toNative, maker_realized 0 none, ⟨closedMaker.atState initial, ⟨closedMaker, rfl, rfl⟩,
    congrArg LiveFiring.toNative closedMaker_at_initial⟩, rfl⟩

/-- **`initial` and its dead-name extension are bisimilar** for every closed program. -/
theorem initial_bisimilar_extended {L : Type} (program : L → ClosedFiring tiny ℕ ([] : Ctx tiny) () → Prop) :
    Race.Generic.Bisimilar tinyNative (liveOffers (closedOffers program)) initial extended :=
  bisimilar_of_deadEquiv (closedOffers_invariant program) (DeadEquiv.of_extension initial_extended)

/-! ## Negative: knowledge that mentions the name -/

/-- The shared name, observed. -/
def nameX : Term (signature tiny oneName) ([] : Ctx tiny) () := generator oneName ()

/-- **`initial` with knowledge `X = true` and `X = false`.** -/
def contradicted : NativeState tiny ℕ ([] : Ctx tiny) () :=
  ⟨Empty, inferInstance, noLocals,
    { Names := Unit
      equality := inferInstance
      declarations := oneName
      occupied := ∅
      equations := [(observe nameX, observe (bit oneName true)), (observe nameX, observe (bit oneName false))]
      present := ∅
      rows := fun _ => ContextualConditionalRows.ofStored noLocals oneName (.shared (bit oneName true)) }⟩

/-- **No live firing is admitted at `contradicted`**: every solution of its information solves the
knowledge, which tells `X` both constants. -/
theorem contradicted_no_firing (f : LiveFiring contradicted) : ¬ f.toNative.Realized := by
  intro realized
  obtain ⟨_, _, ⟨b, σ, solved⟩, _⟩ := (native_admits_iff (S := tiny) f.toNative).mp realized
  have knowledge := ((NativeResidual.models_problemOf_iff f.selection f.rule σ).mp solved).1
  have first := knowledge _ List.mem_cons_self
  have second := knowledge _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have clash := (observe_injective first).symm.trans (observe_injective second)
  cases clash

/-- **`initial` and `contradicted` do not agree up to dead names**: the closed maker is admitted at the
first and not at the second. -/
theorem contradicted_not_deadEquiv : ¬ DeadEquiv initial contradicted := by
  rintro ⟨u, ⟨e⟩, ⟨e'⟩⟩
  have same : e.firing (closedMaker.atState initial) = e'.firing (closedMaker.atState contradicted) :=
    (ClosedFiring.firing_at e.toInclusion closedMaker).trans (ClosedFiring.firing_at e'.toInclusion closedMaker).symm
  have admitted : (closedMaker.atState initial).toNative.Realized := by
    rw [closedMaker_at_initial]
    exact maker_realized 0 none
  exact contradicted_no_firing _ ((DeadEquiv.step e e' same).1.mp admitted)

/-- **`initial` and `contradicted` are not bisimilar** under the maker program. -/
theorem contradicted_not_bisimilar :
    ¬ Race.Generic.Bisimilar tinyNative (liveOffers (closedOffers makerProgram)) initial contradicted := by
  rintro ⟨relation, ⟨forward, _, _⟩, related⟩
  obtain ⟨t, moved⟩ := closed_maker_moves
  obtain ⟨_, ⟨g, admitted, ⟨f, _, rfl⟩, _⟩, _⟩ := forward related () moved
  exact contradicted_no_firing f admitted

end Controls

end NativeDead

#print axioms NativeDead.Controls.initial_extended
#print axioms NativeDead.Controls.extended_not_renaming
#print axioms NativeDead.Controls.closed_maker_moves
#print axioms NativeDead.Controls.initial_bisimilar_extended
#print axioms NativeDead.Controls.contradicted_no_firing
#print axioms NativeDead.Controls.contradicted_not_deadEquiv
#print axioms NativeDead.Controls.contradicted_not_bisimilar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
