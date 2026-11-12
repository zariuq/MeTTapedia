import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.HonestWrites

/-!
# HE's writing machine on keyed rows is bisimilar to HE's writing machine on its spaces

`HonestWrites` runs HE's world machine on keyed rows (`KeyedWorld`: atoms with stable identities),
so that an add writes one fresh row and a removal takes one row. Here that keyed machine is
compared with HE's world machine on HE's own spaces, whose `add-atom` and `remove-atom` are
`HE.Space.add` (the new atom in front) and `HE.Space.remove` (the first occurrence):

* `spaceServices`: HE's writing services on spaces;
* `keyed_to_space`, `space_to_keyed`: every move of the keyed machine is a move of the space
  machine on the presented space, and every move of the space machine is matched by a move of the
  keyed machine on any keyed world presenting that space (an add takes a fresh identity);
* `keyed_bisimulation`: **a strong bisimulation of the two machines** (`heWorldMachine`), relating a
  keyed configuration and a space configuration when the keyed world presents the space and the
  control, stack and publications are equal.

The related configurations are equal outside the world. In particular the positions HE's equation
works record are the same in both: positions in the presented space. Identities are invisible to
HE's machine; what they buy is the honest write footprint of `HonestWrites`.

What this does not give is the placement of the writing machine on the step with one occurrence
per row and a query reading only its region: there a query cannot compute the positions of its
rows from its region, so that encoding can match HE's configurations only up to recorded
positions, or with works recording identities.

## Controls

* `Controls.identities_invisible`: two keyed worlds with different identities present the same
  space, so the bisimulation is not a bijection of worlds.
* `Controls.back_add_not_he` (negative): a keyed add placing the new row at the back would present a
  different space than HE's add, which puts it in front; the keyed services' choice of the front is
  what makes the bisimulation hold.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace KeyedBisimulation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldLocalStepWith)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup WorldServices)
open HEOnTheStep (heWorldMachine Config FramedMachine)
open HonestWrites (KeyedWorld keyedView keyedServices removeFirst map_removeFirst keyed_refines)

/-- **HE's writing services on its own spaces**: `add-atom` is `HE.Space.add`, which puts the new
atom in front, and `remove-atom` is `HE.Space.remove`, which takes the first occurrence; both answer
`()`. -/
def spaceServices : WorldServices Unit Space where
  contextPayload _ := .custom "Space" "self"
  nativeCall _ world name _ argument frame results after :=
    results = [(WorldRemoval.unitValue, frame)] ∧
      ((name = .symbol "add-atom" ∧ after = world.add argument) ∨
        (name = .symbol "remove-atom" ∧ after = world.remove argument))

/-- The world is the space itself. -/
def spaceView : Space → Unit → Space := fun world _ => world

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

theorem le_sum_of_mem : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.sum
  | _ :: _, _, .head _ => by
      simp only [List.sum_cons]
      omega
  | _ :: _, _, .tail _ member => by
      have below := le_sum_of_mem member
      simp only [List.sum_cons]
      omega

/-- An identity no row of the world holds. -/
def freshId (world : KeyedWorld) : ℕ := (world.map Prod.snd).sum + 1

theorem freshId_fresh (world : KeyedWorld) : freshId world ∉ world.map Prod.snd := by
  intro member
  have below := le_sum_of_mem member
  unfold freshId at below
  omega

/-- **Every move of the keyed machine is a move of the space machine on the presented space.** -/
theorem keyed_to_space {world afterWorld : KeyedWorld} {label : Unit}
    {before after : Control Unit × List Continuation}
    (step : WorldLocalStepWith .historical keyedView keyedServices dispatch lookup policy
      world label before afterWorld after) :
    WorldLocalStepWith .historical spaceView spaceServices dispatch lookup policy
      (keyedView world ()) label before (keyedView afterWorld ()) after := by
  induction step with
  | core unscoped managed moved unscopedAfter => exact .core unscoped managed moved unscopedAfter
  | context _ ih => exact .context ih
  | contextReturn => exact .contextReturn
  | evalc => exact .evalc
  | metta => exact .metta
  | contextSpace => exact .contextSpace
  | native call =>
      obtain ⟨answered, (⟨named, same⟩ | ⟨named, same⟩)⟩ := keyed_refines call
      · exact .native ⟨answered, Or.inl ⟨named, same⟩⟩
      · exact .native ⟨answered, Or.inr ⟨named, same⟩⟩
  | callGroundedDone _ _ _ grounded => cases grounded
  | callGroundedResume _ _ _ grounded => cases grounded
  | invocationGroundedDone _ _ grounded => cases grounded
  | invocationGroundedResume _ _ grounded => cases grounded
  | collapseEnter provided => cases provided
  | collectEnter provided => cases provided
  | captureNil provided => cases provided
  | captureEmpty provided => cases provided
  | captureOne provided => cases provided
  | superposeEnter provided => cases provided
  | restoreNil provided => cases provided
  | restoreOne provided => cases provided
  | restoreRejected provided => cases provided

/-- **Every move of the space machine is matched on keyed rows**, from any keyed world presenting
the space: an add takes a fresh identity, a removal takes the first row holding the atom. -/
theorem space_to_keyed {space afterSpace : Space} {label : Unit}
    {before after : Control Unit × List Continuation}
    (step : WorldLocalStepWith .historical spaceView spaceServices dispatch lookup policy
      space label before afterSpace after) :
    ∀ world : KeyedWorld, keyedView world () = space →
      ∃ afterWorld : KeyedWorld, keyedView afterWorld () = afterSpace ∧
        WorldLocalStepWith .historical keyedView keyedServices dispatch lookup policy
          world label before afterWorld after := by
  induction step with
  | core unscoped managed moved unscopedAfter =>
      intro world presents
      subst presents
      exact ⟨world, rfl, .core unscoped managed moved unscopedAfter⟩
  | context _ ih =>
      intro world presents
      obtain ⟨afterWorld, presentsAfter, keyed⟩ := ih world presents
      exact ⟨afterWorld, presentsAfter, .context keyed⟩
  | contextReturn =>
      intro world presents
      exact ⟨world, presents, .contextReturn⟩
  | evalc =>
      intro world presents
      exact ⟨world, presents, .evalc⟩
  | metta =>
      intro world presents
      exact ⟨world, presents, .metta⟩
  | contextSpace =>
      intro world presents
      exact ⟨world, presents, .contextSpace⟩
  | native call =>
      intro world presents
      obtain ⟨answered, (⟨named, rfl⟩ | ⟨named, rfl⟩)⟩ := call
      · refine ⟨(_, freshId world) :: world, ?_,
          .native ⟨answered, Or.inl ⟨named, freshId world, freshId_fresh world, rfl⟩⟩⟩
        rw [← presents]
        rfl
      · refine ⟨removeFirst world _, ?_, .native ⟨answered, Or.inr ⟨named, rfl⟩⟩⟩
        rw [← presents]
        exact congrArg Space.mk (map_removeFirst world _)
  | callGroundedDone _ _ _ grounded => cases grounded
  | callGroundedResume _ _ _ grounded => cases grounded
  | invocationGroundedDone _ _ grounded => cases grounded
  | invocationGroundedResume _ _ grounded => cases grounded
  | collapseEnter provided => cases provided
  | collectEnter provided => cases provided
  | captureNil provided => cases provided
  | captureEmpty provided => cases provided
  | captureOne provided => cases provided
  | superposeEnter provided => cases provided
  | restoreNil provided => cases provided
  | restoreOne provided => cases provided
  | restoreRejected provided => cases provided

/-- A keyed configuration **presents** a space configuration: the keyed world presents the space,
and the control, the stack and the publications are equal. -/
def Presents (x : Config KeyedWorld (Control Unit) Continuation Result)
    (y : Config Space (Control Unit) Continuation Result) : Prop :=
  keyedView x.world () = y.world ∧ x.control = y.control ∧ x.stack = y.stack ∧
    x.emitted = y.emitted

/-- **HE's writing machine on keyed rows is strongly bisimilar to HE's writing machine on its
spaces.** `Presents` is a strong bisimulation between `heWorldMachine` over keyed worlds with the
keyed services and `heWorldMachine` over HE's spaces with HE's own add and remove. -/
theorem keyed_bisimulation :
    (∀ x x' y, Presents x y →
      (heWorldMachine keyedView keyedServices dispatch lookup policy ()).Step x x' →
        ∃ y', (heWorldMachine spaceView spaceServices dispatch lookup policy ()).Step y y' ∧
          Presents x' y') ∧
    (∀ x y y', Presents x y →
      (heWorldMachine spaceView spaceServices dispatch lookup policy ()).Step y y' →
        ∃ x', (heWorldMachine keyedView keyedServices dispatch lookup policy ()).Step x x' ∧
          Presents x' y') := by
  constructor
  · rintro x x' ⟨v, d, t, f⟩ ⟨presents, rfl, rfl, rfl⟩ step
    simp only at presents
    subst presents
    cases step with
    | internal transition =>
        exact ⟨_, .internal (keyed_to_space transition), rfl, rfl, rfl, rfl⟩
    | publish published =>
        exact ⟨_, .publish published, rfl, rfl, rfl, rfl⟩
  · rintro ⟨w, c, s, e⟩ y y' ⟨presents, rfl, rfl, rfl⟩ step
    rcases y with ⟨v, d, t, f⟩
    simp only at presents
    subst presents
    cases step with
    | internal transition =>
        obtain ⟨afterWorld, presentsAfter, keyed⟩ := space_to_keyed transition w rfl
        exact ⟨_, .internal keyed, presentsAfter, rfl, rfl, rfl⟩
    | publish published =>
        exact ⟨_, .publish published, rfl, rfl, rfl, rfl⟩

/-! ## Controls -/

namespace Controls

/-- `(q b)`. -/
def qb : Atom := .expression [.symbol "q", .symbol "b"]

/-- **Identities are invisible to HE's machine**: two keyed worlds holding `(p a)` under different
identities present the same space, so both are related to the same space configurations. -/
theorem identities_invisible :
    keyedView [(WorldRemoval.pa, 0)] () = keyedView [(WorldRemoval.pa, 5)] () ∧
      ([(WorldRemoval.pa, 0)] : KeyedWorld) ≠ [(WorldRemoval.pa, 5)] :=
  ⟨rfl, by decide⟩

/-- **Negative control: the front matters.** Adding `(q b)` as a new row at the back of the keyed
world holding `(p a)` presents a different space than HE's add, which puts `(q b)` in front. -/
theorem back_add_not_he :
    keyedView ([(WorldRemoval.pa, 0)] ++ [(qb, 1)]) () ≠
      (keyedView [(WorldRemoval.pa, 0)] ()).add qb := by
  simp [keyedView, Space.add, WorldRemoval.pa, qb]

end Controls

#print axioms freshId_fresh
#print axioms keyed_to_space
#print axioms space_to_keyed
#print axioms keyed_bisimulation
#print axioms Controls.identities_invisible
#print axioms Controls.back_add_not_he

end KeyedBisimulation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
