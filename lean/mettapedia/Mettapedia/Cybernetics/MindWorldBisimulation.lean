import Mettapedia.Cybernetics.GSLTMindWorldCorrespondence
import Mettapedia.GSLT.Scope.Simulation

/-!
# Exact mind–world correspondences are functional simulations

The mind–world correspondence principle (Goertzel, Pennachin and Geisweiller,
*Engineering General Intelligence, Part 1*, 2014, §11.3–11.4) compares the
free category of world paths with the free category of mind paths through a
world–mind transfer function on states, and asks the induced path transfer
to be a functor, or a goal-weighted approximate functor.  This module treats
the exact case.

A world is a transition system `step : X → X → Prop`, a mind is a transition
system `step' : Y → Y → Prop`, and the world–mind transfer function is a view
`view : X → Y`; both systems are GSLTs with syntactic equations
(`transitionSystem`).

**Simulation gives zero defect.**  A functional simulation, a view that
preserves transitions, is the term map of an operational translation
(`exists_operationalTranslation_iff`), whose path functor maps every world
path to the mind path through the images of the visited states and
composites to composites: an exact, zero-defect correspondence in the sense of
`MindWorldApproximateFunctor`, with the view as object map
(`preservesEdges_exactCorrespondence`).  Exactness of the correspondence does
not require the back law: a functional simulation suffices, and the mind may
still predict transitions the world cannot make (`Spurious`, in
`Mettapedia.GSLT.Scope.Simulation`).  The functional bisimulations, bounded
morphisms, are the exact correspondences that also reflect every mind
transition out of an image.

**Update squares.**  An update square commutes with a given abstract update
exactly when some operationally realized correspondence has the view as its
object map (`square_iff_operationallyRealized`); a supported update therefore
has a zero-budget correspondence over the view (`Supports.exists_zeroDefect`),
and an unsupported one has none, for any abstract update
(`no_realization_of_not_supports`).  Control: the refresh canary admits no such
correspondence over the current-answer view (`refresh_no_realization`).

The real-valued geometry of `MindWorldApproximateFunctor` makes every
statement here that mentions a correspondence depend on `Classical.choice`
through `Real`; the underlying translations are choice-free
(`square_iff_exists_operationalTranslation`).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.MindWorldBisimulation

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Scope
open Mettapedia.Cybernetics.MindWorldApproximateFunctor
open Mettapedia.Cybernetics.GSLTMindWorldCorrespondence
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

variable {X Y : Type u}

/-! ## Functional simulations are exact correspondences -/

section Simulation

variable {step : X → X → Prop} {step' : Y → Y → Prop} {view : X → Y}

/-- **A functional simulation is a zero-defect mind–world correspondence**:
its path functor is exact, with the view as object map. -/
theorem preservesEdges_exactCorrespondence (preserves : PreservesEdges step step' view) :
    (exactCorrespondence (operationalOfPreserves preserves)).toPathCorrespondence.Exact ∧
      ∀ x : X, (exactCorrespondence (operationalOfPreserves preserves)).obj x = view x :=
  ⟨exactCorrespondence_exact _, fun _ => rfl⟩

end Simulation

/-! ## The exact correspondence over a view -/

section Exact

variable {view : X → Y} {f : X → X} {f' : Y → Y}

/-- **An update square commutes exactly when some operationally realized
mind–world correspondence has the view as its object map.** -/
theorem square_iff_operationallyRealized :
    (∀ x, view (f x) = f' (view x)) ↔
      ∃ correspondence : PathCorrespondence (ExecutionObject (updateSystem f))
          (ExecutionObject (updateSystem f')),
        OperationallyRealized correspondence ∧ ∀ x : X, correspondence.obj x = view x := by
  constructor
  · intro commutes
    exact ⟨(exactCorrespondence
        (operationalOfPreserves (preservesEdges_update_iff.mpr commutes))).toPathCorrespondence,
      ⟨_, rfl⟩, fun _ => rfl⟩
  · rintro ⟨correspondence, ⟨τ, rfl⟩, objects⟩ x
    have objectMap : ∀ x : X, τ.mapTerm x = view x := objects
    have moved : f' (τ.mapTerm x) = τ.mapTerm (f x) := τ.mapStep (rfl : f x = f x)
    rw [← objectMap, ← objectMap, moved]

/-- **A supported update has a zero-defect correspondence over the view**:
exact, with zero identity and composition budgets, and the view as object
map. -/
theorem Supports.exists_zeroDefect (supported : Supports view f) :
    ∃ f' : Y → Y, ∃ correspondence : BoundedPathCorrespondence
        (ExecutionObject (updateSystem f)) (ExecutionObject (updateSystem f')),
      correspondence.toPathCorrespondence.Exact ∧
        (∀ x : X, correspondence.obj x = view x) ∧
        (∀ x, correspondence.identityBudget x = 0) ∧
        ∀ {first middle last : ExecutionObject (updateSystem f)}
          (earlier : first ⟶ middle) (later : middle ⟶ last),
          correspondence.compositionBudget earlier later = 0 := by
  obtain ⟨f', commutes⟩ := (squareCloses_iff view view f).mp supported
  let τ := operationalOfPreserves
    ((preservesEdges_update_iff (view := view) (f := f) (f' := f')).mpr commutes)
  exact ⟨f', exactCorrespondence τ, exactCorrespondence_exact τ, fun _ => rfl,
    fun _ => rfl, fun _ _ => rfl⟩

/-- **An unsupported update has no realized correspondence over the view**, for
any abstract update. -/
theorem no_realization_of_not_supports (unsupported : ¬ Supports view f) (f' : Y → Y) :
    ¬ ∃ correspondence : PathCorrespondence (ExecutionObject (updateSystem f))
        (ExecutionObject (updateSystem f')),
      OperationallyRealized correspondence ∧ ∀ x : X, correspondence.obj x = view x := by
  intro realized
  exact unsupported ((squareCloses_iff view view f).mpr
    ⟨f', square_iff_operationallyRealized.mpr realized⟩)

end Exact

/-! ### Control: the refresh canary -/

section Controls

open Mettapedia.GSLT.Core.PolicyFamily.OperationClosureCanary

/-- **The refresh canary has no realized correspondence over the
current-answer view.** -/
theorem refresh_no_realization (f' : _ → _) :
    ¬ ∃ correspondence : PathCorrespondence (ExecutionObject (updateSystem refresh))
        (ExecutionObject (updateSystem f')),
      OperationallyRealized correspondence ∧
        ∀ x, correspondence.obj x = currentAnswer.toObservationClass x :=
  no_realization_of_not_supports refresh_not_supported f'

end Controls

end Mettapedia.Cybernetics.MindWorldBisimulation
