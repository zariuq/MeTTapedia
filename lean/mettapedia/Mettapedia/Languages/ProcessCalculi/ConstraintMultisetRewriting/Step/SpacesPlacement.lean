import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TransformQualification
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpacesReach
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

/-!
# Placing the existing space modules in the step

## The located network of the MeTTa calculus (`MeTTaCalculus.SpaceInteraction`)

`SpaceInteraction` states space contact over a **network**: a family of multisets of atoms indexed
by locations, with an `observe` step (a persistent read) and a `consume` step (a linear take). A
store whose occurrences carry handles has a network: each space's payloads, with multiplicity
(`network`). The translation is adequate:

* **Forward** (`observe_of_admitted`, `consume_of_admitted`): in every instance of the interface, an
  admitted firing that reads exactly one occurrence is an `observe` step of the networks, and one
  that takes exactly one occurrence is a `consume` step, from the network before to the network
  after.
* **Backward** (`observe_iff_present`, `consume_iff_taken`): every `observe` step from a store's
  network is the read of an occurrence of the store with that handle and payload, and every
  `consume` step is the removal of such an occurrence, the target being the network of the store
  without it.
* Multiplicity is kept: equal payloads at one space are distinct occurrences and count twice in the
  network (`network_erase`).

## Selection relative to reach (`NamedSpacesReach`)

The space vocabulary of `NamedSpaces*` (space names as terms, reach as the actor's permission) is a
restriction of the first-order instance: a reach step is exactly an admitted firing of
`AnnotatedRuns.firstOrder` without predicate queries whose selection the actor's reach admits
(`reachStep_iff_admitted`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpacesPlacement

open Interface (Frames)
open AnnotatedRuns (firstOrder)
open MeTTaCalculus.OccurrenceCommits (Commit Enabled fire mem_fire)
open MeTTaCalculus.SpaceInteraction (LocatedStep AccessMode Network)
open Spaces (fiber mem_fiber)

/-! ## The located network -/

section Network

universe uO uT uH uOcc uS uF uN uA

variable {O : Type uOcc} [DecidableEq O] {H : Type uN} [DecidableEq H] {Atom : Type uA}
  (space : O → H) (payload : O → Atom)

/-- **The network of a store with handles**: each space's payloads, with multiplicity. -/
def network (store : Finset O) : Network H Atom := fun h => (fiber space h store).val.map payload

omit [DecidableEq O] in
theorem mem_network {store : Finset O} {h : H} {a : Atom} :
    a ∈ network space payload store h ↔ ∃ o ∈ store, space o = h ∧ payload o = a := by
  simp only [network, Multiset.mem_map, Finset.mem_val, mem_fiber]
  constructor
  · rintro ⟨o, ⟨present, atH⟩, rfl⟩
    exact ⟨o, present, atH, rfl⟩
  · rintro ⟨o, present, atH, rfl⟩
    exact ⟨o, ⟨present, atH⟩, rfl⟩

theorem fiber_erase (store : Finset O) (o : O) (h : H) :
    fiber space h (store.erase o) = (fiber space h store).erase o := by
  ext x
  simp only [mem_fiber, Finset.mem_erase]
  tauto

/-- **Removing an occurrence removes one copy of its payload at its space**, and nothing elsewhere. -/
theorem network_erase {store : Finset O} {o : O} (present : o ∈ store) :
    network space payload store (space o) = payload o ::ₘ network space payload (store.erase o) (space o) ∧
      ∀ h, h ≠ space o → network space payload (store.erase o) h = network space payload store h := by
  constructor
  · have inFiber : o ∈ fiber space (space o) store := (mem_fiber space).mpr ⟨present, rfl⟩
    have whole : fiber space (space o) store = insert o ((fiber space (space o) store).erase o) :=
      (Finset.insert_erase inFiber).symm
    simp only [network, fiber_erase]
    conv_lhs => rw [whole]
    rw [Finset.insert_val_of_notMem (Finset.notMem_erase o _), Multiset.map_cons]
  · intro h other
    simp only [network, fiber_erase]
    congr 2
    apply Finset.erase_eq_of_notMem
    intro member
    exact other ((mem_fiber space).mp member).2.symm

/-- The network after removing an occurrence is the update of its space. -/
theorem network_erase_update {store : Finset O} {o : O} (present : o ∈ store) :
    network space payload (store.erase o) =
      Function.update (network space payload store) (space o)
        (network space payload (store.erase o) (space o)) := by
  funext h
  by_cases same : h = space o
  · subst same
    rw [Function.update_self]
  · rw [Function.update_of_ne same, (network_erase space payload present).2 h same]

omit [DecidableEq O] in
/-- **A present occurrence is observed at its space.** -/
theorem observe_of_present {store : Finset O} {o : O} (present : o ∈ store) :
    LocatedStep .observe (space o) (payload o) (network space payload store) (network space payload store) :=
  .observe ((mem_network space payload).mpr ⟨o, present, rfl, rfl⟩)

/-- **Removing a present occurrence consumes its payload at its space.** -/
theorem consume_of_present {store : Finset O} {o : O} (present : o ∈ store) :
    LocatedStep .consume (space o) (payload o) (network space payload store)
      (network space payload (store.erase o)) := by
  rw [network_erase_update space payload present]
  exact .consume _ (network_erase space payload present).1

omit [DecidableEq O] in
/-- **Every `observe` step of a store's network is the read of one of its occurrences.** -/
theorem observe_iff_present {store : Finset O} {h : H} {a : Atom} {target : Network H Atom} :
    LocatedStep .observe h a (network space payload store) target ↔
      target = network space payload store ∧ ∃ o ∈ store, space o = h ∧ payload o = a := by
  rw [MeTTaCalculus.SpaceInteraction.LocatedStep.observe_iff, mem_network]
  exact And.comm

/-- **Every `consume` step of a store's network is the removal of one of its occurrences.** -/
theorem consume_iff_taken {store : Finset O} {h : H} {a : Atom} {target : Network H Atom} :
    LocatedStep .consume h a (network space payload store) target ↔
      ∃ o ∈ store, space o = h ∧ payload o = a ∧ target = network space payload (store.erase o) := by
  constructor
  · intro step
    obtain ⟨rest, atH, rfl⟩ := MeTTaCalculus.SpaceInteraction.LocatedStep.consume_iff.mp step
    have member : a ∈ network space payload store h := by
      rw [atH]
      exact Multiset.mem_cons_self a rest
    obtain ⟨o, present, rfl, rfl⟩ := (mem_network space payload).mp member
    refine ⟨o, present, rfl, rfl, ?_⟩
    have split := (network_erase space payload present).1
    rw [atH] at split
    have same : rest = network space payload (store.erase o) (space o) :=
      (Multiset.cons_inj_right _).mp split
    rw [network_erase_update space payload present, same]
  · rintro ⟨o, present, rfl, rfl, rfl⟩
    exact consume_of_present space payload present

/-! ### Firings of every instance are network steps -/

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing)

/-- **A firing that reads exactly one occurrence is an `observe` step of the networks.** -/
theorem observe_of_admitted {s : State} {f : Firing s} (admitted : P.Admits f) {o : O}
    (only : P.selection f = ⟨[], [o], []⟩) :
    LocatedStep .observe (space o) (payload o) (network space payload (P.present s))
      (network space payload (P.present (P.result f admitted))) := by
  have enabled := (P.prepares admitted).2.1
  have present : o ∈ P.present s := enabled.kept_subset (by simp [only, Selection.commit])
  have same : P.present (P.result f admitted) = P.present s := by
    rw [P.present_result f admitted, only]
    simp [fire, Selection.commit]
  rw [same]
  exact observe_of_present space payload present

/-- **A firing that takes exactly one occurrence is a `consume` step of the networks.** -/
theorem consume_of_admitted {s : State} {f : Firing s} (admitted : P.Admits f) {o : O}
    (only : P.selection f = ⟨[o], [], []⟩) :
    LocatedStep .consume (space o) (payload o) (network space payload (P.present s))
      (network space payload (P.present (P.result f admitted))) := by
  have enabled := (P.prepares admitted).2.1
  have present : o ∈ P.present s := enabled.taken_subset (by simp [only, Selection.commit])
  have erased : P.present (P.result f admitted) = (P.present s).erase o := by
    rw [P.present_result f admitted, only]
    simp [fire, Selection.commit, Finset.sdiff_singleton_eq_erase]
  rw [erased]
  exact consume_of_present space payload present

end Network

/-! ## Selection relative to reach -/

section Reach

universe uT uS uN uO

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} [DecidableEq N] [DecidableEq O]
  {A : SubstitutionAction T S} {sts : NamedSpaces.SpaceTerms A N} (ns : NamedSpaces.NameSwap sts)

/-- **A reach step is an admitted firing of the first-order instance that the actor's reach
admits.** -/
theorem reachStep_iff_admitted (K : Set T) (space payload : O → T) (r : NamedSpaces.LocatedRule T)
    (C D : Configuration T O) :
    NamedSpaces.ReachStep ns K space payload r C D ↔
      ∃ (selection : Selection O)
        (admitted : (firstOrder (S := S) A (NamedSpaces.located sts space payload)).Admits (s := C)
          (⟨r.toRule sts, [], selection⟩ : AnnotatedRuns.Firing T S O)),
        NamedSpaces.HoldsRule (sts := sts) r K ∧
          (∀ o ∈ selection.taken ++ selection.read, NamedSpaces.AtReached ns K space payload C o) ∧
          (∀ s ∈ r.spaces, NamedSpaces.Resolves sts
            (selection.problem (NamedSpaces.located sts space payload) (r.toRule sts) C) s) ∧
          (firstOrder A (NamedSpaces.located sts space payload)).result _ admitted = D := by
  constructor
  · rintro ⟨selection, admits, rfl⟩
    exact ⟨selection, (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr admits.valid,
      admits.holds, admits.selected, admits.resolved, rfl⟩
  · rintro ⟨selection, admitted, holds, selected, resolved, rfl⟩
    exact ⟨selection, ⟨holds, (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mp admitted,
      selected, resolved⟩, rfl⟩

end Reach

#print axioms mem_network
#print axioms network_erase
#print axioms observe_of_present
#print axioms consume_of_present
#print axioms observe_iff_present
#print axioms consume_iff_taken
#print axioms observe_of_admitted
#print axioms consume_of_admitted
#print axioms reachStep_iff_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpacesPlacement
