import Mettapedia.TypeTheory.MaterialSets.Hypersets.StratifiedSmallMaps
import Mettapedia.SetTheory.Profiles.Ledger

/-!
# Original-bound collection in an explicitly classical hyperset profile

The actual hyperset carrier satisfies strong collection at its original
graph bound when the host's classical choice selects one witness and one
graph for each original root occurrence. Replacement is then derived from
collection and uniqueness. Both operations are instantiated here, rather
than supplied as model fields.

This is a comparison profile: its proofs depend on `Classical.choice`.
The constructive bounded, typed and raised collection constructions remain
separate and do not inherit this rule. The resulting ledger includes actual
set-forming laws and a Quine atom; it does not assert a Grothendieck universe
axiom or impose membership induction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ClassicalHypersetCollection

open Mettapedia.SetTheory.Profiles

universe u

/-- Strong collection on the actual members of an actual set, with a
collecting set at the same graph bound. It asks for at least one witness per
source, not a bound containing every possible witness. -/
def StrongCollection : Prop :=
  ∀ (domain : HSet.{u}) (relation : HSet.{u} → HSet.{u} → Prop),
    (∀ source ∈ domain, ∃ target, relation source target) →
    ∃ collected : HSet.{u},
      (∀ source ∈ domain, ∃ target ∈ collected, relation source target) ∧
      (∀ target ∈ collected, ∃ source ∈ domain, relation source target)

/-- Classical selection is explicitly confined to the witness and graph
families; the root occurrence carrier itself is genuinely small. -/
theorem strongCollection : StrongCollection.{u} := by
  classical
  intro domain relation total
  obtain ⟨graph, same⟩ := HSet.exists_mk domain
  subst domain
  let Child := {vertex : graph.Node // graph.edge graph.point vertex}
  let source (child : Child) := HSet.decorate graph.edge child.val
  have sourceMember (child : Child) : source child ∈ HSet.mk graph :=
    HSet.mem_mk.mpr ⟨child.val, child.property, rfl⟩
  let witness (child : Child) := Classical.choose (total (source child) (sourceMember child))
  have witnessLaw (child : Child) : relation (source child) (witness child) :=
    Classical.choose_spec (total (source child) (sourceMember child))
  let witnessGraph (child : Child) := Classical.choose (HSet.exists_mk (witness child))
  have witnessGraphLaw (child : Child) : HSet.mk (witnessGraph child) = witness child :=
    Classical.choose_spec (HSet.exists_mk (witness child))
  refine ⟨HSet.range witnessGraph, ?_, ?_⟩
  · intro original belongs
    obtain ⟨vertex, available, valueSame⟩ := HSet.mem_mk.mp belongs
    let child : Child := ⟨vertex, available⟩
    refine ⟨witness child, HSet.mem_range.mpr ⟨child, witnessGraphLaw child⟩, ?_⟩
    exact valueSame ▸ witnessLaw child
  · intro target belongs
    obtain ⟨child, graphSame⟩ := HSet.mem_range.mp belongs
    refine ⟨source child, sourceMember child, ?_⟩
    exact ((witnessGraphLaw child).symm.trans graphSame) ▸ witnessLaw child

/-- Functional relation replacement follows from collection without another
selection step: uniqueness makes every relation value a collected value. -/
theorem replacement_of_strongCollection (collection : StrongCollection.{u}) :
    HasReplacement (S := HSet.{u}) (· ∈ ·) := by
  intro domain relation functional
  obtain ⟨collected, covers, justified⟩ := collection domain relation
    (fun source belongs => by
      obtain ⟨target, holds, _⟩ := functional source belongs
      exact ⟨target, holds⟩)
  refine ⟨collected, fun target => ?_⟩
  constructor
  · exact justified target
  · rintro ⟨source, belongs, holds⟩
    obtain ⟨chosen, chosenMember, chosenLaw⟩ := covers source belongs
    obtain ⟨unique, _, only⟩ := functional source belongs
    have same : chosen = target := (only chosen chosenLaw).trans (only target holds).symm
    exact same ▸ chosenMember

theorem replacement : HasReplacement (S := HSet.{u}) (· ∈ ·) :=
  replacement_of_strongCollection strongCollection

/-- This is an actual model of the ledger's displayed hyperset assumptions,
including replacement. It contains no universal-set or universe-selection
field, and its graph-bound collection depends on host choice. -/
theorem assumptions : HypersetAssumptions (S := HSet.{u}) (· ∈ ·) where
  extensional := fun _ _ same => HSet.ext same
  empty := ⟨∅, HSet.notMem_empty⟩
  union := fun domain => ⟨HSet.sUnion domain, fun _ => HSet.mem_sUnion⟩
  power := fun domain => ⟨HSet.powerset domain, fun _ => HSet.mem_powerset⟩
  separation := fun domain predicate => ⟨HSet.sep predicate domain, fun _ => HSet.mem_sep⟩
  replacement := replacement
  quineAtom := ⟨HSet.quineAtom, fun _ => HSet.mem_quineAtom⟩

theorem ledger : HypersetLedger (S := HSet.{u}) (· ∈ ·) assumptions :=
  hypersetLedger (· ∈ ·) assumptions

namespace Controls

/-- An empty source needs an actually empty collecting set. -/
theorem empty_source (relation : HSet.{u} → HSet.{u} → Prop) :
    (∀ source ∈ (∅ : HSet.{u}), ∃ target ∈ (∅ : HSet.{u}), relation source target) ∧
      (∀ target ∈ (∅ : HSet.{u}), ∃ source ∈ (∅ : HSet.{u}), relation source target) :=
  ⟨fun source impossible => (HSet.notMem_empty source impossible).elim,
    fun target impossible => (HSet.notMem_empty target impossible).elim⟩

/-- Strong collection for the everywhere-true relation has a fixed small
witness set, while the complete raised collection cannot descend. -/
theorem selecting_and_collecting_all_differ :
    (∃ collected : HSet.{u},
      (∀ _index : ULift.{u + 1, 0} PUnit, ∃ y, True ∧ y ∈ collected) ∧
      (∀ y ∈ collected, ∃ _index : ULift.{u + 1, 0} PUnit, True)) ∧
      ¬ ∃ collected : HSet.{u}, HSet.lift collected =
        HSet.collectionUp (fun _index : ULift.{u + 1, 0} PUnit =>
          fun _value : HSet.{u} => True) :=
  ⟨StratifiedSmallMaps.Controls.true_relation_strong_collection,
    StratifiedSmallMaps.Controls.true_relation_all_witnesses_do_not_descend⟩

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ClassicalHypersetCollection
