import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedTypeOperations

/-!
# A host Boolean decoder entails computational unique description

This is a precise consequence of a host-valued material Boolean decoder,
not an impossibility claim. A nonempty singleton predicate on Boolean values
can be converted to its actual Boolean witness by collecting its authored
term graphs, taking their material union, and decoding the resulting member.
Neither a singleton predicate nor propositional existence alone supplies
that decoder. This boundary is separate from universe size and from native
material-valued dependent consumers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialBooleanDescription

universe u

/-- An explicitly supplied host decoder has this computational consequence.
The proof itself selects no propositional witness to construct the result. -/
def describeUnique {T : Type u} (model : PresentedType T) (predicate : T → Prop)
    (unique : ∃! value, predicate value) : {value : T // predicate value} :=
  let collected : HSet.{u} := HSet.range fun value : {value : T // predicate value} =>
    model.termGraph value.1
  let observed := HSet.sUnion collected
  have observed_value : ∀ value, predicate value → observed = model.value value := by
    intro value satisfies
    have singleton : collected = {model.value value} := by
      apply HSet.ext
      intro material
      constructor
      · intro member
        obtain ⟨witness, same⟩ := HSet.mem_range.mp member
        exact HSet.mem_singleton.mpr (same.symm.trans
          ((model.mk_termGraph witness.1).trans (congrArg model.value (unique.unique witness.2 satisfies))))
      · intro member
        exact HSet.mem_range.mpr ⟨⟨value, satisfies⟩,
          (model.mk_termGraph value).trans (HSet.mem_singleton.mp member).symm⟩
    exact (congrArg HSet.sUnion singleton).trans (HSet.sUnion_singleton _)
  have belongs : observed ∈ model.carrier := by
    obtain ⟨value, satisfies, _⟩ := unique
    exact observed_value value satisfies ▸ model.value_mem value
  ⟨model.decode ⟨observed, belongs⟩, by
    obtain ⟨value, satisfies, _⟩ := unique
    have same : model.decode ⟨observed, belongs⟩ = value := by
      apply model.decode.symm.injective
      exact Subtype.ext ((model.value_decode _).trans (observed_value value satisfies))
    exact same.symm ▸ satisfies⟩

/-- This consequence applies to a lifted host Boolean carrier at any graph
bound, including the level of generated material families. -/
def describeBool (model : PresentedType (ULift.{u, 0} Bool)) (predicate : Bool → Prop)
    (unique : ∃! value, predicate value) : {value : Bool // predicate value} :=
  have liftedUnique : ∃! value : ULift.{u, 0} Bool, predicate value.down := by
    obtain ⟨value, satisfies, only⟩ := unique
    refine ⟨⟨value⟩, satisfies, ?_⟩
    intro other holds
    exact ULift.ext _ _ (only other.down holds)
  let result := describeUnique model (fun value => predicate value.down) liftedUnique
  ⟨result.1.down, result.2⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialBooleanDescription
