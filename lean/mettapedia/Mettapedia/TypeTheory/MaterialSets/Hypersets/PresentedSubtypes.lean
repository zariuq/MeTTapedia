import Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedMaterialDecoder

/-!
# Material representations of compatibility-restricted types

An actual material representation of a type constructs representations of
all predicate subtypes at the same graph bound. The separating predicate is
stated using the known term encoding. Decoding retains the original term and
its predicate evidence; it never selects a witness from a proposition.

In particular, naturality or observation compatibility can restrict an
actual dependent-function carrier. This constructs the required compatible
section carrier rather than supplying it as an extra smallness input.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedType

open AccessiblePointedGraph

universe u

variable {A : Type u} (model : PresentedType A) (predicate : A → Prop)

/-- The bounded predicate mentions the authored term encoding. -/
def encodedPredicate (value : HSet.{u}) : Prop :=
  ∃ term : A, model.value term = value ∧ predicate term

def restrictGraph : AccessiblePointedGraph.{u} :=
  separationGraph model.graph (encodedPredicate model predicate)

theorem mk_restrictGraph : HSet.mk (restrictGraph model predicate) =
    HSet.sep (encodedPredicate model predicate) model.carrier :=
  mk_separationGraph model.graph (encodedPredicate model predicate)

theorem mem_restrictGraph (value : HSet.{u}) :
    value ∈ HSet.mk (restrictGraph model predicate) ↔
      ∃ term : A, predicate term ∧ model.value term = value := by
  rw [mk_restrictGraph, HSet.mem_sep]
  constructor
  · rintro ⟨_, term, same, satisfies⟩
    exact ⟨term, satisfies, same⟩
  · rintro ⟨term, satisfies, rfl⟩
    exact ⟨model.value_mem term, term, rfl, satisfies⟩

private def unrestrictedMember
    (member : {value : HSet.{u} // value ∈ HSet.mk (restrictGraph model predicate)}) :
    {value : HSet.{u} // value ∈ model.carrier} :=
  ⟨member.val, by
    obtain ⟨term, _, same⟩ := (mem_restrictGraph model predicate member.val).mp member.property
    exact same ▸ model.value_mem term⟩

private theorem decoded_satisfies
    (member : {value : HSet.{u} // value ∈ HSet.mk (restrictGraph model predicate)}) :
    predicate (model.decode (unrestrictedMember model predicate member)) := by
  obtain ⟨term, satisfies, same⟩ := (mem_restrictGraph model predicate member.val).mp member.property
  have identical : model.decode (unrestrictedMember model predicate member) = term :=
    model.value_injective ((model.value_decode _).trans same.symm)
  exact identical.symm ▸ satisfies

/-- The member equivalence is constructed in both directions. Membership
and predicate proofs are formed after decoding the known unrestricted term. -/
def restrictDecode :
    {value : HSet.{u} // value ∈ HSet.mk (restrictGraph model predicate)} ≃ {term : A // predicate term} where
  toFun member := ⟨model.decode (unrestrictedMember model predicate member),
    decoded_satisfies model predicate member⟩
  invFun term := ⟨model.value term.val,
    (mem_restrictGraph model predicate _).mpr ⟨term.val, term.property, rfl⟩⟩
  left_inv member := Subtype.ext (model.value_decode _)
  right_inv term := by
    apply Subtype.ext
    apply model.value_injective
    exact model.value_decode _

/-- Separation builds the graph and the entire member decoder. -/
def restrict : PresentedType {term : A // predicate term} where
  graph := restrictGraph model predicate
  decode := restrictDecode model predicate

theorem restrict_value (term : {term : A // predicate term}) :
    (restrict model predicate).value term = model.value term.val := rfl

theorem restrict_decode
    (member : {value : HSet.{u} // value ∈ (restrict model predicate).carrier}) :
    ((restrict model predicate).decode member).val =
      model.decode (unrestrictedMember model predicate member) := rfl

theorem restrict_termGraph (term : {term : A // predicate term}) :
    HSet.mk ((restrict model predicate).termGraph term) = model.value term.val :=
  (mk_termGraph _ _).trans (restrict_value model predicate term)

theorem mem_restrict_carrier (value : HSet.{u}) :
    value ∈ (restrict model predicate).carrier ↔
      ∃ term : A, predicate term ∧ model.value term = value :=
  mem_restrictGraph model predicate value

theorem restrict_false : (restrict model (fun _ => False)).carrier = (∅ : HSet.{u}) := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  obtain ⟨_, impossible, _⟩ := (mem_restrict_carrier model _ value).mp member
  exact impossible

theorem restrict_true : (restrict model (fun _ => True)).carrier = model.carrier := by
  apply HSet.ext
  intro value
  constructor
  · intro member
    obtain ⟨term, _, same⟩ := (mem_restrict_carrier model _ value).mp member
    exact same ▸ model.value_mem term
  · intro member
    refine (mem_restrict_carrier model _ value).mpr
      ⟨model.decode ⟨value, member⟩, trivial, ?_⟩
    exact model.value_decode ⟨value, member⟩

theorem restrict_mono {other : A → Prop} (implies : ∀ term, predicate term → other term) :
    (restrict model predicate).carrier ⊆ (restrict model other).carrier := by
  intro value member
  obtain ⟨term, satisfies, same⟩ := (mem_restrict_carrier model predicate value).mp member
  exact (mem_restrict_carrier model other value).mpr ⟨term, implies term satisfies, same⟩

/-- Sequential restrictions implement conjunction in the actual material
carrier. Their graphs remain separate authored presentations. -/
theorem restrict_twice (other : A → Prop) :
    (restrict (restrict model predicate) (fun term => other term.val)).carrier =
      (restrict model (fun term => predicate term ∧ other term)).carrier := by
  apply HSet.ext
  intro value
  rw [mem_restrict_carrier, mem_restrict_carrier]
  constructor
  · rintro ⟨term, second, same⟩
    exact ⟨term.val, ⟨term.property, second⟩, same⟩
  · rintro ⟨term, ⟨first, second⟩, same⟩
    exact ⟨⟨term, first⟩, second, same⟩

section Controls

open GeneratedMaterialDecoder LiftedFamilyModel

def quineSeed : PresentedType (Elements ({HSet.quineAtom.{u}, ∅} : HSet.{u})) :=
  liftedModel _

def quineOnly : PresentedType
    {term : Elements ({HSet.quineAtom.{u}, ∅} : HSet.{u}) // term.1 = HSet.quineAtom} :=
  restrict quineSeed (fun term => term.1 = HSet.quineAtom)

theorem quineOnly_carrier : quineOnly.{u}.carrier = {HSet.quineAtom.{u + 1}} := by
  apply HSet.ext
  intro value
  rw [quineOnly, HSet.mem_singleton, mem_restrict_carrier]
  constructor
  · rintro ⟨term, selected, same⟩
    change HSet.lift term.1 = value at same
    rw [selected, HSet.lift_quineAtom] at same
    exact same.symm
  · intro same
    exact ⟨⟨HSet.quineAtom, HSet.mem_pair.mpr (Or.inl rfl)⟩, rfl,
      HSet.lift_quineAtom.trans same.symm⟩

theorem empty_excluded : (∅ : HSet.{u + 1}) ∉ quineOnly.{u}.carrier := by
  rw [quineOnly_carrier]
  intro member
  exact HSet.empty_ne_quineAtom (HSet.mem_singleton.mp member)

end Controls

#print axioms restrict
#print axioms restrict_twice
#print axioms quineOnly_carrier

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedType
