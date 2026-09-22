import Mettapedia.GSLT.Core.LooseRelationEquipment

/-! # Structured proof-relevant relations and their equipment comparison -/

namespace Mettapedia.GSLT.RelationPresentation

open Mettapedia.GSLT.LooseRelationEquipment

universe u

/-- A proof-relevant relation keeps its evidence family as data. -/
structure Rel (Source Target : Type u) where
  evidence : Source → Target → Type u

namespace Rel

@[ext]
theorem ext {Source Target : Type u} {first second : Rel Source Target}
    (evidence : ∀ source target,
      first.evidence source target = second.evidence source target) :
    first = second := by
  cases first
  cases second
  congr
  funext source target
  exact evidence source target

/-- Interpret a proof-relevant relation as the equipment's loose arrow. -/
def toLoose {Source Target : Type u} (relation : Rel Source Target) :
    Loose Source Target :=
  relation.evidence

/-- Every loose arrow can be internalized without discarding witnesses. -/
def ofLoose {Source Target : Type u} (relation : Loose Source Target) :
    Rel Source Target where
  evidence := relation

/-- proof-relevant relations and equipment loose arrows carry exactly the
same data, through an explicit layer boundary. -/
def equipmentEquiv (Source Target : Type u) :
    Rel Source Target ≃ Loose Source Target where
  toFun := toLoose
  invFun := ofLoose
  left_inv relation := by cases relation; rfl
  right_inv _ := rfl

@[simp] theorem toLoose_ofLoose {Source Target : Type u}
    (relation : Loose Source Target) :
    (ofLoose relation).toLoose = relation :=
  rfl

@[simp] theorem ofLoose_toLoose {Source Target : Type u}
    (relation : Rel Source Target) :
    ofLoose relation.toLoose = relation := by
  cases relation
  rfl

/-- A tight function enters the relational language through its companion. -/
def graph {Source Target : Type u} (map : Source → Target) :
    Rel Source Target :=
  ofLoose (companion map)

@[simp] theorem toLoose_graph {Source Target : Type u}
    (map : Source → Target) :
    (graph map).toLoose = companion map :=
  rfl

/-- Genuine semantic Chain is horizontal composition in the equipment. -/
def Chain {First Middle Last : Type u}
    (earlier : Rel First Middle) (later : Rel Middle Last) :
    Rel First Last where
  evidence source target :=
    Sigma fun middle =>
      earlier.evidence source middle × later.evidence middle target

@[simp] theorem toLoose_Chain {First Middle Last : Type u}
    (earlier : Rel First Middle) (later : Rel Middle Last) :
    (Chain earlier later).toLoose =
      Mettapedia.GSLT.LooseRelationEquipment.comp
        earlier.toLoose later.toLoose :=
  rfl

/-- The correspondence preserves the intermediate endpoint and both
derivations, rather than merely preserving visible endpoints. -/
def chainWitnessEquiv {First Middle Last : Type u}
    (earlier : Rel First Middle) (later : Rel Middle Last)
    (source : First) (target : Last) :
    (Chain earlier later).evidence source target ≃
      Mettapedia.GSLT.LooseRelationEquipment.comp
        earlier.toLoose later.toLoose source target :=
  Equiv.refl _

/-- Representation is an earned license for the interpreted loose arrow. -/
abbrev Representation {Source Target : Type u}
    (relation : Rel Source Target) :=
  Mettapedia.GSLT.LooseRelationEquipment.Representation relation.toLoose

/-- A function graph represents itself. -/
def graphRepresentation {Source Target : Type u} (map : Source → Target) :
    Representation (graph map) :=
  Mettapedia.GSLT.LooseRelationEquipment.Representation.companionSelf map

/-- Representable relations are exactly total and proof-relevantly
deterministic on the interpreted fibres. -/
theorem representable_iff_total_and_deterministic
    {Source Target : Type u} (relation : Rel Source Target) :
    Nonempty (Representation relation) ↔
      Mettapedia.GSLT.LooseRelationEquipment.Total relation.toLoose ∧
        Mettapedia.GSLT.LooseRelationEquipment.Deterministic
          relation.toLoose :=
  Mettapedia.GSLT.LooseRelationEquipment.Representation.nonempty_iff_total_and_deterministic

/-- Chaining two represented relations earns ordinary function composition,
without changing the relational meaning used before admission. -/
def chainRepresentation {First Middle Last : Type u}
    {earlier : Rel First Middle} {later : Rel Middle Last}
    (earlierRepresentation : Representation earlier)
    (laterRepresentation : Representation later) :
    Representation (Chain earlier later) :=
  Mettapedia.GSLT.LooseRelationEquipment.Representation.horizontalComp
    earlierRepresentation laterRepresentation

@[simp] theorem chainRepresentation_map {First Middle Last : Type u}
    {earlier : Rel First Middle} {later : Rel Middle Last}
    (earlierRepresentation : Representation earlier)
    (laterRepresentation : Representation later) :
    (chainRepresentation earlierRepresentation laterRepresentation).map =
      laterRepresentation.map ∘ earlierRepresentation.map :=
  rfl

/-- Functional composition agrees with chaining the corresponding graphs at
the exact represented-map seam. -/
@[simp] theorem graph_Chain_compose_map
    {First Middle Last : Type u}
    (earlier : First → Middle) (later : Middle → Last) :
    (chainRepresentation (graphRepresentation earlier)
      (graphRepresentation later)).map = later ∘ earlier :=
  rfl

end Rel

/-! ## Authored GSLT-IL routes through the same relation object -/


/-! ## Positive and negative controls -/

namespace Canary

open Rel

/-- Equality on booleans is a represented proof-relevant relation. -/
def exactBool : Rel Bool Bool := Rel.graph _root_.id

theorem exactBool_representable :
    Nonempty (Rel.Representation exactBool) :=
  ⟨Rel.graphRepresentation _root_.id⟩

/-- Both visible Boolean targets are inhabited from the same source. -/
def choice : Rel Unit Bool where
  evidence _ _ := Unit

theorem choice_executes_both :
    Nonempty (choice.evidence () false) ∧
      Nonempty (choice.evidence () true) :=
  ⟨⟨()⟩, ⟨()⟩⟩

/-- A nondeterministic relation remains executable but earns no map. -/
theorem choice_not_representable :
    ¬ Nonempty (Rel.Representation choice) := by
  rintro ⟨representation⟩
  have falseEq := (representation.exact () false ()).down.down
  have trueEq := (representation.exact () true ()).down.down
  exact Bool.false_ne_true (falseEq.symm.trans trueEq)

/-- This relation is deterministic wherever it fires, but has no result at
`true`. -/
def partialRel : Rel Bool Unit where
  evidence
    | false, () => Unit
    | true, () => Empty

theorem partial_deterministic : Deterministic partialRel.toLoose := by
  intro source
  constructor
  rintro ⟨firstTarget, first⟩ ⟨secondTarget, second⟩
  cases source with
  | false =>
      cases firstTarget
      cases secondTarget
      rfl
  | true => exact first.elim

theorem partial_not_total : ¬ Total partialRel.toLoose := by
  intro total
  exact (total true).elim fun selected => by
    rcases selected with ⟨target, witness⟩
    cases target
    exact witness.elim

/-- Partial determinism is insufficient for companion authority. -/
theorem partial_not_representable :
    ¬ Nonempty (Rel.Representation partialRel) := by
  rintro ⟨representation⟩
  exact partial_not_total representation.total

end Canary


end Mettapedia.GSLT.RelationPresentation
