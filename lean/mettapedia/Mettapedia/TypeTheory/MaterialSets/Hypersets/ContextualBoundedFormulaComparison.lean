import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic

/-!
# Full-future bounded formulas under material membership embeddings

Bounded quantifiers range over the actual members of a named parent. An
injective natural value map reflecting membership and covering these members
preserves and reflects every bounded formula. Implication and bounded universal
quantification still retain all future contexts. The hypotheses do not require
surjectivity onto the larger value carrier and do not license unbounded
first-order reflection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualBoundedFormulaComparison

open _root_.CategoryTheory ContextualMaterialLogic
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v w h
variable {D : Type u} [Category.{u} D]

/-- The bounded fragment uses the existing first-order syntax. -/
inductive Bounded : {n : Nat} → Formula n → Prop where
  | bottom {n : Nat} : Bounded (Formula.bottom (n := n))
  | equal {n : Nat} (first second : Fin n) : Bounded (.equal first second)
  | member {n : Nat} (child parent : Fin n) : Bounded (.member child parent)
  | both {n : Nat} {left right : Formula n} (first : Bounded left) (second : Bounded right) :
      Bounded (.both left right)
  | either {n : Nat} {left right : Formula n} (first : Bounded left) (second : Bounded right) :
      Bounded (.either left right)
  | imply {n : Nat} {left right : Formula n} (first : Bounded left) (second : Bounded right) :
      Bounded (.imply left right)
  | allIn {n : Nat} (parent : Fin n) {body : Formula (n+1)} (bounded : Bounded body) :
      Bounded (.all (.imply (.member 0 parent.succ) body))
  | existIn {n : Nat} (parent : Fin n) {body : Formula (n+1)} (bounded : Bounded body) :
      Bounded (.exist (.both (.member 0 parent.succ) body))

theorem bounded_substitute {n m : Nat} {formula : Formula n} (bounded : Bounded formula)
    (indices : Fin n → Fin m) : Bounded (substitute indices formula) := by
  induction bounded generalizing m with
  | bottom => exact .bottom
  | equal first second => exact .equal (indices first) (indices second)
  | member child parent => exact .member (indices child) (indices parent)
  | both _ _ firstIH secondIH => exact .both (firstIH indices) (secondIH indices)
  | either _ _ firstIH secondIH => exact .either (firstIH indices) (secondIH indices)
  | imply _ _ firstIH secondIH => exact .imply (firstIH indices) (secondIH indices)
  | allIn parent _ bodyIH => exact .allIn (indices parent) (bodyIH (liftVariables indices))
  | existIn parent _ bodyIH => exact .existIn (indices parent) (bodyIH (liftVariables indices))

variable {source : D ⥤ Type v} {target : D ⥤ Type w}

/-- Literal member surjectivity is distinct from surjectivity on all values. -/
structure MembershipEmbedding (sourceModel : Model source) (targetModel : Model target) where
  valueMap : NaturalHom source target
  injective : ∀ point, Function.Injective (valueMap.app point)
  member_iff : ∀ point child parent,
    targetModel.member point (valueMap.app point child) (valueMap.app point parent) ↔
      sourceModel.member point child parent
  member_onto : ∀ point parent child,
    targetModel.member point child (valueMap.app point parent) →
      ∃ original, valueMap.app point original = child

def MembershipEmbedding.comp {later : D ⥤ Type h}
    {sourceModel : Model source} {targetModel : Model target} {laterModel : Model later}
    (first : MembershipEmbedding sourceModel targetModel)
    (second : MembershipEmbedding targetModel laterModel) : MembershipEmbedding sourceModel laterModel where
  valueMap := first.valueMap.comp second.valueMap
  injective point := (second.injective point).comp (first.injective point)
  member_iff point child parent :=
    (second.member_iff point (first.valueMap.app point child) (first.valueMap.app point parent)).trans
      (first.member_iff point child parent)
  member_onto point parent child belongs := by
    change laterModel.member point child (second.valueMap.app point (first.valueMap.app point parent)) at belongs
    obtain ⟨middle, same⟩ := second.member_onto point (first.valueMap.app point parent) child belongs
    have middleMember := (second.member_iff point middle (first.valueMap.app point parent)).mp
      (by simpa only [same] using belongs)
    obtain ⟨original, earlier⟩ := first.member_onto point parent middle middleMember
    exact ⟨original, (congrArg (second.valueMap.app point) earlier).trans same⟩

def mapEnvironment (operation : NaturalHom source target) {n : Nat} (point : D)
    (environment : Environment source n point) : Environment target n point :=
  fun index => operation.app point (environment index)

theorem mapEnvironment_transport (operation : NaturalHom source target) {n : Nat}
    {point later : D} (arrow : point ⟶ later) (environment : Environment source n point) :
    transport target arrow (mapEnvironment operation point environment) =
      mapEnvironment operation later (transport source arrow environment) := by
  funext index
  exact operation.naturality arrow (environment index)

theorem mapEnvironment_extend (operation : NaturalHom source target) {n : Nat}
    (point : D) (environment : Environment source n point) (value : source.obj point) :
    mapEnvironment operation point (extend source environment value) =
      extend target (mapEnvironment operation point environment) (operation.app point value) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

theorem mapEnvironment_substitute (operation : NaturalHom source target) {n m : Nat}
    (indices : Fin n → Fin m) (point : D) (environment : Environment source m point) :
    mapEnvironment operation point (fun index => environment (indices index)) =
      fun index => mapEnvironment operation point environment (indices index) := rfl

theorem mapEnvironment_comp {later : D ⥤ Type h} (first : NaturalHom source target)
    (second : NaturalHom target later) {n : Nat} (point : D)
    (environment : Environment source n point) :
    mapEnvironment (first.comp second) point environment =
      mapEnvironment second point (mapEnvironment first point environment) := rfl

theorem force_allIn_iff (values : D ⥤ Type v) (model : Model values) {n : Nat}
    (parent : Fin n) (body : Formula (n+1)) (point : D)
    (environment : Environment values n point) :
    force values model (.all (.imply (.member 0 parent.succ) body)) point environment ↔
      ∀ (later : D) (arrow : point ⟶ later) (child : values.obj later),
        model.member later child ((transport values arrow environment) parent) →
          force values model body later (extend values (transport values arrow environment) child) := by
  constructor
  · intro universal later arrow child belongs
    have current := universal later arrow child later (𝟙 later)
    rw [transport_id] at current
    exact current belongs
  · intro bounded later arrow child future tail belongs
    change model.member future (values.map tail child)
      (values.map tail ((transport values arrow environment) parent)) at belongs
    have next := bounded future (arrow ≫ tail) (values.map tail child)
      (by
        change model.member future (values.map tail child) (values.map (arrow ≫ tail) (environment parent))
        rw [values.map_comp_apply]
        exact belongs)
    simpa only [transport_extend, ← transport_comp] using next

theorem force_existIn_iff (values : D ⥤ Type v) (model : Model values) {n : Nat}
    (parent : Fin n) (body : Formula (n+1)) (point : D)
    (environment : Environment values n point) :
    force values model (.exist (.both (.member 0 parent.succ) body)) point environment ↔
      ∃ child : values.obj point, model.member point child (environment parent) ∧
        force values model body point (extend values environment child) := Iff.rfl

/-- The same bounded statement is valid on both sides at every future and
assignment. No inverse into the whole larger universe is selected. -/
theorem force_iff (sourceModel : Model source) (targetModel : Model target)
    (embedding : MembershipEmbedding sourceModel targetModel) {n : Nat} {formula : Formula n}
    (bounded : Bounded formula) (point : D) (environment : Environment source n point) :
    force source sourceModel formula point environment ↔
      force target targetModel formula point (mapEnvironment embedding.valueMap point environment) := by
  induction bounded generalizing point with
  | bottom => exact Iff.rfl
  | equal first second =>
    exact ⟨congrArg (embedding.valueMap.app point), fun same => embedding.injective point same⟩
  | member child parent => exact (embedding.member_iff point (environment child) (environment parent)).symm
  | both _ _ firstIH secondIH => exact and_congr (firstIH point environment) (secondIH point environment)
  | either _ _ firstIH secondIH => exact or_congr (firstIH point environment) (secondIH point environment)
  | imply _ _ firstIH secondIH =>
    refine forall_congr' fun later => forall_congr' fun arrow => ?_
    rw [mapEnvironment_transport]
    exact imp_congr (firstIH later (transport source arrow environment))
      (secondIH later (transport source arrow environment))
  | allIn parent _ bodyIH =>
    rw [force_allIn_iff, force_allIn_iff]
    constructor
    · intro lower later arrow child belongs
      rw [mapEnvironment_transport] at belongs ⊢
      obtain ⟨original, same⟩ := embedding.member_onto later
        ((transport source arrow environment) parent) child belongs
      have oldMember := (embedding.member_iff later original
        ((transport source arrow environment) parent)).mp (same ▸ belongs)
      have proof := (bodyIH later (extend source (transport source arrow environment) original)).mp
        (lower later arrow original oldMember)
      simpa only [mapEnvironment_extend, same] using proof
    · intro upper later arrow child belongs
      have proof := upper later arrow (embedding.valueMap.app later child)
        (by rw [mapEnvironment_transport]; exact (embedding.member_iff later child
          ((transport source arrow environment) parent)).mpr belongs)
      apply (bodyIH later (extend source (transport source arrow environment) child)).mpr
      simpa only [mapEnvironment_extend, mapEnvironment_transport] using proof
  | existIn parent _ bodyIH =>
    rw [force_existIn_iff, force_existIn_iff]
    constructor
    · rintro ⟨child, belongs, proof⟩
      refine ⟨embedding.valueMap.app point child,
        (embedding.member_iff point child (environment parent)).mpr belongs, ?_⟩
      simpa only [mapEnvironment_extend] using
        (bodyIH point (extend source environment child)).mp proof
    · rintro ⟨child, belongs, proof⟩
      obtain ⟨original, same⟩ := embedding.member_onto point (environment parent) child belongs
      refine ⟨original, (embedding.member_iff point original (environment parent)).mp (same ▸ belongs), ?_⟩
      apply (bodyIH point (extend source environment original)).mpr
      simpa only [mapEnvironment_extend, same] using proof

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualBoundedFormulaComparison
