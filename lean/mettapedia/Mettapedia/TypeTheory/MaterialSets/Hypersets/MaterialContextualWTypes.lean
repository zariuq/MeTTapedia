import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWTypes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWLabels

/-!
# Actual material encodings of contextual indexed W trees

Each root observes its known context and actual material shape. Every branch
observes the full future world, arrow and dependent position. Collected graph
carriers and bounded singleton-row readout reconstruct the original root and
each indexed child. Accessibility of this actual material child relation
constructs the decoder by recursion, without selecting an encoding witness.

World and arrow encoders are authored faithful graph labels, not host
decoders. Shape and position dictionaries are existing actual material
models. The W graph carrier, root/child readout, accessibility and inverse
are constructed here; none is supplied. All graphs remain at that same bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWTypes

open CategoryTheory
open ContextualWTypes (RawTree Position)
open ContextualWLabels (Branch Label)

universe u
variable {D : Type u} [Category.{u} D]
variable (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u)
variable (worlds : ArgumentCoding D)
variable (arrows : (source target : D) → ArgumentCoding (source ⟶ target))
variable (shapes : (world : D) → PresentedType (shape.obj world))
variable (positions : (point : shape.Elements) → PresentedType (position.obj point))

abbrev TotalTree := (world : D) × RawTree shape position world

def edge : Option (TotalTree shape position) → Label shape position → Option (TotalTree shape position) → Prop
  | none, _, _ => False
  | some ⟨X, .sup label children⟩, observation, target =>
    (observation = .inl ⟨X, label⟩ ∧ target = none) ∨
      ∃ branch : Branch shape position label,
        observation = .inr ⟨⟨X, label⟩, branch⟩ ∧
          target = some ⟨branch.1, children branch.1 branch.2.1 branch.2.2⟩

def treeGraph {X : D} (tree : RawTree shape position X) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.generated
    ((ContextualWLabels.labels shape position worlds arrows shapes positions).edge (edge shape position))
    (HSet.LabelCarrier.atom (some ⟨X, tree⟩))

def encode {X : D} (tree : RawTree shape position X) : HSet.{u} :=
  (ContextualWLabels.labels shape position worlds arrows shapes positions).decorate (edge shape position) (some ⟨X, tree⟩)

theorem mk_treeGraph {X : D} (tree : RawTree shape position X) :
    HSet.mk (treeGraph shape position worlds arrows shapes positions tree) =
      encode shape position worlds arrows shapes positions tree := rfl

theorem decorate_terminal :
    (ContextualWLabels.labels shape position worlds arrows shapes positions).decorate (edge shape position) none = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value belongs
  obtain ⟨_, _, impossible, _⟩ := (ContextualWLabels.labels shape position worlds arrows shapes positions).mem_decorate.mp belongs
  exact impossible

theorem mem_encode_sup_iff {X : D} (label : shape.obj X)
    (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → RawTree shape position Y)
    (value : HSet.{u}) :
    value ∈ encode shape position worlds arrows shapes positions (.sup label children) ↔
      value = HSet.kpair (ContextualWLabels.shapeTag worlds X ((shapes X).value label)) ∅ ∨
        ∃ branch : Branch shape position label,
          value = HSet.kpair (ContextualWLabels.positionTag shape position worlds arrows shapes positions ⟨X, label⟩ branch)
            (encode shape position worlds arrows shapes positions (children branch.1 branch.2.1 branch.2.2)) := by
  rw [encode, (ContextualWLabels.labels shape position worlds arrows shapes positions).mem_decorate]
  constructor
  · rintro ⟨observation, target, step, same⟩
    rcases step with ⟨rfl, rfl⟩ | ⟨branch, rfl, rfl⟩
    · exact Or.inl (same.trans (congrArg (HSet.kpair _) (decorate_terminal shape position worlds arrows shapes positions)))
    · exact Or.inr ⟨branch, same⟩
  · rintro (same | ⟨branch, same⟩)
    · refine ⟨.inl ⟨X, label⟩, none, Or.inl ⟨rfl, rfl⟩, ?_⟩
      exact same.trans (congrArg (HSet.kpair _) (decorate_terminal shape position worlds arrows shapes positions)).symm
    · exact ⟨.inr ⟨⟨X, label⟩, branch⟩, some ⟨branch.1, children branch.1 branch.2.1 branch.2.2⟩,
        Or.inr ⟨branch, rfl, rfl⟩, same⟩

def carrierGraph (X : D) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup (treeGraph shape position worlds arrows shapes positions (X := X))

abbrev Members (X : D) := {root : HSet.{u} // root ∈ HSet.mk (carrierGraph shape position worlds arrows shapes positions X)}

theorem mem_carrierGraph_iff {X : D} {root : HSet.{u}} :
    root ∈ HSet.mk (carrierGraph shape position worlds arrows shapes positions X) ↔
      ∃ tree : RawTree shape position X, encode shape position worlds arrows shapes positions tree = root := HSet.mem_range

def treeMember {X : D} (tree : RawTree shape position X) : Members shape position worlds arrows shapes positions X :=
  ⟨encode shape position worlds arrows shapes positions tree, (mem_carrierGraph_iff shape position worlds arrows shapes positions).mpr ⟨tree, rfl⟩⟩

theorem shapeObservation_sup_iff {X : D} (label : shape.obj X)
    (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → RawTree shape position Y)
    (original : HSet.{u}) :
    HSet.kpair (ContextualWLabels.shapeTag worlds X original) ∅ ∈
        encode shape position worlds arrows shapes positions (.sup label children) ↔ original = (shapes X).value label := by
  rw [mem_encode_sup_iff]
  constructor
  · rintro (same | ⟨branch, same⟩)
    · exact (HSet.kpair_inj.mp (HSet.kpair_inj.mp (HSet.kpair_inj.mp same).1).2).2
    · exact (ContextualWLabels.shapeTag_ne_positionTag shape position worlds arrows shapes positions X original ⟨X, label⟩ branch
        (HSet.kpair_inj.mp same).1).elim
  · intro same
    exact Or.inl (congrArg (fun original => HSet.kpair (ContextualWLabels.shapeTag worlds X original) ∅) same)

theorem positionObservation_sup_iff {X : D} (label : shape.obj X)
    (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → RawTree shape position Y)
    (branch : Branch shape position label) (childValue : HSet.{u}) :
    HSet.kpair (ContextualWLabels.positionTag shape position worlds arrows shapes positions ⟨X, label⟩ branch) childValue ∈
        encode shape position worlds arrows shapes positions (.sup label children) ↔
      childValue = encode shape position worlds arrows shapes positions (children branch.1 branch.2.1 branch.2.2) := by
  rw [mem_encode_sup_iff]
  constructor
  · rintro (same | ⟨otherBranch, same⟩)
    · exact (ContextualWLabels.shapeTag_ne_positionTag shape position worlds arrows shapes positions X _ ⟨X, label⟩ branch
        (HSet.kpair_inj.mp same).1.symm).elim
    · have branches : branch = otherBranch :=
        (ContextualWLabels.branchCoding shape position worlds arrows positions label).injective
          (HSet.kpair_inj.mp (HSet.kpair_inj.mp (HSet.kpair_inj.mp same).1).2).2
      cases branches
      exact (HSet.kpair_inj.mp same).2
  · intro same
    exact Or.inr ⟨branch, congrArg (HSet.kpair _) same⟩

def shapeValue (X : D) (root : HSet.{u}) : HSet.{u} :=
  HSet.sUnion (HSet.sep (fun original => HSet.kpair (ContextualWLabels.shapeTag worlds X original) ∅ ∈ root) (shapes X).carrier)

theorem shapeValue_encode_sup {X : D} (label : shape.obj X)
    (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → RawTree shape position Y) :
    shapeValue shape worlds shapes X (encode shape position worlds arrows shapes positions (.sup label children)) = (shapes X).value label := by
  have row : HSet.sep (fun original => HSet.kpair (ContextualWLabels.shapeTag worlds X original) ∅ ∈
      encode shape position worlds arrows shapes positions (.sup label children)) (shapes X).carrier = {(shapes X).value label} := by
    apply HSet.ext
    intro original
    rw [HSet.mem_sep, shapeObservation_sup_iff, HSet.mem_singleton]
    exact ⟨And.right, fun same => ⟨same ▸ (shapes X).value_mem label, same⟩⟩
  exact (congrArg HSet.sUnion row).trans (HSet.sUnion_singleton _)

def rootShape {X : D} (root : Members shape position worlds arrows shapes positions X) : shape.obj X :=
  (shapes X).decode ⟨shapeValue shape worlds shapes X root.1, by
    obtain ⟨tree, same⟩ := (mem_carrierGraph_iff shape position worlds arrows shapes positions).mp root.2
    cases tree with
    | sup label children =>
      rw [← same, shapeValue_encode_sup]
      exact (shapes X).value_mem label⟩

theorem rootShape_treeMember_sup {X : D} (label : shape.obj X)
    (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → RawTree shape position Y) :
    rootShape shape position worlds arrows shapes positions (treeMember shape position worlds arrows shapes positions (.sup label children)) = label := by
  apply (shapes X).decode.symm.injective
  apply Subtype.ext
  exact (PresentedType.value_decode _ _).trans (shapeValue_encode_sup shape position worlds arrows shapes positions label children)

def childRow (root : HSet.{u}) (point : shape.Elements) (branch : Branch shape position point.2) : HSet.{u} :=
  HSet.sep (fun child => HSet.kpair (ContextualWLabels.positionTag shape position worlds arrows shapes positions point branch) child ∈ root)
    (HSet.mk (carrierGraph shape position worlds arrows shapes positions branch.1))

theorem childRow_encode_sup {X : D} (label : shape.obj X)
    (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → RawTree shape position Y)
    (branch : Branch shape position label) :
    childRow shape position worlds arrows shapes positions
        (encode shape position worlds arrows shapes positions (.sup label children)) ⟨X, label⟩ branch =
      {encode shape position worlds arrows shapes positions (children branch.1 branch.2.1 branch.2.2)} := by
  apply HSet.ext
  intro childValue
  dsimp only [childRow]
  rw [HSet.mem_sep]
  change childValue ∈ HSet.mk (carrierGraph shape position worlds arrows shapes positions branch.1) ∧
    HSet.kpair (ContextualWLabels.positionTag shape position worlds arrows shapes positions ⟨X, label⟩ branch) childValue ∈
      encode shape position worlds arrows shapes positions (.sup label children) ↔ _
  rw [positionObservation_sup_iff, HSet.mem_singleton]
  exact ⟨And.right, fun same => ⟨same ▸ (treeMember shape position worlds arrows shapes positions _).2, same⟩⟩

theorem childRow_cast {X : D} {first second : shape.obj X} (same : first = second)
    (root : HSet.{u}) (Y : D) (arrow : X ⟶ Y) (branch : Position shape position first arrow) :
    childRow shape position worlds arrows shapes positions root ⟨X, first⟩ ⟨Y, arrow, branch⟩ =
      childRow shape position worlds arrows shapes positions root ⟨X, second⟩
        ⟨Y, arrow, cast (congrArg (fun label => Position shape position label arrow) same) branch⟩ := by
  cases same
  rfl

def child {X : D} (root : Members shape position worlds arrows shapes positions X)
    (Y : D) (arrow : X ⟶ Y) (branch : Position shape position (rootShape shape position worlds arrows shapes positions root) arrow) :
    Members shape position worlds arrows shapes positions Y :=
  ⟨HSet.sUnion (childRow shape position worlds arrows shapes positions root.1
      ⟨X, rootShape shape position worlds arrows shapes positions root⟩ ⟨Y, arrow, branch⟩), by
    obtain ⟨tree, same⟩ := (mem_carrierGraph_iff shape position worlds arrows shapes positions).mp root.2
    have memberSame : root = treeMember shape position worlds arrows shapes positions tree := Subtype.ext same.symm
    cases memberSame
    cases tree with
    | sup label children =>
      have row := (childRow_cast shape position worlds arrows shapes positions
        (rootShape_treeMember_sup shape position worlds arrows shapes positions label children)
        (encode shape position worlds arrows shapes positions (.sup label children)) Y arrow branch).trans
        (childRow_encode_sup shape position worlds arrows shapes positions label children _)
      exact ((congrArg HSet.sUnion row).trans (HSet.sUnion_singleton _)).symm ▸
        (treeMember shape position worlds arrows shapes positions _).2⟩

theorem child_treeMember_sup {X : D} (label : shape.obj X)
    (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → RawTree shape position Y)
    (Y : D) (arrow : X ⟶ Y)
    (branch : Position shape position
      (rootShape shape position worlds arrows shapes positions (treeMember shape position worlds arrows shapes positions (.sup label children))) arrow) :
    child shape position worlds arrows shapes positions (treeMember shape position worlds arrows shapes positions (.sup label children)) Y arrow branch =
      treeMember shape position worlds arrows shapes positions
        (children Y arrow (cast (congrArg (fun label => Position shape position label arrow)
          (rootShape_treeMember_sup shape position worlds arrows shapes positions label children)) branch)) := by
  apply Subtype.ext
  exact (congrArg HSet.sUnion ((childRow_cast shape position worlds arrows shapes positions
    (rootShape_treeMember_sup shape position worlds arrows shapes positions label children)
    (encode shape position worlds arrows shapes positions (.sup label children)) Y arrow branch).trans
    (childRow_encode_sup shape position worlds arrows shapes positions label children _))).trans (HSet.sUnion_singleton _)

abbrev TotalMembers := (X : D) × Members shape position worlds arrows shapes positions X

def Child (subtree root : TotalMembers shape position worlds arrows shapes positions) : Prop :=
  ∃ arrow : root.1 ⟶ subtree.1,
    ∃ branch : Position shape position (rootShape shape position worlds arrows shapes positions root.2) arrow,
      subtree.2 = child shape position worlds arrows shapes positions root.2 subtree.1 arrow branch

theorem accessible_treeMember {X : D} (tree : RawTree shape position X) :
    Acc (Child shape position worlds arrows shapes positions) ⟨X, treeMember shape position worlds arrows shapes positions tree⟩ := by
  induction tree with
  | @sup X label children earlier =>
    refine Acc.intro _ ?_
    rintro ⟨Y, subtree⟩ ⟨arrow, branch, sameMember⟩
    change subtree = child shape position worlds arrows shapes positions
      (treeMember shape position worlds arrows shapes positions (.sup label children)) Y arrow branch at sameMember
    have same := congrArg (fun member => (⟨Y, member⟩ : TotalMembers shape position worlds arrows shapes positions))
      (sameMember.trans (child_treeMember_sup shape position worlds arrows shapes positions label children Y arrow branch))
    exact same.symm ▸ earlier Y arrow
      (cast (congrArg (fun label => Position shape position label arrow)
        (rootShape_treeMember_sup shape position worlds arrows shapes positions label children)) branch)

theorem accessible (root : TotalMembers shape position worlds arrows shapes positions) :
    Acc (Child shape position worlds arrows shapes positions) root := by
  rcases root with ⟨X, member⟩
  obtain ⟨tree, same⟩ := (mem_carrierGraph_iff shape position worlds arrows shapes positions).mp member.2
  have memberSame : member = treeMember shape position worlds arrows shapes positions tree := Subtype.ext same.symm
  exact memberSame.symm ▸ accessible_treeMember shape position worlds arrows shapes positions tree

def decodeAcc {root : TotalMembers shape position worlds arrows shapes positions}
    (available : Acc (Child shape position worlds arrows shapes positions) root) : RawTree shape position root.1 :=
  Acc.rec (motive := fun root _ => RawTree shape position root.1)
    (fun parent _ earlier => .sup (rootShape shape position worlds arrows shapes positions parent.2)
      (fun Y arrow branch => earlier ⟨Y, child shape position worlds arrows shapes positions parent.2 Y arrow branch⟩
        ⟨arrow, branch, rfl⟩)) available

def decode {X : D} (root : Members shape position worlds arrows shapes positions X) : RawTree shape position X :=
  decodeAcc shape position worlds arrows shapes positions (accessible shape position worlds arrows shapes positions ⟨X, root⟩)

theorem decode_eq {X : D} (root : Members shape position worlds arrows shapes positions X) :
    decode shape position worlds arrows shapes positions root =
      .sup (rootShape shape position worlds arrows shapes positions root)
        (fun Y arrow branch => decode shape position worlds arrows shapes positions
          (child shape position worlds arrows shapes positions root Y arrow branch)) := by
  have available := accessible shape position worlds arrows shapes positions ⟨X, root⟩
  change decodeAcc shape position worlds arrows shapes positions available = _
  cases available
  rfl

theorem decode_treeMember {X : D} (tree : RawTree shape position X) :
    decode shape position worlds arrows shapes positions (treeMember shape position worlds arrows shapes positions tree) = tree := by
  induction tree with
  | @sup X label children earlier =>
    apply (decode_eq shape position worlds arrows shapes positions (treeMember shape position worlds arrows shapes positions (.sup label children))).trans
    apply RawTree.sup_eq_of_cast (rootShape_treeMember_sup shape position worlds arrows shapes positions label children)
    intro Y arrow branch
    exact (congrArg (decode shape position worlds arrows shapes positions)
      (child_treeMember_sup shape position worlds arrows shapes positions label children Y arrow branch)).trans
      (earlier Y arrow (cast (congrArg (fun label => Position shape position label arrow)
        (rootShape_treeMember_sup shape position worlds arrows shapes positions label children)) branch))

theorem treeMember_decode {X : D} (root : Members shape position worlds arrows shapes positions X) :
    treeMember shape position worlds arrows shapes positions (decode shape position worlds arrows shapes positions root) = root := by
  obtain ⟨tree, same⟩ := (mem_carrierGraph_iff shape position worlds arrows shapes positions).mp root.2
  have memberSame : root = treeMember shape position worlds arrows shapes positions tree := Subtype.ext same.symm
  cases memberSame
  exact congrArg (treeMember shape position worlds arrows shapes positions) (decode_treeMember shape position worlds arrows shapes positions tree)

/-- The actual indexed material carrier and inverse constructed above. -/
def rawModel (X : D) : PresentedType (RawTree shape position X) where
  graph := carrierGraph shape position worlds arrows shapes positions X
  decode :=
    { toFun := decode shape position worlds arrows shapes positions
      invFun := treeMember shape position worlds arrows shapes positions
      left_inv := treeMember_decode shape position worlds arrows shapes positions
      right_inv := decode_treeMember shape position worlds arrows shapes positions }

theorem rawModel_value {X : D} (tree : RawTree shape position X) :
    (rawModel shape position worlds arrows shapes positions X).value tree = encode shape position worlds arrows shapes positions tree := rfl

theorem encode_injective {X : D} : Function.Injective (encode shape position worlds arrows shapes positions (X := X)) :=
  (rawModel shape position worlds arrows shapes positions X).value_injective

/-! Hereditary contextual naturality is enforced by actual material
separation, after the full indexed raw decoder has been constructed. -/

def naturalModel (X : D) : PresentedType (ContextualWTypes.NaturalTree shape position X) :=
  PresentedType.restrict (rawModel shape position worlds arrows shapes positions X) (ContextualWTypes.Natural shape position)

theorem naturalModel_value {X : D} (tree : ContextualWTypes.NaturalTree shape position X) :
    (naturalModel shape position worlds arrows shapes positions X).value tree =
      encode shape position worlds arrows shapes positions tree.val := rfl

theorem mem_naturalModel_iff {X : D} {root : HSet.{u}} :
    root ∈ (naturalModel shape position worlds arrows shapes positions X).carrier ↔
      ∃ tree : RawTree shape position X,
        ContextualWTypes.Natural shape position tree ∧ encode shape position worlds arrows shapes positions tree = root :=
  PresentedType.mem_restrict_carrier _ _ _

abbrev NaturalMembers (X : D) :=
  {root : HSet.{u} // root ∈ (naturalModel shape position worlds arrows shapes positions X).carrier}

def naturalMember {X : D} (tree : ContextualWTypes.NaturalTree shape position X) :
    NaturalMembers shape position worlds arrows shapes positions X :=
  (naturalModel shape position worlds arrows shapes positions X).decode.symm tree

theorem natural_decode_encode {X : D} (tree : ContextualWTypes.NaturalTree shape position X) :
    (naturalModel shape position worlds arrows shapes positions X).decode
      (naturalMember shape position worlds arrows shapes positions tree) = tree := Equiv.apply_symm_apply _ _

theorem natural_encode_decode {X : D} (root : NaturalMembers shape position worlds arrows shapes positions X) :
    naturalMember shape position worlds arrows shapes positions
      ((naturalModel shape position worlds arrows shapes positions X).decode root) = root := Equiv.symm_apply_apply _ _

/-- Actual material substitution retains the hereditary natural tree and
all of its future branches through the constructed inverse. -/
def naturalMap {X Y : D} (arrow : X ⟶ Y)
    (root : NaturalMembers shape position worlds arrows shapes positions X) :
    NaturalMembers shape position worlds arrows shapes positions Y :=
  naturalMember shape position worlds arrows shapes positions
    ((ContextualWTypes.family shape position).map arrow
      ((naturalModel shape position worlds arrows shapes positions X).decode root))

theorem naturalMap_decode {X Y : D} (arrow : X ⟶ Y)
    (root : NaturalMembers shape position worlds arrows shapes positions X) :
    (naturalModel shape position worlds arrows shapes positions Y).decode
        (naturalMap shape position worlds arrows shapes positions arrow root) =
      (ContextualWTypes.family shape position).map arrow
        ((naturalModel shape position worlds arrows shapes positions X).decode root) := natural_decode_encode _ _ _ _ _ _ _

theorem naturalMap_member {X Y : D} (arrow : X ⟶ Y)
    (tree : ContextualWTypes.NaturalTree shape position X) :
    naturalMap shape position worlds arrows shapes positions arrow
        (naturalMember shape position worlds arrows shapes positions tree) =
      naturalMember shape position worlds arrows shapes positions
        ((ContextualWTypes.family shape position).map arrow tree) := by
  unfold naturalMap
  rw [natural_decode_encode]

theorem naturalMap_id {X : D} (root : NaturalMembers shape position worlds arrows shapes positions X) :
    naturalMap shape position worlds arrows shapes positions (𝟙 X) root = root := by
  unfold naturalMap
  rw [(ContextualWTypes.family shape position).map_id X]
  exact natural_encode_decode _ _ _ _ _ _ root

theorem naturalMap_comp {X Y Z : D} (first : X ⟶ Y) (later : Y ⟶ Z)
    (root : NaturalMembers shape position worlds arrows shapes positions X) :
    naturalMap shape position worlds arrows shapes positions (first ≫ later) root =
      naturalMap shape position worlds arrows shapes positions later
        (naturalMap shape position worlds arrows shapes positions first root) := by
  apply (naturalModel shape position worlds arrows shapes positions Z).decode.injective
  rw [naturalMap_decode, naturalMap_decode, naturalMap_decode]
  exact congrArg (fun map => map ((naturalModel shape position worlds arrows shapes positions X).decode root))
    ((ContextualWTypes.family shape position).map_comp first later)

/-- The actual material contextual W family, including restriction maps. -/
def materialFamily : D ⥤ Type (u + 1) where
  obj := NaturalMembers shape position worlds arrows shapes positions
  map arrow := TypeCat.ofHom (naturalMap shape position worlds arrows shapes positions arrow)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    exact naturalMap_id shape position worlds arrows shapes positions
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    exact naturalMap_comp shape position worlds arrows shapes positions first later

theorem naturalMap_value {X Y : D} (arrow : X ⟶ Y)
    (tree : ContextualWTypes.NaturalTree shape position X) :
    (naturalMap shape position worlds arrows shapes positions arrow
      (naturalMember shape position worlds arrows shapes positions tree)).val =
      encode shape position worlds arrows shapes positions (ContextualWTypes.restrict shape position arrow tree.val) := by
  rw [naturalMap_member]
  rfl

/-- A natural constructor's actual branch entry records the externally
retained future world, arrow and dependent position. -/
theorem natural_sup_branch_entry {X Y : D} (label : shape.obj X)
    (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → ContextualWTypes.NaturalTree shape position Y)
    (naturality : ∀ (Y Z : D) (first : X ⟶ Y) (later : Y ⟶ Z) branch,
      ContextualWTypes.restrict shape position later (children Y first branch).val =
        (children Z (first ≫ later) (ContextualWTypes.positionAlong shape position label first later branch)).val)
    (arrow : X ⟶ Y) (branch : Position shape position label arrow) :
    HSet.kpair (ContextualWLabels.positionTag shape position worlds arrows shapes positions ⟨X, label⟩ ⟨Y, arrow, branch⟩)
        ((naturalModel shape position worlds arrows shapes positions Y).value (children Y arrow branch)) ∈
      (naturalModel shape position worlds arrows shapes positions X).value
        (ContextualWTypes.sup shape position label children naturality) := by
  exact (mem_encode_sup_iff shape position worlds arrows shapes positions label
    (fun Y arrow branch => (children Y arrow branch).val) _).mpr (Or.inr ⟨⟨Y, arrow, branch⟩, rfl⟩)

theorem excluded_nonnatural {X : D} (tree : RawTree shape position X)
    (notNatural : ¬ ContextualWTypes.Natural shape position tree) :
    encode shape position worlds arrows shapes positions tree ∉
      (naturalModel shape position worlds arrows shapes positions X).carrier := by
  intro member
  obtain ⟨other, natural, same⟩ := (mem_naturalModel_iff shape position worlds arrows shapes positions).mp member
  exact notNatural (encode_injective shape position worlds arrows shapes positions same ▸ natural)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWTypes
