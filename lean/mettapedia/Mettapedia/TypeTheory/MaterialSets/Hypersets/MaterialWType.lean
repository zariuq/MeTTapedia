import Mettapedia.TypeTheory.MaterialSets.Hypersets.LiftedFamilyModel
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedLabelledBisimulation
import Mettapedia.TypeTheory.FamilyEnclosingUniverse

/-!
# Material W-types with shape and dependent-position observations

Well-founded dependent trees are presented by labelled graphs at the raised
hyperset bound. Every root emits its actual shape value; every outgoing branch
emits its actual dependent position value before reaching the child tree.
Disjoint material tags distinguish shape observations from position steps.
The construction admits arbitrary position carriers, including infinite ones.

The material tree set collects these authored graphs. Bounded separation and
union reconstruct the original shape and each material child. Accessibility
of the material child relation then permits a decoder and dependent recursion
without selecting an encoding witness or a quotient representative.
The graph bound is `u + 1`; no same-level collection or native foundational
axiom package is inferred from this construction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialWType

open FamilyEnclosingUniverse
open LiftedFamilyModel (Elements)

universe u v

abbrev Tree (X : HSet.{u}) (B : Elements X → HSet.{u}) :=
  WTree (Elements X) (fun a => Elements (B a))

abbrev Label (X : HSet.{u}) (B : Elements X → HSet.{u}) :=
  Sum (Elements X) (Σ' a : Elements X, Elements (B a))

private theorem propositionalMembership :
    PropositionalMembership (fun x X : HSet.{u} => x ∈ X) := fun _ _ => inferInstance

def shapeTag (shape : HSet.{u}) : HSet.{u} := HSet.kpair ∅ shape
def positionTag (shape position : HSet.{u}) : HSet.{u} :=
  HSet.kpair {∅} (HSet.kpair shape position)

theorem shapeTag_ne_positionTag (shape shape' position : HSet.{u}) :
    shapeTag shape ≠ positionTag shape' position :=
  fun same => HSet.empty_ne_singleton_empty (HSet.kpair_inj.mp same).1

def labelValue {X : HSet.{u}} {B : Elements X → HSet.{u}} : Label X B → HSet.{u}
  | .inl a => shapeTag a.1
  | .inr ⟨a, p⟩ => positionTag a.1 p.1

theorem labelValue_injective {X : HSet.{u}} {B : Elements X → HSet.{u}} :
    Function.Injective (labelValue (X := X) (B := B)) := by
  intro first second same
  cases first with
  | inl a =>
    cases second with
    | inl a' => exact congrArg Sum.inl (El.ext propositionalMembership (HSet.kpair_inj.mp same).2)
    | inr pair => exact (shapeTag_ne_positionTag a.1 pair.1.1 pair.2.1 same).elim
  | inr pair =>
    cases second with
    | inl a => exact (shapeTag_ne_positionTag a.1 pair.1.1 pair.2.1 same.symm).elim
    | inr pair' =>
      rcases pair with ⟨a, p⟩
      rcases pair' with ⟨a', p'⟩
      have members := HSet.kpair_inj.mp (HSet.kpair_inj.mp same).2
      have shapes : a = a' := El.ext propositionalMembership members.1
      cases shapes
      have positions : p = p' := El.ext propositionalMembership members.2
      cases positions
      rfl

def labelReading {X : HSet.{u}} {B : Elements X → HSet.{u}} (label : Label X B) : HSet.{u + 1} :=
  HSet.lift (labelValue label)

theorem labelReading_injective {X : HSet.{u}} {B : Elements X → HSet.{u}} :
    Function.Injective (labelReading (X := X) (B := B)) :=
  fun _ _ same => labelValue_injective (HSet.lift_injective same)

def presentedLabels (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    HSet.PresentedLabels (labelReading (X := X) (B := B)) where
  graph label := HSet.presentationUp (labelValue label)
  mk_graph label := HSet.mk_presentationUp (labelValue label)

/-- The terminal state has no edges. Each tree has its shape observation
and precisely one labelled successor at every dependent position. -/
def edge {X : HSet.{u}} {B : Elements X → HSet.{u}} :
    Option (Tree X B) → Label X B → Option (Tree X B) → Prop
  | none, _, _ => False
  | some (.sup a children), label, target =>
    (label = .inl a ∧ target = none) ∨
      ∃ p : Elements (B a), label = .inr ⟨a, p⟩ ∧ target = some (children p)

def treeGraph {X : HSet.{u}} {B : Elements X → HSet.{u}} (tree : Tree X B) :
    AccessiblePointedGraph.{u + 1} :=
  AccessiblePointedGraph.generated ((presentedLabels X B).edge edge) (HSet.LabelCarrier.atom (some tree))

def encode {X : HSet.{u}} {B : Elements X → HSet.{u}} (tree : Tree X B) : HSet.{u + 1} :=
  (presentedLabels X B).decorate edge (some tree)

theorem mk_treeGraph {X : HSet.{u}} {B : Elements X → HSet.{u}} (tree : Tree X B) :
    HSet.mk (treeGraph tree) = encode tree := rfl

theorem decorate_terminal (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    (presentedLabels X B).decorate edge none = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro z member
  obtain ⟨label, target, impossible, _⟩ := (presentedLabels X B).mem_decorate.mp member
  exact impossible

/-- The exact membership equation retains the shape and every branch address. -/
theorem mem_encode_sup_iff {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (children : Elements (B a) → Tree X B) (z : HSet.{u + 1}) :
    z ∈ encode (.sup a children) ↔
      z = HSet.kpair (HSet.lift (shapeTag a.1)) ∅ ∨
        ∃ p : Elements (B a), z = HSet.kpair (HSet.lift (positionTag a.1 p.1)) (encode (children p)) := by
  rw [encode, (presentedLabels X B).mem_decorate]
  constructor
  · rintro ⟨label, target, step, same⟩
    rcases step with ⟨rfl, rfl⟩ | ⟨p, rfl, rfl⟩
    · exact Or.inl (same.trans (congrArg (HSet.kpair _) (decorate_terminal X B)))
    · exact Or.inr ⟨p, same⟩
  · rintro (same | ⟨p, same⟩)
    · refine ⟨.inl a, none, Or.inl ⟨rfl, rfl⟩, ?_⟩
      exact same.trans (congrArg (HSet.kpair _) (decorate_terminal X B)).symm
    · exact ⟨.inr ⟨a, p⟩, some (children p), Or.inr ⟨p, rfl, rfl⟩, same⟩

/-- All actual authored tree graphs are collected at the raised bound. -/
def materialW (X : HSet.{u}) (B : Elements X → HSet.{u}) : HSet.{u + 1} :=
  HSet.range (treeGraph (X := X) (B := B))

theorem mem_materialW_iff {X : HSet.{u}} {B : Elements X → HSet.{u}} {z : HSet.{u + 1}} :
    z ∈ materialW X B ↔ ∃ tree : Tree X B, encode tree = z := HSet.mem_range

def treeMember {X : HSet.{u}} {B : Elements X → HSet.{u}} (tree : Tree X B) :
    Elements (materialW X B) := ⟨encode tree, mem_materialW_iff.mpr ⟨tree, rfl⟩⟩

theorem shapeObservation_sup_iff {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (children : Elements (B a) → Tree X B) (original : HSet.{u}) :
    HSet.kpair (HSet.lift (shapeTag original)) ∅ ∈ encode (.sup a children) ↔ original = a.1 := by
  rw [mem_encode_sup_iff]
  constructor
  · rintro (same | ⟨p, same⟩)
    · exact (HSet.kpair_inj.mp (HSet.lift_injective (HSet.kpair_inj.mp same).1)).2
    · exact (shapeTag_ne_positionTag original a.1 p.1
        (HSet.lift_injective (HSet.kpair_inj.mp same).1)).elim
  · intro same
    exact Or.inl (congrArg (fun original => HSet.kpair (HSet.lift (shapeTag original)) ∅) same)

theorem positionObservation_sup_iff {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (children : Elements (B a) → Tree X B)
    (p : Elements (B a)) (childValue : HSet.{u + 1}) :
    HSet.kpair (HSet.lift (positionTag a.1 p.1)) childValue ∈ encode (.sup a children) ↔
      childValue = encode (children p) := by
  rw [mem_encode_sup_iff]
  constructor
  · rintro (same | ⟨p', same⟩)
    · exact (shapeTag_ne_positionTag a.1 a.1 p.1
        (HSet.lift_injective (HSet.kpair_inj.mp same).1).symm).elim
    · have positions : p = p' := El.ext propositionalMembership
        (HSet.kpair_inj.mp (HSet.kpair_inj.mp (HSet.lift_injective (HSet.kpair_inj.mp same).1)).2).2
      cases positions
      exact (HSet.kpair_inj.mp same).2
  · intro same
    exact Or.inr ⟨p, congrArg (HSet.kpair _) same⟩

def shapeValue (X : HSet.{u}) (root : HSet.{u + 1}) : HSet.{u} :=
  HSet.sUnion (HSet.sep (fun original =>
    HSet.kpair (HSet.lift (shapeTag original)) ∅ ∈ root) X)

theorem shapeValue_encode_sup {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (children : Elements (B a) → Tree X B) :
    shapeValue X (encode (.sup a children)) = a.1 := by
  have separated : HSet.sep (fun original => HSet.kpair (HSet.lift (shapeTag original)) ∅ ∈
      encode (.sup a children)) X = {a.1} := by
    apply HSet.ext
    intro original
    rw [HSet.mem_sep, shapeObservation_sup_iff, HSet.mem_singleton]
    exact ⟨And.right, fun same => ⟨same ▸ a.2, same⟩⟩
  exact (congrArg HSet.sUnion separated).trans (HSet.sUnion_singleton _)

/-- Reconstruct the original shape under its original material bound.
An encoding witness is used only to prove membership of this explicit value. -/
def shape {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (root : Elements (materialW X B)) : Elements X :=
  ⟨shapeValue X root.1, by
    obtain ⟨tree, same⟩ := mem_materialW_iff.mp root.2
    rcases tree with ⟨a, children⟩
    rw [← same, shapeValue_encode_sup]
    exact a.2⟩

theorem shape_treeMember_sup {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (children : Elements (B a) → Tree X B) :
    shape (treeMember (.sup a children)) = a :=
  El.ext propositionalMembership (shapeValue_encode_sup a children)

def childRow (X : HSet.{u}) (B : Elements X → HSet.{u})
    (root : HSet.{u + 1}) (originalShape originalPosition : HSet.{u}) : HSet.{u + 1} :=
  HSet.sep (fun child => HSet.kpair (HSet.lift (positionTag originalShape originalPosition)) child ∈ root)
    (materialW X B)

theorem childRow_encode_sup {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (children : Elements (B a) → Tree X B) (p : Elements (B a)) :
    childRow X B (encode (.sup a children)) a.1 p.1 = {encode (children p)} := by
  apply HSet.ext
  intro childValue
  rw [childRow, HSet.mem_sep, positionObservation_sup_iff, HSet.mem_singleton]
  exact ⟨And.right, fun same => ⟨same ▸ (treeMember (children p)).2, same⟩⟩

/-- Recover a child by union of its separated singleton row inside the
actual constructed W set. The result is an actual material W member. -/
def child {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (root : Elements (materialW X B)) (p : Elements (B (shape root))) :
    Elements (materialW X B) :=
  ⟨HSet.sUnion (childRow X B root.1 (shape root).1 p.1), by
    obtain ⟨tree, same⟩ := mem_materialW_iff.mp root.2
    have memberEq : root = treeMember tree := El.ext propositionalMembership same.symm
    cases memberEq
    rcases tree with ⟨a, children⟩
    let p' : Elements (B a) := transport (congrArg B (shape_treeMember_sup a children)) p
    have positionValue : p.1 = p'.1 := (transport_fst _ p).symm
    have rowEq := (congrArg₂ (childRow X B (encode (.sup a children)))
      (congrArg PSigma.fst (shape_treeMember_sup a children)) positionValue).trans
      (childRow_encode_sup a children p')
    have value := (congrArg HSet.sUnion rowEq).trans (HSet.sUnion_singleton _)
    exact value.symm ▸ (treeMember (children p')).2⟩

theorem child_treeMember_sup {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (children : Elements (B a) → Tree X B)
    (p : Elements (B (shape (treeMember (.sup a children))))) :
    child (treeMember (.sup a children)) p =
      treeMember (children (transport (congrArg B (shape_treeMember_sup a children)) p)) := by
  apply El.ext propositionalMembership
  change HSet.sUnion (childRow X B (encode (.sup a children))
    (shape (treeMember (.sup a children))).1 p.1) = _
  have positionValue : p.1 =
      (transport (congrArg B (shape_treeMember_sup a children)) p).1 := (transport_fst _ p).symm
  exact (congrArg HSet.sUnion ((congrArg₂ (childRow X B (encode (.sup a children)))
    (congrArg PSigma.fst (shape_treeMember_sup a children)) positionValue).trans
    (childRow_encode_sup a children _))).trans (HSet.sUnion_singleton _)

/-- Immediate material-child membership retains the dependent position. -/
def Child {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (subtree root : Elements (materialW X B)) : Prop :=
  ∃ p : Elements (B (shape root)), subtree = child root p

theorem accessible_treeMember {X : HSet.{u}} {B : Elements X → HSet.{u}} (tree : Tree X B) :
    Acc (Child (X := X) (B := B)) (treeMember tree) := by
  induction tree with
  | sup a children ih =>
    refine Acc.intro _ ?_
    intro subtree predecessor
    obtain ⟨p, rfl⟩ := predecessor
    exact (child_treeMember_sup a children p).symm ▸
      ih (transport (congrArg B (shape_treeMember_sup a children)) p)

/-- Existential encoding membership proves accessibility in Prop. No tree
witness is selected to define a value or a decoder. -/
theorem accessible {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (root : Elements (materialW X B)) : Acc (Child (X := X) (B := B)) root := by
  obtain ⟨tree, same⟩ := mem_materialW_iff.mp root.2
  have memberEq : root = treeMember tree := El.ext propositionalMembership same.symm
  exact memberEq.symm ▸ accessible_treeMember tree

def decodeAcc {X : HSet.{u}} {B : Elements X → HSet.{u}} {root : Elements (materialW X B)}
    (available : Acc (Child (X := X) (B := B)) root) : Tree X B :=
  Acc.rec (motive := fun _ _ => Tree X B)
    (fun parent _ earlier => .sup (shape parent) (fun p => earlier (child parent p) ⟨p, rfl⟩)) available

theorem decodeAcc_eq {X : HSet.{u}} {B : Elements X → HSet.{u}} {root : Elements (materialW X B)}
    (available : Acc (Child (X := X) (B := B)) root) :
    decodeAcc available = .sup (shape root)
      (fun p => decodeAcc (available.inv (⟨p, rfl⟩ : Child (child root p) root))) := by
  cases available
  rfl

/-- A genuine decoder is obtained by accessibility recursion over actual
material children, not by choosing the existential encoding witness. -/
def decode {X : HSet.{u}} {B : Elements X → HSet.{u}} (root : Elements (materialW X B)) : Tree X B :=
  decodeAcc (accessible root)

theorem decode_eq {X : HSet.{u}} {B : Elements X → HSet.{u}} (root : Elements (materialW X B)) :
    decode root = .sup (shape root) (fun p => decode (child root p)) := decodeAcc_eq (accessible root)

private theorem sup_eq_of_transport {X : HSet.{u}} {B : Elements X → HSet.{u}}
    {first second : Elements X} (same : first = second)
    (left : Elements (B first) → Tree X B) (right : Elements (B second) → Tree X B)
    (children : ∀ p, left p = right (transport (congrArg B same) p)) :
    (WTree.sup first left : Tree X B) = WTree.sup second right := by
  cases same
  exact congrArg (WTree.sup first) (funext children)

/-- The accessibility decoder reconstructs every actual dependent tree,
including all of its arbitrarily many positions. -/
theorem decode_treeMember {X : HSet.{u}} {B : Elements X → HSet.{u}} (tree : Tree X B) :
    decode (treeMember tree) = tree := by
  induction tree with
  | sup a children ih =>
    apply (decode_eq (treeMember (.sup a children))).trans
    apply sup_eq_of_transport (shape_treeMember_sup a children)
    intro p
    exact (congrArg decode (child_treeMember_sup a children p)).trans
      (ih (transport (congrArg B (shape_treeMember_sup a children)) p))

theorem treeMember_decode {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (root : Elements (materialW X B)) : treeMember (decode root) = root := by
  obtain ⟨tree, same⟩ := mem_materialW_iff.mp root.2
  have memberEq : root = treeMember tree := El.ext propositionalMembership same.symm
  cases memberEq
  exact congrArg treeMember (decode_treeMember tree)

/-- Both inverse operations are constructed, rather than extracted from
propositional bijectivity. -/
def materialWEquiv (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Elements (materialW X B) ≃ Tree X B where
  toFun := decode
  invFun := treeMember
  left_inv := treeMember_decode
  right_inv := decode_treeMember

theorem encode_injective {X : HSet.{u}} {B : Elements X → HSet.{u}} :
    Function.Injective (encode (X := X) (B := B)) := by
  intro first second same
  have members : treeMember first = treeMember second := El.ext propositionalMembership same
  exact (decode_treeMember first).symm.trans ((congrArg decode members).trans (decode_treeMember second))

theorem encode_eq_iff_tree_eq {X : HSet.{u}} {B : Elements X → HSet.{u}} {first second : Tree X B} :
    encode first = encode second ↔ first = second :=
  ⟨fun same => encode_injective (X := X) (B := B) same, congrArg encode⟩

theorem encode_eq_iff_labelledBisimilar {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (first second : Tree X B) :
    encode first = encode second ↔ LabelledBisimilar edge edge
      (labelReading (X := X) (B := B)) labelReading (some first) (some second) :=
  (presentedLabels X B).decorate_eq_iff_labelledBisimilar (presentedLabels X B)

/-- Labelled bisimilarity coincides with dependent-tree equality for this
encoding. Shape/position readout injectivity prevents unlabelled bag erasure. -/
theorem labelledBisimilar_iff_tree_eq {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (first second : Tree X B) :
    LabelledBisimilar edge edge (labelReading (X := X) (B := B)) labelReading (some first) (some second) ↔
      first = second := (encode_eq_iff_labelledBisimilar first second).symm.trans encode_eq_iff_tree_eq

/-- The raised material W member carrier has its constructed original tree
model at the smaller host level. -/
theorem materialW_members_small (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Small.{u + 1} (Elements (materialW X B)) := Small.mk' (materialWEquiv X B)

/-- Material construction uses the explicit authored graph of the decoded
children; its computation will recover the supplied actual child members. -/
def node {X : HSet.{u}} {B : Elements X → HSet.{u}} (a : Elements X)
    (children : Elements (B a) → Elements (materialW X B)) : Elements (materialW X B) :=
  treeMember (.sup a (fun p => decode (children p)))

theorem decode_node {X : HSet.{u}} {B : Elements X → HSet.{u}} (a : Elements X)
    (children : Elements (B a) → Elements (materialW X B)) :
    decode (node a children) = .sup a (fun p => decode (children p)) := decode_treeMember _

theorem shape_node {X : HSet.{u}} {B : Elements X → HSet.{u}} (a : Elements X)
    (children : Elements (B a) → Elements (materialW X B)) : shape (node a children) = a :=
  shape_treeMember_sup _ _

theorem child_node {X : HSet.{u}} {B : Elements X → HSet.{u}} (a : Elements X)
    (children : Elements (B a) → Elements (materialW X B))
    (p : Elements (B (shape (node a children)))) :
    child (node a children) p = children (transport (congrArg B (shape_node a children)) p) :=
  (child_treeMember_sup _ _ p).trans (treeMember_decode _)

theorem node_eta {X : HSet.{u}} {B : Elements X → HSet.{u}} (root : Elements (materialW X B)) :
    node (shape root) (child root) = root :=
  (congrArg treeMember (decode_eq root).symm).trans (treeMember_decode root)

private theorem functions_heq_of_transport {X : HSet.{u}} {B : Elements X → HSet.{u}}
    {first second : Elements X} (same : first = second)
    (left : Elements (B first) → Elements (materialW X B))
    (right : Elements (B second) → Elements (materialW X B))
    (children : ∀ p, left p = right (transport (congrArg B same) p)) : HEq left right := by
  cases same
  exact heq_of_eq (funext children)

abbrev Arguments (X : HSet.{u}) (B : Elements X → HSet.{u}) :=
  Σ' a : Elements X, Elements (B a) → Elements (materialW X B)

def construct {X : HSet.{u}} {B : Elements X → HSet.{u}} (arguments : Arguments X B) :
    Elements (materialW X B) := node arguments.1 arguments.2

def destruct {X : HSet.{u}} {B : Elements X → HSet.{u}} (root : Elements (materialW X B)) :
    Arguments X B := ⟨shape root, child root⟩

theorem destruct_construct {X : HSet.{u}} {B : Elements X → HSet.{u}} (arguments : Arguments X B) :
    destruct (construct arguments) = arguments :=
  PSigma.ext (shape_node arguments.1 arguments.2)
    (functions_heq_of_transport (shape_node arguments.1 arguments.2) _ _ (child_node _ _))

theorem construct_destruct {X : HSet.{u}} {B : Elements X → HSet.{u}} (root : Elements (materialW X B)) :
    construct (destruct root) = root := node_eta root

/-- The constructor/destructor polynomial comparison accounts for the
actual original shape, dependent position family and every material child. -/
def constructorEquiv (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Arguments X B ≃ Elements (materialW X B) where
  toFun := construct
  invFun := destruct
  left_inv := destruct_construct
  right_inv := construct_destruct

abbrev Step {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (motive : Elements (materialW X B) → Sort v) :=
  (a : Elements X) → (children : Elements (B a) → Elements (materialW X B)) →
    ((p : Elements (B a)) → motive (children p)) → motive (node a children)

def eliminateAcc {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (motive : Elements (materialW X B) → Sort v) (step : Step motive)
    {root : Elements (materialW X B)} (available : Acc (Child (X := X) (B := B)) root) : motive root :=
  Acc.rec (motive := fun root _ => motive root)
    (fun parent _ earlier => (node_eta parent) ▸
      step (shape parent) (child parent) (fun p => earlier (child parent p) ⟨p, rfl⟩)) available

/-- Full dependent elimination over an arbitrary motive on actual material
tree members. Accessibility supplies recursion independently of the motive. -/
def eliminate {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (motive : Elements (materialW X B) → Sort v) (step : Step motive)
    (root : Elements (materialW X B)) : motive root := eliminateAcc motive step (accessible root)

theorem eliminateAcc_eq {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (motive : Elements (materialW X B) → Sort v) (step : Step motive)
    {root : Elements (materialW X B)} (available : Acc (Child (X := X) (B := B)) root) :
    eliminateAcc motive step available = (node_eta root) ▸
      step (shape root) (child root)
        (fun p => eliminateAcc motive step (available.inv (⟨p, rfl⟩ : Child (child root p) root))) := by
  cases available
  rfl

theorem eliminate_eq {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (motive : Elements (materialW X B) → Sort v) (step : Step motive)
    (root : Elements (materialW X B)) : eliminate motive step root = (node_eta root) ▸
      step (shape root) (child root) (fun p => eliminate motive step (child root p)) :=
  eliminateAcc_eq motive step (accessible root)

private theorem step_transport {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (motive : Elements (materialW X B) → Sort v) (step : Step motive)
    {first second : Arguments X B} (same : first = second)
    (earlier : (root : Elements (materialW X B)) → motive root) :
    Eq.ndrec (motive := motive) (step first.1 first.2 (fun p => earlier (first.2 p)))
      (congrArg construct same) =
      step second.1 second.2 (fun p => earlier (second.2 p)) := by
  cases same
  rfl

/-- Full dependent beta computes at material construction, with the actual
supplied children. Equality transport is discharged by the proved polynomial
constructor/destructor inverse, not by a restriction to constant motives. -/
theorem eliminate_beta {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (motive : Elements (materialW X B) → Sort v) (step : Step motive)
    (a : Elements X) (children : Elements (B a) → Elements (materialW X B)) :
    eliminate motive step (node a children) =
      step a children (fun p => eliminate motive step (children p)) :=
  (eliminate_eq motive step (node a children)).trans
    (step_transport motive step (destruct_construct ⟨a, children⟩) (eliminate motive step))

def fold {X : HSet.{u}} {B : Elements X → HSet.{u}} {C : Sort v}
    (step : (a : Elements X) → (Elements (B a) → C) → C) : Elements (materialW X B) → C :=
  eliminate (fun _ => C) (fun a _ earlier => step a earlier)

theorem fold_beta {X : HSet.{u}} {B : Elements X → HSet.{u}} {C : Sort v}
    (step : (a : Elements X) → (Elements (B a) → C) → C)
    (a : Elements X) (children : Elements (B a) → Elements (materialW X B)) :
    fold step (node a children) = step a (fun p => fold step (children p)) :=
  eliminate_beta _ _ _ _

/-- Every algebra receives a unique homomorphism from this actual material
W algebra. The proof uses its proved full dependent eliminator. -/
theorem fold_unique {X : HSet.{u}} {B : Elements X → HSet.{u}} {C : Sort v}
    (step : (a : Elements X) → (Elements (B a) → C) → C)
    (candidate : Elements (materialW X B) → C)
    (homomorphism : ∀ a children, candidate (node a children) = step a (fun p => candidate (children p))) :
    candidate = fold step := by
  funext root
  apply eliminate (fun root => candidate root = fold step root) _ root
  intro a children earlier
  exact (homomorphism a children).trans
    ((congrArg (step a) (funext earlier)).trans (fold_beta step a children).symm)

/-! ## Substitution of shapes and dependent positions -/

/-- Shape maps are covariant; target positions pull back to source positions.
This structural substitution retains exactly that dependent variance. -/
def mapTree {X Y : HSet.{u}} {B : Elements X → HSet.{u}} {C : Elements Y → HSet.{u}}
    (shapes : Elements X → Elements Y)
    (positions : (a : Elements X) → Elements (C (shapes a)) → Elements (B a)) : Tree X B → Tree Y C
  | .sup a children => .sup (shapes a) (fun p => mapTree shapes positions (children (positions a p)))

theorem mapTree_id {X : HSet.{u}} {B : Elements X → HSet.{u}} (tree : Tree X B) :
    mapTree id (fun _ p => p) tree = tree := by
  induction tree with
  | sup a children ih => exact congrArg (WTree.sup a) (funext ih)

theorem mapTree_comp {X Y Z : HSet.{u}} {B : Elements X → HSet.{u}}
    {C : Elements Y → HSet.{u}} {D : Elements Z → HSet.{u}}
    (first : Elements X → Elements Y) (second : Elements Y → Elements Z)
    (firstPositions : (a : Elements X) → Elements (C (first a)) → Elements (B a))
    (secondPositions : (b : Elements Y) → Elements (D (second b)) → Elements (C b)) (tree : Tree X B) :
    mapTree (second ∘ first) (fun a p => firstPositions a (secondPositions (first a) p)) tree =
      mapTree second secondPositions (mapTree first firstPositions tree) := by
  induction tree with
  | sup a children ih =>
    exact congrArg (WTree.sup (second (first a)))
      (funext fun p => ih (firstPositions a (secondPositions (first a) p)))

/-- Actual material substitution is constructed through the proved decoder
and the authored graph of the substituted tree. -/
def reindex {X Y : HSet.{u}} {B : Elements X → HSet.{u}} {C : Elements Y → HSet.{u}}
    (shapes : Elements X → Elements Y)
    (positions : (a : Elements X) → Elements (C (shapes a)) → Elements (B a))
    (root : Elements (materialW X B)) : Elements (materialW Y C) :=
  treeMember (mapTree shapes positions (decode root))

theorem decode_reindex {X Y : HSet.{u}} {B : Elements X → HSet.{u}} {C : Elements Y → HSet.{u}}
    (shapes : Elements X → Elements Y)
    (positions : (a : Elements X) → Elements (C (shapes a)) → Elements (B a))
    (root : Elements (materialW X B)) :
    decode (reindex shapes positions root) = mapTree shapes positions (decode root) := decode_treeMember _

theorem reindex_node {X Y : HSet.{u}} {B : Elements X → HSet.{u}} {C : Elements Y → HSet.{u}}
    (shapes : Elements X → Elements Y)
    (positions : (a : Elements X) → Elements (C (shapes a)) → Elements (B a))
    (a : Elements X) (children : Elements (B a) → Elements (materialW X B)) :
    reindex shapes positions (node a children) =
      node (shapes a) (fun p => reindex shapes positions (children (positions a p))) := by
  apply (materialWEquiv Y C).injective
  change decode _ = decode _
  rw [decode_reindex, decode_node, decode_node]
  exact congrArg (WTree.sup (shapes a)) (funext fun p => (decode_reindex shapes positions _).symm)

theorem reindex_id {X : HSet.{u}} {B : Elements X → HSet.{u}} (root : Elements (materialW X B)) :
    reindex id (fun _ p => p) root = root :=
  (congrArg treeMember (mapTree_id (decode root))).trans (treeMember_decode root)

theorem reindex_comp {X Y Z : HSet.{u}} {B : Elements X → HSet.{u}}
    {C : Elements Y → HSet.{u}} {D : Elements Z → HSet.{u}}
    (first : Elements X → Elements Y) (second : Elements Y → Elements Z)
    (firstPositions : (a : Elements X) → Elements (C (first a)) → Elements (B a))
    (secondPositions : (b : Elements Y) → Elements (D (second b)) → Elements (C b))
    (root : Elements (materialW X B)) :
    reindex (second ∘ first) (fun a p => firstPositions a (secondPositions (first a) p)) root =
      reindex second secondPositions (reindex first firstPositions root) := by
  apply (materialWEquiv Z D).injective
  change decode _ = decode _
  rw [decode_reindex, decode_reindex, decode_reindex]
  exact mapTree_comp first second firstPositions secondPositions _

/-- Reindex the entire dependent algebra step using the actual material
constructor/substitution square and the pulled-back positions. -/
def reindexStep {X Y : HSet.{u}} {B : Elements X → HSet.{u}} {C : Elements Y → HSet.{u}}
    (shapes : Elements X → Elements Y)
    (positions : (a : Elements X) → Elements (C (shapes a)) → Elements (B a))
    (motive : Elements (materialW Y C) → Sort v) (step : Step motive) :
    Step (fun root => motive (reindex shapes positions root)) :=
  fun a children earlier => Eq.ndrec (motive := motive)
    (step (shapes a) (fun p => reindex shapes positions (children (positions a p)))
      (fun p => earlier (positions a p))) (reindex_node shapes positions a children).symm

private theorem dependentValue_transport {I : Sort u} {motive : I → Sort v}
    (sectionValue : (i : I) → motive i) {first second : I} (same : first = second) :
    Eq.ndrec (motive := motive) (sectionValue first) same = sectionValue second := by
  cases same
  rfl

/-- Full dependent material W elimination commutes with actual substitution
of shapes and the contravariant dependent-position maps. The motive and all
recursive child values are retained across the proved constructor square. -/
theorem eliminate_reindex {X Y : HSet.{u}} {B : Elements X → HSet.{u}} {C : Elements Y → HSet.{u}}
    (shapes : Elements X → Elements Y)
    (positions : (a : Elements X) → Elements (C (shapes a)) → Elements (B a))
    (motive : Elements (materialW Y C) → Sort v) (step : Step motive) (root : Elements (materialW X B)) :
    eliminate motive step (reindex shapes positions root) =
      eliminate (fun root => motive (reindex shapes positions root))
        (reindexStep shapes positions motive step) root := by
  apply eliminate (fun root => eliminate motive step (reindex shapes positions root) =
    eliminate (fun root => motive (reindex shapes positions root))
      (reindexStep shapes positions motive step) root) _ root
  intro a children earlier
  let targetChildren := fun p => reindex shapes positions (children (positions a p))
  let square := reindex_node shapes positions a children
  let castBack := fun value : motive (node (shapes a) targetChildren) =>
    Eq.ndrec (motive := motive) value square.symm
  calc
    _ = castBack (eliminate motive step (node (shapes a) targetChildren)) :=
      (dependentValue_transport (eliminate motive step) square.symm).symm
    _ = castBack (step (shapes a) targetChildren (fun p => eliminate motive step (targetChildren p))) :=
      congrArg castBack (eliminate_beta motive step _ _)
    _ = castBack (step (shapes a) targetChildren (fun p =>
        eliminate (fun root => motive (reindex shapes positions root))
          (reindexStep shapes positions motive step) (children (positions a p)))) :=
      congrArg castBack (congrArg (step (shapes a) targetChildren)
        (funext fun p => earlier (positions a p)))
    _ = _ := (eliminate_beta (fun root => motive (reindex shapes positions root))
      (reindexStep shapes positions motive step) a children).symm

/-! ## Positive and negative interpretation controls -/

/-- The material structural-child relation is well founded, even when
observed shape or position values themselves have membership cycles. -/
theorem materialChild_wellFounded (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    WellFounded (Child (X := X) (B := B)) := ⟨accessible⟩

theorem child_not_self {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (root : Elements (materialW X B)) : ¬ Child root root := by
  have available := accessible root
  induction available with
  | intro root _ earlier =>
    intro selfChild
    exact earlier root selfChild selfChild

/-- A signature with a position at every shape has no well-founded tree.
Existentially inhabited positions are eliminated only into this proposition. -/
theorem no_tree_of_all_positions_inhabited {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (positions : ∀ a, Nonempty (Elements (B a))) (tree : Tree X B) : False := by
  induction tree with
  | sup a _ earlier =>
    obtain ⟨p⟩ := positions a
    exact earlier p

theorem materialW_empty_of_all_positions_inhabited {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (positions : ∀ a, Nonempty (Elements (B a))) : materialW X B = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  obtain ⟨tree, _⟩ := mem_materialW_iff.mp member
  exact no_tree_of_all_positions_inhabited positions tree

theorem materialW_empty_domain (B : Elements (∅ : HSet.{u}) → HSet.{u}) : materialW ∅ B = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  obtain ⟨tree, _⟩ := mem_materialW_iff.mp member
  rcases tree with ⟨a, _⟩
  exact HSet.notMem_empty a.1 a.2

def leaf {X : HSet.{u}} {B : Elements X → HSet.{u}} (a : Elements X) (empty : B a = ∅) : Tree X B :=
  .sup a (fun p => (HSet.notMem_empty p.1 (empty ▸ p.2)).elim)

/-- One leaf is placed at every position of the branch shape. The carrier
of these positions is arbitrary; no finiteness bound enters the construction. -/
def star {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (branch leafShape : Elements X) (empty : B leafShape = ∅) : Tree X B :=
  .sup branch (fun _ => leaf leafShape empty)

theorem star_child {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (branch leafShape : Elements X) (empty : B leafShape = ∅)
    (p : Elements (B (shape (treeMember (star branch leafShape empty))))) :
    child (treeMember (star branch leafShape empty)) p = treeMember (leaf leafShape empty) :=
  child_treeMember_sup _ _ p

def quineShape : Elements ({HSet.quineAtom.{u}} : HSet.{u}) :=
  ⟨HSet.quineAtom, HSet.mem_singleton_self _⟩

def quinePositions (_ : Elements ({HSet.quineAtom.{u}} : HSet.{u})) : HSet.{u} := ∅

def quineLeaf : Tree {HSet.quineAtom.{u}} quinePositions := leaf quineShape rfl

theorem quineLeaf_shape : shape (treeMember quineLeaf.{u}) = quineShape := shape_treeMember_sup _ _

/-- A structurally well-founded material tree can retain a non-well-founded
shape observation. These are different foundation predicates. -/
theorem quineLeaf_not_materialWF : ¬ (encode quineLeaf.{u}).WF := by
  intro founded
  have emitted : HSet.kpair (HSet.lift (shapeTag HSet.quineAtom.{u})) ∅ ∈ encode quineLeaf :=
    (mem_encode_sup_iff _ _ _).mpr (Or.inl rfl)
  have labelFounded := (founded.mem emitted).fst
  rw [HSet.fst_kpair] at labelFounded
  change (HSet.lift (HSet.kpair ∅ HSet.quineAtom.{u})).WF at labelFounded
  rw [HSet.lift_kpair] at labelFounded
  have atomFounded := labelFounded.snd
  rw [HSet.snd_kpair, HSet.lift_quineAtom] at atomFounded
  exact HSet.not_wf_quineAtom atomFounded

theorem quineLeaf_structuralAcc_not_materialWF :
    Acc Child (treeMember quineLeaf.{u}) ∧ ¬ (treeMember quineLeaf).1.WF :=
  ⟨accessible_treeMember quineLeaf, quineLeaf_not_materialWF⟩

/-- Removing branch addresses leaves the same bag of child observations
under every supplied position permutation. -/
theorem position_permutation_same_child_bag {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (children : Elements (B a) → Tree X B)
    (permutation : Elements (B a) ≃ Elements (B a)) (observation : HSet.{u + 1}) :
    (∃ p, encode (children p) = observation) ↔
      ∃ p, encode (children (permutation p)) = observation := by
  constructor
  · rintro ⟨p, same⟩
    exact ⟨permutation.symm p, (congrArg (fun p => encode (children p))
      (permutation.apply_symm_apply p)).trans same⟩
  · rintro ⟨p, same⟩
    exact ⟨permutation p, same⟩

/-- The actual tree encoding retains the branch address, so a permutation
that changes a child is not erased despite its unchanged unlabelled bag. -/
theorem position_permutation_changes_encoding {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (children : Elements (B a) → Tree X B)
    (permutation : Elements (B a) ≃ Elements (B a)) (p : Elements (B a))
    (different : children p ≠ children (permutation p)) :
    encode (.sup a children) ≠ encode (.sup a (fun p => children (permutation p))) := by
  intro same
  have observed : HSet.kpair (HSet.lift (positionTag a.1 p.1)) (encode (children p)) ∈
      encode (.sup a children) := (positionObservation_sup_iff a children p _).mpr rfl
  rw [same] at observed
  exact different (encode_injective ((positionObservation_sup_iff a _ p _).mp observed))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialWType
