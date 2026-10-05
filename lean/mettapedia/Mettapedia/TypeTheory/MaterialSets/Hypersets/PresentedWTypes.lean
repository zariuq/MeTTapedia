import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedTypeOperations
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedLabelledBisimulation
import Mettapedia.TypeTheory.FamilyEnclosingUniverse

/-!
# Same-bound material W formation from constructed term graphs

Small semantic shape and position carriers, already presented as actual
material types, supply every label graph. The authored dependent tree graphs
and their collected material set therefore retain the same graph bound.
Bounded shape and child readout, followed by accessibility recursion, constructs
the inverse without selecting an encoding witness. Position labels retain
every branch address, including arbitrarily large position carriers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedType.W

open Mettapedia.TypeTheory.FamilyEnclosingUniverse

universe u v

variable {A : Type u} {B : A → Type u}
variable (domain : PresentedType A) (fibres : (a : A) → PresentedType (B a))

abbrev Tree := WTree A B
abbrev Label := Sum A (Sigma B)

def shapeTag (a : A) : HSet.{u} := HSet.kpair ∅ (domain.value a)
def positionTag (a : A) (p : B a) : HSet.{u} :=
  HSet.kpair {∅} (HSet.kpair (domain.value a) ((fibres a).value p))

theorem shapeTag_ne_positionTag (a b : A) (p : B b) :
    shapeTag domain a ≠ positionTag domain fibres b p :=
  fun same => HSet.empty_ne_singleton_empty (HSet.kpair_inj.mp same).1

def labelValue : Label (A := A) (B := B) → HSet.{u}
  | .inl a => shapeTag domain a
  | .inr ⟨a, p⟩ => positionTag domain fibres a p

theorem labelValue_injective : Function.Injective (labelValue domain fibres) := by
  intro first second same
  cases first with
  | inl a =>
    cases second with
    | inl b => exact congrArg Sum.inl (domain.value_injective (HSet.kpair_inj.mp same).2)
    | inr pair => exact (shapeTag_ne_positionTag domain fibres a pair.1 pair.2 same).elim
  | inr pair =>
    cases second with
    | inl a => exact (shapeTag_ne_positionTag domain fibres a pair.1 pair.2 same.symm).elim
    | inr pair' =>
      rcases pair with ⟨a, p⟩
      rcases pair' with ⟨b, q⟩
      have members := HSet.kpair_inj.mp (HSet.kpair_inj.mp same).2
      have shapes : a = b := domain.value_injective members.1
      cases shapes
      have positions : p = q := (fibres a).value_injective members.2
      cases positions
      rfl

def labelGraph : Label (A := A) (B := B) → AccessiblePointedGraph.{u}
  | .inl a => AccessiblePointedGraph.kpairGraph AccessiblePointedGraph.empty (domain.termGraph a)
  | .inr ⟨a, p⟩ => AccessiblePointedGraph.kpairGraph
      (AccessiblePointedGraph.singletonGraph AccessiblePointedGraph.empty)
      (AccessiblePointedGraph.kpairGraph (domain.termGraph a) ((fibres a).termGraph p))

theorem mk_labelGraph (label : Label (A := A) (B := B)) :
    HSet.mk (labelGraph domain fibres label) = labelValue domain fibres label := by
  cases label with
  | inl a =>
    rw [labelGraph, AccessiblePointedGraph.mk_kpairGraph, HSet.mk_empty, mk_termGraph]
    rfl
  | inr pair =>
    rw [labelGraph, AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_singletonGraph,
      HSet.mk_empty, AccessiblePointedGraph.mk_kpairGraph, mk_termGraph, mk_termGraph]
    rfl

def labels : HSet.PresentedLabels (labelValue domain fibres) :=
  ⟨labelGraph domain fibres, mk_labelGraph domain fibres⟩

def edge : Option (Tree (A := A) (B := B)) → Label (A := A) (B := B) →
    Option (Tree (A := A) (B := B)) → Prop
  | none, _, _ => False
  | some (.sup a children), label, target =>
    (label = .inl a ∧ target = none) ∨ ∃ p : B a, label = .inr ⟨a, p⟩ ∧ target = some (children p)

def treeGraph (tree : Tree (A := A) (B := B)) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.generated ((labels domain fibres).edge edge) (HSet.LabelCarrier.atom (some tree))

def encode (tree : Tree (A := A) (B := B)) : HSet.{u} := (labels domain fibres).decorate edge (some tree)

theorem mk_treeGraph (tree : Tree (A := A) (B := B)) :
    HSet.mk (treeGraph domain fibres tree) = encode domain fibres tree := rfl

theorem decorate_terminal : (labels domain fibres).decorate edge none = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  obtain ⟨_, _, impossible, _⟩ := (labels domain fibres).mem_decorate.mp member
  exact impossible

theorem mem_encode_sup_iff (a : A) (children : B a → Tree (A := A) (B := B)) (value : HSet.{u}) :
    value ∈ encode domain fibres (.sup a children) ↔
      value = HSet.kpair (shapeTag domain a) ∅ ∨
        ∃ p : B a, value = HSet.kpair (positionTag domain fibres a p) (encode domain fibres (children p)) := by
  rw [encode, (labels domain fibres).mem_decorate]
  constructor
  · rintro ⟨label, target, step, same⟩
    rcases step with ⟨rfl, rfl⟩ | ⟨p, rfl, rfl⟩
    · exact Or.inl (same.trans (congrArg (HSet.kpair _) (decorate_terminal domain fibres)))
    · exact Or.inr ⟨p, same⟩
  · rintro (same | ⟨p, same⟩)
    · exact ⟨.inl a, none, Or.inl ⟨rfl, rfl⟩,
        same.trans (congrArg (HSet.kpair _) (decorate_terminal domain fibres)).symm⟩
    · exact ⟨.inr ⟨a, p⟩, some (children p), Or.inr ⟨p, rfl, rfl⟩, same⟩

def carrierGraph : AccessiblePointedGraph.{u} := AccessiblePointedGraph.sup (treeGraph domain fibres)

abbrev Members := {root : HSet.{u} // root ∈ HSet.mk (carrierGraph domain fibres)}

theorem mem_carrierGraph_iff {root : HSet.{u}} :
    root ∈ HSet.mk (carrierGraph domain fibres) ↔ ∃ tree, encode domain fibres tree = root := HSet.mem_range

def treeMember (tree : Tree (A := A) (B := B)) : Members domain fibres :=
  ⟨encode domain fibres tree, (mem_carrierGraph_iff domain fibres).mpr ⟨tree, rfl⟩⟩

theorem shapeObservation_sup_iff (a : A) (children : B a → Tree (A := A) (B := B)) (original : HSet.{u}) :
    HSet.kpair (HSet.kpair ∅ original) ∅ ∈ encode domain fibres (.sup a children) ↔
      original = domain.value a := by
  rw [mem_encode_sup_iff]
  constructor
  · rintro (same | ⟨_, same⟩)
    · exact (HSet.kpair_inj.mp (HSet.kpair_inj.mp same).1).2
    · exact (HSet.empty_ne_singleton_empty (HSet.kpair_inj.mp (HSet.kpair_inj.mp same).1).1).elim
  · intro same
    exact Or.inl (congrArg (fun original => HSet.kpair (HSet.kpair ∅ original) ∅) same)

theorem positionObservation_sup_iff (a : A) (children : B a → Tree (A := A) (B := B))
    (p : B a) (childValue : HSet.{u}) :
    HSet.kpair (positionTag domain fibres a p) childValue ∈ encode domain fibres (.sup a children) ↔
      childValue = encode domain fibres (children p) := by
  rw [mem_encode_sup_iff]
  constructor
  · rintro (same | ⟨q, same⟩)
    · exact (shapeTag_ne_positionTag domain fibres a a p (HSet.kpair_inj.mp same).1.symm).elim
    · have positions : p = q := (fibres a).value_injective
        (HSet.kpair_inj.mp (HSet.kpair_inj.mp (HSet.kpair_inj.mp same).1).2).2
      cases positions
      exact (HSet.kpair_inj.mp same).2
  · intro same
    exact Or.inr ⟨p, congrArg (HSet.kpair _) same⟩

def shapeValue (root : HSet.{u}) : HSet.{u} :=
  HSet.sUnion (HSet.sep (fun original => HSet.kpair (HSet.kpair ∅ original) ∅ ∈ root) domain.carrier)

theorem shapeValue_encode_sup (a : A) (children : B a → Tree (A := A) (B := B)) :
    shapeValue domain (encode domain fibres (.sup a children)) = domain.value a := by
  have row : HSet.sep (fun original => HSet.kpair (HSet.kpair ∅ original) ∅ ∈
      encode domain fibres (.sup a children)) domain.carrier = {domain.value a} := by
    apply HSet.ext
    intro original
    rw [HSet.mem_sep, shapeObservation_sup_iff, HSet.mem_singleton]
    exact ⟨And.right, fun same => ⟨same ▸ domain.value_mem a, same⟩⟩
  exact (congrArg HSet.sUnion row).trans (HSet.sUnion_singleton _)

def shape (root : Members domain fibres) : A :=
  domain.decode ⟨shapeValue domain root.1, by
    obtain ⟨tree, same⟩ := (mem_carrierGraph_iff domain fibres).mp root.2
    rcases tree with ⟨a, children⟩
    rw [← same, shapeValue_encode_sup]
    exact domain.value_mem a⟩

theorem shape_treeMember_sup (a : A) (children : B a → Tree (A := A) (B := B)) :
    shape domain fibres (treeMember domain fibres (.sup a children)) = a := by
  apply domain.decode.symm.injective
  apply Subtype.ext
  exact (value_decode _ _).trans (shapeValue_encode_sup domain fibres a children)

def childRow (root : HSet.{u}) (originalShape originalPosition : HSet.{u}) : HSet.{u} :=
  HSet.sep (fun child => HSet.kpair (HSet.kpair {∅} (HSet.kpair originalShape originalPosition)) child ∈ root)
    (HSet.mk (carrierGraph domain fibres))

theorem childRow_encode_sup (a : A) (children : B a → Tree (A := A) (B := B)) (p : B a) :
    childRow domain fibres (encode domain fibres (.sup a children)) (domain.value a) ((fibres a).value p) =
      {encode domain fibres (children p)} := by
  apply HSet.ext
  intro childValue
  rw [childRow, HSet.mem_sep]
  change childValue ∈ HSet.mk (carrierGraph domain fibres) ∧
    HSet.kpair (positionTag domain fibres a p) childValue ∈ encode domain fibres (.sup a children) ↔ _
  rw [positionObservation_sup_iff, HSet.mem_singleton]
  exact ⟨And.right, fun same => ⟨same ▸ (treeMember domain fibres (children p)).2, same⟩⟩

def child (root : Members domain fibres) (p : B (shape domain fibres root)) : Members domain fibres :=
  ⟨HSet.sUnion (childRow domain fibres root.1 (domain.value (shape domain fibres root))
    ((fibres (shape domain fibres root)).value p)), by
    obtain ⟨tree, same⟩ := (mem_carrierGraph_iff domain fibres).mp root.2
    have memberSame : root = treeMember domain fibres tree := Subtype.ext same.symm
    cases memberSame
    rcases tree with ⟨a, children⟩
    let p' := cast (congrArg B (shape_treeMember_sup domain fibres a children)) p
    have row := (congrArg₂ (childRow domain fibres (encode domain fibres (.sup a children)))
      (congrArg domain.value (shape_treeMember_sup domain fibres a children))
      (value_cast fibres (shape_treeMember_sup domain fibres a children) p)).trans
      (childRow_encode_sup domain fibres a children p')
    exact ((congrArg HSet.sUnion row).trans (HSet.sUnion_singleton _)).symm ▸
      (treeMember domain fibres (children p')).2⟩

theorem child_treeMember_sup (a : A) (children : B a → Tree (A := A) (B := B))
    (p : B (shape domain fibres (treeMember domain fibres (.sup a children)))) :
    child domain fibres (treeMember domain fibres (.sup a children)) p =
      treeMember domain fibres (children (cast (congrArg B (shape_treeMember_sup domain fibres a children)) p)) := by
  apply Subtype.ext
  exact (congrArg HSet.sUnion ((congrArg₂ (childRow domain fibres (encode domain fibres (.sup a children)))
    (congrArg domain.value (shape_treeMember_sup domain fibres a children))
    (value_cast fibres (shape_treeMember_sup domain fibres a children) p)).trans
    (childRow_encode_sup domain fibres a children _))).trans (HSet.sUnion_singleton _)

def Child (subtree root : Members domain fibres) : Prop :=
  ∃ p : B (shape domain fibres root), subtree = child domain fibres root p

theorem accessible_treeMember (tree : Tree (A := A) (B := B)) :
    Acc (Child domain fibres) (treeMember domain fibres tree) := by
  induction tree with
  | sup a children earlier =>
    refine Acc.intro _ ?_
    rintro subtree ⟨p, rfl⟩
    exact (child_treeMember_sup domain fibres a children p).symm ▸
      earlier (cast (congrArg B (shape_treeMember_sup domain fibres a children)) p)

theorem accessible (root : Members domain fibres) : Acc (Child domain fibres) root := by
  obtain ⟨tree, same⟩ := (mem_carrierGraph_iff domain fibres).mp root.2
  have memberSame : root = treeMember domain fibres tree := Subtype.ext same.symm
  exact memberSame.symm ▸ accessible_treeMember domain fibres tree

def decodeAcc {root : Members domain fibres} (available : Acc (Child domain fibres) root) :
    Tree (A := A) (B := B) :=
  Acc.rec (motive := fun _ _ => Tree (A := A) (B := B))
    (fun parent _ earlier => .sup (shape domain fibres parent)
      (fun p => earlier (child domain fibres parent p) ⟨p, rfl⟩)) available

def decode (root : Members domain fibres) : Tree (A := A) (B := B) :=
  decodeAcc domain fibres (accessible domain fibres root)

theorem decode_eq (root : Members domain fibres) :
    decode domain fibres root = .sup (shape domain fibres root) (fun p => decode domain fibres (child domain fibres root p)) := by
  have available := accessible domain fibres root
  change decodeAcc domain fibres available = _
  cases available
  rfl

private theorem sup_eq_of_cast {first second : A} (same : first = second)
    (left : B first → Tree (A := A) (B := B)) (right : B second → Tree (A := A) (B := B))
    (children : ∀ p, left p = right (cast (congrArg B same) p)) :
    (WTree.sup first left : Tree (A := A) (B := B)) = WTree.sup second right := by
  cases same
  exact congrArg (WTree.sup first) (funext children)

theorem decode_treeMember (tree : Tree (A := A) (B := B)) :
    decode domain fibres (treeMember domain fibres tree) = tree := by
  induction tree with
  | sup a children earlier =>
    apply (decode_eq domain fibres (treeMember domain fibres (.sup a children))).trans
    apply sup_eq_of_cast (shape_treeMember_sup domain fibres a children)
    intro p
    exact (congrArg (decode domain fibres) (child_treeMember_sup domain fibres a children p)).trans
      (earlier (cast (congrArg B (shape_treeMember_sup domain fibres a children)) p))

theorem treeMember_decode (root : Members domain fibres) : treeMember domain fibres (decode domain fibres root) = root := by
  obtain ⟨tree, same⟩ := (mem_carrierGraph_iff domain fibres).mp root.2
  have memberSame : root = treeMember domain fibres tree := Subtype.ext same.symm
  cases memberSame
  exact congrArg (treeMember domain fibres) (decode_treeMember domain fibres tree)

def model : PresentedType (Tree (A := A) (B := B)) where
  graph := carrierGraph domain fibres
  decode := {
    toFun := decode domain fibres
    invFun := treeMember domain fibres
    left_inv := treeMember_decode domain fibres
    right_inv := decode_treeMember domain fibres }

theorem model_value (tree : Tree (A := A) (B := B)) :
    (model domain fibres).value tree = encode domain fibres tree := rfl

theorem encode_injective : Function.Injective (encode domain fibres) := (model domain fibres).value_injective

theorem encode_eq_iff_labelledBisimilar (first second : Tree (A := A) (B := B)) :
    encode domain fibres first = encode domain fibres second ↔
      LabelledBisimilar edge edge (labelValue domain fibres) (labelValue domain fibres) (some first) (some second) :=
  (labels domain fibres).decorate_eq_iff_labelledBisimilar (labels domain fibres)

theorem labelledBisimilar_iff_tree_eq (first second : Tree (A := A) (B := B)) :
    LabelledBisimilar edge edge (labelValue domain fibres) (labelValue domain fibres) (some first) (some second) ↔
      first = second :=
  (encode_eq_iff_labelledBisimilar domain fibres first second).symm.trans
    ⟨fun same => encode_injective domain fibres same, congrArg (encode domain fibres)⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedType.W
