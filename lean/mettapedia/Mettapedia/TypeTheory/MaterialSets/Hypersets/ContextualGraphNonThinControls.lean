import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRealizedGraphs
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualArgumentCodings

/-!
# Infinite contextual graph controls with retained history

The context category has arbitrarily long histories and infinitely many
parallel arrows. Root nodes retain their actual history. A root exposes
the finite ordinals below the current stage precisely when its first
history label agrees with the graph's profile. Ordinal nodes themselves
retain their ordinary descending edges.

Thus the child fibres grow without a fixed finite bound, context actions
preserve actual edges, and two parallel arrivals can disagree about
membership. The empty present observation does not determine the future.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphNonThinControls

open CategoryTheory ContextualGraphDiagrams LabelledContextPaths

abbrev Node (point : World) := (initial ⟶ point) ⊕ Nat

def advance {first second : World} (arrival : first ⟶ second) : Node first → Node second
  | .inl history => .inl (history ≫ arrival)
  | .inr ordinal => .inr ordinal

def nodes : World ⥤ Type where
  obj := Node
  map arrival := TypeCat.ofHom (advance arrival)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro node
    cases node with
    | inl history => exact congrArg Sum.inl (Category.comp_id history)
    | inr ordinal => rfl
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro node
    cases node with
    | inl history => exact congrArg Sum.inl (Category.assoc history earlier later).symm
    | inr ordinal => rfl

def edge (label : Nat) (point : World) : Node point → Node point → Prop
  | .inl history, .inr ordinal =>
      ordinal < point.length ∧ ∃ rest, history.val = label :: rest
  | .inr parent, .inr child => child < parent
  | _, _ => False

theorem edge_transport (label : Nat) {first second : World} (arrival : first ⟶ second)
    {parent child : Node first} (available : edge label first parent child) :
    edge label second (advance arrival parent) (advance arrival child) := by
  cases parent with
  | inl history =>
    cases child with
    | inl other => exact available.elim
    | inr ordinal =>
      rcases available with ⟨small, rest, starts⟩
      refine ⟨Nat.lt_of_lt_of_le small
        ((Nat.le_add_right first.length arrival.val.length).trans_eq arrival.property),
        rest ++ arrival.val, ?_⟩
      change history.val ++ arrival.val = label :: (rest ++ arrival.val)
      rw [starts]
      rfl
  | inr ordinal =>
    cases child with
    | inl history => exact available.elim
    | inr child => exact available

def diagram (label : Nat) : Diagram World where
  nodes := nodes
  edge := edge label
  edge_transport := edge_transport label

def root (label : Nat) : Value World initial :=
  ⟨diagram label, Sum.inl (𝟙 initial)⟩

def arrived (label : Nat) {point : World} (history : initial ⟶ point) : Value World point :=
  move World history (root label)

theorem arrived_node (label : Nat) {point : World} (history : initial ⟶ point) :
    (arrived label history).2 = Sum.inl history :=
  congrArg Sum.inl (Category.id_comp history)

def ordinalValue (label : Nat) (point : World) (ordinal : Nat) : Value World point :=
  ⟨diagram label, Sum.inr ordinal⟩

theorem ordinal_transport (label : Nat) {first second : World} (arrival : first ⟶ second)
    (ordinal : Nat) :
    move World arrival (ordinalValue label first ordinal) = ordinalValue label second ordinal := rfl

theorem initial_children_empty (label : Nat) : IsEmpty (Child World (root label)) := by
  refine ⟨fun receipt => ?_⟩
  rcases receipt with ⟨node, available⟩
  cases node with
  | inl history => exact available
  | inr ordinal => exact Nat.not_lt_zero ordinal available.1

def initial_current_matching (label : Nat) :
    GraphSetRealization.Equal (picture World (root label)) AccessiblePointedGraph.empty :=
  GraphSetRealization.extensionality
    (fun _ proof => False.elim
      ((initial_children_empty label).false ⟨proof.1.val.val, proof.1.property⟩))
    (fun _ proof => PEmpty.elim (GraphSetRealization.emptyEliminate proof))

theorem initial_material_readings_agree (first second : Nat) :
    HSet.mk (picture World (root first)) = HSet.mk (picture World (root second)) :=
  HSet.mk_eq_mk_iff.mpr
    ((initial_current_matching first).trans (initial_current_matching second).symm).forget

def firstChild (label : Nat) : Child World (arrived label (extension label)) :=
  ⟨Sum.inr 0, by
    change edge label next (Sum.inl ((𝟙 initial) ≫ extension label)) (Sum.inr 0)
    rw [Category.id_comp]
    exact ⟨Nat.zero_lt_succ 0, [], rfl⟩⟩

theorem wrong_label_children_empty {label other : Nat} (different : label ≠ other) :
    IsEmpty (Child World (arrived label (extension other))) := by
  refine ⟨fun receipt => ?_⟩
  rcases receipt with ⟨node, available⟩
  cases node with
  | inl history => exact available
  | inr ordinal =>
    rcases available.2 with ⟨rest, same⟩
    exact different (List.cons.inj same).1.symm

theorem parallel_arrivals_injective (label : Nat) :
    Function.Injective (fun other => arrived label (extension other)) := by
  intro first second same
  have equalNodes := eq_of_heq (Sigma.mk.inj_iff.mp same).2
  have paths := congrArg (fun node : Node next =>
    match node with | .inl history => history.val | .inr _ => []) equalNodes
  exact List.singleton_injective paths

theorem parallel_arrivals_have_different_membership :
    Nonempty (Child World (arrived 0 (extension 0))) ∧
      IsEmpty (Child World (arrived 0 (extension 1))) :=
  ⟨⟨firstChild 0⟩, wrong_label_children_empty Nat.zero_ne_one⟩

theorem initial_profiles_not_equal {first second : Nat} (different : first ≠ second) :
    ¬ Nonempty (ContextualRealizedGraphs.Equal (root first) (root second)) := by
  rintro ⟨matching⟩
  let answer := ContextualGraphRealizers.Realizer.forth matching
    ⟨next, extension first⟩ (firstChild first)
  exact (wrong_label_children_empty different.symm).false answer.1

theorem present_reading_does_not_reflect_future_equality :
    HSet.mk (picture World (root 0)) = HSet.mk (picture World (root 1)) ∧
      ¬ Nonempty (ContextualRealizedGraphs.Equal (root 0) (root 1)) :=
  ⟨initial_material_readings_agree 0 1, initial_profiles_not_equal Nat.zero_ne_one⟩

def stage (count : Nat) : World := ⟨count + 1⟩

def history (label count : Nat) : initial ⟶ stage count :=
  ⟨label :: List.replicate count label, by simp [initial, stage]⟩

def grow (label count : Nat) : stage count ⟶ stage (count + 1) :=
  ⟨[label], rfl⟩

def newest (label count : Nat) : Child World (arrived label (history label count)) :=
  ⟨Sum.inr count, by
    change edge label (stage count) (Sum.inl ((𝟙 initial) ≫ history label count)) (Sum.inr count)
    rw [Category.id_comp]
    exact ⟨Nat.lt_succ_self count, List.replicate count label, rfl⟩⟩

theorem newest_value (label count : Nat) :
    childValue World (arrived label (history label count)) (newest label count) =
      ordinalValue label (stage count) count := rfl

theorem old_children_bounded (label count : Nat)
    (receipt : Child World (arrived label (history label count))) :
    ∃ ordinal, receipt.val = Sum.inr ordinal ∧ ordinal < count + 1 := by
  rcases receipt with ⟨node, available⟩
  cases node with
  | inl path => exact available.elim
  | inr ordinal => exact ⟨ordinal, rfl, available.1⟩

theorem newest_not_from_previous (label count : Nat)
    (receipt : Child World (arrived label (history label count))) :
    advance (grow label count) receipt.val ≠ (newest label (count + 1)).val := by
  obtain ⟨ordinal, same, bound⟩ := old_children_bounded label count receipt
  rw [same]
  intro impossible
  have equalOrdinals : ordinal = count + 1 := Sum.inr.inj impossible
  exact (Nat.ne_of_lt bound) equalOrdinals

theorem infinitely_many_worlds : Function.Injective stage := by
  intro first second same
  exact Nat.add_right_cancel (congrArg World.length same)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphNonThinControls
