import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mettapedia.Logic.FinitaryRuleSystem.Initiality

/-!
# List-branched finite derivations

The generic replay certificate is often easiest to state as the initial algebra
of the polynomial endofunctor

`F X = J × W × List X`.

The existing `Derivation` type stores the same finite branching as an arity
`n : Nat` and a family `Fin n → X`.  This module proves that the two
representations are exactly equivalent.  The equivalence preserves roots,
branch order, branch multiplicity, node count, and replay.  It therefore
exposes a representation-independent finite construction without selecting an
object logic or a bootstrap host.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v w

/-- A witnessed derivation tree whose finite children are stored as a list. -/
inductive ListBranchedDerivation (J : Type u) (W : Type v) : Type (max u v) where
  | node (conclusion : J) (witness : W)
      (children : List (ListBranchedDerivation J W))

namespace ListBranchedDerivation

variable {J : Type u} {W : Type v}

/-- Root conclusion of a list-branched certificate. -/
def concl : ListBranchedDerivation J W → J
  | .node conclusion _witness _children => conclusion

@[simp]
theorem concl_node (conclusion : J) (witness : W)
    (children : List (ListBranchedDerivation J W)) :
    concl (.node conclusion witness children) = conclusion := rfl

/-- Number of physical rule nodes in a list-branched certificate. -/
def nodeCount : ListBranchedDerivation J W → Nat
  | .node _conclusion _witness children =>
      1 + (children.map nodeCount).sum

@[simp]
theorem nodeCount_node (conclusion : J) (witness : W)
    (children : List (ListBranchedDerivation J W)) :
    nodeCount (.node conclusion witness children) =
      1 + (children.map nodeCount).sum := by
  simp [nodeCount]

/-- Exact replay of a list-branched certificate. -/
def valid {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) :
    ListBranchedDerivation J interface.W → Bool
  | .node conclusion witness children =>
      interface.isInstance witness (children.map concl) conclusion &&
        (children.map (valid interface)).all id

@[simp]
theorem valid_node {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    (conclusion : J) (witness : interface.W)
    (children : List (ListBranchedDerivation J interface.W)) :
    valid interface (.node conclusion witness children) =
      (interface.isInstance witness (children.map concl) conclusion &&
        (children.map (valid interface)).all id) := by
  simp [valid]

/-- Build the indexed representation from a list of already-converted
children.  `List.equivSigmaTuple` carries the exact finite-list/finite-family
isomorphism. -/
def indexedNodeFromList (conclusion : J) (witness : W)
    (children : List (Derivation J W)) : Derivation J W :=
  let packed := List.equivSigmaTuple children
  .node conclusion witness packed.1 packed.2

@[simp]
theorem indexedNodeFromList_ofFn (conclusion : J) (witness : W)
    (n : Nat) (children : Fin n → Derivation J W) :
    indexedNodeFromList conclusion witness (List.ofFn children) =
      .node conclusion witness n children := by
  unfold indexedNodeFromList
  have packed : List.equivSigmaTuple (List.ofFn children) = ⟨n, children⟩ :=
    List.equivSigmaTuple.right_inv ⟨n, children⟩
  rw [packed]

mutual
  /-- Convert list-branched syntax to the existing indexed syntax. -/
  def toIndexed : ListBranchedDerivation J W → Derivation J W
    | .node conclusion witness children =>
        indexedNodeFromList conclusion witness (toIndexedList children)

  /-- Map the conversion over a list, stated mutually so recursive calls are
  structurally evident to Lean. -/
  def toIndexedList :
      List (ListBranchedDerivation J W) → List (Derivation J W)
    | [] => []
    | child :: children => toIndexed child :: toIndexedList children
end

@[simp]
theorem toIndexedList_eq_map :
    ∀ children : List (ListBranchedDerivation J W),
      toIndexedList children = children.map toIndexed
  | [] => rfl
  | _child :: _children => by
      simp [toIndexedList, toIndexedList_eq_map]

/-- Convert existing indexed syntax to list-branched syntax. -/
def ofIndexed : Derivation J W → ListBranchedDerivation J W
  | .node conclusion witness _n children =>
      .node conclusion witness (List.ofFn fun i => ofIndexed (children i))

@[simp]
theorem ofIndexed_indexedNodeFromList (conclusion : J) (witness : W)
    (children : List (Derivation J W)) :
    ofIndexed (indexedNodeFromList conclusion witness children) =
      .node conclusion witness (children.map ofIndexed) := by
  simp [indexedNodeFromList, List.equivSigmaTuple, ofIndexed]

/-- Converting an indexed tree to a list tree and back is the identity. -/
theorem toIndexed_ofIndexed :
    ∀ tree : Derivation J W, toIndexed (ofIndexed tree) = tree := by
  intro tree
  induction tree with
  | node conclusion witness n children ih =>
      simp only [ofIndexed, toIndexed]
      have mapped :
          toIndexedList (List.ofFn fun i => ofIndexed (children i)) =
            List.ofFn children := by
        rw [toIndexedList_eq_map, List.map_ofFn]
        apply congrArg List.ofFn
        funext i
        exact ih i
      rw [mapped, indexedNodeFromList_ofFn]

mutual
  /-- Converting a list tree to an indexed tree and back is the identity. -/
  theorem ofIndexed_toIndexed :
      ∀ tree : ListBranchedDerivation J W,
        ofIndexed (toIndexed tree) = tree
    | .node conclusion witness children => by
        simp only [toIndexed, ofIndexed_indexedNodeFromList]
        congr 1
        exact ofIndexed_toIndexedList children

  theorem ofIndexed_toIndexedList :
      ∀ children : List (ListBranchedDerivation J W),
        (toIndexedList children).map ofIndexed = children
    | [] => rfl
    | child :: children => by
        simp only [toIndexedList, List.map_cons, List.cons.injEq]
        exact ⟨ofIndexed_toIndexed child, ofIndexed_toIndexedList children⟩
end

/-- The exact equivalence between list and indexed finite branching. -/
def equivIndexed : ListBranchedDerivation J W ≃ Derivation J W where
  toFun := toIndexed
  invFun := ofIndexed
  left_inv := ofIndexed_toIndexed
  right_inv := toIndexed_ofIndexed

@[simp]
theorem indexedNodeFromList_concl (conclusion : J) (witness : W)
    (children : List (Derivation J W)) :
    (indexedNodeFromList conclusion witness children).concl = conclusion := by
  simp [indexedNodeFromList, List.equivSigmaTuple, Derivation.concl]

@[simp]
theorem concl_toIndexed : ∀ tree : ListBranchedDerivation J W,
    (toIndexed tree).concl = tree.concl
  | .node conclusion witness children => by
      simp [toIndexed, concl]

@[simp]
theorem concl_ofIndexed (tree : Derivation J W) :
    (ofIndexed tree).concl = tree.concl := by
  have preserved := concl_toIndexed (ofIndexed tree)
  rw [toIndexed_ofIndexed] at preserved
  exact preserved.symm

@[simp]
theorem indexedNodeFromList_nodeCount (conclusion : J) (witness : W)
    (children : List (Derivation J W)) :
    (indexedNodeFromList conclusion witness children).nodeCount =
      1 + (children.map Derivation.nodeCount).sum := by
  simp [indexedNodeFromList, List.equivSigmaTuple]

mutual
  /-- Node count is invariant under conversion to indexed branching. -/
  theorem nodeCount_toIndexed :
      ∀ tree : ListBranchedDerivation J W,
        (toIndexed tree).nodeCount = tree.nodeCount
    | .node conclusion witness children => by
        rw [toIndexed, indexedNodeFromList_nodeCount]
        simp only [nodeCount]
        congr 1
        exact congrArg List.sum (nodeCounts_toIndexedList children)

  theorem nodeCounts_toIndexedList :
      ∀ children : List (ListBranchedDerivation J W),
        (toIndexedList children).map Derivation.nodeCount =
          children.map nodeCount
    | [] => rfl
    | child :: children => by
        simp only [toIndexedList, List.map_cons, List.cons.injEq]
        exact ⟨nodeCount_toIndexed child,
          nodeCounts_toIndexedList children⟩
end

@[simp]
theorem nodeCount_ofIndexed (tree : Derivation J W) :
    (ofIndexed tree).nodeCount = tree.nodeCount := by
  have preserved := nodeCount_toIndexed (ofIndexed tree)
  rw [toIndexed_ofIndexed] at preserved
  exact preserved.symm

@[simp]
theorem indexedNodeFromList_valid {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    (conclusion : J) (witness : interface.W)
    (children : List (Derivation J interface.W)) :
    (indexedNodeFromList conclusion witness children).valid interface =
      (interface.isInstance witness (children.map Derivation.concl) conclusion &&
        (children.map (Derivation.valid interface)).all id) := by
  simp [indexedNodeFromList, List.equivSigmaTuple, Derivation.valid]

mutual
  /-- Replay is invariant under conversion to indexed branching. -/
  theorem valid_toIndexed {rules : List J → J → Prop}
      (interface : RuleWitness.{u, v} rules) :
      ∀ tree : ListBranchedDerivation J interface.W,
        (toIndexed tree).valid interface = tree.valid interface
    | .node conclusion witness children => by
        rw [toIndexed, indexedNodeFromList_valid]
        simp only [valid]
        have conclusions :
            (toIndexedList children).map Derivation.concl =
              children.map concl := by
          rw [toIndexedList_eq_map, List.map_map]
          apply List.map_congr_left
          intro child _member
          exact concl_toIndexed child
        rw [conclusions, validities_toIndexedList interface children]

  theorem validities_toIndexedList {rules : List J → J → Prop}
      (interface : RuleWitness.{u, v} rules) :
      ∀ children : List (ListBranchedDerivation J interface.W),
        (toIndexedList children).map (Derivation.valid interface) =
          children.map (valid interface)
    | [] => rfl
    | child :: children => by
        simp only [toIndexedList, List.map_cons, List.cons.injEq]
        exact ⟨valid_toIndexed interface child,
          validities_toIndexedList interface children⟩
end

@[simp]
theorem valid_ofIndexed {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    (tree : Derivation J interface.W) :
    (ofIndexed tree).valid interface = tree.valid interface := by
  have preserved := valid_toIndexed interface (ofIndexed tree)
  rw [toIndexed_ofIndexed] at preserved
  exact preserved.symm

/-- Accepted list-branched certificates reconstruct semantic derivability. -/
theorem valid_sound {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    (certificate : ListBranchedDerivation J interface.W)
    (accepted : certificate.valid interface = true) :
    Derives rules certificate.concl := by
  have indexedAccepted :
      (toIndexed certificate).valid interface = true := by
    rw [valid_toIndexed interface certificate]
    exact accepted
  have derivable := Derivation.valid_sound interface
    (toIndexed certificate) indexedAccepted
  simpa using derivable

/-- Derivability is exactly the existence of an accepted list-branched
certificate with the requested root. -/
theorem derives_iff_exists_accepted {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (judgment : J) :
    Derives rules judgment ↔
      ∃ certificate : ListBranchedDerivation J interface.W,
        certificate.valid interface = true ∧ certificate.concl = judgment := by
  constructor
  · intro derivable
    obtain ⟨certificate, accepted, root⟩ :=
      Derives.exists_derivation interface derivable
    exact ⟨ofIndexed certificate, by simpa, by simpa using root⟩
  · rintro ⟨certificate, accepted, root⟩
    rw [← root]
    exact valid_sound interface certificate accepted

/-- An interpretation of one list-branched derivation layer. -/
structure ListNodeAlgebra (J : Type u) (W : Type v) where
  Carrier : Type w
  node : J → W → List Carrier → Carrier

namespace ListNodeAlgebra

variable {J : Type u} {W : Type v}

/-- A function preserving list-branched node formation. -/
@[ext]
structure Hom (A B : ListNodeAlgebra.{u, v, w} J W) where
  toFun : A.Carrier → B.Carrier
  map_node : ∀ conclusion witness children,
    toFun (A.node conclusion witness children) =
      B.node conclusion witness (children.map toFun)

instance {A B : ListNodeAlgebra.{u, v, w} J W} :
    CoeFun (Hom A B) (fun _ => A.Carrier → B.Carrier) :=
  ⟨Hom.toFun⟩

@[ext]
theorem Hom.ext' {A B : ListNodeAlgebra.{u, v, w} J W} (f g : Hom A B)
    (pointwise : ∀ value, f value = g value) : f = g := by
  cases f with
  | mk f preservesF =>
      cases g with
      | mk g preservesG =>
          change ∀ value, f value = g value at pointwise
          have functionsEqual : f = g := funext pointwise
          subst g
          rfl

def Hom.id (A : ListNodeAlgebra.{u, v, w} J W) : Hom A A where
  toFun := fun value => value
  map_node := by intros; simp

def Hom.comp {A B C : ListNodeAlgebra.{u, v, w} J W}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  toFun := fun value => g (f value)
  map_node := by
    intro conclusion witness children
    rw [f.map_node, g.map_node, List.map_map]
    simp [Function.comp_def]

instance : Category (ListNodeAlgebra.{u, v, w} J W) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by intros; ext; simp [Hom.comp, Hom.id]
  comp_id := by intros; ext; simp [Hom.comp, Hom.id]
  assoc := by intros; ext; simp [Hom.comp]

/-- The list-branched syntax algebra itself. -/
def syntaxAlgebra : ListNodeAlgebra.{u, v, max u v} J W where
  Carrier := ListBranchedDerivation J W
  node := ListBranchedDerivation.node

/-- Structural fold from list-branched syntax. -/
def fold (A : ListNodeAlgebra.{u, v, max u v} J W) :
    ListBranchedDerivation J W → A.Carrier
  | .node conclusion witness children =>
      A.node conclusion witness (children.map (fold A))

@[simp]
theorem fold_node (A : ListNodeAlgebra.{u, v, max u v} J W)
    (conclusion : J) (witness : W)
    (children : List (ListBranchedDerivation J W)) :
    fold A (.node conclusion witness children) =
      A.node conclusion witness (children.map (fold A)) := by
  simp [fold]

def foldHom (A : ListNodeAlgebra.{u, v, max u v} J W) :
    syntaxAlgebra ⟶ A where
  toFun := fold A
  map_node := by intros; simp [syntaxAlgebra]

mutual
  /-- Every homomorphism from syntax is its structural fold. -/
  theorem hom_eq_fold_pointwise
      (A : ListNodeAlgebra.{u, v, max u v} J W)
      (f : syntaxAlgebra ⟶ A) :
      ∀ tree, f.toFun tree = fold A tree
    | .node conclusion witness children => by
        calc
          f.toFun (.node conclusion witness children) =
              A.node conclusion witness (children.map f.toFun) := by
                simpa [syntaxAlgebra] using
                  f.map_node conclusion witness children
          _ = A.node conclusion witness (children.map (fold A)) := by
                rw [hom_eq_fold_children A f children]
          _ = fold A (.node conclusion witness children) := by
                rw [fold_node]

  theorem hom_eq_fold_children
      (A : ListNodeAlgebra.{u, v, max u v} J W)
      (f : syntaxAlgebra ⟶ A) :
      ∀ children : List (ListBranchedDerivation J W),
        children.map f.toFun = children.map (fold A)
    | [] => rfl
    | child :: children => by
        exact congrArg₂ List.cons
          (hom_eq_fold_pointwise A f child)
          (hom_eq_fold_children A f children)
end

theorem hom_eq_fold (A : ListNodeAlgebra.{u, v, max u v} J W)
    (f : syntaxAlgebra ⟶ A) : f = foldHom A := by
  apply Hom.ext'
  exact hom_eq_fold_pointwise A f

/-- `ListBranchedDerivation` is the initial algebra of
`F X = J × W × List X`. -/
def syntaxAlgebra_isInitial :
    IsInitial (syntaxAlgebra (J := J) (W := W)) :=
  IsInitial.ofUniqueHom foldHom (fun A f => hom_eq_fold A f)

/-- Node interpretation retaining only the root conclusion. -/
def conclusionAlgebra : ListNodeAlgebra.{u, v, max u v} J W where
  Carrier := ULift.{max u v, u} J
  node := fun conclusion _witness _children => ULift.up conclusion

theorem fold_conclusion (tree : ListBranchedDerivation J W) :
    (fold conclusionAlgebra tree).down = tree.concl := by
  cases tree
  simp [conclusionAlgebra, ListBranchedDerivation.concl]

/-- Node interpretation counting physical rule nodes. -/
def nodeCountAlgebra : ListNodeAlgebra.{u, v, max u v} J W where
  Carrier := ULift.{max u v, 0} Nat
  node := fun _conclusion _witness children =>
    ULift.up (1 + (children.map ULift.down).sum)

mutual
  theorem fold_nodeCount :
      ∀ tree : ListBranchedDerivation J W,
        (fold nodeCountAlgebra tree).down = tree.nodeCount
    | .node conclusion witness children => by
        simp only [fold_node, nodeCountAlgebra,
          ListBranchedDerivation.nodeCount]
        congr 1
        exact congrArg List.sum (fold_nodeCounts children)

  theorem fold_nodeCounts :
      ∀ children : List (ListBranchedDerivation J W),
        (children.map (fold nodeCountAlgebra)).map ULift.down =
          children.map ListBranchedDerivation.nodeCount
    | [] => rfl
    | child :: children => by
        exact congrArg₂ List.cons
          (fold_nodeCount child)
          (fold_nodeCounts children)
end

/-- A single fold computing both root conclusion and exact replay. -/
def replayAlgebra {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) :
    ListNodeAlgebra.{u, v, max u v} J interface.W where
  Carrier := ULift.{max u v, max u 0} (J × Bool)
  node := fun conclusion witness children =>
    ULift.up (conclusion,
      interface.isInstance witness (children.map (fun child => child.down.1))
          conclusion &&
        (children.map (fun child => child.down.2)).all id)

private theorem map_ulift_down_fst {A B : Type*}
    (values : List (ULift (A × B))) :
    values.map (fun value => value.down.1) =
      (values.map ULift.down).map Prod.fst := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.map_cons]
      rw [ih]

private theorem map_ulift_down_snd {A B : Type*}
    (values : List (ULift (A × B))) :
    values.map (fun value => value.down.2) =
      (values.map ULift.down).map Prod.snd := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.map_cons]
      rw [ih]

mutual
  theorem fold_replay {rules : List J → J → Prop}
      (interface : RuleWitness.{u, v} rules) :
      ∀ tree : ListBranchedDerivation J interface.W,
        (fold (replayAlgebra interface) tree).down =
          (tree.concl, tree.valid interface)
    | .node conclusion witness children => by
        simp only [fold_node,
          ListBranchedDerivation.concl, ListBranchedDerivation.valid]
        change
          (conclusion,
            interface.isInstance witness
                  ((children.map (fold (replayAlgebra interface))).map
                    (fun child => child.down.1)) conclusion &&
                ((children.map (fold (replayAlgebra interface))).map
                  (fun child => child.down.2)).all id) =
            (conclusion,
              interface.isInstance witness
                  (children.map ListBranchedDerivation.concl) conclusion &&
                (children.map
                  (ListBranchedDerivation.valid interface)).all id)
        simp only [Prod.mk.injEq, true_and]
        have evaluated := fold_replays interface children
        have conclusions :
            (children.map (fold (replayAlgebra interface))).map
                (fun child => child.down.1) =
              children.map ListBranchedDerivation.concl := by
          calc
            _ = ((children.map (fold (replayAlgebra interface))).map
                  ULift.down).map Prod.fst := by
                  exact map_ulift_down_fst _
            _ = (children.map fun child =>
                  (child.concl, child.valid interface)).map Prod.fst :=
                  congrArg (List.map Prod.fst) evaluated
            _ = _ := by
                  simp only [List.map_map, Function.comp_def]
        have validities :
            (children.map (fold (replayAlgebra interface))).map
                (fun child => child.down.2) =
              children.map (ListBranchedDerivation.valid interface) := by
          calc
            _ = ((children.map (fold (replayAlgebra interface))).map
                  ULift.down).map Prod.snd := by
                  exact map_ulift_down_snd _
            _ = (children.map fun child =>
                  (child.concl, child.valid interface)).map Prod.snd :=
                  congrArg (List.map Prod.snd) evaluated
            _ = _ := by
                  simp only [List.map_map, Function.comp_def]
        rw [conclusions, validities]

  theorem fold_replays {rules : List J → J → Prop}
      (interface : RuleWitness.{u, v} rules) :
      ∀ children : List (ListBranchedDerivation J interface.W),
        (children.map (fold (replayAlgebra interface))).map ULift.down =
          children.map fun child => (child.concl, child.valid interface)
    | [] => rfl
    | child :: children => by
        exact congrArg₂ List.cons
          (fold_replay interface child)
          (fold_replays interface children)
end

end ListNodeAlgebra

end ListBranchedDerivation

end Mettapedia.Logic.FinitaryRuleSystem
