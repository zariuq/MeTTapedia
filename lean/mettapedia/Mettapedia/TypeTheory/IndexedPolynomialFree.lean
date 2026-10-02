import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Free indexed polynomial terms with typed holes

The existing indexed polynomial fixed point is applied to `Holes + P`.
Leaves retain their output index, and a constructor retains every recursive
position and its child index. Filling holes is substitution in this same tree.
Reconstruction is its unique fold into a polynomial algebra with an
interpretation of the holes. No search order or object-language rule is added.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial

universe uBase uIndex uShape uPosition uHole uNext uLast uCarrier

variable {Base : Type uBase} {Index : Base → Type uIndex}

/-- Add a hole shape at its own index, without changing existing positions. -/
def withHoles
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)
    (holes : (base : Base) → Index base → Type uHole) :
    IndexedPolynomial Base Index where
  Shape base index := holes base index ⊕ polynomial.Shape base index
  Position shape := match shape with
    | .inl _ => PEmpty.{uPosition + 1}
    | .inr constructor => polynomial.Position constructor
  next shape position := match shape with
    | .inl _ => position.elim
    | .inr constructor => polynomial.next constructor position

/-- A well-founded constructor tree whose leaves are typed holes. -/
abbrev Free
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)
    (holes : (base : Base) → Index base → Type uHole) :=
  (polynomial.withHoles holes).Fix

namespace Free

variable (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)
variable {holes : (base : Base) → Index base → Type uHole}
variable {nextHoles : (base : Base) → Index base → Type uNext}
variable {lastHoles : (base : Base) → Index base → Type uLast}
variable {carrier : (base : Base) → Index base → Type uCarrier}

/-- An outstanding obligation remains a leaf at its exact index. -/
def pure {base : Base} {index : Index base} (hole : holes base index) :
    polynomial.Free holes base index :=
  .roll (.inl hole) (fun position => position.elim)

/-- One method application retains all indexed child plans. -/
def node {base : Base} {index : Index base}
    (shape : polynomial.Shape base index)
    (children : ∀ position, polynomial.Free holes base (polynomial.next shape position)) :
    polynomial.Free holes base index := .roll (.inr shape) children

/-- Interpret actual hole values and recursively reconstruct every node. -/
noncomputable def fold
    (interpret : ∀ base index, holes base index → carrier base index)
    (algebra : polynomial.Algebra carrier) :
    ∀ base index, polynomial.Free holes base index → carrier base index :=
  Fix.fold (polynomial.withHoles holes) (fun base index layer =>
    match layer with
    | ⟨.inl hole, _⟩ => interpret base index hole
    | ⟨.inr shape, children⟩ => algebra.act base index ⟨shape, children⟩)

@[simp] theorem fold_pure
    (interpret : ∀ base index, holes base index → carrier base index)
    (algebra : polynomial.Algebra carrier)
    {base : Base} {index : Index base} (hole : holes base index) :
    fold polynomial interpret algebra base index (pure polynomial hole) =
      interpret base index hole := rfl

@[simp] theorem fold_node
    (interpret : ∀ base index, holes base index → carrier base index)
    (algebra : polynomial.Algebra carrier)
    {base : Base} {index : Index base} (shape : polynomial.Shape base index)
    (children : ∀ position, polynomial.Free holes base (polynomial.next shape position)) :
    fold polynomial interpret algebra base index (node polynomial shape children) =
      algebra.act base index ⟨shape,
        fun position => fold polynomial interpret algebra base _ (children position)⟩ := rfl

/-- The free constructor tree carries the original polynomial's algebra. -/
def algebra : polynomial.Algebra (polynomial.Free holes) where
  act := fun _ _ layer => node polynomial layer.1 layer.2

/-- Filling holes preserves existing nodes and substitutes typed child trees. -/
noncomputable def bind
    (fill : ∀ base index, holes base index → polynomial.Free nextHoles base index) :
    ∀ base index, polynomial.Free holes base index → polynomial.Free nextHoles base index :=
  fold polynomial fill (algebra polynomial)

@[simp] theorem bind_pure
    (fill : ∀ base index, holes base index → polynomial.Free nextHoles base index)
    {base : Base} {index : Index base} (hole : holes base index) :
    bind polynomial fill base index (pure polynomial hole) = fill base index hole := rfl

@[simp] theorem bind_node
    (fill : ∀ base index, holes base index → polynomial.Free nextHoles base index)
    {base : Base} {index : Index base} (shape : polynomial.Shape base index)
    (children : ∀ position, polynomial.Free holes base (polynomial.next shape position)) :
    bind polynomial fill base index (node polynomial shape children) =
      node polynomial shape
        (fun position => bind polynomial fill base _ (children position)) := rfl

/-- Any reconstruction preserving leaves and nodes is this fold. -/
theorem fold_unique
    (interpret : ∀ base index, holes base index → carrier base index)
    (targetAlgebra : polynomial.Algebra carrier)
    (candidate : ∀ base index, polynomial.Free holes base index → carrier base index)
    (onPure : ∀ base index (hole : holes base index),
      candidate base index (pure polynomial hole) = interpret base index hole)
    (onNode : ∀ base index (shape : polynomial.Shape base index)
      (children : ∀ position, polynomial.Free holes base (polynomial.next shape position)),
      candidate base index (node polynomial shape children) =
        targetAlgebra.act base index ⟨shape,
          fun position => candidate base _ (children position)⟩) :
    ∀ base index (plan : polynomial.Free holes base index),
      candidate base index plan = fold polynomial interpret targetAlgebra base index plan := by
  intro base index plan
  induction plan with
  | roll shape children inductionHypothesis =>
      cases shape with
      | inl hole =>
          have same : children = (fun position => position.elim) := by
            funext position
            exact position.elim
          subst children
          exact onPure base _ hole
      | inr shape =>
          dsimp only [withHoles] at children inductionHypothesis
          change candidate base _ (node polynomial shape children) =
            targetAlgebra.act base _ ⟨shape,
              fun position => fold polynomial interpret targetAlgebra base _ (children position)⟩
          refine (onNode base _ shape children).trans ?_
          congr 2
          funext position
          exact inductionHypothesis position

/-- Filling every hole by the same outstanding obligation changes no tree. -/
@[simp] theorem bind_pure_right {base : Base} {index : Index base}
    (plan : polynomial.Free holes base index) :
    bind polynomial (fun _ _ hole => pure polynomial hole) base index plan = plan := by
  exact (fold_unique polynomial (fun _ _ hole => pure polynomial hole)
    (algebra polynomial) (fun _ _ tree => tree)
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) base index plan).symm

/-- Successive hole filling associates while retaining the same constructor tree. -/
theorem bind_assoc
    (earlier : ∀ base index, holes base index → polynomial.Free nextHoles base index)
    (later : ∀ base index, nextHoles base index → polynomial.Free lastHoles base index)
    {base : Base} {index : Index base} (plan : polynomial.Free holes base index) :
    bind polynomial later base index (bind polynomial earlier base index plan) =
      bind polynomial
        (fun base index hole => bind polynomial later base index (earlier base index hole))
        base index plan := by
  apply fold_unique polynomial
    (fun base index hole => bind polynomial later base index (earlier base index hole))
    (algebra polynomial)
    (fun base index tree => bind polynomial later base index (bind polynomial earlier base index tree))
  · intro base index hole
    rw [bind_pure]
  · intro base index shape children
    rw [bind_node, bind_node]
    rfl

/-- Reconstruction after filling holes equals interpreting their filled plans first. -/
theorem fold_bind
    (fill : ∀ base index, holes base index → polynomial.Free nextHoles base index)
    (interpret : ∀ base index, nextHoles base index → carrier base index)
    (targetAlgebra : polynomial.Algebra carrier)
    {base : Base} {index : Index base} (plan : polynomial.Free holes base index) :
    fold polynomial interpret targetAlgebra base index (bind polynomial fill base index plan) =
      fold polynomial (fun base index hole =>
        fold polynomial interpret targetAlgebra base index (fill base index hole))
        targetAlgebra base index plan := by
  apply fold_unique polynomial
    (fun base index hole => fold polynomial interpret targetAlgebra base index (fill base index hole))
    targetAlgebra
    (fun base index tree => fold polynomial interpret targetAlgebra base index
      (bind polynomial fill base index tree))
  · intro base index hole
    rw [bind_pure]
  · intro base index shape children
    rw [bind_node, fold_node]

/-- Relabel typed leaves without changing any constructor or position. -/
noncomputable def map
    (mapping : ∀ base index, holes base index → nextHoles base index) :
    ∀ base index, polynomial.Free holes base index → polynomial.Free nextHoles base index :=
  bind polynomial (fun base index hole => pure polynomial (mapping base index hole))

@[simp] theorem map_pure
    (mapping : ∀ base index, holes base index → nextHoles base index)
    {base : Base} {index : Index base} (hole : holes base index) :
    map polynomial mapping base index (pure polynomial hole) =
      pure polynomial (mapping base index hole) := rfl

@[simp] theorem map_node
    (mapping : ∀ base index, holes base index → nextHoles base index)
    {base : Base} {index : Index base} (shape : polynomial.Shape base index)
    (children : ∀ position, polynomial.Free holes base (polynomial.next shape position)) :
    map polynomial mapping base index (node polynomial shape children) =
      node polynomial shape (fun position => map polynomial mapping base _ (children position)) := rfl

@[simp] theorem map_id {base : Base} {index : Index base}
    (plan : polynomial.Free holes base index) :
    map polynomial (fun _ _ hole => hole) base index plan = plan :=
  bind_pure_right polynomial plan

theorem map_comp
    (earlier : ∀ base index, holes base index → nextHoles base index)
    (later : ∀ base index, nextHoles base index → lastHoles base index)
    {base : Base} {index : Index base} (plan : polynomial.Free holes base index) :
    map polynomial later base index (map polynomial earlier base index plan) =
      map polynomial (fun base index hole => later base index (earlier base index hole))
        base index plan := by
  exact bind_assoc polynomial
    (fun base index hole => pure polynomial (earlier base index hole))
    (fun base index hole => pure polynomial (later base index hole)) plan

/-- Flatten a tree whose outstanding leaves are themselves trees. -/
noncomputable def join {base : Base} {index : Index base}
    (plan : polynomial.Free (polynomial.Free holes) base index) :
    polynomial.Free holes base index := bind polynomial (fun _ _ tree => tree) base index plan

@[simp] theorem join_pure {base : Base} {index : Index base}
    (plan : polynomial.Free holes base index) :
    join polynomial (pure polynomial plan) = plan := rfl

@[simp] theorem join_map_pure {base : Base} {index : Index base}
    (plan : polynomial.Free holes base index) :
    join polynomial (map polynomial (fun _ _ hole => pure polynomial hole) base index plan) =
      plan := by
  exact (bind_assoc polynomial (fun _ _ hole => pure polynomial (pure polynomial hole))
    (fun _ _ tree => tree) plan).trans (bind_pure_right polynomial plan)

theorem join_assoc {base : Base} {index : Index base}
    (plan : polynomial.Free (polynomial.Free (polynomial.Free holes)) base index) :
    join polynomial (join polynomial plan) =
      join polynomial (map polynomial (fun _ _ tree => join polynomial tree) base index plan) := by
  unfold join map
  rw [bind_assoc, bind_assoc]
  rfl

/-- Transporting a leaf along an index equality commutes with embedding it. -/
theorem pure_transport {base : Base} {first second : Index base}
    (equal : first = second) (hole : holes base first) :
    equal ▸ (pure polynomial hole : polynomial.Free holes base first) =
      pure polynomial (equal ▸ hole : holes base second) := by
  cases equal
  rfl

end Free

#print axioms Free.fold_unique
#print axioms Free.bind_pure_right
#print axioms Free.bind_assoc
#print axioms Free.fold_bind
#print axioms Free.map_comp
#print axioms Free.join_map_pure
#print axioms Free.join_assoc

end Mettapedia.TypeTheory.IndexedPolynomial
