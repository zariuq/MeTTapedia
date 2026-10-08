import Mettapedia.TypeTheory.IndexedGSOSLaw

/-!
# Operational lifting of an arbitrary indexed GSOS law

The polynomial fold computes a complete source term and its one-step
behavior. Constructor conclusions are flattened by the existing free
monad multiplication. Naturality of the supplied law and covariance of
the arbitrary behavior functor earn operational substitution, relabeling
and flattening; no case analysis on a particular behavior datatype is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.IndexedGSOS

open _root_.CategoryTheory IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u, u, u, u} Base Index}
variable {B : Family Base Index ⥤ Family Base Index}

abbrev VariableCoalgebra (B : Family Base Index ⥤ Family Base Index)
    (X : Family Base Index) := X ⟶ B.obj X

namespace Operational

variable (law : Law P B)

abbrev Result (X : Family Base Index) : Family Base Index :=
  (sourceBehaviourFunctor B).obj (P.Free X)

/-- The actual constructor action retains the complete node and maps its
independently computed behavior through free-monad multiplication. -/
noncomputable def algebra (X : Family Base Index) :
    P.Algebra (Result (P := P) (B := B) X) where
  act := fun base index layer =>
    (Free.node P layer.1 (fun position => (layer.2 position).1),
      B.map ((FreeAdjunction.monad P).μ.app X) base index
        (law.app (P.Free X) base index layer))

noncomputable def leaf {X : Family Base Index} (inputs : VariableCoalgebra B X)
    (base : Base) (index : Index base) (value : X base index) :
    Result (P := P) (B := B) X base index :=
  (Free.pure P value,
    B.map ((FreeAdjunction.monad P).η.app X) base index (inputs base index value))

/-- This is the existing indexed free fold, with actual leaf and node actions. -/
noncomputable def evaluate {X : Family Base Index} (inputs : VariableCoalgebra B X) :
    ∀ base index, P.Free X base index → Result (P := P) (B := B) X base index :=
  Free.fold P (leaf inputs) (algebra law X)

@[simp]
theorem evaluate_pure {X : Family Base Index} (inputs : VariableCoalgebra B X)
    {base : Base} {index : Index base} (value : X base index) :
    evaluate law inputs base index (Free.pure P value) = leaf inputs base index value := rfl

@[simp]
theorem evaluate_node {X : Family Base Index} (inputs : VariableCoalgebra B X)
    {base : Base} {index : Index base} (shape : P.Shape base index)
    (children : ∀ position, P.Free X base (P.next shape position)) :
    evaluate law inputs base index (Free.node P shape children) =
      (algebra law X).act base index
        ⟨shape, fun position => evaluate law inputs base _ (children position)⟩ := rfl

/-- Fold uniqueness recovers the complete supplied term, not an observation. -/
theorem evaluate_source {X : Family Base Index} (inputs : VariableCoalgebra B X)
    (base : Base) (index : Index base) (term : P.Free X base index) :
    (evaluate law inputs base index term).1 = term := by
  have same := Free.fold_unique P
    (fun base index value => Free.pure P value) (Free.algebra P)
    (fun base index term => (evaluate law inputs base index term).1)
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) base index term
  exact same.trans (Free.bind_pure_right P term)

noncomputable def coalgebra {X : Family Base Index} (inputs : VariableCoalgebra B X) :
    VariableCoalgebra B (P.Free X) :=
  fun base index => ↾(fun term => (evaluate law inputs base index term).2)

@[simp]
theorem coalgebra_pure {X : Family Base Index} (inputs : VariableCoalgebra B X)
    {base : Base} {index : Index base} (value : X base index) :
    coalgebra law inputs base index (Free.pure P value) =
      B.map ((FreeAdjunction.monad P).η.app X) base index (inputs base index value) := rfl

/-- The constructor uses complete child values and behaviors from the
actual source-retaining fold. -/
theorem coalgebra_node {X : Family Base Index} (inputs : VariableCoalgebra B X)
    {base : Base} {index : Index base} (shape : P.Shape base index)
    (children : ∀ position, P.Free X base (P.next shape position)) :
    coalgebra law inputs base index (Free.node P shape children) =
      B.map ((FreeAdjunction.monad P).μ.app X) base index
        (law.app (P.Free X) base index
          ⟨shape, fun position =>
            (children position, coalgebra law inputs base _ (children position))⟩) := by
  change B.map _ base index
    (law.app (P.Free X) base index
      ⟨shape, fun position => evaluate law inputs base _ (children position)⟩) = _
  have recovered : (fun position => evaluate law inputs base _ (children position)) =
      fun position =>
        (children position, coalgebra law inputs base _ (children position)) := by
    funext position
    apply Prod.ext
    · exact evaluate_source law inputs base _ (children position)
    · rfl
  rw [recovered]
  rfl

noncomputable def bindMap {X Y : Family Base Index} (fill : X ⟶ P.Free Y) :
    P.Free X ⟶ P.Free Y :=
  fun base index => ↾(Free.bind P (fun base index => fill base index) base index)

theorem pure_bind {X Y : Family Base Index} (fill : X ⟶ P.Free Y) :
    (FreeAdjunction.monad P).η.app X ≫ bindMap fill = fill := rfl

/-- Typed substitution commutes with flattening a complete two-level target. -/
theorem bind_join_map {X Y : Family Base Index} (fill : X ⟶ P.Free Y)
    {base : Base} {index : Index base} (term : P.Free (P.Free X) base index) :
    Free.bind P (fun base index => fill base index) base index (Free.join P term) =
      Free.join P (Free.map P
        (fun base index => Free.bind P (fun base index => fill base index) base index)
        base index term) := by
  unfold Free.join Free.map
  rw [Free.bind_assoc, Free.bind_assoc]
  rfl

theorem bind_join_arrow {X Y : Family Base Index} (fill : X ⟶ P.Free Y) :
    (FreeAdjunction.monad P).μ.app X ≫ bindMap fill =
      (FreeAdjunction.monad P).map (bindMap fill) ≫ (FreeAdjunction.monad P).μ.app Y := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro term
  exact bind_join_map fill term

/-- An independently supplied coalgebra-respecting variable substitution
respects the complete operational behavior of every free term. -/
theorem coalgebra_bind {X Y : Family Base Index}
    (first : VariableCoalgebra B X) (second : VariableCoalgebra B Y)
    (fill : X ⟶ P.Free Y)
    (respects : ∀ base index value,
      coalgebra law second base index (fill base index value) =
        B.map fill base index (first base index value))
    (base : Base) (index : Index base) (term : P.Free X base index) :
    coalgebra law second base index (bindMap fill base index term) =
      B.map (bindMap fill) base index (coalgebra law first base index term) := by
  refine Fix.rec (polynomial := P.withHoles X) (base := base)
    (motive := fun index current =>
      coalgebra law second base index (bindMap fill base index current) =
        B.map (bindMap fill) base index (coalgebra law first base index current))
    (fun {index} shape children ih => ?_) term
  cases shape with
  | inl value =>
      have empty : children = fun position => position.elim := by
        funext position
        exact position.elim
      subst children
      change coalgebra law second base index (fill base index value) =
        B.map (bindMap fill) base index
          (coalgebra law first base index (Free.pure P value))
      rw [respects, coalgebra_pure]
      have combined := map_apply_comp B ((FreeAdjunction.monad P).η.app X)
        (bindMap fill) base index (first base index value)
      rw [pure_bind] at combined
      exact combined.symm
  | inr shape =>
      change P.Shape base index at shape
      change (position : P.Position shape) → P.Free X base (P.next shape position) at children
      change coalgebra law second base index
        (Free.bind P (fun base index => fill base index) base index
          (Free.node P shape children)) =
        B.map (bindMap fill) base index
          (coalgebra law first base index (Free.node P shape children))
      rw [Free.bind_node, coalgebra_node, coalgebra_node]
      let mapping : P.Free X ⟶ P.Free Y := bindMap fill
      let inputs : (position : P.Position shape) →
          (sourceBehaviourFunctor B).obj (P.Free X) base (P.next shape position) :=
        fun position => (children position, coalgebra law first base _ (children position))
      have matching : (fun position =>
          (Free.bind P (fun base index => fill base index) base _ (children position),
            coalgebra law second base _
              (Free.bind P (fun base index => fill base index) base _ (children position)))) =
          fun position =>
            (mapping base _ (inputs position).1, B.map mapping base _ (inputs position).2) := by
        funext position
        apply Prod.ext
        · rfl
        · exact ih position
      have natural := congrArg (fun arrow => arrow base index ⟨shape, inputs⟩)
        (law.naturality mapping)
      change law.app (P.Free Y) base index
          ⟨shape, fun position =>
            (mapping base _ (inputs position).1, B.map mapping base _ (inputs position).2)⟩ =
        B.map ((FreeAdjunction.monad P).map mapping) base index
          (law.app (P.Free X) base index ⟨shape, inputs⟩) at natural
      change B.map ((FreeAdjunction.monad P).μ.app Y) base index
          (law.app (P.Free Y) base index
            ⟨shape, fun position =>
              (Free.bind P (fun base index => fill base index) base _ (children position),
                coalgebra law second base _
                  (Free.bind P (fun base index => fill base index) base _ (children position)))⟩) =
        B.map mapping base index (B.map ((FreeAdjunction.monad P).μ.app X) base index
          (law.app (P.Free X) base index ⟨shape, inputs⟩))
      rw [matching, natural]
      have flatten := map_apply_comp B ((FreeAdjunction.monad P).map mapping)
        ((FreeAdjunction.monad P).μ.app Y) base index
        (law.app (P.Free X) base index ⟨shape, inputs⟩)
      change B.map ((FreeAdjunction.monad P).μ.app Y) base index
          (B.map ((FreeAdjunction.monad P).map (bindMap fill)) base index
            (law.app (P.Free X) base index ⟨shape, inputs⟩)) =
        B.map ((FreeAdjunction.monad P).map (bindMap fill) ≫
          (FreeAdjunction.monad P).μ.app Y) base index
          (law.app (P.Free X) base index ⟨shape, inputs⟩) at flatten
      rw [← bind_join_arrow] at flatten
      exact flatten.trans (map_apply_comp B ((FreeAdjunction.monad P).μ.app X)
        mapping base index (law.app (P.Free X) base index ⟨shape, inputs⟩)).symm

theorem coalgebra_join {X : Family Base Index} (inputs : VariableCoalgebra B X)
    (base : Base) (index : Index base) (term : P.Free (P.Free X) base index) :
    coalgebra law inputs base index (Free.join P term) =
      B.map ((FreeAdjunction.monad P).μ.app X) base index
        (coalgebra law (coalgebra law inputs) base index term) := by
  exact coalgebra_bind law (coalgebra law inputs) inputs (𝟙 (P.Free X))
    (fun base index value => (map_apply_identity B _ base index _).symm) base index term

theorem coalgebra_rename {X Y : Family Base Index}
    (first : VariableCoalgebra B X) (second : VariableCoalgebra B Y)
    (mapping : X ⟶ Y)
    (respects : ∀ base index value,
      second base index (mapping base index value) =
        B.map mapping base index (first base index value))
    (base : Base) (index : Index base) (term : P.Free X base index) :
    coalgebra law second base index ((FreeAdjunction.monad P).map mapping base index term) =
      B.map ((FreeAdjunction.monad P).map mapping) base index
        (coalgebra law first base index term) := by
  apply coalgebra_bind law first second (mapping ≫ (FreeAdjunction.monad P).η.app Y)
  intro base index value
  change coalgebra law second base index (Free.pure P (mapping base index value)) =
    B.map (mapping ≫ (FreeAdjunction.monad P).η.app Y) base index (first base index value)
  rw [coalgebra_pure, respects]
  exact map_apply_comp B mapping ((FreeAdjunction.monad P).η.app Y)
    base index (first base index value)

end Operational
end Mettapedia.TypeTheory.IndexedGSOS
