import Mettapedia.OSLF.Syntax.DeterministicGSOSCorrespondence

/-!
# Operational extension of an actual deterministic GSOS law

An independently supplied variable coalgebra extends to the actual free
constructor terms. The fold retains each complete term and calculates its
one-step behavior from the natural law, flattening its supplied conclusion
with the existing free-monad multiplication. Coalgebra-respecting typed
substitution commutes with this operational extension.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS

open CategoryTheory Mettapedia.TypeTheory

universe u

variable {S : Signature.{u}} (Actions : S.Srt → Type u)

/-- A variable's independently supplied complete deterministic behavior. -/
abbrev VariableCoalgebra (X : S.Families) := X ⟶ (behaviourFunctor S Actions).obj X

namespace Operational

variable {Actions} (law : Law S Actions)

abbrev Result (X : S.Families) : S.Families :=
  (sourceBehaviourFunctor S Actions).obj (S.polynomial.Free X)

/-- The actual constructor action calculates an edge and flattens its target. -/
noncomputable def algebra (X : S.Families) : S.polynomial.Algebra (Result (Actions := Actions) X) where
  act := fun base sort layer =>
    (IndexedPolynomial.Free.node S.polynomial layer.1 (fun position => (layer.2 position).1),
      fun action => (law.app (S.polynomial.Free X) base sort layer action).map
        (IndexedPolynomial.Free.join S.polynomial))

/-- The independent variable coalgebra is the fold's actual leaf interpretation. -/
noncomputable def leaf {X : S.Families} (coalgebra : VariableCoalgebra Actions X)
    (base : PUnit.{u + 1}) (sort : S.Srt) (value : X base sort) :
    Result (Actions := Actions) X base sort :=
  (IndexedPolynomial.Free.pure S.polynomial value,
    fun action => (coalgebra base sort value action).map (IndexedPolynomial.Free.pure S.polynomial))

/-- Calculate the source and one-step behavior by the existing free fold. -/
noncomputable def evaluate {X : S.Families} (coalgebra : VariableCoalgebra Actions X) :
    ∀ base sort, S.polynomial.Free X base sort → Result (Actions := Actions) X base sort :=
  IndexedPolynomial.Free.fold S.polynomial (leaf coalgebra) (algebra law X)

@[simp] theorem evaluate_pure {X : S.Families} (coalgebra : VariableCoalgebra Actions X)
    {base : PUnit.{u + 1}} {sort : S.Srt} (value : X base sort) :
    evaluate law coalgebra base sort (IndexedPolynomial.Free.pure S.polynomial value) =
      leaf coalgebra base sort value := rfl

@[simp] theorem evaluate_node {X : S.Families} (coalgebra : VariableCoalgebra Actions X)
    {base : PUnit.{u + 1}} {sort : S.Srt} (operator : S.Operator sort)
    (children : ∀ position, S.polynomial.Free X base (S.argument operator position)) :
    evaluate law coalgebra base sort (IndexedPolynomial.Free.node S.polynomial operator children) =
      (algebra law X).act base sort
        ⟨operator, fun position => evaluate law coalgebra base _ (children position)⟩ := rfl

/-- The fold's first coordinate is the supplied complete constructor term. -/
theorem evaluate_source {X : S.Families} (coalgebra : VariableCoalgebra Actions X)
    (base : PUnit.{u + 1}) (sort : S.Srt) (term : S.polynomial.Free X base sort) :
    (evaluate law coalgebra base sort term).1 = term := by
  have same := IndexedPolynomial.Free.fold_unique S.polynomial
    (fun base sort value => IndexedPolynomial.Free.pure S.polynomial value)
    (IndexedPolynomial.Free.algebra S.polynomial)
    (fun base sort term => (evaluate law coalgebra base sort term).1)
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) base sort term
  exact same.trans (IndexedPolynomial.Free.bind_pure_right S.polynomial term)

/-- The genuine one-step coalgebra on all free terms. -/
noncomputable def coalgebra {X : S.Families} (inputs : VariableCoalgebra Actions X) :
    VariableCoalgebra Actions (S.polynomial.Free X) :=
  fun base sort => ↾(fun term => (evaluate law inputs base sort term).2)

@[simp] theorem coalgebra_pure {X : S.Families} (inputs : VariableCoalgebra Actions X)
    {base : PUnit.{u + 1}} {sort : S.Srt} (value : X base sort) (action : Actions sort) :
    coalgebra law inputs base sort (IndexedPolynomial.Free.pure S.polynomial value) action =
      (inputs base sort value action).map (IndexedPolynomial.Free.pure S.polynomial) := rfl

/-- The operational constructor equation uses the complete actual child behaviors. -/
theorem coalgebra_node {X : S.Families} (inputs : VariableCoalgebra Actions X)
    {base : PUnit.{u + 1}} {sort : S.Srt} (operator : S.Operator sort)
    (children : ∀ position, S.polynomial.Free X base (S.argument operator position))
    (action : Actions sort) :
    coalgebra law inputs base sort (IndexedPolynomial.Free.node S.polynomial operator children) action =
      (law.app (S.polynomial.Free X) base sort
        ⟨operator, fun position => (children position, coalgebra law inputs base _ (children position))⟩
        action).map (IndexedPolynomial.Free.join S.polynomial) := by
  change (law.app (S.polynomial.Free X) base sort
    ⟨operator, fun position => evaluate law inputs base _ (children position)⟩ action).map _ = _
  have recovered : (fun position => evaluate law inputs base _ (children position)) =
      fun position => (children position, coalgebra law inputs base _ (children position)) := by
    funext position
    apply Prod.ext
    · exact evaluate_source law inputs base _ (children position)
    · rfl
  rw [recovered]
  rfl

/-- Filling variables commutes with flattening a supplied two-level target. -/
theorem bind_join_map {X Y : S.Families}
    (fill : ∀ base sort, X base sort → S.polynomial.Free Y base sort)
    {base : PUnit.{u + 1}} {sort : S.Srt}
    (term : S.polynomial.Free (S.polynomial.Free X) base sort) :
    IndexedPolynomial.Free.bind S.polynomial fill base sort
        (IndexedPolynomial.Free.join S.polynomial term) =
      IndexedPolynomial.Free.join S.polynomial
        (IndexedPolynomial.Free.map S.polynomial
          (fun base sort => IndexedPolynomial.Free.bind S.polynomial fill base sort) base sort term) := by
  unfold IndexedPolynomial.Free.join IndexedPolynomial.Free.map
  rw [IndexedPolynomial.Free.bind_assoc, IndexedPolynomial.Free.bind_assoc]
  rfl

/-- Actual operational behavior respects every coalgebra-respecting typed substitution. -/
theorem coalgebra_bind {X Y : S.Families}
    (first : VariableCoalgebra Actions X) (second : VariableCoalgebra Actions Y)
    (fill : ∀ base sort, X base sort → S.polynomial.Free Y base sort)
    (respects : ∀ base sort value,
      coalgebra law second base sort (fill base sort value) =
        fun action => (first base sort value action).map (fill base sort))
    (base : PUnit.{u + 1}) (sort : S.Srt) (term : S.polynomial.Free X base sort) :
    coalgebra law second base sort (IndexedPolynomial.Free.bind S.polynomial fill base sort term) =
      fun action => (coalgebra law first base sort term action).map
        (IndexedPolynomial.Free.bind S.polynomial fill base sort) := by
  refine IndexedPolynomial.Fix.rec
    (polynomial := S.polynomial.withHoles X) (base := base)
    (motive := fun index current =>
      coalgebra law second base index (IndexedPolynomial.Free.bind S.polynomial fill base index current) =
        fun action => (coalgebra law first base index current action).map
          (IndexedPolynomial.Free.bind S.polynomial fill base index))
    (fun {index} shape children ih => ?_) term
  cases shape with
      | inl value =>
          cases base
          have empty : children = fun position => position.elim := by
            funext position
            exact position.elim
          subst children
          change coalgebra law second PUnit.unit index (fill PUnit.unit index value) =
            fun action => (coalgebra law first PUnit.unit index
              (IndexedPolynomial.Free.pure S.polynomial value) action).map
                (IndexedPolynomial.Free.bind S.polynomial fill PUnit.unit index)
          rw [respects]
          funext action
          rw [coalgebra_pure]
          cases first PUnit.unit _ value action <;> rfl
      | inr operator =>
          cases base
          change S.Operator index at operator
          change (position : S.Position operator) →
            S.polynomial.Free X PUnit.unit (S.argument operator position) at children
          change coalgebra law second PUnit.unit index
            (IndexedPolynomial.Free.bind S.polynomial fill PUnit.unit index
              (IndexedPolynomial.Free.node S.polynomial operator children)) =
            fun action => (coalgebra law first PUnit.unit index
              (IndexedPolynomial.Free.node S.polynomial operator children) action).map
                (IndexedPolynomial.Free.bind S.polynomial fill PUnit.unit index)
          rw [IndexedPolynomial.Free.bind_node]
          funext action
          rw [coalgebra_node, coalgebra_node]
          let mapping : S.polynomial.Free X ⟶ S.polynomial.Free Y :=
            fun base sort => ↾(IndexedPolynomial.Free.bind S.polynomial fill base sort)
          let inputs : BehaviourArguments S Actions (S.polynomial.Free X) operator :=
            fun position => (children position, coalgebra law first PUnit.unit _ (children position))
          have matching : (fun position =>
              (IndexedPolynomial.Free.bind S.polynomial fill PUnit.unit _ (children position),
                coalgebra law second PUnit.unit _
                  (IndexedPolynomial.Free.bind S.polynomial fill PUnit.unit _ (children position)))) =
              mapArguments Actions mapping inputs := by
            funext position
            apply Prod.ext
            · rfl
            · exact ih position
          have natural := congrArg (fun map => map PUnit.unit _ ⟨operator, inputs⟩ action)
            (law.naturality mapping)
          change law.app (S.polynomial.Free Y) PUnit.unit _
              ⟨operator, mapArguments Actions mapping inputs⟩ action =
            (law.app (S.polynomial.Free X) PUnit.unit _ ⟨operator, inputs⟩ action).map
              (IndexedPolynomial.Free.map S.polynomial (fun base sort => mapping base sort) PUnit.unit _) at natural
          have flatten : ∀ result : Option (S.polynomial.Free (S.polynomial.Free X) PUnit.unit index),
              (result.map (IndexedPolynomial.Free.map S.polynomial
                (fun base sort => IndexedPolynomial.Free.bind S.polynomial fill base sort) PUnit.unit index)).map
                  (IndexedPolynomial.Free.join S.polynomial) =
                (result.map (IndexedPolynomial.Free.join S.polynomial)).map
                  (IndexedPolynomial.Free.bind S.polynomial fill PUnit.unit index) := by
            intro result
            cases result with
            | none => rfl
            | some target => exact congrArg some (bind_join_map fill target).symm
          exact (congrArg (fun input : BehaviourArguments S Actions (S.polynomial.Free Y) operator =>
              (law.app (S.polynomial.Free Y) PUnit.unit index ⟨operator, input⟩ action).map
                (IndexedPolynomial.Free.join S.polynomial)) matching).trans
            ((congrArg (Option.map (IndexedPolynomial.Free.join S.polynomial)) natural).trans (flatten _))

/-- The actual monad multiplication is a coalgebra morphism for the lifted behavior. -/
theorem coalgebra_join {X : S.Families} (inputs : VariableCoalgebra Actions X)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free (S.polynomial.Free X) base sort) :
    coalgebra law inputs base sort (IndexedPolynomial.Free.join S.polynomial term) =
      fun action => (coalgebra law (coalgebra law inputs) base sort term action).map
        (IndexedPolynomial.Free.join S.polynomial) :=
  coalgebra_bind law (coalgebra law inputs) inputs (fun _ _ term => term)
    (fun _ _ _ => by funext action; cases coalgebra law inputs _ _ _ action <;> rfl) base sort term

/-- A map respecting the independently supplied variable coalgebras respects all free terms. -/
theorem coalgebra_rename {X Y : S.Families}
    (first : VariableCoalgebra Actions X) (second : VariableCoalgebra Actions Y)
    (mapping : X ⟶ Y)
    (respects : ∀ base sort value,
      second base sort (mapping base sort value) =
        fun action => (first base sort value action).map (mapping base sort))
    (base : PUnit.{u + 1}) (sort : S.Srt) (term : S.polynomial.Free X base sort) :
    coalgebra law second base sort
        (IndexedPolynomial.Free.map S.polynomial (fun base sort => mapping base sort) base sort term) =
      fun action => (coalgebra law first base sort term action).map
        (IndexedPolynomial.Free.map S.polynomial (fun base sort => mapping base sort) base sort) := by
  apply coalgebra_bind law first second
    (fun base sort value => IndexedPolynomial.Free.pure S.polynomial (mapping base sort value))
  intro base sort value
  funext action
  rw [coalgebra_pure, respects]
  dsimp only
  cases first base sort value action <;> rfl

end Operational

end Mettapedia.OSLF.DeterministicGSOS
