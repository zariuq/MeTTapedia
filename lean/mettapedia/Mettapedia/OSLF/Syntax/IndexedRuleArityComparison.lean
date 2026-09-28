import Mettapedia.OSLF.Syntax.IndexedRuleFiniteContextSemantics
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Arity comparison for product-preserving interpretations

The finitary premise context of a constructor is the product of its typed
singleton contexts. A finite-product-preserving functor therefore turns the
single arity object into the family of semantic values at every ordered
premise position. This comparison is the nontrivial input to recovering an
algebra action from an arbitrary interpretation of the syntactic category.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts

open Mettapedia.TypeTheory
open CategoryTheory
open CategoryTheory.Limits

universe uIndex uShape uSem uFamily

variable {Judgment : Type uIndex}
variable (P : IndexedPolynomial.{0, uIndex, uShape, 0}
  Unit (fun _ => Judgment))

/-- A product-preserving functor takes the proved arity fan to a semantic
product fan. -/
noncomputable def mappedArityIsLimit
    (F : Context P ⥤ Type (max uIndex uSem)) [PreservesFiniteProducts F]
    {judgment : Judgment} (shape : P.Shape PUnit.unit judgment)
    [Finite (P.Position shape)] :
    IsLimit (Fan.mk (F.obj (arityContext P shape))
      (fun position => F.map (positionProjection P shape position))) :=
  isLimitFanMkObjOfIsLimit F
    (fun position => singleton P (P.next shape position))
    (positionProjection P shape) (arityFanIsLimit P shape)

/-- In types, a limiting fan identifies its vertex with the dependent
family of its projections. The inverse uses its actual universal lift. -/
noncomputable def typeFanComparison
    {I : Type uFamily} {family : I → Type uSem} {X : Type uSem}
    (projection : ∀ index, X ⟶ family index)
    (limit : IsLimit (Fan.mk X projection)) :
    X ≃ ((index : I) → family index) where
  toFun := fun value index => projection index value
  invFun := fun values =>
    limit.lift (Fan.mk PUnit (fun index => TypeCat.ofHom (fun _ => values index)))
      PUnit.unit
  left_inv := by
    intro value
    let fan : Fan family := Fan.mk PUnit
      (fun index => TypeCat.ofHom (fun _ => projection index value))
    have h := limit.uniq fan (TypeCat.ofHom (fun _ => value)) (by
      intro index
      apply TypeCat.Hom.ext
      apply TypeCat.Fun.ext
      funext point
      cases point
      rfl)
    have atPoint := congrArg (fun mapping : PUnit ⟶ X => mapping PUnit.unit) h
    exact atPoint.symm
  right_inv := by
    intro values
    funext index
    have h := limit.fac
      (Fan.mk PUnit (fun i => TypeCat.ofHom (fun _ => values i))) ⟨index⟩
    have atPoint := congrArg
      (fun mapping : PUnit ⟶ family index => mapping PUnit.unit) h
    exact atPoint

/-- The explicit semantic comparison. Its inverse is the unique lift of
the point-valued fan, not an assumed map of arbitrary event functions. -/
noncomputable def arityComparison
    (F : Context P ⥤ Type (max uIndex uSem)) [PreservesFiniteProducts F]
    {judgment : Judgment} (shape : P.Shape PUnit.unit judgment)
    [Finite (P.Position shape)] :
    F.obj (arityContext P shape) ≃
      ((position : P.Position shape) →
        F.obj (singleton P (P.next shape position))) :=
  typeFanComparison (fun position => F.map (positionProjection P shape position))
    (mappedArityIsLimit P F shape)

/-- The arity comparison is natural in a map of interpretations. It does
not require that the map cover or inject firing events. -/
theorem arityComparison_natural
    (F G : Context P ⥤ Type (max uIndex uSem))
    [PreservesFiniteProducts F] [PreservesFiniteProducts G]
    (mapping : F ⟶ G)
    {judgment : Judgment} (shape : P.Shape PUnit.unit judgment)
    [Finite (P.Position shape)]
    (value : F.obj (arityContext P shape)) :
    (arityComparison P G shape) (mapping.app (arityContext P shape) value) =
      (fun position =>
        mapping.app (singleton P (P.next shape position))
          ((arityComparison P F shape) value position)) := by
  funext position
  have h := congrArg
    (fun arrow : F.obj (arityContext P shape) ⟶
        G.obj (singleton P (P.next shape position)) => arrow value)
    (mapping.naturality (positionProjection P shape position))
  exact h.symm

set_option linter.style.haveILetI false in
/-- A product-preserving functor also preserves the product decomposition of
an arbitrary finite event-variable context. -/
noncomputable def mappedContextIsLimit
    (F : Context P ⥤ Type (max uIndex uSem)) [PreservesFiniteProducts F]
    (Γ : Context P) :
    IsLimit (Fan.mk (F.obj Γ)
      (fun selected : Σ judgment, Γ.slots judgment =>
        F.map (variableProjection P Γ selected))) := by
  letI : Finite (Σ judgment, Γ.slots judgment) := Γ.finite
  exact isLimitFanMkObjOfIsLimit F
    (fun selected : Σ judgment, Γ.slots judgment => singleton P selected.1)
    (variableProjection P Γ) (contextFanIsLimit P Γ)

/-- Currying the finite family of projected values gives a valuation. -/
def selectedValuesEquiv
    (F : Context P ⥤ Type (max uIndex uSem)) (Γ : Context P) :
    ((selected : Σ judgment, Γ.slots judgment) →
      F.obj (singleton P selected.1)) ≃
      Valuation P (carrier := fun judgment => F.obj (singleton P judgment)) Γ where
  toFun := fun values judgment slot => values ⟨judgment, slot⟩
  invFun := fun assignment ⟨judgment, slot⟩ => assignment judgment slot
  left_inv := by intro values; funext ⟨judgment, slot⟩; rfl
  right_inv := by intro assignment; funext judgment slot; rfl

/-- An interpretation of a finite context is exactly an assignment of
semantic values to its typed variables. This is the object comparison in
the reverse classifier direction. -/
noncomputable def contextComparison
    (F : Context P ⥤ Type (max uIndex uSem)) [PreservesFiniteProducts F]
    (Γ : Context P) :
    F.obj Γ ≃
      Valuation P (carrier := fun judgment => F.obj (singleton P judgment)) Γ :=
  (typeFanComparison
    (fun selected : Σ judgment, Γ.slots judgment =>
      F.map (variableProjection P Γ selected))
    (mappedContextIsLimit P F Γ)).trans (selectedValuesEquiv P F Γ)

/-- The context comparison also respects ordinary natural maps between
product-preserving interpretations, pointwise at each typed variable. -/
theorem contextComparison_map_natural
    (F G : Context P ⥤ Type (max uIndex uSem))
    [PreservesFiniteProducts F] [PreservesFiniteProducts G]
    (mapping : F ⟶ G) (Γ : Context P) (value : F.obj Γ) :
    (contextComparison P G Γ) (mapping.app Γ value) =
      (fun judgment slot =>
        mapping.app (singleton P judgment)
          (((contextComparison P F Γ) value) judgment slot)) := by
  funext judgment slot
  have h := congrArg
    (fun arrow : F.obj Γ ⟶ G.obj (singleton P judgment) => arrow value)
    (mapping.naturality (variableProjection P Γ ⟨judgment, slot⟩))
  exact h.symm

/-- Recover the semantic action of every constructor from its arrow in a
finite-product-preserving interpretation. Finitarity supplies the actual
arity object; the functor supplies its interpretation. -/
noncomputable def recoverAlgebra
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape))
    (F : Context P ⥤ Type (max uIndex uSem)) [PreservesFiniteProducts F] :
    P.Algebra (fun _ judgment => F.obj (singleton P judgment)) where
  act := fun _ judgment ⟨shape, children⟩ => by
    letI : Finite (P.Position shape) := finitePositions judgment shape
    exact F.map (constructorArrow P shape)
      ((arityComparison P F shape).symm children)

set_option linter.style.haveILetI false in
/-- Every ordinary natural map of product-preserving interpretations
induces a homomorphism of the recovered rule algebras. No coverage or
injectivity condition is imposed on the natural map. -/
noncomputable def recoverAlgebraMap
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape))
    (F G : Context P ⥤ Type (max uIndex uSem))
    [PreservesFiniteProducts F] [PreservesFiniteProducts G]
    (mapping : F ⟶ G) :
    IndexedPolynomial.Algebra.Hom
      (recoverAlgebra P finitePositions F)
      (recoverAlgebra P finitePositions G) where
  toFun := fun _ judgment => mapping.app (singleton P judgment)
  commutes := by
    intro base judgment layer
    obtain ⟨shape, children⟩ := layer
    letI : Finite (P.Position shape) := finitePositions judgment shape
    let arguments := (arityComparison P F shape).symm children
    have hargs : mapping.app (arityContext P shape) arguments =
        (arityComparison P G shape).symm
          (fun position => mapping.app (singleton P (P.next shape position))
            (children position)) := by
      apply (arityComparison P G shape).injective
      have h := arityComparison_natural P F G mapping shape arguments
      dsimp [arguments] at h
      simpa only [Equiv.apply_symm_apply] using h
    have hnat := congrArg
      (fun arrow : F.obj (arityContext P shape) ⟶
          G.obj (singleton P judgment) => arrow arguments)
      (mapping.naturality (constructorArrow P shape))
    change mapping.app (singleton P judgment)
        (F.map (constructorArrow P shape) arguments) =
      G.map (constructorArrow P shape)
        ((arityComparison P G shape).symm
          (fun position => mapping.app (singleton P (P.next shape position))
            (children position)))
    exact hnat.trans (congrArg
      (fun value => G.map (constructorArrow P shape) value) hargs)

set_option linter.style.haveILetI false in
/-- Reconstructing the algebra of a Set-valued interpretation returns the
original action, through the concrete singleton-context equivalences. -/
noncomputable def recoverSemanticsHom
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape))
    {carrier : Judgment → Type uSem}
    (A : P.Algebra (fun _ judgment => carrier judgment)) :
    IndexedPolynomial.Algebra.Hom
      (recoverAlgebra P finitePositions (algebraSemantics P A)) A where
  toFun := fun _ judgment => singletonValuation P judgment
  commutes := by
    intro base judgment layer
    obtain ⟨shape, children⟩ := layer
    letI : Finite (P.Position shape) := finitePositions judgment shape
    let assignment :=
      (arityComparison P (algebraSemantics P A) shape).symm children
    change (singletonValuation P judgment)
        ((algebraSemantics P A).map (constructorArrow P shape) assignment) =
      A.act PUnit.unit judgment
        ⟨shape, fun position =>
          (singletonValuation P (P.next shape position)) (children position)⟩
    refine (algebraSemantics_constructor P A shape assignment).trans ?_
    have hchildren :
        (arityValuation P shape) assignment =
          (fun position =>
            (singletonValuation P (P.next shape position)) (children position)) := by
      funext position
      have h := congrFun
        ((arityComparison P (algebraSemantics P A) shape).apply_symm_apply children)
        position
      exact congrArg (singletonValuation P (P.next shape position)) h
    rw [hchildren]

/-- The inverse singleton equivalences also preserve every constructor
action. Thus the recovered algebra is genuinely isomorphic to the original
algebra, not merely equivalent as a family of carriers. -/
noncomputable def recoverSemanticsInvHom
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape))
    {carrier : Judgment → Type uSem}
    (A : P.Algebra (fun _ judgment => carrier judgment)) :
    IndexedPolynomial.Algebra.Hom A
      (recoverAlgebra P finitePositions (algebraSemantics P A)) where
  toFun := fun _ judgment => (singletonValuation P judgment).symm
  commutes := by
    intro base judgment layer
    apply (singletonValuation P judgment).injective
    let h := recoverSemanticsHom P finitePositions A
    have law := h.commutes base judgment
      (IndexedPolynomial.Extension.map P
        (fun _ j value => (singletonValuation P j).symm value) layer)
    change A.act base judgment layer =
      (singletonValuation P judgment)
        ((recoverAlgebra P finitePositions (algebraSemantics P A)).act
          base judgment
          (IndexedPolynomial.Extension.map P
            (fun _ j value => (singletonValuation P j).symm value) layer))
    refine Eq.trans ?_ law.symm
    cases layer with
    | mk shape children =>
        change A.act base judgment ⟨shape, children⟩ =
          A.act base judgment
            ⟨shape, fun position =>
              (singletonValuation P (P.next shape position))
                ((singletonValuation P (P.next shape position)).symm
                  (children position))⟩
        simp

/-- The two algebra homomorphisms are inverse on each original carrier. -/
theorem recoverSemantics_original_roundTrip
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape))
    {carrier : Judgment → Type uSem}
    (A : P.Algebra (fun _ judgment => carrier judgment))
    (judgment : Judgment) (value : carrier judgment) :
    (recoverSemanticsHom P finitePositions A).toFun PUnit.unit judgment
      ((recoverSemanticsInvHom P finitePositions A).toFun
        PUnit.unit judgment value) = value :=
  (singletonValuation P judgment).apply_symm_apply value

/-- The same round trip is the identity on recovered carrier values. -/
theorem recoverSemantics_recovered_roundTrip
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape))
    {carrier : Judgment → Type uSem}
    (A : P.Algebra (fun _ judgment => carrier judgment))
    (judgment : Judgment)
    (value : (algebraSemantics P A).obj (singleton P judgment)) :
    (recoverSemanticsInvHom P finitePositions A).toFun PUnit.unit judgment
      ((recoverSemanticsHom P finitePositions A).toFun
        PUnit.unit judgment value) = value :=
  (singletonValuation P judgment).symm_apply_apply value

set_option linter.style.haveILetI false in
/-- Every free term arrow is interpreted by the recovered algebra's fold.
This is the substitution-sensitive coherence theorem needed for the
functor-to-algebra-to-functor round trip. -/
theorem termArrow_interpretation
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape))
    (F : Context P ⥤ Type (max uIndex uSem)) [PreservesFiniteProducts F]
    (Γ : Context P) (value : F.obj Γ)
    (judgment : Judgment) (tree : Term P Γ judgment) :
    F.map (termArrow P tree) value =
      interpretTerm P (recoverAlgebra P finitePositions F)
        ((contextComparison P F Γ) value) tree := by
  apply IndexedPolynomial.Free.fold_unique P
    (fun _ index slot => ((contextComparison P F Γ) value) index slot)
    (recoverAlgebra P finitePositions F)
    (fun _ index term => F.map (termArrow P term) value)
  · intro base index slot
    change F.map (termArrow P (IndexedPolynomial.Free.pure P slot)) value =
      ((contextComparison P F Γ) value) index slot
    rw [termArrow_pure]
    rfl
  · intro base index shape children
    letI : Finite (P.Position shape) := finitePositions index shape
    let arguments := tupleArrow P shape children
    let results : (position : P.Position shape) →
        F.obj (singleton P (P.next shape position)) :=
      fun position => F.map (termArrow P (children position)) value
    have hargs : F.map arguments value =
        (arityComparison P F shape).symm results := by
      apply (arityComparison P F shape).injective
      funext position
      simp only [Equiv.apply_symm_apply]
      change F.map (positionProjection P shape position)
          (F.map arguments value) = results position
      calc
        F.map (positionProjection P shape position)
            (F.map arguments value) =
          F.map (arguments ≫ positionProjection P shape position) value := by
            rw [F.map_comp]
            rfl
        _ = results position := by
          change F.map (arguments ≫ positionProjection P shape position) value =
            F.map (termArrow P (children position)) value
          rw [tupleArrow_projection]
    change F.map (termArrow P
        (IndexedPolynomial.Free.node P shape children)) value =
      F.map (constructorArrow P shape)
        ((arityComparison P F shape).symm results)
    calc
      F.map (termArrow P
          (IndexedPolynomial.Free.node P shape children)) value =
        F.map (constructorArrow P shape) (F.map arguments value) := by
          rw [← tupleArrow_constructor P shape children, F.map_comp]
          rfl
      _ = _ := by rw [hargs]

/-- The context comparison respects every simultaneous substitution. The
tree induction above supplies the nontrivial componentwise equation. -/
theorem contextComparison_natural
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape))
    (F : Context P ⥤ Type (max uIndex uSem)) [PreservesFiniteProducts F]
    {Γ Δ : Context P} (substitution : Γ ⟶ Δ) (value : F.obj Γ) :
    (contextComparison P F Δ) (F.map substitution value) =
      (algebraSemantics P (recoverAlgebra P finitePositions F)).map substitution
        ((contextComparison P F Γ) value) := by
  funext judgment slot
  calc
    ((contextComparison P F Δ) (F.map substitution value)) judgment slot =
      F.map (variableProjection P Δ ⟨judgment, slot⟩)
        (F.map substitution value) := rfl
    _ = F.map (termArrow P (substitution judgment slot)) value := by
      calc
        F.map (variableProjection P Δ ⟨judgment, slot⟩)
            (F.map substitution value) =
          F.map (substitution ≫ variableProjection P Δ ⟨judgment, slot⟩)
            value := by rw [F.map_comp]; rfl
        _ = F.map (termArrow P (substitution judgment slot)) value := by
          rw [compose_variableProjection]
    _ = interpretTerm P (recoverAlgebra P finitePositions F)
        ((contextComparison P F Γ) value)
        (substitution judgment slot) :=
      termArrow_interpretation P finitePositions F Γ value judgment
        (substitution judgment slot)
    _ = ((algebraSemantics P (recoverAlgebra P finitePositions F)).map
        substitution ((contextComparison P F Γ) value)) judgment slot := rfl

/-- The recovered algebra's Set-valued semantics is naturally isomorphic
to the original finite-product-preserving interpretation. -/
noncomputable def contextComparisonIso
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape))
    (F : Context P ⥤ Type (max uIndex uSem)) [PreservesFiniteProducts F] :
    F ≅ algebraSemantics P (recoverAlgebra P finitePositions F) :=
  NatIso.ofComponents
    (fun Γ => (contextComparison P F Γ).toIso)
    (by
      intro Γ Δ substitution
      apply TypeCat.Hom.ext
      apply TypeCat.Fun.ext
      funext value
      exact contextComparison_natural P finitePositions F substitution value)

end Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts
