import Mettapedia.OSLF.Syntax.IndexedRuleFiniteContexts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Set-valued interpretation of finite event-variable contexts

An indexed polynomial algebra interprets each free tree under an assignment
of its event variables. These assignments form a functor from the finite
context category to types. The constructor arrow is interpreted by the
algebra's actual action on its recursive arguments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts

open Mettapedia.TypeTheory
open CategoryTheory
open CategoryTheory.Limits

universe uIndex uShape uCarrier

variable {Judgment : Type uIndex}
variable (P : IndexedPolynomial.{0, uIndex, uShape, 0}
  Unit (fun _ => Judgment))
variable {carrier : Judgment → Type uCarrier}

/-- An assignment gives a semantic value to every event variable at its
judgment. -/
abbrev Valuation (Γ : Context P) : Type _ :=
  ∀ judgment, Γ.slots judgment → carrier judgment

/-- Evaluate a free tree using the chosen event assignments and the
polynomial algebra. -/
noncomputable def interpretTerm (A : P.Algebra (fun _ judgment => carrier judgment))
    {Γ : Context P} (assignment : Valuation P (carrier := carrier) Γ)
    {judgment : Judgment} (tree : Term P Γ judgment) : carrier judgment :=
  IndexedPolynomial.Free.fold P
    (fun _ index slot => assignment index slot) A PUnit.unit judgment tree

/-- Substitute variables first or evaluate their substituted trees first:
the two routes have the same semantic value. -/
theorem interpretTerm_compose (A : P.Algebra (fun _ judgment => carrier judgment))
    {Γ Δ Θ : Context P} (assignment : Valuation P (carrier := carrier) Γ)
    (earlier : Γ ⟶ Δ) (later : Δ ⟶ Θ)
    {judgment : Judgment} (slot : Θ.slots judgment) :
    interpretTerm P A assignment ((earlier ≫ later) judgment slot) =
      interpretTerm P A
        (fun index slotValue => interpretTerm P A assignment (earlier index slotValue))
        (later judgment slot) := by
  exact IndexedPolynomial.Free.fold_bind P
    (fun _ index slotValue => earlier index slotValue)
    (fun _ index slotValue => assignment index slotValue)
    A (later judgment slot)

/-- The interpretation functor sends a context to its assignments and a
substitution to simultaneous evaluation of its target terms. -/
noncomputable def algebraSemantics
    (A : P.Algebra (fun _ judgment => carrier judgment)) :
    Context P ⥤ Type (max uIndex uCarrier) where
  obj Γ := Valuation P (carrier := carrier) Γ
  map f := TypeCat.ofHom (fun assignment judgment slot =>
    interpretTerm P A assignment (f judgment slot))
  map_id := by
    intro Γ
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext assignment judgment slot
    change interpretTerm P A assignment (identity P Γ judgment slot) =
      assignment judgment slot
    rfl
  map_comp := by
    intro Γ Δ Θ earlier later
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext assignment judgment slot
    exact interpretTerm_compose P A assignment earlier later slot

/-- One semantic assignment to a singleton context is one value at the
chosen judgment. -/
def singletonValuation (judgment : Judgment) :
    Valuation P (carrier := carrier) (singleton P judgment) ≃
      carrier judgment where
  toFun := fun assignment => assignment judgment ⟨rfl⟩
  invFun := fun value other ⟨equal⟩ => by cases equal; exact value
  left_inv := by
    intro assignment
    funext other slot
    obtain ⟨equal⟩ := slot
    cases equal
    rfl
  right_inv := by intro value; rfl

/-- Assignments to the constructor's arity context are exactly its family
of recursively typed arguments. -/
def arityValuation {judgment : Judgment}
    (shape : P.Shape PUnit.unit judgment)
    [Finite (P.Position shape)] :
    Valuation P (carrier := carrier) (arityContext P shape) ≃
      ((position : P.Position shape) → carrier (P.next shape position)) where
  toFun := fun assignment position =>
    assignment (P.next shape position) ⟨position, rfl⟩
  invFun := fun children child ⟨position, equal⟩ => by
    cases equal
    exact children position
  left_inv := by
    intro assignment
    funext child slot
    obtain ⟨position, equal⟩ := slot
    cases equal
    rfl
  right_inv := by intro children; funext position; rfl

/-- Semantic assignments to the sum context split into independent
assignments to its two constituent contexts. -/
def productValuation (Γ Δ : Context P) :
    Valuation P (carrier := carrier) (product P Γ Δ) ≃
      Valuation P (carrier := carrier) Γ ×
        Valuation P (carrier := carrier) Δ where
  toFun := fun assignment =>
    (fun judgment slot => assignment judgment (.inl slot),
      fun judgment slot => assignment judgment (.inr slot))
  invFun := fun assignments judgment => fun
    | .inl slot => assignments.1 judgment slot
    | .inr slot => assignments.2 judgment slot
  left_inv := by
    intro assignment
    funext judgment slot
    cases slot <;> rfl
  right_inv := by
    intro assignments
    cases assignments with
    | mk first second => rfl

/-- The first context projection evaluates to the first semantic
assignment, with no event evidence discarded from any term. -/
theorem algebraSemantics_firstProjection
    (A : P.Algebra (fun _ judgment => carrier judgment))
    (Γ Δ : Context P)
    (assignment : Valuation P (carrier := carrier) (product P Γ Δ)) :
    (algebraSemantics P A).map (firstProjection P Γ Δ) assignment =
      ((productValuation P Γ Δ) assignment).1 := by
  funext judgment slot
  rfl

/-- The second context projection evaluates to the second semantic
assignment. -/
theorem algebraSemantics_secondProjection
    (A : P.Algebra (fun _ judgment => carrier judgment))
    (Γ Δ : Context P)
    (assignment : Valuation P (carrier := carrier) (product P Γ Δ)) :
    (algebraSemantics P A).map (secondProjection P Γ Δ) assignment =
      ((productValuation P Γ Δ) assignment).2 := by
  funext judgment slot
  rfl

/-- The interpreted sum-context fan is a product in types. This is the
explicit finite-product preservation needed by the forward classifier map. -/
noncomputable def algebraSemanticsProductIsLimit
    (A : P.Algebra (fun _ judgment => carrier judgment))
    (Γ Δ : Context P) :
    IsLimit (BinaryFan.mk
      ((algebraSemantics P A).map (firstProjection P Γ Δ))
      ((algebraSemantics P A).map (secondProjection P Γ Δ))) :=
  BinaryFan.IsLimit.mk _
    (fun f g => TypeCat.ofHom (fun value =>
      (productValuation P Γ Δ).symm (f value, g value)))
    (by
      intro X f g
      apply TypeCat.Hom.ext
      apply TypeCat.Fun.ext
      funext value
      change ((productValuation P Γ Δ)
        ((productValuation P Γ Δ).symm (f value, g value))).1 = f value
      simp
      rfl)
    (by
      intro X f g
      apply TypeCat.Hom.ext
      apply TypeCat.Fun.ext
      funext value
      change ((productValuation P Γ Δ)
        ((productValuation P Γ Δ).symm (f value, g value))).2 = g value
      simp
      rfl)
    (by
      intro X f g mapping first second
      apply TypeCat.Hom.ext
      apply TypeCat.Fun.ext
      funext value
      apply (productValuation P Γ Δ).injective
      apply Prod.ext
      · have h := congrArg (fun h : X ⟶ Valuation P (carrier := carrier) Γ =>
          h value) first
        change ((productValuation P Γ Δ) (mapping value)).1 = f value at h
        exact h
      · have h := congrArg (fun h : X ⟶ Valuation P (carrier := carrier) Δ =>
          h value) second
        change ((productValuation P Γ Δ) (mapping value)).2 = g value at h
        exact h)

/-- There is exactly one assignment to the empty event-variable context. -/
def emptyValuation : Valuation P (carrier := carrier) (empty P) :=
  fun _ slot => slot.elim

/-- An algebra interpretation sends the empty source context to a terminal
semantic object. -/
noncomputable def algebraSemanticsEmptyIsTerminal
    (A : P.Algebra (fun _ judgment => carrier judgment)) :
    IsTerminal ((algebraSemantics P A).obj (empty P)) :=
  IsTerminal.ofUniqueHom
    (fun _ => TypeCat.ofHom (fun _ => emptyValuation P))
    (fun _ mapping => by
      apply TypeCat.Hom.ext
      apply TypeCat.Fun.ext
      funext value judgment slot
      exact slot.elim)

/-- Preservation of the selected binary product cone in the syntactic
category. -/
theorem algebraSemanticsPreservesPair
    (A : P.Algebra (fun _ judgment => carrier judgment))
    (Γ Δ : Context P) :
    PreservesLimit (Limits.pair Γ Δ) (algebraSemantics P A) := by
  apply preservesLimit_of_preserves_limit_cone (productIsLimit P Γ Δ)
  exact (isLimitMapConeBinaryFanEquiv
    (algebraSemantics P A) (firstProjection P Γ Δ)
    (secondProjection P Γ Δ)).symm (algebraSemanticsProductIsLimit P A Γ Δ)

/-- Preservation of the terminal object in the syntactic category. -/
theorem algebraSemanticsPreservesEmpty
    (A : P.Algebra (fun _ judgment => carrier judgment)) :
    PreservesLimit (Functor.empty.{0} (Context P)) (algebraSemantics P A) := by
  apply preservesLimit_of_preserves_limit_cone (emptyIsTerminal P)
  exact (isLimitMapConeEmptyConeEquiv (algebraSemantics P A) (empty P)).symm
    (algebraSemanticsEmptyIsTerminal P A)

set_option linter.style.haveILetI false in
/-- Every indexed-polynomial algebra determines a finite-product-preserving
interpretation of its free finite-variable context category. -/
theorem algebraSemanticsPreservesFiniteProducts
    (A : P.Algebra (fun _ judgment => carrier judgment)) :
    PreservesFiniteProducts (algebraSemantics P A) := by
  haveI : PreservesLimitsOfShape (Discrete WalkingPair) (algebraSemantics P A) := {
    preservesLimit := by
      intro K
      haveI : PreservesLimit
          (Limits.pair (K.obj ⟨WalkingPair.left⟩)
            (K.obj ⟨WalkingPair.right⟩))
          (algebraSemantics P A) :=
        algebraSemanticsPreservesPair P A _ _
      exact preservesLimit_of_iso_diagram (algebraSemantics P A)
        (diagramIsoPair K).symm }
  haveI : PreservesLimit (Functor.empty.{0} (Context P))
      (algebraSemantics P A) := algebraSemanticsPreservesEmpty P A
  haveI : PreservesLimitsOfShape (Discrete.{0} PEmpty.{1})
      (algebraSemantics P A) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal (algebraSemantics P A)
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal
    (algebraSemantics P A)

noncomputable instance algebraSemantics_preservesFiniteProducts
    (A : P.Algebra (fun _ judgment => carrier judgment)) :
    PreservesFiniteProducts (algebraSemantics P A) :=
  algebraSemanticsPreservesFiniteProducts P A

/-- An algebra homomorphism acts pointwise on every assignment of event
variables. -/
def mapValuation
    {targetCarrier : Judgment → Type uCarrier}
    {A : P.Algebra (fun _ judgment => carrier judgment)}
    {B : P.Algebra (fun _ judgment => targetCarrier judgment)}
    (h : IndexedPolynomial.Algebra.Hom A B)
    {Γ : Context P} (assignment : Valuation P (carrier := carrier) Γ) :
    Valuation P (carrier := targetCarrier) Γ :=
  fun judgment slot => h.toFun PUnit.unit judgment (assignment judgment slot)

/-- Interpreting a free tree commutes with every algebra homomorphism.
The proof uses the actual constructor law, including all indexed children. -/
theorem interpretTerm_hom
    {targetCarrier : Judgment → Type uCarrier}
    {A : P.Algebra (fun _ judgment => carrier judgment)}
    {B : P.Algebra (fun _ judgment => targetCarrier judgment)}
    (h : IndexedPolynomial.Algebra.Hom A B)
    {Γ : Context P} (assignment : Valuation P (carrier := carrier) Γ)
    {judgment : Judgment} (tree : Term P Γ judgment) :
    h.toFun PUnit.unit judgment (interpretTerm P A assignment tree) =
      interpretTerm P B (mapValuation P h assignment) tree := by
  exact IndexedPolynomial.Free.fold_unique P
    (fun _ index slot => h.toFun PUnit.unit index (assignment index slot))
    B
    (fun base index plan => h.toFun base index
      (IndexedPolynomial.Free.fold P
        (fun _ j slot => assignment j slot) A base index plan))
    (by intro base index slot; rfl)
    (by
      intro base index shape children
      exact h.commutes base index
        ⟨shape, fun position =>
          IndexedPolynomial.Free.fold P
            (fun _ j slot => assignment j slot) A base _ (children position)⟩)
    PUnit.unit judgment tree

/-- Each algebra homomorphism induces a natural map between its
finite-product-preserving contextual interpretations. -/
noncomputable def algebraSemanticsHom
    {targetCarrier : Judgment → Type uCarrier}
    {A : P.Algebra (fun _ judgment => carrier judgment)}
    {B : P.Algebra (fun _ judgment => targetCarrier judgment)}
    (h : IndexedPolynomial.Algebra.Hom A B) :
    algebraSemantics P A ⟶ algebraSemantics P B where
  app Γ := TypeCat.ofHom (mapValuation P h)
  naturality := by
    intro Γ Δ substitution
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext assignment judgment slot
    exact interpretTerm_hom P h assignment (substitution judgment slot)

/-- Interpreting a constructor arrow applies precisely the model's rule
action to the supplied recursive events. -/
theorem algebraSemantics_constructor
    (A : P.Algebra (fun _ judgment => carrier judgment))
    {judgment : Judgment} (shape : P.Shape PUnit.unit judgment)
    [Finite (P.Position shape)]
    (assignment : Valuation P (carrier := carrier) (arityContext P shape)) :
    (singletonValuation P judgment)
      ((algebraSemantics P A).map (constructorArrow P shape) assignment) =
        A.act PUnit.unit judgment
          ⟨shape, (arityValuation P shape) assignment⟩ := by
  change interpretTerm P A assignment
      (IndexedPolynomial.Free.node P shape
        (fun position => IndexedPolynomial.Free.pure P
          (⟨position, rfl⟩ : (arityContext P shape).slots (P.next shape position)))) =
      A.act PUnit.unit judgment
        ⟨shape, fun position => assignment (P.next shape position) ⟨position, rfl⟩⟩
  unfold interpretTerm
  rw [IndexedPolynomial.Free.fold_node]
  rfl

end Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts
