import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalTotalContext
import Mathlib.CategoryTheory.Category.Cat.Op

/-!
# Contextual category for the combined authored presentation

Authored equation models vary contravariantly in contextual assignments.
To retain the intended direction of program substitutions and firing-tree
arrows, the category of operational contexts is formed from opposite event
fibers and then opposite totalized. An arrow from `(X, Γ)` to `(Y, Δ)` is
an authored program assignment `X ⟶ Y` together with an event substitution
`Γ ⟶ Δ` after reindexing `Δ` along that assignment.

This constructs the free contextual carrier and its generators. Its
universal equivalence with independently specified semantic models is a
separate theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClassifierContext

open CategoryTheory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFiniteContextChange
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalTotalContext
open Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M)) (equations : List (EqAxiom S M))

/-- Reindexing of contextual event syntax, with the fiber arrow direction
reversed to form a cartesian fibration over program contexts. -/
noncomputable def classifierFibers :
    (EquationContexts (authoredEquationPresentation S equations))ᵒᵖ ⥤
      Cat.{0, 0} :=
  authoredOperationalFibers R equations ⋙ Cat.opFunctor

/-- Objects are authored program contexts carrying finite lists of
contextual event variables. Both kinds of substitution occur in arrows. -/
abbrev ClassifierContext := (Grothendieck (classifierFibers R equations))ᵒᵖ

/-- One authored program context and one ordered event-variable context. -/
def object
    (X : EquationContexts (authoredEquationPresentation S equations))
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)) :
    ClassifierContext R equations :=
  Opposite.op
    (⟨Opposite.op X, Opposite.op Γ⟩ :
      Grothendieck (classifierFibers R equations))

/-- The concrete shape of a combined arrow: a program-context assignment
and a free-tree substitution after reindexing target event variables. -/
noncomputable def arrow
    {X Y : EquationContexts (authoredEquationPresentation S equations)}
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra))
    (Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra))
    (assignment : X ⟶ Y)
    (events : Γ ⟶ pushContext R
      (authoredEquationModelMapQuot S equations assignment) Δ) :
    object R equations X Γ ⟶ object R equations Y Δ :=
  Quiver.Hom.op (⟨assignment.op, events.op⟩ :
      (⟨Opposite.op Y, Opposite.op Δ⟩ :
        Grothendieck (classifierFibers R equations)) ⟶
      (⟨Opposite.op X, Opposite.op Γ⟩ :
        Grothendieck (classifierFibers R equations)))

/-- Every combined arrow is uniquely an authored contextual assignment
and a simultaneous substitution of contextual firing trees in its
reindexed event-variable context. -/
noncomputable def homEquiv
    {X Y : EquationContexts (authoredEquationPresentation S equations)}
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra))
    (Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)) :
    (object R equations X Γ ⟶ object R equations Y Δ) ≃
      Σ assignment : X ⟶ Y,
        Γ ⟶ pushContext R
          (authoredEquationModelMapQuot S equations assignment) Δ where
  toFun combined := ⟨combined.unop.base.unop, combined.unop.fiber.unop⟩
  invFun pair := arrow R equations Γ Δ pair.1 pair.2
  left_inv combined := by
    apply Quiver.Hom.unop_inj
    cases combined with
    | op underlying =>
        cases underlying
        rfl
  right_inv pair := by
    cases pair
    rfl

/-- The identity combined arrow has the identity authored program
assignment, before its event-context cast is considered. -/
theorem homEquiv_id_base
    {X : EquationContexts (authoredEquationPresentation S equations)}
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)) :
    (homEquiv R equations Γ Γ (𝟙 (object R equations X Γ))).1 = 𝟙 X :=
  rfl

/-- The event component of a combined identity is exactly the canonical
cast from an event context to its reindexing along identity. -/
theorem homEquiv_id_events
    {X : EquationContexts (authoredEquationPresentation S equations)}
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)) :
    (homEquiv R equations Γ Γ (𝟙 (object R equations X Γ))).2 =
      (eqToHom (by
        have baseId : authoredEquationModelMapQuot S equations (𝟙 X) =
            FreeBindingClone.Hom.id
              (authoredEquationModelAt S equations X.as).algebra := by
          change authoredEquationModelMap S equations (𝟙 X.as) = _
          exact authoredEquationModelMap_id S equations X.as
        rw [baseId]
        exact (pushContext_id R
          (authoredEquationModelAt S equations X.as).algebra Γ).symm) :
        Γ ⟶ pushContext R
          (authoredEquationModelMapQuot S equations (𝟙 X)) Γ) := by
  dsimp only [homEquiv]
  change (Grothendieck.id
      (⟨Opposite.op X, Opposite.op Γ⟩ :
        Grothendieck (classifierFibers R equations))).fiber.unop = _
  dsimp only [Grothendieck.id]
  unfold classifierFibers
  exact eqToHom_unop _

/-- The authored program assignment of a composite combined arrow is
the composite of its two authored program assignments. -/
theorem homEquiv_comp_base
    {X Y Z : EquationContexts (authoredEquationPresentation S equations)}
    {Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)}
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    {Θ : ListContext
      (rules R (authoredEquationModelAt S equations Z.as).algebra)}
    (first : object R equations X Γ ⟶ object R equations Y Δ)
    (second : object R equations Y Δ ⟶ object R equations Z Θ) :
    (homEquiv R equations Γ Θ (first ≫ second)).1 =
      (homEquiv R equations Γ Δ first).1 ≫
        (homEquiv R equations Δ Θ second).1 :=
    rfl

/-- Reindexing an event context along two authored assignments agrees
with reindexing along their equation-class composite. This equality is
propositional because the model map on quotient arrows is a `Quot.liftOn`. -/
theorem reindexedContext_comp
    {X Y Z : EquationContexts (authoredEquationPresentation S equations)}
    (Θ : ListContext
      (rules R (authoredEquationModelAt S equations Z.as).algebra))
    (first : X ⟶ Y) (second : Y ⟶ Z) :
    pushContext R (authoredEquationModelMapQuot S equations first)
      (pushContext R (authoredEquationModelMapQuot S equations second) Θ) =
    pushContext R (authoredEquationModelMapQuot S equations (first ≫ second)) Θ := by
  have modelMapComp :
      authoredEquationModelMapQuot S equations (first ≫ second) =
        FreeBindingClone.Hom.comp
          (authoredEquationModelMapQuot S equations second)
          (authoredEquationModelMapQuot S equations first) := by
    exact (authoredEquationQuotientModelPresheaf S equations).map_comp
      second.op first.op
  exact (pushContext_comp R
    (authoredEquationModelMapQuot S equations second)
    (authoredEquationModelMapQuot S equations first) Θ).symm.trans
      (congrArg (fun base => pushContext R base Θ) modelMapComp.symm)

/-- The opposite-fiber action is the existing substitution-preserving
translation of complete authored firing trees. -/
theorem classifierFibers_map_events
    {X Y : EquationContexts (authoredEquationPresentation S equations)}
    {Δ Θ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    (assignment : X ⟶ Y) (events : Δ ⟶ Θ) :
    (((classifierFibers R equations).map assignment.op).toFunctor.map
      events.op).unop =
      pushSubstitution R
        (authoredEquationModelMapQuot S equations assignment) events := by
  rfl

/-- The event substitution of a composite combined arrow is the first
substitution followed by the second one transported through the first
program assignment. The final equality records quotient-model coherence. -/
theorem homEquiv_comp_events
    {X Y Z : EquationContexts (authoredEquationPresentation S equations)}
    {Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)}
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    {Θ : ListContext
      (rules R (authoredEquationModelAt S equations Z.as).algebra)}
    (first : object R equations X Γ ⟶ object R equations Y Δ)
    (second : object R equations Y Δ ⟶ object R equations Z Θ) :
    (homEquiv R equations Γ Θ (first ≫ second)).2 =
      (homEquiv R equations Γ Δ first).2 ≫
        pushSubstitution R
          (authoredEquationModelMapQuot S equations
            (homEquiv R equations Γ Δ first).1)
          (homEquiv R equations Δ Θ second).2 ≫
        eqToHom (reindexedContext_comp R equations Θ
          (homEquiv R equations Γ Δ first).1
          (homEquiv R equations Δ Θ second).1) := by
  apply Quiver.Hom.op_inj
  change (second.unop ≫ first.unop).fiber =
    ((homEquiv R equations Γ Δ first).2 ≫
      pushSubstitution R
        (authoredEquationModelMapQuot S equations
          (homEquiv R equations Γ Δ first).1)
        (homEquiv R equations Δ Θ second).2 ≫
      eqToHom (reindexedContext_comp R equations Θ
        (homEquiv R equations Γ Δ first).1
        (homEquiv R equations Δ Θ second).1)).op
  rw [Grothendieck.comp_fiber, op_comp, op_comp]
  rw [eqToHom_op]
  dsimp only [homEquiv, Equiv.coe_fn_mk]
  simp [classifierFibers, authoredOperationalFibers, operationalFibers,
    pushFunctor, Cat.opFunctor, Category.assoc]
  simp [forgetEquations, authoredEquationQuotientModelPresheaf]
  cases first with
  | op firstUnderlying =>
      cases firstUnderlying with
      | mk firstBase firstFiber =>
          cases firstFiber with
          | op firstEvent =>
              rfl

/-- Forget retained firing variables and histories, recovering the
authored equation context and its contextual program assignment. -/
noncomputable def baseProjection :
    ClassifierContext R equations ⥤
      EquationContexts (authoredEquationPresentation S equations) :=
  (Grothendieck.forget (classifierFibers R equations)).op ⋙
    unopUnop _

/-- The original equation-context category is the zero-event-variable
part of the combined contextual category. -/
noncomputable def programSection :
    EquationContexts (authoredEquationPresentation S equations) ⥤
      ClassifierContext R equations where
  obj X := object R equations X
    (emptyList R (authoredEquationModelAt S equations X.as).algebra)
  map {X Y} assignment :=
    arrow R equations
      (emptyList R (authoredEquationModelAt S equations X.as).algebra)
      (emptyList R (authoredEquationModelAt S equations Y.as).algebra)
      assignment (fun _ slot => Fin.elim0 slot.1)
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply Grothendieck.ext
    case w_base => rfl
    case w_fiber =>
      apply Quiver.Hom.unop_inj
      funext judgment slot
      exact Fin.elim0 slot.1
  map_comp first second := by
    apply Quiver.Hom.unop_inj
    apply Grothendieck.ext
    case w_base => rfl
    case w_fiber =>
      apply Quiver.Hom.unop_inj
      funext judgment slot
      exact Fin.elim0 slot.1

/-- Adding no event variables and then forgetting the event layer is
literally the original equation-context interpretation. -/
theorem programSection_baseProjection :
    programSection R equations ⋙ baseProjection R equations =
      𝟭 (EquationContexts (authoredEquationPresentation S equations)) := by
  apply CategoryTheory.Functor.hext
  · intro X
    rfl
  · intro X Y assignment
    rfl

/-- The combined contextual category is a conservative extension of the
authored equation-context category on zero-event-variable objects. -/
instance programSection_full : (programSection R equations).Full where
  map_surjective := by
    intro X Y combined
    refine ⟨combined.unop.base.unop, ?_⟩
    apply Quiver.Hom.unop_inj
    apply Grothendieck.ext
    case w_base => rfl
    case w_fiber =>
      apply Quiver.Hom.unop_inj
      funext judgment slot
      exact Fin.elim0 slot.1

instance programSection_faithful : (programSection R equations).Faithful where
  map_injective := by
    intro X Y first second equal
    exact congrArg (fun combined => combined.unop.base.unop) equal

/-- A free firing-tree substitution at one program context remains an
arrow of the combined classifier in the original substitution direction. -/
noncomputable def fiberArrow
    (X : EquationContexts (authoredEquationPresentation S equations))
    {Γ Δ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)}
    (events : Γ ⟶ Δ) :
    object R equations X Γ ⟶ object R equations X Δ :=
  Quiver.Hom.op
    ((Grothendieck.ι (classifierFibers R equations)
      (Opposite.op X)).map (Quiver.Hom.op events))

theorem homEquiv_fiberArrow_base
    (X : EquationContexts (authoredEquationPresentation S equations))
    {Γ Δ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)}
    (events : Γ ⟶ Δ) :
    (homEquiv R equations Γ Δ (fiberArrow R equations X events)).1 = 𝟙 X :=
  rfl

theorem homEquiv_fiberArrow_events
    (X : EquationContexts (authoredEquationPresentation S equations))
    {Γ Δ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)}
    (events : Γ ⟶ Δ) :
    (homEquiv R equations Γ Δ (fiberArrow R equations X events)).2 =
      events ≫
        (homEquiv R equations Δ Δ
          (𝟙 (object R equations X Δ))).2 := by
  rfl

/-- Passing to the combined classifier does not identify distinct firing
trees or distinct event-variable positions in a fixed program context. -/
theorem fiberArrow_injective
    (X : EquationContexts (authoredEquationPresentation S equations))
    {Γ Δ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)} :
    Function.Injective (fiberArrow R equations X (Γ := Γ) (Δ := Δ)) := by
  intro first second equal
  have innerEqual := Quiver.Hom.op_inj equal
  have oppositeEqual :=
    (Grothendieck.ι (classifierFibers R equations)
      (Opposite.op X)).map_injective innerEqual
  exact Quiver.Hom.op_inj oppositeEqual

/-- The ordinary operational fiber embeds in the combined classifier,
preserving substitution order and complete authored firing trees. -/
noncomputable def fiberFunctor
    (X : EquationContexts (authoredEquationPresentation S equations)) :
    ListContext (rules R (authoredEquationModelAt S equations X.as).algebra) ⥤
      ClassifierContext R equations where
  obj Γ := object R equations X Γ
  map := fiberArrow R equations X
  map_id Γ := by
    apply Quiver.Hom.unop_inj
    change (Grothendieck.ι (classifierFibers R equations)
      (Opposite.op X)).map (Quiver.Hom.op (𝟙 Γ)) =
        𝟙 ((Grothendieck.ι (classifierFibers R equations)
          (Opposite.op X)).obj (Opposite.op Γ))
    change (Grothendieck.ι (classifierFibers R equations)
      (Opposite.op X)).map (𝟙 (Opposite.op Γ)) =
        𝟙 ((Grothendieck.ι (classifierFibers R equations)
          (Opposite.op X)).obj (Opposite.op Γ))
    exact (Grothendieck.ι (classifierFibers R equations)
      (Opposite.op X)).map_id (Opposite.op Γ)
  map_comp first second := by
    apply Quiver.Hom.unop_inj
    change (Grothendieck.ι (classifierFibers R equations)
      (Opposite.op X)).map (Quiver.Hom.op (first ≫ second)) =
        (Grothendieck.ι (classifierFibers R equations)
          (Opposite.op X)).map (Quiver.Hom.op second) ≫
        (Grothendieck.ι (classifierFibers R equations)
          (Opposite.op X)).map (Quiver.Hom.op first)
    change (Grothendieck.ι (classifierFibers R equations)
      (Opposite.op X)).map
        (Quiver.Hom.op second ≫ Quiver.Hom.op first) =
        (Grothendieck.ι (classifierFibers R equations)
          (Opposite.op X)).map (Quiver.Hom.op second) ≫
        (Grothendieck.ι (classifierFibers R equations)
          (Opposite.op X)).map (Quiver.Hom.op first)
    exact (Grothendieck.ι (classifierFibers R equations)
      (Opposite.op X)).map_comp (Quiver.Hom.op second)
        (Quiver.Hom.op first)

instance fiberFunctor_faithful
    (X : EquationContexts (authoredEquationPresentation S equations)) :
    (fiberFunctor R equations X).Faithful where
  map_injective := by
    intro Γ Δ first second equal
    exact fiberArrow_injective R equations X equal

/-- The authored conditional-rule generator is an arrow in the combined
classifier from its ordered binder-local premise context to its conclusion
judgment. It remains a firing occurrence, not an equation of programs. -/
noncomputable def constructor
    (X : EquationContexts (authoredEquationPresentation S equations))
    {judgment : Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment
      (authoredEquationModelAt S equations X.as).algebra}
    (shape : (rules R (authoredEquationModelAt S equations X.as).algebra).Shape
      PUnit.unit judgment) :
    object R equations X
      (arityList R (authoredEquationModelAt S equations X.as).algebra shape) ⟶
    object R equations X
      (singletonList R (authoredEquationModelAt S equations X.as).algebra
        judgment) :=
  fiberArrow R equations X
    (constructorArrowList R
      (authoredEquationModelAt S equations X.as).algebra shape)

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClassifierContext
