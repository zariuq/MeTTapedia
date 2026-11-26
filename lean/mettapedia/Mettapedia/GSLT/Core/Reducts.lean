import Mettapedia.GSLT.Core.StaticPart

/-!
# Classes of GSLTs by their components

A GSLT has terms, equations and steps. Requiring components to be trivial gives
full subcategories of the operational category, whose morphisms are term maps
that preserve equations and steps:

* no steps: a setoid of terms (`StaticPart.StepFree`);
* equations are equality: an abstract rewriting system (`EquationFree`);
* both: a set of terms (`Discrete`).

Forgetting a component is right adjoint to the inclusion of its class, and the
forgetful functors commute. Abstract rewriting systems are also reflective: the
left adjoint passes to equation classes and carries the steps along. Step-free
theories are not reflective, since a theory with a step has no morphism into a
step-free one. A discrete theory is its set of terms: every function between
term sets is a morphism, and morphisms are determined by their term maps.

Without steps any two terms are bisimilar. A map that only has to preserve
bisimilarity is therefore unconstrained on step-free theories, while a map in
the operational category must preserve their equations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.Reducts

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open StaticPart (StepFree StaticTheory includeStatic forgetSteps)

universe u

/-- Equality as an equivalence relation. -/
abbrev equality (Term : Type u) : Setoid Term := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

/-! ## Abstract rewriting systems -/

/-- The equations of the theory are equality. -/
def EquationFree : ObjectProperty OperationalTheory.{u} :=
  fun X => ∀ s t, X.theory.Equiv s t → s = t

abbrev RewritingSystem := EquationFree.{u}.FullSubcategory

abbrev includeRewriting : RewritingSystem.{u} ⥤ OperationalTheory.{u} := EquationFree.ι

/-- Keep the terms and steps of a theory, with equality as its equations. -/
def withoutEquations (G : GSLT.{u}) : GSLT.{u} where
  Term := G.Term
  equations := equality G.Term
  rewrites := G.rewrites
  rewrites_resp_left := fun {_ _ u} same moved => by
    cases same
    exact ⟨u, moved, rfl⟩
  rewrites_resp_right := fun moved same => by
    cases same
    exact moved

def dropEquations (X : OperationalTheory.{u}) : RewritingSystem.{u} :=
  ⟨⟨withoutEquations X.theory⟩, fun _ _ same => same⟩

/-- Equations are forgotten functorially along operational translations. -/
def forgetEquations : OperationalTheory.{u} ⥤ RewritingSystem.{u} where
  obj := dropEquations
  map f := ObjectProperty.homMk
    { mapTerm := f.mapTerm
      mapEquiv := fun same => congrArg f.mapTerm same
      mapStep := fun moved => f.mapStep moved }
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    rfl

def rewritingHomEquiv (A : RewritingSystem.{u}) (X : OperationalTheory.{u}) :
    (includeRewriting.obj A ⟶ X) ≃ (A ⟶ forgetEquations.obj X) where
  toFun f := ObjectProperty.homMk
    { mapTerm := f.mapTerm
      mapEquiv := fun {left right} same => congrArg f.mapTerm (A.property left right same)
      mapStep := fun moved => f.mapStep moved }
  invFun g :=
    { mapTerm := g.hom.mapTerm
      mapEquiv := fun {left right} same => by
        rw [A.property left right same]
        exact X.theory.equations.iseqv.refl _
      mapStep := fun moved => g.hom.mapStep moved }
  left_inv _ := OperationalTranslation.ext rfl
  right_inv _ := by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    rfl

/-- Abstract rewriting systems are coreflective: forgetting equations is right
adjoint to the inclusion. -/
def rewritingAdjunction : includeRewriting.{u} ⊣ forgetEquations.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := rewritingHomEquiv
      homEquiv_naturality_left_symm := by
        intros
        apply OperationalTranslation.ext
        rfl
      homEquiv_naturality_right := by
        intros
        apply ObjectProperty.hom_ext
        apply OperationalTranslation.ext
        rfl }

/-! ## Passing to equation classes -/

/-- Equation classes as terms, with a step between two classes when some
members take a step. -/
def quotientTheory (G : GSLT.{u}) : GSLT.{u} where
  Term := Quotient G.equations
  equations := equality (Quotient G.equations)
  rewrites first last := ∃ s t, Quotient.mk _ s = first ∧ Quotient.mk _ t = last ∧ G.Step s t
  rewrites_resp_left := fun {_ _ last} same moved => by
    cases same
    exact ⟨last, moved, rfl⟩
  rewrites_resp_right := fun moved same => by
    cases same
    exact moved

def quotientObj (X : OperationalTheory.{u}) : RewritingSystem.{u} :=
  ⟨⟨quotientTheory X.theory⟩, fun _ _ same => same⟩

/-- Every term goes to its equation class. -/
def project (X : OperationalTheory.{u}) : X ⟶ includeRewriting.obj (quotientObj X) where
  mapTerm s := Quotient.mk _ s
  mapEquiv same := Quotient.sound (s := X.theory.equations) same
  mapStep {s t} moved := ⟨s, t, rfl, rfl, moved⟩

def quotientMap {X Y : OperationalTheory.{u}} (f : X ⟶ Y) : quotientObj X ⟶ quotientObj Y :=
  ObjectProperty.homMk
    { mapTerm := Quotient.lift (fun s => Quotient.mk Y.theory.equations (f.mapTerm s))
        fun _ _ same => Quotient.sound (s := Y.theory.equations) (f.mapEquiv same)
      mapEquiv := fun same => congrArg _ same
      mapStep := fun moved => by
        obtain ⟨s, t, rfl, rfl, moved⟩ := moved
        exact ⟨f.mapTerm s, f.mapTerm t, rfl, rfl, f.mapStep moved⟩ }

def quotientFunctor : OperationalTheory.{u} ⥤ RewritingSystem.{u} where
  obj := quotientObj
  map := quotientMap
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    funext q
    induction q using Quotient.ind
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    funext q
    induction q using Quotient.ind
    rfl

def quotientHomEquiv (X : OperationalTheory.{u}) (A : RewritingSystem.{u}) :
    (quotientFunctor.obj X ⟶ A) ≃ (X ⟶ includeRewriting.obj A) where
  toFun g :=
    { mapTerm := fun s => g.hom.mapTerm (Quotient.mk _ s)
      mapEquiv := fun {left right} same => by
        rw [Quotient.sound (s := X.theory.equations) same]
        exact A.obj.theory.equations.iseqv.refl _
      mapStep := fun {s t} moved => g.hom.mapStep ⟨s, t, rfl, rfl, moved⟩ }
  invFun f := ObjectProperty.homMk
    { mapTerm := Quotient.lift f.mapTerm fun _ _ same => A.property _ _ (f.mapEquiv same)
      mapEquiv := fun same => by
        cases same
        exact A.obj.theory.equations.iseqv.refl _
      mapStep := fun moved => by
        obtain ⟨s, t, rfl, rfl, moved⟩ := moved
        exact f.mapStep moved }
  left_inv _ := by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    funext q
    induction q using Quotient.ind
    rfl
  right_inv _ := OperationalTranslation.ext rfl

/-- Abstract rewriting systems are reflective: passing to equation classes is
left adjoint to the inclusion. -/
def quotientAdjunction : quotientFunctor.{u} ⊣ includeRewriting.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := quotientHomEquiv
      homEquiv_naturality_left_symm := by
        intros
        apply ObjectProperty.hom_ext
        apply OperationalTranslation.ext
        funext q
        induction q using Quotient.ind
        rfl
      homEquiv_naturality_right := by
        intros
        apply OperationalTranslation.ext
        rfl }

/-- The unit of the reflection is the projection to equation classes. -/
theorem quotientAdjunction_unit (X : OperationalTheory.{u}) :
    quotientAdjunction.unit.app X = project X :=
  OperationalTranslation.ext rfl

/-! ## Step-free theories are not reflective -/

/-- A theory with a step has no morphism into a step-free theory. -/
theorem no_morphism_to_stepFree {X : OperationalTheory.{u}} {s t : X.theory.Term}
    (moved : X.theory.Step s t) (A : StaticTheory.{u}) : IsEmpty (X ⟶ includeStatic.obj A) :=
  ⟨fun f => A.property _ _ (f.mapStep moved)⟩

/-- Two terms and one step between them. -/
def oneStep : OperationalTheory.{u} :=
  ⟨{ Term := ULift.{u} Bool
     equations := equality _
     rewrites := fun s t => s.down = false ∧ t.down = true
     rewrites_resp_left := fun {_ _ u} same moved => by
       cases same
       exact ⟨u, moved, rfl⟩
     rewrites_resp_right := fun moved same => by
       cases same
       exact moved }⟩

theorem oneStep_moves : oneStep.{u}.theory.Step (ULift.up false) (ULift.up true) := ⟨rfl, rfl⟩

/-- No functor is left adjoint to the inclusion of step-free theories. -/
theorem stepFree_not_reflective :
    ¬ ∃ L : OperationalTheory.{u} ⥤ StaticTheory.{u}, Nonempty (L ⊣ includeStatic) := by
  rintro ⟨L, ⟨adjunction⟩⟩
  exact (no_morphism_to_stepFree oneStep_moves (L.obj oneStep)).false (adjunction.unit.app oneStep)

/-! ## Sets of terms -/

/-- Equations are equality and there are no steps. -/
def Discrete : ObjectProperty OperationalTheory.{u} :=
  fun X => StepFree X ∧ EquationFree X

abbrev DiscreteTheory := Discrete.{u}.FullSubcategory

abbrev includeDiscrete : DiscreteTheory.{u} ⥤ OperationalTheory.{u} := Discrete.ι

/-- The discrete theory of a type of terms. -/
def discreteOf (Term : Type u) : DiscreteTheory.{u} :=
  ⟨⟨GSLT.stepFree Term⟩, fun _ _ moved => moved, fun _ _ same => same⟩

/-- Forget equations and steps. -/
def discretePart : OperationalTheory.{u} ⥤ DiscreteTheory.{u} where
  obj X := discreteOf X.theory.Term
  map f := ObjectProperty.homMk
    { mapTerm := f.mapTerm
      mapEquiv := fun same => congrArg f.mapTerm same
      mapStep := fun moved => moved.elim }

/-- Forget the equations of a step-free theory. -/
def staticToDiscrete : StaticTheory.{u} ⥤ DiscreteTheory.{u} where
  obj A := discreteOf A.obj.theory.Term
  map f := ObjectProperty.homMk
    { mapTerm := f.hom.mapTerm
      mapEquiv := fun same => congrArg f.hom.mapTerm same
      mapStep := fun moved => moved.elim }

/-- Forget the steps of an abstract rewriting system. -/
def rewritingToDiscrete : RewritingSystem.{u} ⥤ DiscreteTheory.{u} where
  obj A := discreteOf A.obj.theory.Term
  map f := ObjectProperty.homMk
    { mapTerm := f.hom.mapTerm
      mapEquiv := fun same => congrArg f.hom.mapTerm same
      mapStep := fun moved => moved.elim }

/-- Forgetting steps and then equations is forgetting both. -/
theorem steps_then_equations : forgetSteps ⋙ staticToDiscrete = discretePart.{u} :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    rfl

/-- Forgetting equations and then steps is forgetting both. -/
theorem equations_then_steps : forgetEquations ⋙ rewritingToDiscrete = discretePart.{u} :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    rfl

/-- The square of forgetful functors commutes. -/
theorem forgetful_square :
    forgetSteps ⋙ staticToDiscrete = forgetEquations.{u} ⋙ rewritingToDiscrete :=
  steps_then_equations.trans equations_then_steps.symm

def discreteHomEquiv (D : DiscreteTheory.{u}) (X : OperationalTheory.{u}) :
    (includeDiscrete.obj D ⟶ X) ≃ (D ⟶ discretePart.obj X) where
  toFun f := ObjectProperty.homMk
    { mapTerm := f.mapTerm
      mapEquiv := fun {left right} same => congrArg f.mapTerm (D.property.2 left right same)
      mapStep := fun moved => (D.property.1 _ _ moved).elim }
  invFun g :=
    { mapTerm := g.hom.mapTerm
      mapEquiv := fun {left right} same => by
        rw [D.property.2 left right same]
        exact X.theory.equations.iseqv.refl _
      mapStep := fun moved => (D.property.1 _ _ moved).elim }
  left_inv _ := OperationalTranslation.ext rfl
  right_inv _ := by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    rfl

/-- Discrete theories are coreflective: forgetting equations and steps is right
adjoint to the inclusion. -/
def discreteAdjunction : includeDiscrete.{u} ⊣ discretePart.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := discreteHomEquiv
      homEquiv_naturality_left_symm := by
        intros
        apply OperationalTranslation.ext
        rfl
      homEquiv_naturality_right := by
        intros
        apply ObjectProperty.hom_ext
        apply OperationalTranslation.ext
        rfl }

/-- Morphisms between discrete theories are exactly the functions between their
terms. -/
def discreteMorphisms (D E : DiscreteTheory.{u}) :
    (D ⟶ E) ≃ (D.obj.theory.Term → E.obj.theory.Term) where
  toFun f := f.hom.mapTerm
  invFun h := ObjectProperty.homMk
    { mapTerm := h
      mapEquiv := fun {left right} same => by
        rw [D.property.2 left right same]
        exact E.obj.theory.equations.iseqv.refl _
      mapStep := fun moved => (D.property.1 _ _ moved).elim }
  left_inv _ := by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    rfl
  right_inv _ := rfl

/-- Every type is the set of terms of a discrete theory. -/
theorem discreteOf_terms (Term : Type u) : (discreteOf Term).obj.theory.Term = Term := rfl

/-! ## Bisimilarity does not see equations -/

/-- Without steps, any relation is a bisimulation, so any two terms are bisimilar. -/
theorem bisimilar_of_stepFree {X : OperationalTheory.{u}} (quiet : StepFree X)
    (s t : X.theory.Term) : X.theory.Bisimilar s t :=
  ⟨fun _ _ => True,
    ⟨fun {_ _} _ {_} moved => (quiet _ _ moved).elim, fun {_ _} _ {_} moved => (quiet _ _ moved).elim⟩,
    trivial⟩

/-- On step-free theories every function preserves bisimilarity. -/
def bisimilarityMorphism (A B : StaticTheory.{u}) (h : A.obj.theory.Term → B.obj.theory.Term) :
    GSLT.Morphism A.obj.theory B.obj.theory :=
  ⟨h, fun _ => bisimilar_of_stepFree B.property _ _⟩

/-- All terms of `ULift Bool` identified, with no steps. -/
def collapsed : StaticTheory.{u} :=
  ⟨⟨GSLT.equationOnly (ULift.{u} Bool) ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial,
    fun _ _ => trivial⟩⟩⟩, fun _ _ moved => moved⟩

/-- The two terms of `ULift Bool`, kept apart, with no steps. -/
def separated : StaticTheory.{u} := ⟨(discreteOf (ULift.{u} Bool)).obj, fun _ _ moved => moved⟩

/-- **Negative**: the identity on terms preserves bisimilarity but not the
equations, so it is no morphism of the operational category. -/
theorem identity_not_operational :
    IsEmpty { f : collapsed.{u} ⟶ separated.{u} // ∀ s, f.hom.mapTerm s = s } := by
  refine ⟨fun ⟨f, same⟩ => ?_⟩
  have equal : f.hom.mapTerm (ULift.up false) = f.hom.mapTerm (ULift.up true) :=
    f.hom.mapEquiv (left := ULift.up false) (right := ULift.up true) trivial
  have flipped := ((same _).symm.trans equal).trans (same _)
  exact Bool.false_ne_true (congrArg ULift.down flipped)

/-- **Positive**: the same function is a morphism of bisimilarity. -/
theorem identity_preserves_bisimilarity :
    (bisimilarityMorphism collapsed.{u} separated.{u} id).toFun = id := rfl

/-- The two terms are bisimilar and not equivalent. -/
theorem bisimilar_not_equivalent :
    separated.{u}.obj.theory.Bisimilar (ULift.up false) (ULift.up true) ∧
      ¬ separated.{u}.obj.theory.Equiv (ULift.up false) (ULift.up true) :=
  ⟨bisimilar_of_stepFree separated.property _ _, fun same => Bool.false_ne_true (congrArg ULift.down same)⟩

end Mettapedia.GSLT.IndexedOperational.Reducts

#print axioms Mettapedia.GSLT.IndexedOperational.Reducts.rewritingAdjunction
#print axioms Mettapedia.GSLT.IndexedOperational.Reducts.quotientAdjunction
#print axioms Mettapedia.GSLT.IndexedOperational.Reducts.quotientAdjunction_unit
#print axioms Mettapedia.GSLT.IndexedOperational.Reducts.stepFree_not_reflective
#print axioms Mettapedia.GSLT.IndexedOperational.Reducts.forgetful_square
#print axioms Mettapedia.GSLT.IndexedOperational.Reducts.discreteAdjunction
#print axioms Mettapedia.GSLT.IndexedOperational.Reducts.discreteMorphisms
#print axioms Mettapedia.GSLT.IndexedOperational.Reducts.identity_not_operational
#print axioms Mettapedia.GSLT.IndexedOperational.Reducts.bisimilar_not_equivalent
