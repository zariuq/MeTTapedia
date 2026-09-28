import Mettapedia.OSLF.Syntax.SecondOrderEquationContext
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Whiskering

/-!
# Universal interpretation of second-order equation contexts

For a substitution-stable equation presentation, an interpretation of its
raw second-order context category into any category is lawful exactly when
it identifies every generated equation. Such interpretations and their
natural maps are classified by the quotient category.

This is the equation-context rung. Closed structure and individual firing
events require further relative construction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory

variable {S : Signature} {schema : List (MetaArity S)}
variable (P : EquationPresentation S schema)
variable (D : Type*) [Category D]

/-- Independently specified interpretations of the raw context category
that respect the equation relation on its arrows. -/
structure LawfulEquationInterpretation where
  functor : Object S ⥤ D
  respects : ∀ {X Y : Object S} {first second : X ⟶ Y},
    P.homRel first second → functor.map first = functor.map second

instance : Category (LawfulEquationInterpretation P D) where
  Hom F G := F.functor ⟶ G.functor
  id F := 𝟙 F.functor
  comp f g := f ≫ g
  id_comp := by intros; simp
  comp_id := by intros; simp
  assoc := by intros; simp [Category.assoc]

/-- Restrict an interpretation of the quotient along the canonical quotient
functor. Its equation law follows from quotient soundness. -/
def restrict :
    (EquationContexts P ⥤ D) ⥤ LawfulEquationInterpretation P D where
  obj F := {
    functor := P.quotientFunctor ⋙ F
    respects := by
      intro X Y first second related
      exact congrArg F.map
        (_root_.CategoryTheory.Quotient.sound P.homRel related) }
  map transformation := Functor.whiskerLeft P.quotientFunctor transformation
  map_id := by intro; rfl
  map_comp := by intros; rfl

/-- A lawful interpretation extends uniquely to a functor on the equation
quotient, using the generated relation rather than an assumed classifier. -/
def extend (F : LawfulEquationInterpretation P D) :
    EquationContexts P ⥤ D :=
  _root_.CategoryTheory.Quotient.lift P.homRel F.functor
    (fun _ _ _ _ related => F.respects related)

/-- Restricting the extension recovers the given lawful interpretation,
including its action on all raw substitutions. -/
theorem restrict_extend (F : LawfulEquationInterpretation P D) :
    (restrict P D).obj (extend P D F) = F := by
  cases F with
  | mk original law =>
      cases _root_.CategoryTheory.Quotient.lift_spec P.homRel
        original (fun _ _ _ _ related => law related)
      rfl

/-- Every functor on the quotient is the unique extension of its own
restriction. -/
theorem extend_restrict (F : EquationContexts P ⥤ D) :
    extend P D ((restrict P D).obj F) = F := by
  exact (_root_.CategoryTheory.Quotient.lift_unique P.homRel
    ((restrict P D).obj F).functor
    (fun _ _ _ _ related =>
      ((restrict P D).obj F).respects related)
    F rfl).symm

/-- Restriction loses no interpretation map: a natural transformation is
determined by its components on the unchanged context objects. -/
instance restrict_faithful : (restrict P D).Faithful where
  map_injective := by
    intro F G first second equal
    exact _root_.CategoryTheory.Quotient.natTrans_ext first second equal

/-- Every natural map between lawful interpretations extends uniquely over
the equation quotient. -/
instance restrict_full : (restrict P D).Full where
  map_surjective := by
    intro F G transformation
    refine ⟨_root_.CategoryTheory.Quotient.natTransLift
      P.homRel transformation, ?_⟩
    apply NatTrans.ext
    funext X
    rfl

/-- Every independently specified lawful interpretation is obtained by
restricting an interpretation of the equation quotient. -/
instance restrict_essSurj : (restrict P D).EssSurj where
  mem_essImage F :=
    ⟨extend P D F, ⟨eqToIso (restrict_extend P D F)⟩⟩

instance restrict_isEquivalence : (restrict P D).IsEquivalence where

/-- The equation-context classifier has its genuine universal property at
arbitrary target categories, including interpretation maps and coherent
unit/counit isomorphisms. The larger closed operational classifier remains
to be constructed. -/
noncomputable def equationUniversalEquivalence :
    (EquationContexts P ⥤ D) ≌ LawfulEquationInterpretation P D :=
  (restrict P D).asEquivalence

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.equationUniversalEquivalence
