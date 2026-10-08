import Mettapedia.TypeTheory.Calculi.NativeDependent.PresheafInterpretation
import Mettapedia.TypeTheory.DisplayedPresheafLogicalActionCoherence
import Mettapedia.TypeTheory.DependentProductRestrictionEvaluation

/-!
# Theory restriction of generated quantifier interpretations

Changing the supplied object presheaf and its primitive meanings changes
the independently generated context and object-term interpretations.
The comparisons use the actual theory functor, including its action on
worlds and arrows. They do not identify arbitrary reflective observers
with the admitted source context image.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryInterpretation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafTheoryRestriction
open ObjectInterpretation

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- Primitive object sections are restricted at the actual image world. -/
def restrictedSection (F : C ⥤ D) {objects : Dᵒᵖ ⥤ Type u}
    (value : objects.sections) : (F.op ⋙ objects).sections where
  val world := value.val (F.op.obj world)
  property arrow := value.property (F.op.map arrow)

/-- Iterated object comprehension agrees with actual presheaf restriction. -/
theorem context_restriction (F : C ⥤ D) (objects : Dᵒᵖ ⥤ Type u) (n : Nat) :
    context (F.op ⋙ objects) n = F.op ⋙ context objects n := by
  induction n with
  | zero => rfl
  | succ n prior =>
      change totalSpace (objectFamily (F.op ⋙ objects) (context (F.op ⋙ objects) n)) =
        F.op ⋙ totalSpace (objectFamily objects (context objects n))
      rw [prior]
      rfl

/-- The comparison maps the complete generated tuple at the actual image
world, retaining every binding position. -/
def contextMap (F : C ⥤ D) (objects : Dᵒᵖ ⥤ Type u) : (n : Nat) →
    context (F.op ⋙ objects) n ⟶ F.op ⋙ context objects n
  | 0 => { app _ := TypeCat.ofHom id
           naturality _ _ _ := by ext value; rfl }
  | n + 1 =>
      { app world := TypeCat.ofHom fun value =>
          ⟨(contextMap F objects n).app world value.1, value.2⟩
        naturality X Y arrow := by
          ext value
          apply Sigma.ext
          · exact (contextMap F objects n).naturality_apply arrow value.1
          · rfl }

def contextUnmap (F : C ⥤ D) (objects : Dᵒᵖ ⥤ Type u) : (n : Nat) →
    F.op ⋙ context objects n ⟶ context (F.op ⋙ objects) n
  | 0 => { app _ := TypeCat.ofHom id
           naturality _ _ _ := by ext value; rfl }
  | n + 1 =>
      { app world := TypeCat.ofHom fun value =>
          ⟨(contextUnmap F objects n).app world value.1, value.2⟩
        naturality X Y arrow := by
          ext value
          apply Sigma.ext
          · exact (contextUnmap F objects n).naturality_apply arrow value.1
          · rfl }

theorem contextMap_unmap (F : C ⥤ D) (objects : Dᵒᵖ ⥤ Type u) (n : Nat) :
    contextMap F objects n ≫ contextUnmap F objects n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n prior =>
      ext world value
      apply Sigma.ext
      · exact congrArg (fun map => map.app world value.1) prior
      · rfl

theorem contextUnmap_map (F : C ⥤ D) (objects : Dᵒᵖ ⥤ Type u) (n : Nat) :
    contextUnmap F objects n ≫ contextMap F objects n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n prior =>
      ext world value
      apply Sigma.ext
      · exact congrArg (fun map => map.app world value.1) prior
      · rfl

/-- A canonical isomorphism is built from the independently constructed
tuple maps, with both round trips checked on every binding position. -/
def contextIso (F : C ⥤ D) (objects : Dᵒᵖ ⥤ Type u) (n : Nat) :
    context (F.op ⋙ objects) n ≅ F.op ⋙ context objects n where
  hom := contextMap F objects n
  inv := contextUnmap F objects n
  hom_inv_id := contextMap_unmap F objects n
  inv_hom_id := contextUnmap_map F objects n

set_option backward.isDefEq.respectTransparency false in
theorem variable_restriction (F : C ⥤ D) (objects : Dᵒᵖ ⥤ Type u)
    {n : Nat} (index : Fin n) :
    contextMap F objects n ≫ Functor.whiskerLeft F.op (objectVariable objects index) =
      objectVariable (F.op ⋙ objects) index := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n prior =>
      refine Fin.cases ?_ (fun earlier => ?_) index
      · ext world value
        rfl
      · ext world value
        exact congrArg (fun map => map.app world value.1) (prior earlier)

variable {Constant : Type u}

/-- Every authored object term commutes with actual theory restriction;
constants and bound variables are handled independently. -/
theorem term_restriction (F : C ⥤ D) (objects : Dᵒᵖ ⥤ Type u)
    (constants : Constant → objects.sections) {n : Nat} (expression : ObjectTerm Constant n) :
    contextMap F objects n ≫ Functor.whiskerLeft F.op (term objects constants expression) =
      term (F.op ⋙ objects) (fun name => restrictedSection F (constants name)) expression := by
  cases expression with
  | var index => exact variable_restriction F objects index
  | constant name => ext world value; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The generated simultaneous substitution square retains the complete
object vector through both independent interpretations. -/
theorem substitution_restriction (F : C ⥤ D) (objects : Dᵒᵖ ⥤ Type u)
    (constants : Constant → objects.sections) {n m : Nat}
    (replacements : ObjectSubstitution Constant n m) :
    substitution (F.op ⋙ objects) (fun name => restrictedSection F (constants name)) replacements ≫
        contextMap F objects m =
      contextMap F objects n ≫ Functor.whiskerLeft F.op
        (substitution objects constants replacements) := by
  induction m with
  | zero => ext world value; rfl
  | succ m prior =>
      ext world value
      apply Sigma.ext
      · exact congrArg (fun map => map.app world value)
          (prior (fun i => replacements i.succ))
      · exact heq_of_eq (congrArg (fun map => map.app world value)
          (term_restriction F objects constants (replacements 0)).symm)

theorem contextMap_identity (objects : Cᵒᵖ ⥤ Type u) (n : Nat) :
    contextMap (𝟭 C) objects n = 𝟙 (context objects n) := by
  induction n with
  | zero => rfl
  | succ n prior =>
      ext world value
      apply Sigma.ext
      · exact congrArg (fun map => map.app world value.1) prior
      · rfl

set_option backward.isDefEq.respectTransparency false in
theorem contextMap_composition {E : Type u} [Category.{u} E]
    (F : C ⥤ D) (G : D ⥤ E) (objects : Eᵒᵖ ⥤ Type u) (n : Nat) :
    contextMap (F ⋙ G) objects n =
      contextMap F (G.op ⋙ objects) n ≫ Functor.whiskerLeft F.op (contextMap G objects n) := by
  induction n with
  | zero => rfl
  | succ n prior =>
      ext world value
      apply Sigma.ext
      · exact congrArg (fun map => map.app world value.1) prior
      · rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryInterpretation
