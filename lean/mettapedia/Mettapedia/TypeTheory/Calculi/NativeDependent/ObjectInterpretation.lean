import Mettapedia.TypeTheory.Calculi.NativeDependent.Syntax
import Mettapedia.TypeTheory.DisplayedPresheafComprehension

/-!
# Object substitution in the quantified presheaf interpretation

The object sort is an arbitrary presheaf. Syntactic contexts are interpreted
by iterated extensions with that object presheaf. De Bruijn substitution,
weakening, lifting under a binder and opening a binder are interpreted by
actual natural context maps; their equations are proved on those maps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.ObjectInterpretation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension

universe u
variable {C : Type u} [Category.{u} C]
variable (D : Cᵒᵖ ⥤ Type u)

/-- Every extended context binds another object of the given presheaf. -/
def objectFamily (P : Cᵒᵖ ⥤ Type u) : DisplayedFamily P :=
  CategoryOfElements.π P ⋙ D

/-- The empty context and successive object binders are independent of
atomic predicates and proof declarations. -/
def context : Nat → Cᵒᵖ ⥤ Type u
  | 0 => (Functor.const Cᵒᵖ).obj PUnit
  | n + 1 => totalSpace (objectFamily D (context n))

def newest (n : Nat) : context D (n + 1) ⟶ D where
  app _ := TypeCat.ofHom Sigma.snd
  naturality _ _ _ := by ext value; rfl

def objectVariable : {n : Nat} → Fin n → (context D n ⟶ D)
  | 0, index => Fin.elim0 index
  | n + 1, index => Fin.cases (newest D n)
      (fun prior => totalProjection (objectFamily D (context D n)) ≫ objectVariable prior) index

variable {Constant : Type u}
variable (constants : Constant → D.sections)

/-- Constants are interpreted by supplied natural global object sections. -/
def constant (n : Nat) (name : Constant) : context D n ⟶ D where
  app point := TypeCat.ofHom fun _ => (constants name).val point
  naturality X Y arrow := by
    ext value
    exact ((constants name).property arrow).symm

def term {n : Nat} : ObjectTerm Constant n → (context D n ⟶ D)
  | .var index => objectVariable D index
  | .constant name => constant D constants n name

/-- Append an object map to an interpreted earlierTuple substitution. -/
def tuple {n m : Nat} (earlierTuple : context D n ⟶ context D m)
    (last : context D n ⟶ D) : context D n ⟶ context D (m + 1) where
  app point := TypeCat.ofHom fun value => ⟨earlierTuple.app point value, last.app point value⟩
  naturality X Y arrow := by
    ext value
    apply Sigma.ext
    · exact earlierTuple.naturality_apply arrow value
    · change HEq (last.app Y ((context D n).map arrow value)) (D.map arrow (last.app X value))
      exact heq_of_eq (last.naturality_apply arrow value)

/-- Interpret the finite substitution vector without evaluating any proof. -/
def substitution {n : Nat} : {m : Nat} → ObjectSubstitution Constant n m →
    (context D n ⟶ context D m)
  | 0, _ =>
      { app _ := TypeCat.ofHom fun _ => PUnit.unit
        naturality _ _ _ := by ext value; rfl }
  | m + 1, replacements => tuple D
      (substitution (fun index : Fin m => replacements index.succ))
      (term D constants (replacements 0))

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem substitution_variable {n m : Nat}
    (replacements : ObjectSubstitution Constant n m) (index : Fin m) :
    substitution D constants replacements ≫ objectVariable D index =
      term D constants (replacements index) := by
  induction m with
  | zero => exact Fin.elim0 index
  | succ m ih =>
      refine Fin.cases ?_ (fun prior => ?_) index
      · ext point value
        rfl
      · change tuple D _ _ ≫ (totalProjection _ ≫ objectVariable D prior) = _
        rw [← Category.assoc]
        have projection : tuple D
            (substitution D constants (fun i : Fin m => replacements i.succ))
            (term D constants (replacements 0)) ≫
              totalProjection (objectFamily D (context D m)) =
            substitution D constants (fun i : Fin m => replacements i.succ) := by
          ext point value
          rfl
        rw [projection]
        exact ih _ prior

@[simp] theorem term_substitution {n m : Nat}
    (replacements : ObjectSubstitution Constant n m) (expression : ObjectTerm Constant m) :
    term D constants (ObjectTerm.substitute replacements expression) =
      substitution D constants replacements ≫ term D constants expression := by
  cases expression with
  | var index => exact (substitution_variable D constants replacements index).symm
  | constant name => ext point value; rfl

/-- A tuple is determined by its object variables, including multiplicity. -/
theorem context_map_ext {n m : Nat} (first second : context D n ⟶ context D m)
    (agreement : ∀ index : Fin m, first ≫ objectVariable D index = second ≫ objectVariable D index) :
    first = second := by
  induction m with
  | zero => ext point value; change (_ : PUnit) = _; exact Subsingleton.elim _ _
  | succ m ih =>
      have earlierTuplees : first ≫ totalProjection (objectFamily D (context D m)) =
          second ≫ totalProjection (objectFamily D (context D m)) := by
        apply ih
        intro index
        exact (Category.assoc _ _ _).trans ((agreement index.succ).trans
          (Category.assoc _ _ _).symm)
      have lasts := agreement 0
      ext point value
      apply Sigma.ext
      · exact congrArg (fun map : context D n ⟶ context D m => map.app point value) earlierTuplees
      · apply heq_of_eq
        exact congrArg (fun map : context D n ⟶ D => map.app point value) lasts

/-- Identity de Bruijn substitution reconstructs the full supplied environment. -/
@[simp] theorem substitution_identity (n : Nat) :
    substitution D constants (ObjectSubstitution.identity : ObjectSubstitution Constant n n) =
      𝟙 (context D n) := by
  apply context_map_ext D
  intro index
  rw [substitution_variable]
  exact (Category.id_comp _).symm

@[simp] theorem substitution_compose {n m k : Nat}
    (earlier : ObjectSubstitution Constant n m) (later : ObjectSubstitution Constant m k) :
    substitution D constants (ObjectSubstitution.compose earlier later) =
      substitution D constants earlier ≫ substitution D constants later := by
  apply context_map_ext D
  intro index
  rw [Category.assoc, substitution_variable, substitution_variable]
  exact term_substitution D constants earlier (later index)

@[simp] theorem substitution_weaken (n : Nat) :
    substitution D constants (ObjectSubstitution.weaken : ObjectSubstitution Constant (n + 1) n) =
      totalProjection (objectFamily D (context D n)) := by
  apply context_map_ext D
  intro index
  rw [substitution_variable]
  rfl

@[simp] theorem term_weaken {n : Nat} (expression : ObjectTerm Constant n) :
    term D constants (ObjectTerm.weaken expression) =
      totalProjection (objectFamily D (context D n)) ≫ term D constants expression := by
  cases expression with
  | var index => rfl
  | constant name => ext point value; rfl

/-- Natural context maps do not change the underlying world's object sort. -/
theorem objectFamily_reindex {n m : Nat} (f : context D n ⟶ context D m) :
    reindexDisplayed f (objectFamily D (context D m)) = objectFamily D (context D n) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Syntactic lifting keeps the new object and changes only the older tuple. -/
theorem substitution_lift {n m : Nat} (replacements : ObjectSubstitution Constant n m) :
    substitution D constants (ObjectSubstitution.lift replacements) =
      totalReindexMap (substitution D constants replacements)
        (objectFamily D (context D m)) := by
  apply context_map_ext D
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rw [substitution_variable]
    ext point value
    rfl
  · rw [substitution_variable]
    change term D constants (ObjectTerm.weaken (replacements prior)) = _
    rw [term_weaken]
    rw [← substitution_variable D constants replacements prior]
    rw [← Category.assoc]
    have square := totalReindexMap_square (substitution D constants replacements)
      (objectFamily D (context D m))
    change _ = totalReindexMap (substitution D constants replacements)
      (objectFamily D (context D m)) ≫
        (totalProjection (objectFamily D (context D m)) ≫ objectVariable D prior)
    rw [← Category.assoc, square]
    rfl


/-- An object expression is also a natural term of the bound object family. -/
def objectSection {n : Nat} (expression : ObjectTerm Constant n) :
    (objectFamily D (context D n)).sections where
  val point := (term D constants expression).app point.1 point.2
  property := by
    intro source target arrow
    change D.map arrow.val ((term D constants expression).app source.1 source.2) = _
    rw [← (term D constants expression).naturality_apply arrow.val source.2]
    exact congrArg ((term D constants expression).app target.1) arrow.property

/-- Opening the binder uses the original tuple and the exact supplied object. -/
theorem substitution_instantiate {n : Nat} (argument : ObjectTerm Constant n) :
    substitution D constants (ObjectSubstitution.instantiate argument) =
      sectionLift (objectFamily D (context D n)) (objectSection D constants argument) := by
  apply context_map_ext D
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rw [substitution_variable]
    ext point value
    rfl
  · rw [substitution_variable]
    have projection := sectionLift_projection (objectFamily D (context D n))
      (objectSection D constants argument)
    exact ((Category.assoc _ _ _).symm.trans (congrArg
      (fun earlierTuple : context D n ⟶ context D n => earlierTuple ≫ objectVariable D prior) projection)).trans
        (Category.id_comp _)

end Mettapedia.TypeTheory.Calculi.NativeDependent.ObjectInterpretation
