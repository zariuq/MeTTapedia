import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Types.Basic
import Mettapedia.TypeTheory.ContextualComputationKleisli

/-!
# The contextual Kleisli adjunction

Value types form `Type`; computation objects belong to the existing contextual
Kleisli category. The left functor embeds value maps as pure computations. The
right functor sends a computation object to its type of contextual programs,
and sends a Kleisli arrow to sequencing with that arrow. It does not forget an
object to its answer type.

The natural hom equivalence gives a genuine adjunction. Its induced monad has
the existing `Program` syntax, pure return, map and bind, with no new evaluator
or equality on effects. These are free-computation Kleisli objects, not a claim
that all computation algebras or the type formers of dependent CBPV have been
constructed. In particular, the counit does not allocate or memoize a Need cell.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualKleisliAdjunction

open CategoryTheory
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open ContextualComputationKleisli (Object)

universe u

/-- Include value types and pure maps in the existing Kleisli category. -/
def free (State Intent : Type u) : Type u ⥤ Object State Intent where
  obj Answer := ⟨Answer⟩
  map function := Object.Hom.ofFunction function
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The carrier of a free computation object is its contextual program type.
An arrow acts on that carrier by the already defined sequencing operation. -/
def underlying (State Intent : Type u) : Object State Intent ⥤ Type u where
  obj object := Program State object.Carrier Intent
  map arrow := TypeCat.ofHom (fun program => Program.bind program arrow.toFun)
  map_id object := by
    ext program
    exact ContextualComputationKleisli.Program.bind_pure program
  map_comp first second := by
    ext program
    exact (ContextualComputationKleisli.Program.bind_assoc program first.toFun second.toFun).symm

variable (State Intent : Type u)

/-- Transposition preserves the actual function into contextual programs. -/
def homEquiv (Answer : Type u) (object : Object State Intent) :
    ((free State Intent).obj Answer ⟶ object) ≃
      (Answer ⟶ (underlying State Intent).obj object) where
  toFun arrow := TypeCat.ofHom arrow.toFun
  invFun function := ⟨function⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem homEquiv_naturality_left {First Second : Type u} {object : Object State Intent}
    (function : First ⟶ Second) (arrow : (free State Intent).obj Second ⟶ object) :
    homEquiv State Intent First object ((free State Intent).map function ≫ arrow) =
      function ≫ homEquiv State Intent Second object arrow := by
  rfl

theorem homEquiv_naturality_right {Answer : Type u} {first second : Object State Intent}
    (arrow : (free State Intent).obj Answer ⟶ first) (later : first ⟶ second) :
    homEquiv State Intent Answer second (arrow ≫ later) =
      homEquiv State Intent Answer first arrow ≫ (underlying State Intent).map later := by
  rfl

def adjunction : free State Intent ⊣ underlying State Intent :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv State Intent
      homEquiv_naturality_left_symm := by intros; rfl
      homEquiv_naturality_right := homEquiv_naturality_right State Intent }

@[simp] theorem unit_apply {Answer : Type u} (answer : Answer) :
    (adjunction State Intent).unit.app Answer answer = Program.pure answer :=
  rfl

/-- The counit exposes the supplied program as a Kleisli computation. It is
not a value-returning interpreter and does not record any cache ownership. -/
@[simp] theorem counit_apply (object : Object State Intent)
    (program : Program State object.Carrier Intent) :
    ((adjunction State Intent).counit.app object).toFun program = program :=
  rfl

theorem left_triangle (Answer : Type u) :
    (free State Intent).map ((adjunction State Intent).unit.app Answer) ≫
      (adjunction State Intent).counit.app ((free State Intent).obj Answer) =
        𝟙 ((free State Intent).obj Answer) :=
  (adjunction State Intent).left_triangle_components Answer

theorem right_triangle (object : Object State Intent) :
    (adjunction State Intent).unit.app ((underlying State Intent).obj object) ≫
      (underlying State Intent).map ((adjunction State Intent).counit.app object) =
        𝟙 ((underlying State Intent).obj object) :=
  (adjunction State Intent).right_triangle_components object

/-- The monad is induced by the proved adjunction, not separately postulated. -/
def inducedMonad : CategoryTheory.Monad (Type u) :=
  (adjunction State Intent).toMonad

@[simp] theorem inducedMonad_obj (Answer : Type u) :
    (inducedMonad State Intent).obj Answer = Program State Answer Intent :=
  rfl

@[simp] theorem inducedMonad_map {Answer OtherAnswer : Type u}
    (function : Answer → OtherAnswer) (program : Program State Answer Intent) :
    (inducedMonad State Intent).map (TypeCat.ofHom function) program =
      Program.map function program :=
  rfl

@[simp] theorem inducedMonad_unit {Answer : Type u} (answer : Answer) :
    (inducedMonad State Intent).η.app Answer answer = Program.pure answer :=
  rfl

@[simp] theorem inducedMonad_multiply {Answer : Type u}
    (program : Program State (Program State Answer Intent) Intent) :
    (inducedMonad State Intent).μ.app Answer program =
      Program.bind program (fun next => next) :=
  rfl

/-- The adjunction's substitution operation is exactly existing bind. -/
theorem inducedMonad_bind {Answer OtherAnswer : Type u}
    (program : Program State Answer Intent)
    (next : Answer → Program State OtherAnswer Intent) :
    (inducedMonad State Intent).μ.app OtherAnswer
      ((inducedMonad State Intent).map (TypeCat.ofHom next) program) =
      Program.bind program next := by
  rw [inducedMonad_map, inducedMonad_multiply]
  unfold Program.map
  rw [ContextualComputationKleisli.Program.bind_assoc]
  rfl

/-- Pure values embed injectively, but the unit need not cover computations. -/
theorem unit_injective (Answer : Type u) :
    Function.Injective ((adjunction State Intent).unit.app Answer) := by
  intro first second equal
  change Program.pure first = Program.pure second at equal
  cases equal
  rfl

section Controls

/-- Multiplication retains both the outer alternatives and the inner choice. -/
theorem multiply_nested_choice :
    (inducedMonad Bool Unit).μ.app Bool
      (.choose (.pure (.choose (.pure false) (.pure true))) (.pure (.pure true))) =
      .choose (.choose (.pure false) (.pure true)) (.pure true) :=
  rfl

theorem nested_choice_observations :
    (runWorlds ((inducedMonad Bool Unit).μ.app Bool
      (.choose (.pure (.choose (.pure false) (.pure true))) (.pure (.pure true)))) false).map
      WorldResult.answer = [false, true, true] :=
  rfl

/-- A choice computation is outside the pure unit's image. -/
theorem unit_not_surjective :
    ¬ Function.Surjective ((adjunction Bool Unit).unit.app Bool) := by
  intro onto
  obtain ⟨answer, equal⟩ := onto (.choose (.pure false) (.pure true))
  change Program.pure answer = Program.choose (.pure false) (.pure true) at equal
  cases equal

/-- The left functor is not full: a real effectful arrow is not a pure map. -/
theorem choice_not_free_image :
    ¬ ∃ function : Unit ⟶ Bool,
      (free Bool Unit).map function = ContextualComputationKleisli.Object.chooseBool := by
  rintro ⟨function, equal⟩
  have impossible := congrArg (fun arrow => arrow.toFun ()) equal
  change Program.pure (function ()) = Program.choose (.pure false) (.pure true) at impossible
  cases impossible

end Controls

#print axioms adjunction
#print axioms left_triangle
#print axioms right_triangle
#print axioms inducedMonad
#print axioms inducedMonad_bind
#print axioms nested_choice_observations
#print axioms unit_not_surjective
#print axioms choice_not_free_image

end Mettapedia.TypeTheory.ContextualKleisliAdjunction
