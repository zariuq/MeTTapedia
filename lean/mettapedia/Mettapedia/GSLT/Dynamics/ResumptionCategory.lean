import Mettapedia.GSLT.Dynamics.WeightedResumption
import Mathlib.Control.Monad.Writer
import Mathlib.CategoryTheory.Category.KleisliCat
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Resumption handlers and their Kleisli categories

The free operation construction is a lawful monad. Its coefficient handler
lands in Mathlib's writer transformer over occurrence-sensitive lists, with
ordered multiplication as the writer operation. Consequently the handler is
a functor between the existing Kleisli categories: substitution in a free
computation agrees with composition of its weighted interpretations.

A coefficient homomorphism induces a second Kleisli functor and commutes with
handling. This is the multiplicative change-of-base boundary. Combining
alternative coefficients needs additive laws as well; neither support nor a
Born readout receives those laws automatically.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ResumptionCategory

open ResumptionAlgebra
open CategoryTheory

universe u

variable (Operation : Type u) (Response : Operation → Type u)

instance computationMonad : Monad (Computation Operation Response) where
  pure := ResumptionAlgebra.pure
  bind := ResumptionAlgebra.bind

instance computationLawfulMonad : LawfulMonad (Computation Operation Response) :=
  LawfulMonad.mk'
    (id_map := fun computation => ResumptionAlgebra.bind_pure computation)
    (pure_bind := fun answer next => ResumptionAlgebra.pure_bind answer next)
    (bind_assoc := fun computation first second =>
      ResumptionAlgebra.bind_assoc computation first second)

variable {Operation Response} {V W : Type u}

/-- Interpret through the standard noncommutative writer transformer. -/
def handle [Monoid V]
    (responses : (operation : Operation) → WeightedResumption.Contributions (Response operation) V)
    {Answer : Type u} (computation : Computation Operation Response Answer) :
    WriterT V List Answer := WriterT.mk (WeightedResumption.interpret responses computation)

@[simp] theorem handle_pure [Monoid V]
    (responses : (operation : Operation) → WeightedResumption.Contributions (Response operation) V)
    {Answer : Type u} (answer : Answer) :
    handle responses (ResumptionAlgebra.pure answer) = (Pure.pure answer : WriterT V List Answer) :=
  rfl

/-- Actual writer sequencing is the independently defined contribution algorithm. -/
theorem writer_bind [Monoid V] {Answer Other : Type u}
    (contributions : WriterT V List Answer) (next : Answer → WriterT V List Other) :
    (contributions >>= next).run =
      WeightedResumption.sequence contributions.run (fun answer => (next answer).run) := rfl

theorem handle_bind [Monoid V]
    (responses : (operation : Operation) → WeightedResumption.Contributions (Response operation) V)
    {Answer Other : Type u} (computation : Computation Operation Response Answer)
    (next : Answer → Computation Operation Response Other) :
    handle responses (ResumptionAlgebra.bind computation next) =
      (handle responses computation >>= fun answer => handle responses (next answer)) := by
  apply WriterT.ext
  rw [writer_bind]
  exact WeightedResumption.interpret_bind responses computation next

/-- The native interpretation boundary is a functor, rather than unrelated folds. -/
def handlerFunctor [Monoid V]
    (responses : (operation : Operation) → WeightedResumption.Contributions (Response operation) V) :
    CategoryTheory.KleisliCat (Computation Operation Response) ⥤
      CategoryTheory.KleisliCat (WriterT V List) where
  obj answer := CategoryTheory.KleisliCat.mk (WriterT V List) answer
  map computation := fun answer => handle responses (computation answer)
  map_id _ := by funext answer; exact handle_pure responses answer
  map_comp first second := by
    funext answer
    exact handle_bind responses (first answer) second

/-- Change only the coefficient interpretation, retaining every occurrence. -/
def coefficientFunctor [Monoid V] [Monoid W] (hom : V →* W) :
    CategoryTheory.KleisliCat (WriterT V List) ⥤
      CategoryTheory.KleisliCat (WriterT W List) where
  obj answer := CategoryTheory.KleisliCat.mk (WriterT W List) answer
  map computation := fun answer =>
    WriterT.mk (WeightedResumption.mapCoefficients hom (computation answer).run)
  map_id _ := by
    funext answer
    apply WriterT.ext
    change [(answer, hom 1)] = [(answer, 1)]
    rw [hom.map_one]
  map_comp first second := by
    funext answer
    apply WriterT.ext
    change WeightedResumption.mapCoefficients hom
      (WeightedResumption.sequence (first answer).run (fun value => (second value).run)) = _
    exact WeightedResumption.mapCoefficients_sequence hom hom.map_mul _ _

/-- The handler/change-of-base square commutes on every actual free computation. -/
theorem handle_changeOfBase [Monoid V] [Monoid W] (hom : V →* W)
    (responses : (operation : Operation) → WeightedResumption.Contributions (Response operation) V)
    {Answer : Type u} (computation : Computation Operation Response Answer) :
    WeightedResumption.mapCoefficients hom (handle responses computation).run =
      (handle (fun operation => WeightedResumption.mapCoefficients hom (responses operation))
        computation).run :=
  WeightedResumption.interpret_mapCoefficients hom responses computation

end Mettapedia.GSLT.Dynamics.ResumptionCategory
