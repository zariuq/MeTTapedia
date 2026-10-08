import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualDoctrine
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualRefinementSubstitution

/-!
# Refinement capabilities of the generated dependent model

The chosen source quotient CwF supplies actual refinement inhabitants. Its
predicate doctrine acts by the same generated substitution presheaf as the
refinement guard. The generated introduction, forgetting, beta and eta
equations, together with their complete substitution comparisons, therefore
instantiate the local refinement capability interface.

The guard denotes generated entailment. It neither selects a data witness
from existential truth nor identifies the generated predicate fibre with all
subobjects of the source context category.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.RefinementModel

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualPredicateCapabilities

universe u
variable {S : Symbols.{u}} {D : Signature S}

/-- The doctrine and the refinement guard use the same actual arrow action. -/
theorem doctrine_reindex {source target : QuotientCwf.QContext D}
    (substitution : source ⟶ target) (predicate : QPredicate target.as) :
    (predicateDoctrine D).reindex substitution predicate =
      RefinementValues.predicateSub predicate substitution := rfl

noncomputable def operations (D : Signature S) : RefinementOperations (predicateDoctrine D) where
  refined := Refinements.type
  intro := fun _ predicate term evidence => RefinementValues.intro_of_top predicate term evidence
  forget := fun _ predicate term => RefinementValues.forget predicate term
  forget_guard := fun _ predicate term => RefinementValues.guard_forget_top predicate term
  beta := fun _ predicate term evidence =>
    RefinementValues.beta predicate term ((Logic.entails_iff_eq_top _).mpr evidence)
  eta := fun _ predicate term => RefinementValues.eta predicate term
  formation_substitution := RefinementValues.formation_substitution
  intro_substitution := fun substitution _ predicate term evidence transportedEvidence =>
    RefinementValues.intro_substitution substitution predicate term
      ((Logic.entails_iff_eq_top _).mpr evidence)
      ((Logic.entails_iff_eq_top _).mpr transportedEvidence)
  forget_substitution := fun substitution _ predicate term transported same =>
    RefinementValues.forget_substitution substitution predicate term transported same

/-- A complete generated refinement inhabitant retains exactly a supplied
value satisfying its generated predicate. The two inverse equations are
earned from the generated refinement beta and eta derivations. -/
noncomputable def inhabitantEquiv {context : QuotientCwf.QContext D}
    {type : QuotientCwf.Ty context} (predicate : QPredicate (QuotientCwf.ext context type).as) :
    QuotientCwf.Tm context (Refinements.type type predicate) ≃
      {term : QuotientCwf.Tm context type // RefinementValues.guard predicate term = ⊤} where
  toFun term := ⟨RefinementValues.forget predicate term,
    RefinementValues.guard_forget_top predicate term⟩
  invFun term := RefinementValues.intro_of_top predicate term.val term.property
  left_inv term := RefinementValues.eta predicate term
  right_inv term := Subtype.ext
    (RefinementValues.beta predicate term.val ((Logic.entails_iff_eq_top _).mpr term.property))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.RefinementModel
