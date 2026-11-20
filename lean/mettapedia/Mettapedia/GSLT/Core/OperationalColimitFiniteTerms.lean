import Mettapedia.GSLT.Core.OperationalColimits

/-!
# A common stage for a finite ordered list of ambient terms

Filteredness transports the stage representatives of finitely many carrier
terms to one common stage. The representation retains list order and every
occurrence, including repetitions.

This is a carrier-level support theorem. A finite execution also has step
and equation witnesses to transport. Finite-presentability of an authored
presentation, its compiler realization and negative observations require
their own laws; none is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalColimits

open CategoryTheory

universe u

variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- A finite ordered family of ambient carrier terms has simultaneous
representatives at one stage, through the actual diagram maps. -/
theorem finite_terms_factor (diagram : J ⥤ OperationalTheory.{u})
    (terms : List (Term diagram)) :
    ∃ stage, ∃ representatives : List (diagram.obj stage).theory.Term,
      representatives.map (inject diagram stage) = terms := by
  induction terms with
  | nil =>
      obtain ⟨stage⟩ := (IsFiltered.nonempty : Nonempty J)
      exact ⟨stage, [], rfl⟩
  | cons first rest ih =>
      obtain ⟨firstStage, firstTerm, firstEq⟩ := term_from_stage diagram first
      obtain ⟨restStage, restTerms, restEq⟩ := ih
      obtain ⟨common, firstRoute, restRoute, _⟩ :=
        IsFilteredOrEmpty.cocone_objs firstStage restStage
      refine ⟨common, (diagram.map firstRoute).mapTerm firstTerm ::
        restTerms.map (diagram.map restRoute).mapTerm, ?_⟩
      rw [List.map_cons]
      apply congrArg₂ List.cons ((inject_along diagram firstRoute firstTerm).symm.trans firstEq)
      have tail :
          (restTerms.map (diagram.map restRoute).mapTerm).map (inject diagram common) =
            restTerms.map (inject diagram restStage) := by
        rw [List.map_map]
        apply congrArg (fun function => restTerms.map function)
        funext term
        exact (inject_along diagram restRoute term).symm
      exact tail.trans restEq

/-- Factorization does not turn repeated occurrences into a set. -/
theorem finite_terms_factor_with_count (diagram : J ⥤ OperationalTheory.{u})
    (terms : List (Term diagram)) :
    ∃ stage, ∃ representatives : List (diagram.obj stage).theory.Term,
      representatives.map (inject diagram stage) = terms ∧
        representatives.length = terms.length := by
  obtain ⟨stage, representatives, same⟩ := finite_terms_factor diagram terms
  refine ⟨stage, representatives, same, ?_⟩
  simpa only [List.length_map] using congrArg List.length same

/-- Abstract compact requests factor through the constructed ambient
colimit. The request's finite-presentability is an explicit, independent
hypothesis; a finite authored syntax does not supply that instance here. -/
theorem finitely_presentable_request_factors (diagram : J ⥤ OperationalTheory.{u})
    {request : OperationalTheory.{u}} [IsFinitelyPresentable.{u} request]
    (map : request ⟶ (cocone diagram).pt) :
    ∃ stage, ∃ through : request ⟶ diagram.obj stage,
      through ≫ (cocone diagram).ι.app stage = map :=
  IsFinitelyPresentable.exists_hom_of_isColimit (isColimit diagram) map

#print axioms finite_terms_factor
#print axioms finite_terms_factor_with_count
#print axioms finitely_presentable_request_factors

end Mettapedia.GSLT.IndexedOperational.OperationalColimits
