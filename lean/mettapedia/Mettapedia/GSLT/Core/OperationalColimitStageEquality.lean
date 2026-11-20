import Mettapedia.GSLT.Core.OperationalColimitFiniteTerms
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Eventual equality of transported stage representatives

Equality in the constructed carrier of a filtered operational diagram is
witnessed by two transport routes to one common stage. For representatives
already at one stage, a single further route witnesses their equality.
This concerns carrier equality, not authored equations or terminality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalColimits

open CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type u} [SmallCategory J]

def carrierDiagram (diagram : J ⥤ OperationalTheory.{u}) : J ⥤ Type u where
  obj stage := (diagram.obj stage).theory.Term
  map route := TypeCat.ofHom (diagram.map route).mapTerm
  map_id stage := by
    apply ConcreteCategory.hom_ext
    intro term
    exact congrArg (fun map : diagram.obj stage ⟶ diagram.obj stage => map.mapTerm term)
      (diagram.map_id stage)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro term
    exact congrArg (fun map : diagram.obj _ ⟶ diagram.obj _ => map.mapTerm term)
      (diagram.map_comp first second)

private theorem transport_eventually_equal (diagram : J ⥤ OperationalTheory.{u})
    {first second : StageTerm diagram} (transport : Transport diagram first second) :
    Types.FilteredColimit.Rel (carrierDiagram diagram) first second := by
  cases transport with
  | @along first second route term =>
      refine ⟨second, route, 𝟙 second, ?_⟩
      change (diagram.map route).mapTerm term =
        (diagram.map (𝟙 second)).mapTerm ((diagram.map route).mapTerm term)
      rw [diagram.map_id]
      rfl

variable [IsFilteredOrEmpty J]

/-- Carrier identifications have finite, explicitly transported witnesses.
The two routes are allowed to differ; filteredness equalizes parallel
routes only after a further stage. -/
theorem inject_eq_iff_eventually_equal (diagram : J ⥤ OperationalTheory.{u})
    {first second : J} (left : (diagram.obj first).theory.Term)
    (right : (diagram.obj second).theory.Term) :
    inject diagram first left = inject diagram second right ↔
      ∃ common, ∃ firstRoute : first ⟶ common, ∃ secondRoute : second ⟶ common,
        (diagram.map firstRoute).mapTerm left = (diagram.map secondRoute).mapTerm right := by
  constructor
  · intro same
    have generated := Quot.eqvGen_exact same
    have transported : Relation.EqvGen (Types.FilteredColimit.Rel (carrierDiagram diagram))
        ⟨first, left⟩ ⟨second, right⟩ :=
      Relation.EqvGen.mono (fun _ _ edge => transport_eventually_equal diagram edge)
        _ _ generated
    exact (Types.FilteredColimit.rel_equiv (carrierDiagram diagram)).eqvGen_iff.mp transported
  · rintro ⟨common, firstRoute, secondRoute, same⟩
    exact (inject_along diagram firstRoute left).trans
      ((congrArg (inject diagram common) same).trans
        (inject_along diagram secondRoute right).symm)

/-- At one stage, eventual equality can use one route for both terms. No
injectivity of the diagram maps has been assumed. -/
theorem inject_eq_iff_equal_after (diagram : J ⥤ OperationalTheory.{u})
    {stage : J} (left right : (diagram.obj stage).theory.Term) :
    inject diagram stage left = inject diagram stage right ↔
      ∃ common, ∃ route : stage ⟶ common,
        (diagram.map route).mapTerm left = (diagram.map route).mapTerm right := by
  constructor
  · intro same
    obtain ⟨common, firstRoute, secondRoute, equal⟩ :=
      (inject_eq_iff_eventually_equal diagram left right).mp same
    obtain ⟨later, onward, commutes⟩ := IsFilteredOrEmpty.cocone_maps firstRoute secondRoute
    refine ⟨later, firstRoute ≫ onward, ?_⟩
    have carried := congrArg (fun term => (diagram.map onward).mapTerm term) equal
    have first := congrArg (fun map : diagram.obj stage ⟶ diagram.obj later => map.mapTerm left)
      (diagram.map_comp firstRoute onward)
    have second := congrArg (fun map : diagram.obj stage ⟶ diagram.obj later => map.mapTerm right)
      (diagram.map_comp secondRoute onward)
    exact first.trans (carried.trans (second.symm.trans
      (congrArg (fun route => (diagram.map route).mapTerm right) commutes.symm)))
  · rintro ⟨common, route, equal⟩
    exact (inject_eq_iff_eventually_equal diagram left right).mpr ⟨common, route, route, equal⟩

#print axioms inject_eq_iff_eventually_equal
#print axioms inject_eq_iff_equal_after

end Mettapedia.GSLT.IndexedOperational.OperationalColimits
