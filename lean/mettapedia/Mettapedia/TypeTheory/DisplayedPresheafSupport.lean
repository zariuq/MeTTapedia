import Mettapedia.TypeTheory.DisplayedPresheafCwf
import Mettapedia.GSLT.Topos.PresheafEvidenceSupport

/-!
# Predicate support of the proof-relevant presheaf CwF

Support is the image of the existing comprehension projection. It commutes
with the CwF's actual type substitution, and a term supplies support without
changing the retained term. The shared family carrier is a functor on the
category of elements; no second family or transport authority is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafSupport

open _root_.CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafCwf

universe u v w

variable {Context : Type u} [Category.{v} Context]
variable {base : Face.{u, v, w} Context}

/-- Forgetting the dependent witness gives exactly the range of the
semantic context-extension projection, not a separate notion of validity. -/
theorem support_eq_comprehension_range
    (family : DisplayedFamily.{u, v, w, w} base) :
    support family = Subfunctor.range (totalProjection family) := by
  ext context value
  constructor
  · rintro ⟨evidence⟩
    exact ⟨⟨value, evidence⟩, rfl⟩
  · rintro ⟨⟨otherValue, evidence⟩, same⟩
    change otherValue = value at same
    subst otherValue
    exact ⟨evidence⟩

/-- CwF type substitution and predicate pullback commute at the level of
whole subfunctors, for arbitrary natural context substitutions. -/
theorem support_cwf_substitution
    {replacement : Face.{u, v, w} Context}
    (substitution : replacement ⟶ base)
    (family : DisplayedFamily.{u, v, w, w} base) :
    support ((presheafCwf Context).tySub family substitution) =
      (support family).preimage substitution :=
  support_reindex substitution family

/-- A supplied dependent term supports every value of its context. This
uses the actual section, not a search for replacement evidence. -/
theorem support_of_term
    (family : DisplayedFamily.{u, v, w, w} base)
    (term : (presheafCwf Context).Tm base family) :
    support family = ⊤ := by
  ext context value
  exact ⟨fun _ => trivial, fun _ => ⟨term.val ⟨context, value⟩⟩⟩

/-- The CwF dependent last variable still returns the original witness
after the corresponding value is observed in predicate support. -/
theorem variable_retains_supported_witness
    (family : DisplayedFamily.{u, v, w, w} base)
    (context : Contextᵒᵖ) (value : base.obj context)
    (evidence : family.obj ⟨context, value⟩) :
    value ∈ (support family).obj context ∧
      ((presheafCwf Context).vz family).val
        ⟨context, ⟨value, evidence⟩⟩ = evidence :=
  ⟨⟨evidence⟩, rfl⟩

#print axioms support_eq_comprehension_range
#print axioms support_cwf_substitution
#print axioms support_of_term
#print axioms variable_retains_supported_witness

end Mettapedia.TypeTheory.DisplayedPresheafSupport
