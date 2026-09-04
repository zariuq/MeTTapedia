import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryAlignedRestoration

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A collapsing root admits no rigid descent step. -/
theorem CanonicalStopAligned.given_of_collapsingRoot_left
    {declaration : ReflectivePresentationDecl}
    {stop : Pattern → Pattern → Prop} {left right : Pattern}
    (aligned : CanonicalStopAligned declaration stop left right)
    (collapsing : CollapsingRoot declaration left) :
    stop left right := by
  cases aligned with
  | leaf given => exact given
  | bvar index => rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | fvar name => rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | apply ne arguments =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩
      · injection shape with headEq _
        exact absurd headEq ne
      · simp at shape
  | lambda binder body =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | multiLambda arity binders body =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | subst body replacement =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | collection ne elements =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩
      · simp at shape
      · injection shape with typeEq _ _
        exact absurd typeEq ne
  | collectionRest collectionType rest elements =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
