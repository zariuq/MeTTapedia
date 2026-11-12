import Mettapedia.Machines.TIsa.CellEffects
import Mettapedia.GSLT.Logic.ResourceFrame

/-!
# Locality and trace framing for the admitted resource profile

A frame outside every complete recipe footprint cannot enable another
instruction instance. The existing forward safety calculus then frames all
outcomes, and complete firing traces are preserved and reflected. Shared
inputs belong to the demand, so checking only written cells is insufficient.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Framing

open Cells CellEffects
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Logic.ResourceFrame
open Mettapedia.GSLT.SeparationAlgebra

universe u
variable {Key : Type u} [DecidableEq Key]

theorem profile_frame_inert (recipes : List (Recipe Key)) (frameKeys : Finset Key)
    (frameValues : Key → Word) (world : Multiset (Cell Key))
    (apart : ∀ recipe ∈ recipes, Disjoint recipe.support frameKeys) :
    NoNewEnabled (profile recipes) (fun _ => True) world (encode frameKeys frameValues) := by
  apply noNewEnabled_of_apart
  rintro ⟨index, invocation⟩ _ ⟨key, value⟩ framed demanded
  have demandSame : demand (profile recipes) ⟨index, invocation⟩ =
      encode recipes[index.down].support invocation.before := CellEffects.demand_eq _ invocation
  rw [demandSame] at demanded
  have sourceKey := ((mem_encode _ _ _ _).mp demanded).1
  have frameKey := ((mem_encode _ _ _ _).mp framed).1
  exact Finset.disjoint_left.mp (apart recipes[index.down] (List.getElem_mem index.down.isLt)) sourceKey frameKey

theorem profile_fires_unframe (recipes : List (Recipe Key)) (frameKeys : Finset Key)
    (frameValues : Key → Word)
    (apart : ∀ recipe ∈ recipes, Disjoint recipe.support frameKeys) :
    ∀ (entries : List (profile recipes).Entry) (before after : Multiset (Cell Key)),
      (profile recipes).Fires entries (before + encode frameKeys frameValues) (after + encode frameKeys frameValues) →
      (profile recipes).Fires entries before after := by
  intro entries
  induction entries with
  | nil =>
      intro before after fires
      exact add_right_cancel fires
  | cons entry later ih =>
      intro before after fires
      obtain ⟨enabled, rest⟩ := fires
      have localEnabled := profile_frame_inert recipes frameKeys frameValues before apart entry trivial enabled
      refine ⟨localEnabled, ?_⟩
      rw [fire_add_frame (profile recipes) entry localEnabled] at rest
      exact ih _ _ rest

theorem profile_fires_frame_iff (recipes : List (Recipe Key)) (frameKeys : Finset Key)
    (frameValues : Key → Word) (entries : List (profile recipes).Entry)
    (before after : Multiset (Cell Key))
    (apart : ∀ recipe ∈ recipes, Disjoint recipe.support frameKeys) :
    (profile recipes).Fires entries (before + encode frameKeys frameValues) (after + encode frameKeys frameValues) ↔
      (profile recipes).Fires entries before after :=
  ⟨profile_fires_unframe recipes frameKeys frameValues apart entries before after,
    fun fires => fires_add_frame (profile recipes) entries fires (encode frameKeys frameValues)⟩

/-- The established forward safety calculus applies to the actual native profile. -/
theorem profile_safe_frame (recipes : List (Recipe Key)) (pre post : Multiset (Cell Key) → Prop)
    (frameKeys : Finset Key) (frameValues : Key → Word)
    (specification : SafeTriple (profile recipes) (fun _ => True) pre post)
    (apart : ∀ recipe ∈ recipes, Disjoint recipe.support frameKeys) :
    SafeTriple (profile recipes) (fun _ => True)
      (sepConj pre (fun frame => frame = encode frameKeys frameValues))
      (sepConj post (fun frame => frame = encode frameKeys frameValues)) := by
  apply safeTriple_frame (profile recipes) specification
  intro world frame _ same
  subst frame
  exact profile_frame_inert recipes frameKeys frameValues world apart

end Mettapedia.Machines.TIsa.Framing
