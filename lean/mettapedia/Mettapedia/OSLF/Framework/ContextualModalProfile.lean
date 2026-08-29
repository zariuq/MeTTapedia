import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mettapedia.OSLF.Framework.ContextualModalSignature
import Mettapedia.OSLF.Framework.DisplayedContextProfileTransport
import Mettapedia.OSLF.Framework.CarrierUniverseSignature

/-!
# Local hypercube profiles for contextual modal type formers

A displayed occurrence with `n` fixed-context dependencies has exactly
`n + 1` local sort slots: one for every rely input and one for the dependent
result family.  A local hypercube profile assigns either `star` or `box` to
each slot.

The slot type is finite by construction.  Consequently an assignment cannot
omit, duplicate, or reorder a contextual dependency, and the signature
compiler cannot silently choose a hypercube vertex.  Profiles transport along
structural language morphisms because contextual binding arity is invariant
under reindexing.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

namespace ContextualModalProfile

/-- Exact local slot indices: all relies followed by the result family. -/
abbrev Slot {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :=
  Fin ((DisplayedContextProfile.bindings typing).length + 1)

/-- A local hypercube vertex for one displayed occurrence. -/
abbrev Profile {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :=
  Slot typing → CarrierUniverseSignature.Code

/-- Embed a fixed-context dependency index into the corresponding local
profile slot. -/
def relySlot {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source)
    (index : Fin (DisplayedContextProfile.bindings typing).length) :
    Slot typing :=
  ⟨index.1, by omega⟩

/-- The final local slot belongs to the dependent result family. -/
def resultSlot {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) : Slot typing :=
  Fin.last (DisplayedContextProfile.bindings typing).length

/-- Read the code assigned to one rely input. -/
def relyCode {source : ValidatedLanguageDef}
    {typing : DisplayedRewriteTyping source} (profile : Profile typing)
    (index : Fin (DisplayedContextProfile.bindings typing).length) :
    CarrierUniverseSignature.Code :=
  profile (relySlot typing index)

/-- Read the code assigned to the dependent result family. -/
def resultCode {source : ValidatedLanguageDef}
    {typing : DisplayedRewriteTyping source} (profile : Profile typing) :
    CarrierUniverseSignature.Code :=
  profile (resultSlot typing)

/-- Constant local vertex, useful for the all-star and all-box endpoints. -/
def constant {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source)
    (code : CarrierUniverseSignature.Code) : Profile typing :=
  fun _ => code

/-- Local profiles are extensionally equal exactly when every slot agrees. -/
theorem ext {source : ValidatedLanguageDef}
    {typing : DisplayedRewriteTyping source} {first second : Profile typing}
    (pointwise : ∀ slot, first slot = second slot) : first = second :=
  funext pointwise

/-- Every displayed occurrence has exactly `2^(n+1)` local vertices. -/
theorem card_profile {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :
    Fintype.card (Profile typing) =
      2 ^ ((DisplayedContextProfile.bindings typing).length + 1) := by
  rw [Fintype.card_fun, Fintype.card_fin]
  rfl

/-- Structural transport preserves the exact number of local slots. -/
theorem slot_count_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (typing : DisplayedRewriteTyping source) :
    (DisplayedContextProfile.bindings (typing.map morphism)).length + 1 =
      (DisplayedContextProfile.bindings typing).length + 1 := by
  have lengths := congrArg List.length
    (DisplayedContextProfile.bindings_map morphism typing)
  simpa using lengths

/-- Reindex a profile along a structural language morphism.  Codes do not
change; only their carrier names and occurrence data are transported. -/
noncomputable def map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {typing : DisplayedRewriteTyping source} (profile : Profile typing) :
    Profile (typing.map morphism) :=
  fun targetSlot => profile ⟨targetSlot.1, by
    rw [← slot_count_map morphism typing]
    exact targetSlot.2⟩

@[simp]
theorem map_apply {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {typing : DisplayedRewriteTyping source} (profile : Profile typing)
    (slot : Slot (typing.map morphism)) :
    map morphism profile slot =
      profile ⟨slot.1, by
        rw [← slot_count_map morphism typing]
        exact slot.2⟩ :=
  rfl

/-- Canonical authored-order serialization of the local profile. -/
def choices {source : ValidatedLanguageDef}
    {typing : DisplayedRewriteTyping source} (profile : Profile typing) :
    List CarrierUniverseSignature.Code :=
  List.ofFn profile

@[simp]
theorem length_choices {source : ValidatedLanguageDef}
    {typing : DisplayedRewriteTyping source} (profile : Profile typing) :
    (choices profile).length =
      (DisplayedContextProfile.bindings typing).length + 1 := by
  simp [choices]

/-- The serialized choices determine the intrinsically indexed profile. -/
theorem choices_injective {source : ValidatedLanguageDef}
    {typing : DisplayedRewriteTyping source} :
    Function.Injective (@choices source typing) := by
  intro first second equality
  exact List.ofFn_injective equality

/-- Structural reindexing preserves every local choice and its order. -/
theorem choices_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {typing : DisplayedRewriteTyping source} (profile : Profile typing) :
    choices (map morphism profile) = choices profile := by
  unfold choices
  rw [List.ofFn_congr (slot_count_map morphism typing)]
  rw [List.ofFn_inj]
  funext slot
  rfl

/-- Identity transport is observationally exact on the profile wire. -/
theorem choices_map_id {source : ValidatedLanguageDef}
    {typing : DisplayedRewriteTyping source} (profile : Profile typing) :
    choices (map (StructuralMorphism.id source) profile) = choices profile :=
  choices_map (StructuralMorphism.id source) profile

/-- Composite structural transport is observationally exact on the same
profile wire, without quotienting occurrence or typing evidence. -/
theorem choices_map_comp {first second third : ValidatedLanguageDef}
    (earlier : StructuralMorphism first second)
    (later : StructuralMorphism second third)
    {typing : DisplayedRewriteTyping first} (profile : Profile typing) :
    choices (map later (map earlier profile)) = choices profile := by
  rw [choices_map later, choices_map earlier]

/-! ## Positive and negative controls -/

/-- The all-star and all-box vertices are always distinct because the result
slot remains observable even in an empty context. -/
theorem allStar_ne_allBox {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :
    constant typing .star ≠ constant typing .box := by
  intro equality
  have resultEquality := congrFun equality (resultSlot typing)
  cases resultEquality

/-- A context with two relies has exactly eight local vertices. -/
theorem card_profile_eq_eight_of_two_relies
    {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source)
    (twoRelies : (DisplayedContextProfile.bindings typing).length = 2) :
    Fintype.card (Profile typing) = 8 := by
  rw [card_profile, twoRelies]
  decide

/-- A unary profile cannot erase the additional choices introduced by a
genuinely contextual occurrence. -/
theorem card_profile_ne_two_of_nonempty
    {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source)
    (nonempty : DisplayedContextProfile.bindings typing ≠ []) :
    Fintype.card (Profile typing) ≠ 2 := by
  rw [card_profile]
  have positive : 0 < (DisplayedContextProfile.bindings typing).length :=
    List.length_pos_of_ne_nil nonempty
  have exponent :
      2 ≤ (DisplayedContextProfile.bindings typing).length + 1 := by
    omega
  have lowerBound :
      2 ^ 2 ≤ 2 ^ ((DisplayedContextProfile.bindings typing).length + 1) :=
    Nat.pow_le_pow_right (by decide) exponent
  change 4 ≤ 2 ^ ((DisplayedContextProfile.bindings typing).length + 1) at lowerBound
  omega

#print axioms card_profile
#print axioms slot_count_map
#print axioms choices_injective
#print axioms choices_map
#print axioms choices_map_id
#print axioms choices_map_comp
#print axioms allStar_ne_allBox
#print axioms card_profile_eq_eight_of_two_relies
#print axioms card_profile_ne_two_of_nonempty

end ContextualModalProfile

end Mettapedia.OSLF.Framework
