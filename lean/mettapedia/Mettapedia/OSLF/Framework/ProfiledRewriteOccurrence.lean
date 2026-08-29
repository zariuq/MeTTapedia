import Mettapedia.OSLF.Framework.ContextualModalProfile
import Mettapedia.OSLF.Framework.GroundedRewriteOccurrence

/-!
# Atomic inputs to profiled native-type generation

A selected rewrite occurrence contributes three inseparable coordinates to
native-type generation: its occurrence typing, evidence that every required
carrier is grounded in the source language, and one local contextual modal
profile.  Packaging them in one dependent record prevents a profile from
drifting away from the typing that determines its finite slot type.

Ordered generation demands are lists of these atoms.  Carrier-foundation and
hypercube-vertex views are derived projections; they are not parallel stores.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.GSLT.LanguageDef

/-- One typed, grounded, and locally profiled displayed rewrite occurrence. -/
structure ProfiledRewriteOccurrence (source : ValidatedLanguageDef) where
  typing : DisplayedRewriteTyping source
  grounded : SelectedNativeTypeFoundation.CarrierGrounded typing
  profile : ContextualModalProfile.Profile typing

namespace ProfiledRewriteOccurrence

/-- Forget only the local modal profile, retaining the exact typed and
grounded occurrence needed by signature generation. -/
def groundedOccurrence {source : ValidatedLanguageDef}
    (occurrence : ProfiledRewriteOccurrence source) :
    GroundedRewriteOccurrence source where
  typing := occurrence.typing
  grounded := occurrence.grounded

@[simp]
theorem groundedOccurrence_typing {source : ValidatedLanguageDef}
    (occurrence : ProfiledRewriteOccurrence source) :
    occurrence.groundedOccurrence.typing = occurrence.typing :=
  rfl

/-- Stable finite wire for the local profile. -/
def choices {source : ValidatedLanguageDef}
    (occurrence : ProfiledRewriteOccurrence source) :
    List CarrierUniverseSignature.Code :=
  ContextualModalProfile.choices occurrence.profile

/-- A profiled occurrence is determined by its typing and local profile wire;
grounding evidence lives in `Prop` and contributes no duplicate data. -/
@[ext]
theorem ext {source : ValidatedLanguageDef}
    {first second : ProfiledRewriteOccurrence source}
    (typing : first.typing = second.typing)
    (profile : first.choices = second.choices) : first = second := by
  cases first with
  | mk firstTyping firstGrounded firstProfile =>
      cases second with
      | mk secondTyping secondGrounded secondProfile =>
          dsimp at typing profile
          cases typing
          have profileEquality : firstProfile = secondProfile :=
            ContextualModalProfile.choices_injective profile
          cases profileEquality
          rfl

/-- Structural reindexing transports the typing and its grounding evidence;
the local profile codes remain unchanged. -/
noncomputable def map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (occurrence : ProfiledRewriteOccurrence source) :
    ProfiledRewriteOccurrence target where
  typing := occurrence.typing.map morphism
  grounded := occurrence.grounded.map morphism
  profile := ContextualModalProfile.map morphism occurrence.profile

@[simp]
theorem map_typing {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (occurrence : ProfiledRewriteOccurrence source) :
    (occurrence.map morphism).typing = occurrence.typing.map morphism :=
  rfl

/-- Reindexing preserves the complete local profile wire. -/
@[simp]
theorem choices_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (occurrence : ProfiledRewriteOccurrence source) :
    (occurrence.map morphism).choices = occurrence.choices :=
  ContextualModalProfile.choices_map morphism occurrence.profile

@[simp]
theorem map_id (source : ValidatedLanguageDef)
    (occurrence : ProfiledRewriteOccurrence source) :
    occurrence.map (StructuralMorphism.id source) = occurrence := by
  apply ProfiledRewriteOccurrence.ext
  · exact DisplayedRewriteTyping.map_id source occurrence.typing
  · exact choices_map (StructuralMorphism.id source) occurrence

theorem map_comp {first second third : ValidatedLanguageDef}
    (earlier : StructuralMorphism first second)
    (later : StructuralMorphism second third)
    (occurrence : ProfiledRewriteOccurrence first) :
    occurrence.map (StructuralMorphism.comp earlier later) =
      (occurrence.map earlier).map later := by
  apply ProfiledRewriteOccurrence.ext
  · exact DisplayedRewriteTyping.map_comp earlier later occurrence.typing
  · calc
      (occurrence.map (StructuralMorphism.comp earlier later)).choices =
          occurrence.choices := choices_map _ _
      _ = (occurrence.map earlier).choices :=
        (choices_map earlier occurrence).symm
      _ = ((occurrence.map earlier).map later).choices :=
        (choices_map later (occurrence.map earlier)).symm

/-- Choose a constant local endpoint for one already grounded typing. -/
def constant {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source)
    (grounded : SelectedNativeTypeFoundation.CarrierGrounded typing)
    (code : CarrierUniverseSignature.Code) :
    ProfiledRewriteOccurrence source where
  typing := typing
  grounded := grounded
  profile := ContextualModalProfile.constant typing code

/-- Star and box remain distinct on every individual occurrence. -/
theorem constant_star_ne_box {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source)
    (grounded : SelectedNativeTypeFoundation.CarrierGrounded typing) :
    constant typing grounded .star ≠ constant typing grounded .box := by
  intro equality
  have wires := congrArg ProfiledRewriteOccurrence.choices equality
  have profiles :
      ContextualModalProfile.constant typing .star =
        ContextualModalProfile.constant typing .box :=
    ContextualModalProfile.choices_injective (by
      simpa [constant, choices] using wires)
  exact ContextualModalProfile.allStar_ne_allBox typing profiles

#print axioms ext
#print axioms groundedOccurrence_typing
#print axioms map_id
#print axioms map_comp
#print axioms constant_star_ne_box

end ProfiledRewriteOccurrence

end Mettapedia.OSLF.Framework
