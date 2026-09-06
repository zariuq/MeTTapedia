import Mettapedia.Coalgebra.StreamFinality

/-!
# Coherent towers of finite stream observations

A raw family containing one prefix at every depth may be incoherent: its
longer views need not restrict to its shorter views.  The semantic object
determined by finite observation is therefore the subtype of coherent towers,
not the unrestricted dependent function space.

Streams and coherent prefix towers are equivalent.  This sharpens the
finite-view result: every fixed component is lossy, but the compatible tower
of all components retains exactly the stream and neither more nor less.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.CoherentPrefixTower

open Mettapedia.Coalgebra.StreamFinality

universe uLabel

/-- One prefix at every depth, compatible with every restriction map. -/
structure Tower (Label : Type uLabel) where
  view : (depth : Nat) → Prefix Label depth
  coherent : ∀ {earlier later : Nat} (bounded : earlier ≤ later),
    restrictPrefix bounded (view later) = view earlier

namespace Tower

variable {Label : Type uLabel}

@[ext]
theorem ext {first second : Tower Label}
    (views : first.view = second.view) : first = second := by
  cases first
  cases second
  cases views
  rfl

/-- Every stream determines its compatible tower of finite views. -/
def ofStream (stream : Stream Label) : Tower Label where
  view := allPrefixes stream
  coherent := by
    intro earlier later bounded
    exact restrictPrefix_finiteView bounded stream

/-- Read position `index` from any prefix long enough to contain it.  The
successor depth is the canonical such choice. -/
def toStream (tower : Tower Label) : Stream Label :=
  fun index => tower.view (index + 1) ⟨index, Nat.lt_succ_self index⟩

@[simp]
theorem toStream_ofStream (stream : Stream Label) :
    toStream (ofStream stream) = stream := by
  funext index
  rfl

@[simp]
theorem ofStream_toStream (tower : Tower Label) :
    ofStream (toStream tower) = tower := by
  apply Tower.ext
  funext depth index
  have bounded : index.val + 1 ≤ depth :=
    Nat.succ_le_iff.mpr index.isLt
  have restriction := congrFun (tower.coherent bounded)
    ⟨index.val, Nat.lt_succ_self index.val⟩
  exact restriction.symm

/-- Streams and coherent towers carry exactly the same information. -/
def streamEquiv (Label : Type uLabel) :
    Stream Label ≃ Tower Label where
  toFun := ofStream
  invFun := toStream
  left_inv := toStream_ofStream
  right_inv := ofStream_toStream

theorem ofStream_injective :
    Function.Injective (@ofStream Label) :=
  (streamEquiv Label).injective

theorem ofStream_surjective :
    Function.Surjective (@ofStream Label) :=
  (streamEquiv Label).surjective

theorem toStream_injective :
    Function.Injective (@toStream Label) :=
  (streamEquiv Label).symm.injective

theorem toStream_surjective :
    Function.Surjective (@toStream Label) :=
  (streamEquiv Label).symm.surjective

/-! ## Raw towers contain incoherent families -/

/-- A raw Boolean tower whose depth-one observation is false and whose
depth-two observation at the same position is true. -/
def incoherentBooleanViews : (depth : Nat) → Prefix Bool depth :=
  fun depth _index => if depth = 1 then false else true

theorem incoherentBooleanViews_violate_restriction :
    restrictPrefix (show 1 ≤ 2 by decide) (incoherentBooleanViews 2) ≠
      incoherentBooleanViews 1 := by
  intro equality
  have atZero := congrFun equality ⟨0, by decide⟩
  simp [restrictPrefix, incoherentBooleanViews] at atZero

/-- Consequently no coherent tower has the deliberately incompatible raw
family above. -/
theorem no_tower_has_incoherentBooleanViews :
    ¬ ∃ tower : Tower Bool, tower.view = incoherentBooleanViews := by
  rintro ⟨tower, views⟩
  apply incoherentBooleanViews_violate_restriction
  rw [← views]
  exact tower.coherent (show 1 ≤ 2 by decide)

/-! ## Axiom audit -/

#print axioms Tower.ext
#print axioms toStream_ofStream
#print axioms ofStream_toStream
#print axioms streamEquiv
#print axioms incoherentBooleanViews_violate_restriction
#print axioms no_tower_has_incoherentBooleanViews

end Tower

end Mettapedia.Coalgebra.CoherentPrefixTower
