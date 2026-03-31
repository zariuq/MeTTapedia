import Mettapedia.Computability.PNP.CompressionObstruction
import Mettapedia.Hyperseed.Ultrainfinitism
import Mathlib.Data.Fintype.EquivFin

/-!
# P vs NP background theory: encoded hypothesis classes

This file develops an optimistic background layer for the current switching
program.  The adversarial files show that the *full* class of local rules on a
log-radius neighborhood is far too large.  The optimistic route therefore needs
an explicit theorem that the switched predictors lie in a much smaller,
compressible subclass.

The core abstraction here is simple:

* a hypothesis class is realized by decoding a finite code space,
* therefore the realized class cardinality is bounded by the code budget,
* so any successful switching theorem must exhibit a concrete decoder family,
  not merely a locality radius.

We also expose a Hyperseed-flavored surface in which inputs are restricted to an
observer-relative available region.  This lets the same background theory speak
about "what a decoder can see" using existing Mettapedia infrastructure.
-/

namespace Mettapedia.Computability.PNP

open Mettapedia.Hyperseed

universe u v w

/-- A finite coded family of functions `Input → Output`. -/
structure EncodedFamily (Input : Type u) (Output : Type v) where
  Code : Type w
  codeFintype : Fintype Code
  decode : Code → Input → Output

attribute [instance] EncodedFamily.codeFintype

namespace EncodedFamily

variable {Input : Type u} {Output : Type v}

/-- The realized hypothesis class: all functions produced by some code. -/
def realized (H : EncodedFamily Input Output) : Set (Input → Output) :=
  Set.range H.decode

noncomputable instance finiteRealized (H : EncodedFamily Input Output) :
    Finite (realized H) := by
  classical
  let f : H.Code → realized H := fun c => ⟨H.decode c, ⟨c, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro h
    rcases h.2 with ⟨c, hc⟩
    refine ⟨c, Subtype.ext ?_⟩
    exact hc
  exact Finite.of_surjective f hf

noncomputable instance fintypeRealized (H : EncodedFamily Input Output) :
    Fintype (realized H) :=
  Fintype.ofFinite (realized H)

/-- The realized class cannot have more elements than the code space. -/
theorem card_realized_le (H : EncodedFamily Input Output) :
    Fintype.card (realized H) ≤ Fintype.card H.Code := by
  classical
  let f : H.Code → realized H := fun c => ⟨H.decode c, ⟨c, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro h
    rcases h.2 with ⟨c, hc⟩
    refine ⟨c, Subtype.ext ?_⟩
    exact hc
  exact Fintype.card_le_of_surjective f hf

end EncodedFamily

/-- Inputs visible through one Hyperseed perspective/budget/guard slice. -/
abbrev AvailableInput
    {World : Type u} {Signal : Type v} {Cost : Type w} [Preorder Cost]
    (P : Perspective World Signal Cost) (B : Cost) (guard : Set World) :=
  { x : World // x ∈ availableRegion P B guard }

/-- A family of boolean classifiers encoded by `s` bits. -/
structure BitEncodedClassifierFamily (Input : Type u) (s : ℕ) where
  decode : BitCode s → Input → Bool

namespace BitEncodedClassifierFamily

variable {Input : Type u} {s : ℕ}

/-- Package a bit-encoded classifier family as a generic finite encoded family. -/
def toEncodedFamily (F : BitEncodedClassifierFamily Input s) :
    EncodedFamily Input Bool where
  Code := BitCode s
  codeFintype := inferInstance
  decode := F.decode

/-- Any `s`-bit encoded classifier family realizes at most `2^s` classifiers. -/
theorem card_realized_le (F : BitEncodedClassifierFamily Input s) :
    Fintype.card (EncodedFamily.realized F.toEncodedFamily) ≤ 2 ^ s := by
  simpa [BitEncodedClassifierFamily.toEncodedFamily, card_bitCode] using
    EncodedFamily.card_realized_le F.toEncodedFamily

end BitEncodedClassifierFamily

/-- Optimistic bridge theorem:
if a switched/local predictor family is explicitly compressed into `s` bits, then
its realized hypothesis class has size at most `2^s`. -/
theorem card_realized_localFamily_le_of_bitBudget {n s : ℕ}
    (F : BitEncodedClassifierFamily (VisibleBits n) s) :
    Fintype.card (EncodedFamily.realized F.toEncodedFamily) ≤ 2 ^ s :=
  F.card_realized_le

/-- Conversely, no `s`-bit decoder can cover the full local-rule class on `n`
visible bits once `s < 2^n`.  This isolates exactly what extra theorem the
optimistic program still needs: a proof that the switched rules lie in a much
smaller subclass than `LocalRule n`. -/
theorem not_surjective_decode_to_fullLocalRule_of_lt {n s : ℕ}
    (decode : BitCode s → LocalRule n) (hs : s < 2 ^ n) :
    ¬ Function.Surjective decode := by
  intro hsurj
  have hcard : Fintype.card (LocalRule n) ≤ Fintype.card (BitCode s) :=
    Fintype.card_le_of_surjective decode hsurj
  rw [card_localRule, card_bitCode] at hcard
  have hlt : 2 ^ s < 2 ^ (2 ^ n) := Nat.pow_lt_pow_right Nat.one_lt_two hs
  exact Nat.not_le_of_lt hlt hcard

/-- Hyperseed-flavored version:
an `s`-bit classifier over one available region of a perspective still realizes
at most `2^s` classifiers, regardless of how large the ambient world is. -/
theorem card_realized_availableFamily_le_of_bitBudget
    {World : Type u} {Signal : Type v} {Cost : Type w} [Preorder Cost]
    (P : Perspective World Signal Cost) (B : Cost) (guard : Set World)
    {s : ℕ}
    (F : BitEncodedClassifierFamily (AvailableInput P B guard) s) :
    Fintype.card (EncodedFamily.realized F.toEncodedFamily) ≤ 2 ^ s :=
  F.card_realized_le

end Mettapedia.Computability.PNP
