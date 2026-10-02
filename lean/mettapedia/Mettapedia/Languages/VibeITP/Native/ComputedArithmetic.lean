import Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
import Mettapedia.Languages.VibeITP.Presentation.CompleteLiterals
import Mettapedia.Languages.VibeITP.Presentation.Soundness
import Mettapedia.Languages.VibeITP.Native.Word64Bridge

/-!
# Exact computed arithmetic leaves for the Vibe rule package

Ground arithmetic queries are checked by computation and may replace replay
subtrees. Their qualification is proved against the actual first-order rule
package, in both directions, uniformly over structurally hosted theories.
These are operational judgments, not `VThm` statements: an unrelated admitted
axiom cannot make an incorrect arithmetic result a correct operation.

The natural-number claims retain unbounded intermediates. In particular,
wrapping addition consists of an addition judgment followed by a modulo
judgment; the addition relation is not silently changed to word addition.
Native bit-vector division and byte encoding specialize the same boundary.
This does not yet connect the generated guest's C bodies to these leaves.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.ComputedArithmetic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.Languages.VibeITP.Spec
open Mettapedia.Languages.VibeITP.Presentation

inductive Claim where
  | add (a b result : Nat)
  | mul (a b result : Nat)
  | divMod (a b quotient remainder : Nat)
  | mod64 (a result : Nat)
  | word (a : Nat)
  | monus (a b result : Nat)
  | max (a b result : Nat)
  | natLiteral (a : Nat) (bytes : List UInt8)

def judgment : Claim → Pattern
  | .add a b c => jNAdd (encNat a) (encNat b) (encNat c)
  | .mul a b c => jNMul (encNat a) (encNat b) (encNat c)
  | .divMod a b q r => jNDivMod (encNat a) (encNat b) (encNat q) (encNat r)
  | .mod64 a c => jNMod64 (encNat a) (encNat c)
  | .word a => jNWord (encNat a)
  | .monus a b c => jNMonus (encNat a) (encNat b) (encNat c)
  | .max a b c => jNMax (encNat a) (encNat b) (encNat c)
  | .natLiteral a bytes => jNatLit (encNat a) (encBytes bytes)

def valid : Claim → Bool
  | .add a b c => decide (c = a + b)
  | .mul a b c => decide (c = a * b)
  | .divMod a b q r => decide (0 < b ∧ q = a / b ∧ r = a % b)
  | .mod64 a c => decide (c = a % wordBound)
  | .word a => decide (a < wordBound)
  | .monus a b c => decide (c = a - b)
  | .max a b c => decide (c = max a b)
  | .natLiteral a bytes => decide (bytes = Spec.natLiteral a)

def evaluate (claim : Claim) : Option Pattern :=
  if valid claim then some (judgment claim) else none

theorem valid_iff_derivable {T : Theory} {n : Nat} (hosted : Hosted T n)
    (claim : Claim) : valid claim = true ↔
      FODerivable (kernelRules ++ theoryRules T n) (judgment claim) := by
  have included : kernelRules ⊆ kernelRules ++ theoryRules T n := by
    intro rule member
    exact List.mem_append_left _ member
  cases claim with
  | add a b c =>
      simp only [valid, decide_eq_true_eq, judgment]
      constructor
      · rintro rfl; exact complete_nadd included a b
      · intro derived
        have meaning : NAddM (encNat a) (encNat b) (encNat c) :=
          meaning_of_foDerivable hosted derived
        simpa only [decNat_encNat, Option.some.injEq] using
          meaning.1 a b (decNat_encNat a) (decNat_encNat b)
  | mul a b c =>
      simp only [valid, decide_eq_true_eq, judgment]
      constructor
      · rintro rfl; exact complete_nmul included a b
      · intro derived
        have meaning : NMulM (encNat a) (encNat b) (encNat c) :=
          meaning_of_foDerivable hosted derived
        simpa only [decNat_encNat, Option.some.injEq] using
          meaning.1 a b (decNat_encNat a) (decNat_encNat b)
  | divMod a b q r =>
      simp only [valid, decide_eq_true_eq, judgment]
      constructor
      · rintro ⟨positive, rfl, rfl⟩
        exact complete_ndivmod included a b positive
      · intro derived
        have meaning : NDivModM (encNat a) (encNat b) (encNat q) (encNat r) :=
          meaning_of_foDerivable hosted derived
        obtain ⟨u, v, hu, hv, decomposition, remainder⟩ :=
          meaning a b (decNat_encNat a) (decNat_encNat b)
        simp only [decNat_encNat, Option.some.injEq] at hu hv
        subst u; subst v
        have positive : 0 < b := by omega
        refine ⟨positive, ?_, ?_⟩
        · rw [decomposition, Nat.mul_add_div positive, Nat.div_eq_of_lt remainder]
          simp
        · rw [decomposition, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt remainder]
  | mod64 a c =>
      simp only [valid, decide_eq_true_eq, judgment]
      constructor
      · rintro rfl; exact complete_nmod64 included a
      · intro derived
        have meaning : NMod64M (encNat a) (encNat c) :=
          meaning_of_foDerivable hosted derived
        simpa only [decNat_encNat, Option.some.injEq] using meaning a (decNat_encNat a)
  | word a =>
      simp only [valid, decide_eq_true_eq, judgment]
      constructor
      · exact complete_nword included a
      · intro derived
        have meaning : NWordM (encNat a) := meaning_of_foDerivable hosted derived
        obtain ⟨value, decoded, bound⟩ := meaning
        have same : a = value := by simpa only [decNat_encNat, Option.some.injEq] using decoded
        exact same ▸ bound
  | monus a b c =>
      simp only [valid, decide_eq_true_eq, judgment]
      constructor
      · rintro rfl; exact complete_nmonus included a b
      · intro derived
        have meaning : NMonusM (encNat a) (encNat b) (encNat c) :=
          meaning_of_foDerivable hosted derived
        simpa only [decNat_encNat, Option.some.injEq] using
          meaning a b (decNat_encNat a) (decNat_encNat b)
  | max a b c =>
      simp only [valid, decide_eq_true_eq, judgment]
      constructor
      · rintro rfl; exact complete_nmax included a b
      · intro derived
        have meaning : NMaxM (encNat a) (encNat b) (encNat c) :=
          meaning_of_foDerivable hosted derived
        simpa only [decNat_encNat, Option.some.injEq] using
          meaning a b (decNat_encNat a) (decNat_encNat b)
  | natLiteral a bytes =>
      simp only [valid, decide_eq_true_eq, judgment]
      constructor
      · rintro rfl; exact complete_natlit included a
      · intro derived
        have meaning : NatLitM (encNat a) (encBytes bytes) :=
          meaning_of_foDerivable hosted derived
        exact encBytes_inj (meaning a (decNat_encNat a))

theorem valid_iff_replay {T : Theory} {n : Nat} (hosted : Hosted T n) (claim : Claim) :
    valid claim = true ↔
      ∃ raw, checkRaw (kernelValidated T n) (judgment claim) raw = true :=
  (valid_iff_derivable hosted claim).trans
    (checkRaw_exists_iff_foDerivable (kernelValidated_presents T n) _).symm

/-- This instance discharges qualification using the Vibe rules, not an
assumed implementation/reference agreement supplied by its caller. -/
def computation {T : Theory} {n : Nat} (hosted : Hosted T n) :
    QualifiedComputation (kernelValidated T n) Claim where
  evaluate := evaluate
  sound := by
    intro claim goal returned
    unfold evaluate at returned
    split at returned
    next accepted =>
      cases returned
      obtain ⟨raw, replayed⟩ := (valid_iff_replay hosted claim).mp accepted
      exact checkRaw_soundness replayed
    next refused => cases returned

theorem compact_iff_replay {T : Theory} {n : Nat} (hosted : Hosted T n) (goal : Pattern) :
    (∃ proof, check (kernelValidated T n) evaluate goal proof = true) ↔
      ∃ raw, checkRaw (kernelValidated T n) goal raw = true :=
  accepted_iff_replay (computation hosted) goal

/-- Invalid computations exclude every replay witness for that operation. -/
theorem invalid_rejects_every_replay {T : Theory} {n : Nat} (hosted : Hosted T n)
    {claim : Claim} (invalid : valid claim = false) (raw : RawProof) :
    checkRaw (kernelValidated T n) (judgment claim) raw = false := by
  cases accepted : checkRaw (kernelValidated T n) (judgment claim) raw with
  | false => rfl
  | true =>
      have impossible := (valid_iff_replay hosted claim).mpr ⟨raw, accepted⟩
      simp [invalid] at impossible

open Mettapedia.GSLT.LanguageDef.NativeWord64

/-- Guarded native division computes the unique quotient and remainder
authorized by the reference operation, over the entire 64-bit input range. -/
theorem native_division_valid (a b : Word) :
    valid (.divMod a.val b.val ((encode a / encode b).toNat)
      ((encode a % encode b).toNat)) = decide (0 < b.val) := by
  simp [valid, BitVec.toNat_udiv, BitVec.toNat_umod]

theorem native_literal_valid (a : Word) :
    valid (.natLiteral a.val (Word64Bridge.nativeNatLiteral (encode a))) = true := by
  simp [valid, Word64Bridge.native_number_literal_correspondence]

/-- The word result is the modulo output; the unbounded addition remains
available as the intermediate premise of `vibe-lit-add`. -/
theorem native_wrapped_add_valid (a b : Word) :
    valid (.add a.val b.val (a.val + b.val)) = true ∧
      valid (.mod64 (a.val + b.val) (encode a + encode b).toNat) = true := by
  simp [valid, wordBound]

theorem native_wrapped_mul_valid (a b : Word) :
    valid (.mul a.val b.val (a.val * b.val)) = true ∧
      valid (.mod64 (a.val * b.val) (encode a * encode b).toNat) = true := by
  simp [valid, wordBound]

/-- Qualification composes with the unchanged theorem checker. -/
theorem compact_theorem_sound {T : Theory} {n : Nat} (hosted : Hosted T n)
    {statement : Term} {proof : CompactProof Claim}
    (accepted : check (kernelValidated T n) evaluate
      (jThm (encTerm T.sig statement)) proof = true) : Derives T statement := by
  obtain ⟨raw, replayed⟩ := accepted_has_replay (computation hosted) accepted
  exact checkRaw_kernel_sound hosted replayed

end Mettapedia.Languages.VibeITP.Native.ComputedArithmetic
