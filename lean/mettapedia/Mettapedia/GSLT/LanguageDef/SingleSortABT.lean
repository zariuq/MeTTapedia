import Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
import Mettapedia.GSLT.LanguageDef.SortedABTSubstitutionCongruence
import Mathlib.Tactic

/-!
# Reusing sorted simultaneous substitution on the one-axis ABT

The existing one-axis and single-sort carriers are isomorphic. This module
constructs that isomorphism, preserving every field's binder count, and uses
it to reuse the existing sorted renaming and substitution implementation.
No third term carrier, evaluator, or native refinement claim is introduced.

Application permits reordered, repeated, or compound arguments. Scope checking
is independent of invertibility: a legal application need not have a unique
inverse matching problem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

namespace SingleSort


variable {Head : Type}

mutual

def encode : Term Head → SortedSignatureIndexedABT.Term Unit Head
  | .idx i => .idx () i
  | .node h fs => .node h (encodeFields fs)

def encodeFields : Fields Head → SortedSignatureIndexedABT.Fields Unit Head
  | .nil => .nil
  | .cons d t rest => .cons (List.replicate d ()) (encode t) (encodeFields rest)

end

mutual

def decode : SortedSignatureIndexedABT.Term Unit Head → Term Head
  | .idx _ i => .idx i
  | .node h fs => .node h (decodeFields fs)

def decodeFields : SortedSignatureIndexedABT.Fields Unit Head → Fields Head
  | .nil => .nil
  | .cons binders t rest => .cons binders.length (decode t) (decodeFields rest)

end

mutual

@[simp] theorem decode_encode (t : Term Head) : decode (encode t) = t := by
  cases t with
  | idx i => rfl
  | node h fs => simp [encode, decode, decode_encodeFields fs]

@[simp] theorem decode_encodeFields (fs : Fields Head) : decodeFields (encodeFields fs) = fs := by
  cases fs with
  | nil => rfl
  | cons d t rest => simp [encodeFields, decodeFields, decode_encode t, decode_encodeFields rest]

end

theorem unit_binders (binders : List Unit) : List.replicate binders.length () = binders := by
  exact (List.eq_replicate_of_mem (fun _ _ => Subsingleton.elim _ _)).symm

mutual

@[simp] theorem encode_decode (t : SortedSignatureIndexedABT.Term Unit Head) : encode (decode t) = t := by
  cases t with
  | idx u i => cases u; rfl
  | node h fs => simp [decode, encode, encode_decodeFields fs]

@[simp] theorem encode_decodeFields (fs : SortedSignatureIndexedABT.Fields Unit Head) : encodeFields (decodeFields fs) = fs := by
  cases fs with
  | nil => rfl
  | cons bs t rest => simp [decodeFields, encodeFields, encode_decode t,
      encode_decodeFields rest, unit_binders]

end

theorem encode_injective : Function.Injective (encode : Term Head → SortedSignatureIndexedABT.Term Unit Head) :=
  Function.LeftInverse.injective decode_encode

theorem enter_unit (n d : ℕ) :
    SortedSignatureIndexedABT.Term.enter (fun _ : Unit => n) (List.replicate d ()) = fun _ => n + d := by
  funext u
  cases u
  simp [SortedSignatureIndexedABT.Term.enter, SortedSignatureIndexedABT.Term.binderCount]

mutual

@[simp] theorem supported_encode (n : ℕ) (t : Term Head) :
    SortedSignatureIndexedABT.Term.supportedAt (fun _ : Unit => n) (encode t) = Term.supportedAt n t := by
  cases t with
  | idx i => rfl
  | node h fs => exact supported_encodeFields n fs

@[simp] theorem supported_encodeFields (n : ℕ) (fs : Fields Head) :
    SortedSignatureIndexedABT.Term.Fields.supportedAt (fun _ : Unit => n) (encodeFields fs) =
      Term.Fields.supportedAt n fs := by
  cases fs with
  | nil => rfl
  | cons d t rest =>
      simp only [encodeFields, SortedSignatureIndexedABT.Term.Fields.supportedAt, Term.Fields.supportedAt, enter_unit]
      rw [supported_encode (n + d) t, supported_encodeFields n rest]

end

end SingleSort

namespace Term

open SingleSort

variable {Head : Type}

/-- General renaming, including permutations and contraction, through the
existing sorted implementation and the proved carrier isomorphism. -/
def renameMany (ρ : ℕ → ℕ) (t : Term Head) : Term Head :=
  decode (SortedSignatureIndexedABT.Term.parallelRename (fun _ : Unit => ρ) (encode t))

/-- Capture-avoiding simultaneous substitution, using the existing sorted
operation. Inserted terms are weakened beneath the field's binders. -/
def substituteMany (σ : ℕ → Term Head) (t : Term Head) : Term Head :=
  decode (SortedSignatureIndexedABT.Term.parallelSubstitute (fun _ : Unit => fun i => encode (σ i)) (encode t))

@[simp] theorem renameMany_idx (ρ : ℕ → ℕ) (i : ℕ) :
    renameMany ρ (.idx i : Term Head) = .idx (ρ i) := rfl

@[simp] theorem substituteMany_idx (σ : ℕ → Term Head) (i : ℕ) :
    substituteMany σ (.idx i) = σ i := decode_encode _

@[simp] theorem encode_renameMany (ρ : ℕ → ℕ) (t : Term Head) :
    encode (renameMany ρ t) = SortedSignatureIndexedABT.Term.parallelRename (fun _ : Unit => ρ) (encode t) := by
  simp [renameMany]

@[simp] theorem encode_substituteMany (σ : ℕ → Term Head) (t : Term Head) :
    encode (substituteMany σ t) =
      SortedSignatureIndexedABT.Term.parallelSubstitute (fun _ : Unit => fun i => encode (σ i)) (encode t) := by
  simp [substituteMany]

@[simp] theorem renameMany_id (t : Term Head) : renameMany id t = t := by
  apply encode_injective
  rw [encode_renameMany]
  exact SortedSignatureIndexedABT.Term.parallelRename_id (encode t)

theorem renameMany_comp (ρ ξ : ℕ → ℕ) (t : Term Head) :
    renameMany ρ (renameMany ξ t) = renameMany (fun i => ρ (ξ i)) t := by
  apply encode_injective
  simp only [encode_renameMany, SortedSignatureIndexedABT.Term.parallelRename_comp]

theorem renameMany_leftInverse (ρ ξ : ℕ → ℕ) (inverse : Function.LeftInverse ξ ρ) :
    Function.LeftInverse (renameMany ξ : Term Head → Term Head) (renameMany ρ) := by
  intro t
  rw [renameMany_comp]
  have same : (fun i => ξ (ρ i)) = id := funext inverse
  rw [same, renameMany_id]

@[simp] theorem substituteMany_ids (t : Term Head) : substituteMany Term.idx t = t := by
  apply encode_injective
  simpa only [encode_substituteMany, SingleSort.encode] using SortedSignatureIndexedABT.Term.parallelSubstitute_ids (encode t)

theorem substituteMany_comp (τ σ : ℕ → Term Head) (t : Term Head) :
    substituteMany τ (substituteMany σ t) =
      substituteMany (fun i => substituteMany τ (σ i)) t := by
  apply encode_injective
  simp only [encode_substituteMany, SortedSignatureIndexedABT.Term.parallelSubstitute_comp]

theorem substituteMany_renaming (ρ : ℕ → ℕ) (t : Term Head) :
    substituteMany (fun i => .idx (ρ i)) t = renameMany ρ t := by
  apply encode_injective
  simpa only [encode_substituteMany, encode_renameMany, SingleSort.encode] using
    SortedSignatureIndexedABT.Term.parallelSubstitute_renaming (fun _ : Unit => ρ) (encode t)

theorem renameMany_substitute (ρ : ℕ → ℕ) (σ : ℕ → Term Head) (t : Term Head) :
    renameMany ρ (substituteMany σ t) =
      substituteMany (fun i => renameMany ρ (σ i)) t := by
  apply encode_injective
  simp only [encode_substituteMany, encode_renameMany, SortedSignatureIndexedABT.Term.parallelRename_substitute]

theorem substituteMany_rename (σ : ℕ → Term Head) (ρ : ℕ → ℕ) (t : Term Head) :
    substituteMany σ (renameMany ρ t) = substituteMany (fun i => σ (ρ i)) t := by
  apply encode_injective
  simp only [encode_substituteMany, encode_renameMany, SortedSignatureIndexedABT.Term.parallelSubstitute_rename]

theorem substituteMany_supported {source target : ℕ} {σ : ℕ → Term Head}
    (replacements : ∀ i < source, supportedAt target (σ i) = true)
    (t : Term Head) (wellScoped : supportedAt source t = true) :
    supportedAt target (substituteMany σ t) = true := by
  rw [← supported_encode target, encode_substituteMany]
  apply SortedSignatureIndexedABT.Term.supportedAt_parallelSubstitute
  · intro u i hi
    exact (supported_encode target (σ i)).trans (replacements i hi)
  · simpa using wellScoped

theorem substituteMany_congr_scoped {depth : ℕ} {σ τ : ℕ → Term Head}
    (agree : ∀ i < depth, σ i = τ i) (t : Term Head)
    (wellScoped : supportedAt depth t = true) : substituteMany σ t = substituteMany τ t := by
  apply encode_injective
  simp only [encode_substituteMany]
  apply SortedSignatureIndexedABT.Term.parallelSubstitute_congr_scoped (depth := fun _ => depth)
  · intro sort index available
    change encode (σ index) = encode (τ index)
    rw [agree index available]
  · simpa using wellScoped

theorem renameMany_supported {source target : ℕ} {ρ : ℕ → ℕ}
    (bounded : ∀ i < source, ρ i < target) (t : Term Head)
    (wellScoped : supportedAt source t = true) : supportedAt target (renameMany ρ t) = true := by
  rw [← supported_encode target, encode_renameMany]
  apply SortedSignatureIndexedABT.Term.supportedAt_parallelRename
  · intro sort index available
    exact bounded index available
  · simpa using wellScoped

end Term
end Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
