import Mettapedia.Languages.Agda.SourceEvidence.ProofRoundtrip
import Mettapedia.Languages.Agda.SourceEvidence.NumeralCode

/-!
Natural-number serialization and constructive recovery of actual source
proofs. Recovery searches a decidable code predicate and requires an existing
inhabitation proof to justify termination. It is neither a decision procedure
for derivability nor a normalization theorem. The source proof supplied as a
Prop witness is not eliminated into Type and is not an external checked trace.
-/

namespace Mettapedia.Languages.Agda.SourceEvidence.Codec
open Mettapedia.Languages.Agda.StaticSpecification

instance packedEncodable : Encodable Packed :=
  Encodable.ofLeftInjection encodePacked decode decode_encodePacked

instance evidenceEncodable (j : Judgment) : Encodable (Evidence j) :=
  Encodable.ofLeftInjection (fun d => encodePacked ⟨j, d⟩)
    (decodeAt j) (decodeAt_encodePacked j)

/-- Source-indexed evidence is serialized without identifying proof histories. -/
def encodeNat (j : Judgment) (d : Evidence j) : Nat := Encodable.encode d

def decodeNat (j : Judgment) (code : Nat) : Option (Evidence j) := Encodable.decode code

@[simp] theorem decodeNat_encodeNat (j : Judgment) (d : Evidence j) :
    decodeNat j (encodeNat j d) = some d := Encodable.encodek d

theorem encodeNat_injective (j : Judgment) : Function.Injective (encodeNat j) :=
  Encodable.encode_injective

structure Recovered (j : Judgment) where
  code : Nat
  derivation : Evidence j
  checked : decodeNat j code = some derivation

/-- The search is ordinary well-founded natural-number search, justified by
completeness of this actual decoder for the inhabited source judgment. -/
def recover (j : Judgment) (inhabited : Nonempty (Evidence j)) : Recovered j := by
  have succeeds : ∃ code, (decodeNat j code).isSome := by
    obtain ⟨d⟩ := inhabited
    exact ⟨encodeNat j d, by simp only [decodeNat_encodeNat, Option.isSome_some]⟩
  let code := Nat.find succeeds
  have good : (decodeNat j code).isSome := Nat.find_spec succeeds
  generalize checked : decodeNat j code = result at good
  cases result with
  | none => contradiction
  | some d => exact ⟨code, d, checked⟩

def recoverContext {Γ : RawContext n} (h : Nonempty (FormCtx Γ)) : FormCtx Γ :=
  (recover (.context Γ) h).derivation

def recoverFormation {Γ : RawContext n} {a : Ty n}
    (h : Nonempty (FormTy Γ a)) : FormTy Γ a :=
  (recover (.formation Γ a) h).derivation

def recoverTyping {Γ : RawContext n} {t : Term n} {a : Ty n}
    (h : Nonempty (Typing Γ t a)) : Typing Γ t a :=
  (recover (.typing Γ t a) h).derivation

def recoverTypeEquality {Γ : RawContext n} {a b : Ty n}
    (h : Nonempty (TypeEq Γ a b)) : TypeEq Γ a b :=
  (recover (.typeEquality Γ a b) h).derivation

def recoverTermEquality {Γ : RawContext n} {t u : Term n} {a : Ty n}
    (h : Nonempty (TermEq Γ t u a)) : TermEq Γ t u a :=
  (recover (.termEquality Γ t u a) h).derivation

/-- Proof irrelevance makes the search independent of the inhabitation receipt;
this says nothing about uniqueness of the retained source derivations. -/
theorem recover_receipt_independent (j : Judgment)
    (left right : Nonempty (Evidence j)) : recover j left = recover j right := rfl

end Mettapedia.Languages.Agda.SourceEvidence.Codec
