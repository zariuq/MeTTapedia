import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwarePatternCodec
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Literal matching of canonical scalar data

Encoded declaration names and indices are literal data. Matching them against
themselves introduces no metavariable bindings, and applying bindings leaves
them unchanged. These laws avoid expanding the encoded strings at every
native computation rule.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwarePatternCodec

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match

@[simp] theorem match_encodeNat_self (value : Nat) :
    matchPattern (encodeNat value) (encodeNat value) = [[]] := by
  induction value with
  | zero => simp [encodeNat, matchPattern, matchArgs]
  | succ value ih =>
    simp [encodeNat, matchPattern, matchArgs, mergeBindings, ih]

@[simp] theorem applyBindings_encodeNat (bindings : Bindings) (value : Nat) :
    applyBindings bindings (encodeNat value) = encodeNat value := by
  induction value with
  | zero => simp [encodeNat, applyBindings]
  | succ value ih => simp [encodeNat, applyBindings, ih]

@[simp] theorem applyBindingsScoped_encodeNat (lhs : Pattern) (bindings : Bindings)
    (depth value : Nat) :
    applyBindingsScoped lhs bindings depth (encodeNat value) = encodeNat value := by
  induction value with
  | zero => simp [encodeNat]
  | succ value ih => simp [encodeNat, ih]

@[simp] theorem match_encodeChars_self (value : List Char) :
    matchPattern (encodeChars value) (encodeChars value) = [[]] := by
  induction value with
  | nil => simp [encodeChars, matchPattern, matchArgs]
  | cons character rest ih =>
    simp [encodeChars, matchPattern, matchArgs, mergeBindings, ih]

@[simp] theorem applyBindings_encodeChars (bindings : Bindings) (value : List Char) :
    applyBindings bindings (encodeChars value) = encodeChars value := by
  induction value with
  | nil => simp [encodeChars, applyBindings]
  | cons character rest ih => simp [encodeChars, applyBindings, ih]

@[simp] theorem applyBindingsScoped_encodeChars (lhs : Pattern) (bindings : Bindings)
    (depth : Nat) (value : List Char) :
    applyBindingsScoped lhs bindings depth (encodeChars value) = encodeChars value := by
  induction value with
  | nil => simp [encodeChars]
  | cons character rest ih =>
      simp [encodeChars, applyBindingsScoped_encodeNat, ih]

@[simp] theorem match_encodeString_self (value : String) :
    matchPattern (encodeString value) (encodeString value) = [[]] :=
  match_encodeChars_self value.toList

@[simp] theorem applyBindings_encodeString (bindings : Bindings) (value : String) :
    applyBindings bindings (encodeString value) = encodeString value :=
  applyBindings_encodeChars bindings value.toList

@[simp] theorem applyBindingsScoped_encodeString (lhs : Pattern) (bindings : Bindings)
    (depth : Nat) (value : String) :
    applyBindingsScoped lhs bindings depth (encodeString value) = encodeString value :=
  applyBindingsScoped_encodeChars lhs bindings depth value.toList

@[simp] theorem match_encodeDeclName_self (value : Lean.Name) :
    matchPattern (encodeDeclName value) (encodeDeclName value) = [[]] := by
  induction value with
  | anonymous => simp [encodeDeclName, matchPattern, matchArgs]
  | str pre component ih =>
    simp [encodeDeclName, matchPattern, matchArgs, mergeBindings, ih]
  | num pre index ih =>
    simp [encodeDeclName, matchPattern, matchArgs, mergeBindings, ih]

@[simp] theorem applyBindings_encodeDeclName (bindings : Bindings) (value : Lean.Name) :
    applyBindings bindings (encodeDeclName value) = encodeDeclName value := by
  induction value with
  | anonymous => simp [encodeDeclName, applyBindings]
  | str pre component ih => simp [encodeDeclName, applyBindings, ih]
  | num pre index ih => simp [encodeDeclName, applyBindings, ih]

@[simp] theorem applyBindingsScoped_encodeDeclName (lhs : Pattern) (bindings : Bindings)
    (depth : Nat) (value : Lean.Name) :
    applyBindingsScoped lhs bindings depth (encodeDeclName value) = encodeDeclName value := by
  induction value with
  | anonymous => simp [encodeDeclName]
  | str pre component ih =>
      simp [encodeDeclName, applyBindingsScoped_encodeString, ih]
  | num pre index ih =>
      simp [encodeDeclName, applyBindingsScoped_encodeNat, ih]

/-! Match-correctness is structural in encoded scalar data. Proving these
laws for arbitrary inputs avoids reducing concrete character codepoints
while establishing each computation rule's correctness premise. -/

@[simp] theorem isMatchCorrectAux_encodeNat (value : Nat) :
    isMatchCorrectAux (encodeNat value) = true := by
  induction value with
  | zero => rfl
  | succ value ih =>
    simp only [encodeNat, isMatchCorrectAux, isMatchCorrectListAux, ih, Bool.and_self]

@[simp] theorem isMatchCorrectAux_encodeChars (value : List Char) :
    isMatchCorrectAux (encodeChars value) = true := by
  induction value with
  | nil => rfl
  | cons character rest ih =>
    simp only [encodeChars, isMatchCorrectAux, isMatchCorrectListAux,
      isMatchCorrectAux_encodeNat, ih, Bool.and_self]

@[simp] theorem isMatchCorrectAux_encodeString (value : String) :
    isMatchCorrectAux (encodeString value) = true :=
  isMatchCorrectAux_encodeChars value.toList

@[simp] theorem isMatchCorrectAux_encodeDeclName (value : Lean.Name) :
    isMatchCorrectAux (encodeDeclName value) = true := by
  induction value with
  | anonymous => rfl
  | str pre component ih =>
    simp only [encodeDeclName, isMatchCorrectAux, isMatchCorrectListAux, ih,
      isMatchCorrectAux_encodeString, Bool.and_self]
  | num pre index ih =>
    simp only [encodeDeclName, isMatchCorrectAux, isMatchCorrectListAux, ih,
      isMatchCorrectAux_encodeNat, Bool.and_self]

#print axioms isMatchCorrectAux_encodeNat
#print axioms isMatchCorrectAux_encodeDeclName

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwarePatternCodec
