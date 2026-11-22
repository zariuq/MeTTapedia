import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Basic
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution
import Mathlib.Logic.Encodable.Basic

/-!
# Closed rho codes for complete signature multisets

Signing atoms have an explicit countable encoding. Each atom becomes a closed
output chain; a signature becomes a parallel bag of those chains. Decoding
retains repeated atoms. These are data processes, not minted funding resources.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.SignatureCodec

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open CanonicalTyping
open Canonical CanonicalBag CanonicalStepperCompleteness
open LanguageDefRewriteSystem
open Mettapedia.OSLF.Framework.ConstructorCategory

universe u

def zero : Pattern := .apply "PZero" []

def zeroName : Pattern := .apply "NQuote" [zero]

/-- A number encoded using only closed rho constructors. -/
def numberCode : Nat → Pattern
  | 0 => zero
  | n + 1 => .apply "POutput" [zeroName, numberCode n]

/-- Reject malformed atom codes rather than assigning them a signing atom. -/
def numberRead : Pattern → Option Nat
  | .apply "PZero" [] => some 0
  | .apply "POutput" [.apply "NQuote" [.apply "PZero" []], tail] =>
      (· + 1) <$> numberRead tail
  | _ => none

@[simp]
theorem number_roundtrip (n : Nat) : numberRead (numberCode n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numberCode, numberRead, zeroName, zero, ih]

theorem numberCode_injective : Function.Injective numberCode := by
  intro n k equality
  exact Option.some.inj ((congrArg numberRead equality).trans (number_roundtrip k) |>
    (number_roundtrip n).symm.trans)

theorem number_typed (n : Nat) (bound : List String) :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty bound (numberCode n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .output (.quote .unit) ih

@[simp]
theorem number_safe (n depth : Nat) : binderSafeAt "NQuote" depth (numberCode n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numberCode, zeroName, zero, binderSafeAt, binderSafeListAt, ih]

@[simp]
theorem number_normal (n : Nat) : semanticNormalizeProc (numberCode n) = numberCode n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numberCode, zeroName, zero, semanticNormalizeProc,
      semanticNormalizeName, ih]

@[simp]
theorem number_subst (n k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement (numberCode n) = numberCode n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numberCode, zeroName, zero, semanticSubstProc,
      semanticSubstName, semanticSubstNameMark, semanticNormalizeName,
      semanticNormalizeProc, canonicalize, canonicalizeList, normalizeQuote, ih]

variable {Ground : Type u} [Encodable Ground]

/-- Every atom has a nonunit outer prime, including an atom encoded by zero. -/
def atomCode (atom : Ground) : Pattern :=
  .apply "POutput" [zeroName, numberCode (Encodable.encode atom)]

def atomRead : Pattern → Option Ground
  | .apply "POutput" [.apply "NQuote" [.apply "PZero" []], payload] =>
      match numberRead payload with
      | some number => Encodable.decode number
      | none => none
  | _ => none

@[simp]
theorem atom_roundtrip (atom : Ground) : atomRead (atomCode atom) = some atom := by
  simp [atomRead, atomCode, zeroName, zero, Encodable.encodek]

@[simp]
theorem number_canonical (number : Nat) : canonicalize (numberCode number) = numberCode number := by
  induction number with
  | zero => rfl
  | succ number ih => simp [numberCode, canonicalize, canonicalizeList, zeroName, zero, normalizeQuote, ih]

@[simp]
theorem atom_canonical (atom : Ground) : canonicalize (atomCode atom) = atomCode atom := by
  simp [atomCode, canonicalize, canonicalizeList, zeroName, zero, normalizeQuote]

theorem atom_typed (atom : Ground) (bound : List String) :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty bound (atomCode atom) :=
  .output (.quote .unit) (number_typed _ _)

@[simp]
theorem atom_safe (atom : Ground) (depth : Nat) : binderSafeAt "NQuote" depth (atomCode atom) = true := by
  simp [atomCode, zeroName, zero, binderSafeAt, binderSafeListAt]

@[simp]
theorem atom_normal (atom : Ground) : semanticNormalizeProc (atomCode atom) = atomCode atom := by
  simp [atomCode, zeroName, zero, semanticNormalizeProc, semanticNormalizeName]

@[simp]
theorem atom_subst (atom : Ground) (index : Nat) (replacement : Pattern) :
    semanticSubstProc index replacement (atomCode atom) = atomCode atom := by
  simp [atomCode, zeroName, zero, semanticSubstProc, semanticSubstName,
    semanticSubstNameMark, semanticNormalizeName, semanticNormalizeProc,
    canonicalize, canonicalizeList, normalizeQuote]

theorem atom_prime (atom : Ground) : IsPrime (atomCode atom) := by
  refine ⟨(rhoClosedTermWellSorted_process_iff _).mpr ⟨atom_typed _ [], atom_safe _ 0⟩,
    ?_, ?_, ?_⟩
  · have canonical := canonicalize_isCanonical (atomCode atom)
    rwa [atom_canonical] at canonical
  · simp [atomCode]
  · intro elements
    simp [atomCode]

/-- Encoding does not impose an order on atoms within one commutative signature. -/
noncomputable def rawSignatureCode (signature : CostSig Ground) : Pattern :=
  .collection .hashBag (signature.toList.map atomCode) none

def atomListRead : List Pattern → Option (List Ground)
  | [] => some []
  | code :: rest =>
      match atomRead code with
      | none => none
      | some atom =>
          match atomListRead rest with
          | some atoms => some (atom :: atoms)
          | none => none

def rawSignatureRead : Pattern → Option (CostSig Ground)
  | .collection .hashBag codes none =>
      match atomListRead (Ground := Ground) codes with
      | some atoms => some (↑atoms : Multiset Ground)
      | none => none
  | _ => none

@[simp]
theorem atomList_roundtrip (atoms : List Ground) :
    atomListRead (atoms.map atomCode) = some atoms := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [atomListRead, ih]

@[simp]
theorem raw_signature_roundtrip (signature : CostSig Ground) :
    rawSignatureRead (rawSignatureCode signature) = some signature := by
  simp [rawSignatureCode, rawSignatureRead]

/-- Complete signatures are recovered, not merely their cardinalities. -/
theorem rawSignatureCode_injective : Function.Injective (rawSignatureCode (Ground := Ground)) := by
  intro first second equality
  have read := congrArg (rawSignatureRead (Ground := Ground)) equality
  simpa using read

theorem raw_signature_typed (signature : CostSig Ground) (bound : List String) :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty bound
      (rawSignatureCode signature) := by
  apply ProcWellSorted.parallel
  apply procListWellSorted_iff_forall_mem.mpr
  intro process membership
  obtain ⟨atom, _, rfl⟩ := List.mem_map.mp membership
  exact atom_typed _ _

private theorem safe_mapped_numbers (atoms : List Ground) (depth : Nat) :
    binderSafeListAt "NQuote" depth
      (atoms.map atomCode) = true := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [binderSafeListAt, ih]

@[simp]
theorem raw_signature_safe (signature : CostSig Ground) (depth : Nat) :
    binderSafeAt "NQuote" depth (rawSignatureCode signature) = true := by
  exact safe_mapped_numbers _ _

private theorem normal_mapped_numbers (atoms : List Ground) :
    semanticNormalizeProcList (atoms.map atomCode) = atoms.map atomCode := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [semanticNormalizeProcList, ih]

@[simp]
theorem raw_signature_normal (signature : CostSig Ground) :
    semanticNormalizeProc (rawSignatureCode signature) = rawSignatureCode signature := by
  simp only [rawSignatureCode, semanticNormalizeProc, normal_mapped_numbers]

private theorem subst_mapped_numbers (atoms : List Ground) (k : Nat) (replacement : Pattern) :
    semanticSubstProcList k replacement (atoms.map atomCode) = atoms.map atomCode := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [semanticSubstProcList, ih]

@[simp]
theorem raw_signature_subst (signature : CostSig Ground) (k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement (rawSignatureCode signature) = rawSignatureCode signature := by
  simp only [rawSignatureCode, semanticSubstProc, subst_mapped_numbers]

/-- Counting any individual ground atom after decoding gives its original multiplicity. -/
theorem raw_signature_atom_multiplicity [DecidableEq Ground] (signature : CostSig Ground)
    (atom : Ground) :
    ((rawSignatureRead (rawSignatureCode signature)).map (Multiset.count atom)) =
      some (signature.count atom) := by
  rw [raw_signature_roundtrip]
  rfl

/-- The actual canonical rho payload, including unit and singleton normalization. -/
noncomputable def signatureCode (signature : CostSig Ground) : Pattern :=
  canonicalize (rawSignatureCode signature)

/-- A semantic observation of the actual canonical parallel-prime inventory.
Outside the code image malformed primes contribute no signing atom. -/
def signatureRead (process : Pattern) : CostSig Ground :=
  (bagContents [canonicalize process] : Multiset Pattern).filterMap atomRead

theorem raw_signature_inventory (signature : CostSig Ground) :
    (bagContents [canonicalize (rawSignatureCode signature)] : Multiset Pattern) =
      signature.map atomCode := by
  let atoms := signature.toList.map (atomCode (Ground := Ground))
  have prime : ∀ pattern ∈ atoms, IsPrime pattern := by
    intro pattern membership
    obtain ⟨atom, _, rfl⟩ := List.mem_map.mp membership
    exact atom_prime _
  have inventory := fromProcess_ofList_primes atoms prime
  rw [fromProcess_inventory] at inventory
  change (bagContents [canonicalize (rawSignatureCode signature)] : Multiset Pattern) = _ at inventory
  exact inventory.trans (by
    change (↑(signature.toList.map atomCode) : Multiset Pattern) = signature.map atomCode
    rw [← Multiset.map_coe, Multiset.coe_toList])

@[simp]
theorem signature_roundtrip (signature : CostSig Ground) :
    signatureRead (signatureCode signature) = signature := by
  unfold signatureRead signatureCode
  rw [canonicalize_idempotent, raw_signature_inventory, Multiset.filterMap_map]
  have inverse : atomRead (Ground := Ground) ∘ atomCode = some := by
    funext atom
    exact atom_roundtrip atom
  rw [inverse, Multiset.filterMap_some]

theorem signatureCode_injective : Function.Injective (signatureCode (Ground := Ground)) := by
  intro first second equality
  simpa using congrArg (signatureRead (Ground := Ground)) equality

@[simp]
theorem signature_canonical (signature : CostSig Ground) :
    canonicalize (signatureCode signature) = signatureCode signature :=
  canonicalize_idempotent _

theorem signature_typed (signature : CostSig Ground) (bound : List String) :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty bound (signatureCode signature) :=
  canonicalize_procWellSorted bound (raw_signature_typed signature bound)

@[simp]
theorem signature_safe (signature : CostSig Ground) (depth : Nat) :
    binderSafeAt "NQuote" depth (signatureCode signature) = true :=
  canonicalize_binderSafeAt _ _ (raw_signature_safe signature depth)

theorem signature_shape (signature : CostSig Ground) :
    signatureCode signature = collapseBag (sortPatterns (signature.toList.map atomCode)) := by
  unfold signatureCode rawSignatureCode
  rw [canonicalize_bag]
  have unchanged : (signature.toList.map (atomCode (Ground := Ground))).map canonicalize =
      signature.toList.map atomCode := by
    simp
  rw [unchanged, normalizeBagElements_eq_sort_bagContents]
  rw [bagContents_eq_self]
  · intro pattern member
    obtain ⟨atom, _, rfl⟩ := List.mem_map.mp member
    exact (atom_prime atom).2.2.1
  · intro pattern member elements
    obtain ⟨atom, _, rfl⟩ := List.mem_map.mp member
    exact (atom_prime atom).2.2.2 elements

private theorem normalized_list (processes : List Pattern)
    (stable : ∀ process ∈ processes, semanticNormalizeProc process = process) :
    semanticNormalizeProcList processes = processes := by
  induction processes with
  | nil => rfl
  | cons process rest ih =>
      simp only [semanticNormalizeProcList]
      rw [stable process (by simp), ih (fun p member => stable p (by simp [member]))]

private theorem substituted_list (processes : List Pattern) (index : Nat) (replacement : Pattern)
    (stable : ∀ process ∈ processes, semanticSubstProc index replacement process = process) :
    semanticSubstProcList index replacement processes = processes := by
  induction processes with
  | nil => rfl
  | cons process rest ih =>
      simp only [semanticSubstProcList]
      rw [stable process (by simp), ih (fun p member => stable p (by simp [member]))]

@[simp]
theorem signature_normal (signature : CostSig Ground) :
    semanticNormalizeProc (signatureCode signature) = signatureCode signature := by
  rw [signature_shape]
  have fixed : ∀ process ∈ sortPatterns (signature.toList.map (atomCode (Ground := Ground))),
      semanticNormalizeProc process = process := by
    intro process membership
    obtain ⟨atom, _, rfl⟩ := List.mem_map.mp (sortPatterns_mem_iff.mp membership)
    exact atom_normal atom
  generalize h : sortPatterns (signature.toList.map (atomCode (Ground := Ground))) = processes at fixed ⊢
  cases processes with
  | nil => rfl
  | cons process rest =>
      cases rest with
      | nil => exact fixed process (by simp)
      | cons second rest =>
          simp only [collapseBag, semanticNormalizeProc]
          exact congrArg (fun xs => Pattern.collection .hashBag xs none) (normalized_list _ fixed)

@[simp]
theorem signature_subst (signature : CostSig Ground) (index : Nat) (replacement : Pattern) :
    semanticSubstProc index replacement (signatureCode signature) = signatureCode signature := by
  rw [signature_shape]
  have fixed : ∀ process ∈ sortPatterns (signature.toList.map (atomCode (Ground := Ground))),
      semanticSubstProc index replacement process = process := by
    intro process membership
    obtain ⟨atom, _, rfl⟩ := List.mem_map.mp (sortPatterns_mem_iff.mp membership)
    exact atom_subst atom index replacement
  generalize h : sortPatterns (signature.toList.map (atomCode (Ground := Ground))) = processes at fixed ⊢
  cases processes with
  | nil => rfl
  | cons process rest =>
      cases rest with
      | nil => exact fixed process (by simp)
      | cons second rest =>
          simp only [collapseBag, semanticSubstProc]
          exact congrArg (fun xs => Pattern.collection .hashBag xs none) (substituted_list _ _ _ fixed)

theorem signature_atom_multiplicity [DecidableEq Ground] (signature : CostSig Ground) (atom : Ground) :
    (signatureRead (signatureCode signature)).count atom = signature.count atom := by
  rw [signature_roundtrip]

/-- Even an atom whose numerical encoding is zero remains a real prime. -/
theorem zero_atom_not_empty : signatureCode ({0} : CostSig Nat) ≠ signatureCode (0 : CostSig Nat) := by
  intro equality
  have same := signatureCode_injective equality
  simp at same

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.SignatureCodec
