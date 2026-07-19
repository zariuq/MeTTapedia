import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Basic
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary

/-!
# Erasing cost decorations to pure rho syntax

Cost-accounted rho adds signatures, signed wrappers, and located temporal
purses around the pure communication calculus.  This module defines the
syntax-level erasure of those decorations.  The interpretation of a signature
as a pure rho name is an explicit parameter: choosing a concrete injective
encoding is a separate representation decision.

The erasure exposes an important substitution boundary.  Cost substitution is
capture-avoiding binder elimination.  The operational pure-rho substitution
uses the named-variable behavior of the runtime and therefore agrees directly
on the matched-drop case, while a global de-Bruijn commutation theorem needs a
scoping/elaboration invariant.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

universe u

/-- Interpretation of cost signatures as names in the pure rho carrier. -/
abbrev SignatureNameEncoding (Ground : Type u) := CostSig Ground → Pattern

mutual
  /-- Erase a cost name, delegating only the signature representation. -/
  def CostName.erase {Ground : Type u}
      (signatureName : SignatureNameEncoding Ground) : CostName Ground → Pattern
    | .bvar index => .bvar index
    | .quote term => .apply "NQuote" [term.erase signatureName]
    | .signature signature => signatureName signature

  /-- Erase signed-process structure to the corresponding pure rho process. -/
  def CostProc.erase {Ground : Type u}
      (signatureName : SignatureNameEncoding Ground) : CostProc Ground → Pattern
    | .nil => .collection .hashBag [] none
    | .par left right =>
        .collection .hashBag [left.erase signatureName, right.erase signatureName] none
    | .send channel payload =>
        .apply "POutput" [channel.erase signatureName, payload.erase signatureName]
    | .recv channel body =>
        .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)]

  /-- Forget signed wrappers and purses while retaining the underlying pure
  communication process.  A purse has no computational process after cost
  decorations are forgotten, so it maps to the parallel identity. -/
  def CostTerm.erase {Ground : Type u}
      (signatureName : SignatureNameEncoding Ground) : CostTerm Ground → Pattern
    | .nil => .collection .hashBag [] none
    | .signed process _ => process.erase signatureName
    | .par left right =>
        .collection .hashBag [left.erase signatureName, right.erase signatureName] none
    | .drop name => .apply "PDrop" [name.erase signatureName]
    | .purse _ _ => .collection .hashBag [] none
end

mutual
  /-- Lifting by zero leaves cost names unchanged. -/
  @[simp]
  theorem CostName.lift_zero {Ground : Type u} (cutoff : Nat) :
      ∀ name : CostName Ground, name.lift 0 cutoff = name
    | .bvar index => by simp [CostName.lift]
    | .quote term => rfl
    | .signature signature => rfl

  /-- Lifting by zero leaves cost processes unchanged. -/
  @[simp]
  theorem CostProc.lift_zero {Ground : Type u} (cutoff : Nat) :
      ∀ process : CostProc Ground, process.lift 0 cutoff = process
    | .nil => rfl
    | .par left right => by
        simp [CostProc.lift, CostProc.lift_zero cutoff left,
          CostProc.lift_zero cutoff right]
    | .send channel payload => by
        simp [CostProc.lift, CostName.lift_zero cutoff channel,
          CostTerm.lift_zero cutoff payload]
    | .recv channel body => by
        simp [CostProc.lift, CostName.lift_zero cutoff channel,
          CostTerm.lift_zero (cutoff + 1) body]

  /-- Lifting by zero leaves cost terms unchanged. -/
  @[simp]
  theorem CostTerm.lift_zero {Ground : Type u} (cutoff : Nat) :
      ∀ term : CostTerm Ground, term.lift 0 cutoff = term
    | .nil => rfl
    | .signed process signature => by
        simp [CostTerm.lift, CostProc.lift_zero cutoff process]
    | .par left right => by
        simp [CostTerm.lift, CostTerm.lift_zero cutoff left,
          CostTerm.lift_zero cutoff right]
    | .drop name => by
        simp [CostTerm.lift, CostName.lift_zero cutoff name]
    | .purse surface stack => by
        simp [CostTerm.lift, CostName.lift_zero cutoff surface]
end

mutual
  /-- Pure signature encodings make every erased cost name `hashSet`-free. -/
  theorem CostName.hashSetFree_erase {Ground : Type u}
      {signatureName : SignatureNameEncoding Ground}
      (signaturePure : ∀ signature, HashSetFree (signatureName signature)) :
      ∀ name : CostName Ground, HashSetFree (name.erase signatureName)
    | .bvar _ => by simp [CostName.erase, HashSetFree]
    | .quote term => by
        simp [CostName.erase, HashSetFree, HashSetFreeList,
          CostTerm.hashSetFree_erase signaturePure term]
    | .signature signature => signaturePure signature

  /-- Pure signature encodings make every erased cost process `hashSet`-free. -/
  theorem CostProc.hashSetFree_erase {Ground : Type u}
      {signatureName : SignatureNameEncoding Ground}
      (signaturePure : ∀ signature, HashSetFree (signatureName signature)) :
      ∀ process : CostProc Ground, HashSetFree (process.erase signatureName)
    | .nil => by simp [CostProc.erase, HashSetFree, HashSetFreeList]
    | .par left right => by
        simp [CostProc.erase, HashSetFree, HashSetFreeList,
          CostProc.hashSetFree_erase signaturePure left,
          CostProc.hashSetFree_erase signaturePure right]
    | .send channel payload => by
        simp [CostProc.erase, HashSetFree, HashSetFreeList,
          CostName.hashSetFree_erase signaturePure channel,
          CostTerm.hashSetFree_erase signaturePure payload]
    | .recv channel body => by
        simp [CostProc.erase, HashSetFree, HashSetFreeList,
          CostName.hashSetFree_erase signaturePure channel,
          CostTerm.hashSetFree_erase signaturePure body]

  /-- Pure signature encodings make every erased cost term `hashSet`-free. -/
  theorem CostTerm.hashSetFree_erase {Ground : Type u}
      {signatureName : SignatureNameEncoding Ground}
      (signaturePure : ∀ signature, HashSetFree (signatureName signature)) :
      ∀ term : CostTerm Ground, HashSetFree (term.erase signatureName)
    | .nil => by simp [CostTerm.erase, HashSetFree, HashSetFreeList]
    | .signed process _ => CostProc.hashSetFree_erase signaturePure process
    | .par left right => by
        simp [CostTerm.erase, HashSetFree, HashSetFreeList,
          CostTerm.hashSetFree_erase signaturePure left,
          CostTerm.hashSetFree_erase signaturePure right]
    | .drop name => by
        simp [CostTerm.erase, HashSetFree, HashSetFreeList,
          CostName.hashSetFree_erase signaturePure name]
    | .purse _ _ => by simp [CostTerm.erase, HashSetFree, HashSetFreeList]
end

/-- Erasure commutes with the defining semantic dequotation case whenever the
erased payload is already in semantic normal form. -/
theorem CostTerm.erase_commSubst_bound_drop {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground) (payload : CostTerm Ground)
    (payload_normal :
      semanticNormalizeProc (payload.erase signatureName) = payload.erase signatureName) :
    ((CostTerm.drop (.bvar 0)).commSubst payload).erase signatureName =
      semanticCommSubst
        ((CostTerm.drop (.bvar 0)).erase signatureName)
        (payload.erase signatureName) := by
  simp [CostTerm.commSubst, CostTerm.substitute, CostTerm.erase,
    CostName.erase, semanticCommSubst_collapses_bound_drop, payload_normal]

/-- Positive executable control: the inert payload is dequoted identically by
cost substitution and pure semantic COMM substitution. -/
theorem CostTerm.erase_commSubst_bound_drop_nil {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground) :
    ((CostTerm.drop (.bvar 0)).commSubst (.nil : CostTerm Ground)).erase signatureName =
      semanticCommSubst
        ((CostTerm.drop (.bvar 0)).erase signatureName)
        ((CostTerm.nil : CostTerm Ground).erase signatureName) := by
  apply CostTerm.erase_commSubst_bound_drop
  rfl

/-- Negative boundary: binder-eliminating de-Bruijn substitution decrements a
higher index, whereas the named-variable operational substitution leaves a
different variable identity unchanged.  A general agreement theorem must
therefore carry the elaboration/scoping relation between the presentations. -/
theorem CostTerm.erase_commSubst_higher_index_differs {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground) :
    ((CostTerm.drop (.bvar 1)).commSubst (.nil : CostTerm Ground)).erase signatureName ≠
      semanticCommSubst
        ((CostTerm.drop (.bvar 1)).erase signatureName)
        ((CostTerm.nil : CostTerm Ground).erase signatureName) := by
  simp [CostTerm.commSubst, CostTerm.substitute, CostTerm.erase,
    CostName.erase, semanticCommSubst, semanticSubstProc,
    semanticSubstNameMark, semanticNormalizeName,
    semanticNormalizeProc, semanticNormalizeProcList]

/-- Cost purses are bookkeeping resources rather than pure rho processes. -/
@[simp]
theorem CostTerm.erase_purse {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground)
    (surface : CostName Ground) (stack : CostStack Ground) :
    (CostTerm.purse surface stack).erase signatureName =
      .collection .hashBag [] none :=
  rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
