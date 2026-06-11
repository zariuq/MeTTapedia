import Mathlib.Algebra.Order.Quantale
import Mettapedia.Algebra.QuantaleWeakness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoOpening
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution
import Mettapedia.Languages.MeTTa.HE.ExecutableBoundary

/-!
# Rhometta Reduction Layer

This file adds the smallest Lean semantics layer needed to talk about
Rhometta's deferred MeTTa-at-COMM behavior without forking the rho reducer.

The core design is:

- reuse the ordinary rho reduction relation as a base case
- add one explicit `rho:eval-payload` COMM rule
- quantify that rule over certified HE evaluation results
- expose reachability lemmas showing that every certified HE result induces a
  corresponding Rhometta branch

This makes branch-dropping inexpressible at the semantic rule level.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhometaReduction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Reduction
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore

/-- Structural unary encoding for naturals inside rho-side inert syntax. -/
def natToPattern : Nat → Pattern
  | 0 => .apply "NatZ" []
  | n + 1 => .apply "NatS" [natToPattern n]

/-- Partial inverse of `natToPattern`. -/
def patternToNat? : Pattern → Option Nat
  | .apply "NatZ" [] => some 0
  | .apply "NatS" [p] => (patternToNat? p).map Nat.succ
  | _ => none

theorem patternToNat_natToPattern (n : Nat) :
    patternToNat? (natToPattern n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natToPattern, patternToNat?, ih]

/-- Structural embedding of HE grounded values into inert rho-side syntax. -/
def groundedValueToPattern : GroundedValue → Pattern
  | .int (.ofNat n) => .apply "HEIntOfNat" [natToPattern n]
  | .int (.negSucc n) => .apply "HEIntNegSucc" [natToPattern n]
  | .string s => .apply "HEString" [.fvar s]
  | .bool true => .apply "HEBoolTrue" []
  | .bool false => .apply "HEBoolFalse" []
  | .custom ty data => .apply "HECustom" [.fvar ty, .fvar data]

/-- Structural embedding of HE atoms into inert rho-side syntax. -/
def atomToPattern : Atom → Pattern
  | .symbol s => .apply "HESymbol" [.fvar s]
  | .var v => .apply "HEVar" [.fvar v]
  | .grounded g => groundedValueToPattern g
  | .expression es => .apply "HEExpr" (es.map atomToPattern)

/-- Partial inverse of the grounded-value embedding. -/
def patternToGroundedValue? : Pattern → Option GroundedValue
  | .apply "HEIntOfNat" [p] =>
      (patternToNat? p).map (fun n => .int (.ofNat n))
  | .apply "HEIntNegSucc" [p] =>
      (patternToNat? p).map (fun n => .int (.negSucc n))
  | .apply "HEString" [.fvar s] => some (.string s)
  | .apply "HEBoolTrue" [] => some (.bool true)
  | .apply "HEBoolFalse" [] => some (.bool false)
  | .apply "HECustom" [.fvar ty, .fvar data] => some (.custom ty data)
  | _ => none

mutual

/-- Partial inverse of `atomToPattern` for the Rhometta inert embedding. -/
def patternToAtom? : Pattern → Option Atom
  | .apply "HESymbol" [.fvar s] => some (.symbol s)
  | .apply "HEVar" [.fvar v] => some (.var v)
  | p@(.apply "HEIntOfNat" _) => patternToGroundedValue? p |>.map .grounded
  | p@(.apply "HEIntNegSucc" _) => patternToGroundedValue? p |>.map .grounded
  | p@(.apply "HEString" _) => patternToGroundedValue? p |>.map .grounded
  | p@(.apply "HEBoolTrue" _) => patternToGroundedValue? p |>.map .grounded
  | p@(.apply "HEBoolFalse" _) => patternToGroundedValue? p |>.map .grounded
  | p@(.apply "HECustom" _) => patternToGroundedValue? p |>.map .grounded
  | .apply "HEExpr" ps => (patternToAtoms? ps).map .expression
  | _ => none

/-- Partial inverse on lists, aligned with `List.map atomToPattern`. -/
def patternToAtoms? : List Pattern → Option (List Atom)
  | [] => some []
  | p :: ps => do
      let a <- patternToAtom? p
      let as <- patternToAtoms? ps
      pure (a :: as)

end

theorem patternToGroundedValue_groundedValueToPattern (g : GroundedValue) :
    patternToGroundedValue? (groundedValueToPattern g) = some g := by
  cases g with
  | int i =>
      cases i using Int.rec with
      | ofNat n =>
          simp [groundedValueToPattern, patternToGroundedValue?,
            patternToNat_natToPattern]
      | negSucc n =>
          simp [groundedValueToPattern, patternToGroundedValue?,
            patternToNat_natToPattern]
  | string s =>
      simp [groundedValueToPattern, patternToGroundedValue?]
  | bool b =>
      cases b <;> simp [groundedValueToPattern, patternToGroundedValue?]
  | custom ty data =>
      simp [groundedValueToPattern, patternToGroundedValue?]

theorem natToPattern_injective :
    Function.Injective natToPattern := by
  intro n m h
  have hnat := congrArg patternToNat? h
  simpa [patternToNat_natToPattern] using hnat

theorem groundedValueToPattern_injective :
    Function.Injective groundedValueToPattern := by
  intro g h hpat
  have hground := congrArg patternToGroundedValue? hpat
  simpa [patternToGroundedValue_groundedValueToPattern] using hground

/-- Internal deferred-payload marker used by Rhometta sends. -/
def deferredPayload (payload : Atom) : Pattern :=
  .apply "rho:eval-payload" [.apply "quote" [atomToPattern payload]]

/-- Wrapped non-rho value carried back through ordinary rho substitution. -/
def wrappedValue (value : Atom) : Pattern :=
  .apply "rho:val" [atomToPattern value]

mutual

private theorem patternToAtom_atomToPattern :
    ∀ a : Atom, patternToAtom? (atomToPattern a) = some a
  | .symbol s => by
      simp [atomToPattern, patternToAtom?]
  | .var v => by
      simp [atomToPattern, patternToAtom?]
  | .grounded g => by
      cases g with
      | int i =>
          cases i using Int.rec with
          | ofNat n =>
              simp [atomToPattern, groundedValueToPattern, patternToAtom?,
                patternToGroundedValue?, patternToNat_natToPattern]
          | negSucc n =>
              simp [atomToPattern, groundedValueToPattern, patternToAtom?,
                patternToGroundedValue?, patternToNat_natToPattern]
      | string s =>
          simp [atomToPattern, groundedValueToPattern, patternToAtom?,
            patternToGroundedValue?]
      | bool b =>
          cases b <;> simp [atomToPattern, groundedValueToPattern, patternToAtom?,
            patternToGroundedValue?]
      | custom ty data =>
          simp [atomToPattern, groundedValueToPattern, patternToAtom?,
            patternToGroundedValue?]
  | .expression es => by
      simpa [atomToPattern, patternToAtom?] using
        patternToAtoms_map_atomToPattern es
termination_by a => sizeOf a

private theorem patternToAtoms_map_atomToPattern :
    ∀ xs : List Atom, patternToAtoms? (xs.map atomToPattern) = some xs
  | [] => by
      simp [patternToAtoms?]
  | x :: xs => by
      simp [patternToAtoms?, patternToAtom_atomToPattern x,
        patternToAtoms_map_atomToPattern xs]
termination_by xs => sizeOf xs

end

theorem atomToPattern_injective :
    Function.Injective atomToPattern := by
  intro a b h
  have hdecoded := congrArg patternToAtom? h
  simpa [patternToAtom_atomToPattern a, patternToAtom_atomToPattern b] using hdecoded

theorem wrappedValue_injective :
    Function.Injective (fun a : Atom => wrappedValue a) := by
  intro a b h
  have hargs : [atomToPattern a] = [atomToPattern b] := by
    injection h with hargs
  have hatom : atomToPattern a = atomToPattern b := List.cons.inj hargs |>.1
  exact atomToPattern_injective hatom

theorem semanticNormalizeProc_wrappedValue (value : Atom) :
    semanticNormalizeProc (wrappedValue value) = wrappedValue value := by
  simp [wrappedValue, semanticNormalizeProc]

theorem semanticNormalizeProc_deferredPayload (payload : Atom) :
    semanticNormalizeProc (deferredPayload payload) = deferredPayload payload := by
  simp [deferredPayload, semanticNormalizeProc]

mutual

/-- Collapse the administrative SC wrappers that can surround inert Rhometta/HE
payload shells: quote-drop representatives and singleton/zero parallel bags. -/
private def stripSCWrappers : Pattern → Pattern
  | .apply "NQuote" [.apply "PDrop" [n]] =>
      stripSCWrappers n
  | .apply f args =>
      .apply f (stripSCWrappersList args)
  | .lambda nm body =>
      .lambda nm (stripSCWrappers body)
  | .multiLambda n nms body =>
      .multiLambda n nms (stripSCWrappers body)
  | .subst body repl =>
      .subst (stripSCWrappers body) (stripSCWrappers repl)
  | .collection .hashBag elems none =>
      let elems' :=
        (stripSCWrappersList elems).filter (fun e => e ≠ .apply "PZero" [])
      match elems' with
      | [e] => e
      | _ => .collection .hashBag elems' none
  | .collection .hashSet elems none =>
      let elems' :=
        (stripSCWrappersList elems).filter (fun e => e ≠ .apply "PZero" [])
      match elems' with
      | [e] => e
      | _ => .collection .hashSet elems' none
  | .collection ct elems g =>
      .collection ct (stripSCWrappersList elems) g
  | p => p

/-- List recursion for `stripSCWrappers`. -/
private def stripSCWrappersList : List Pattern → List Pattern
  | [] => []
  | p :: ps => stripSCWrappers p :: stripSCWrappersList ps

end

private theorem stripSCWrappers_natToPattern :
    ∀ n : Nat, stripSCWrappers (natToPattern n) = natToPattern n
  | 0 => by
      simp [natToPattern, stripSCWrappers, stripSCWrappersList]
  | n + 1 => by
      simp [natToPattern, stripSCWrappers, stripSCWrappersList,
        stripSCWrappers_natToPattern n]

private theorem stripSCWrappersList_eq_map (elems : List Pattern) :
    stripSCWrappersList elems = elems.map stripSCWrappers := by
  induction elems with
  | nil =>
      rfl
  | cons p ps ih =>
      simp [stripSCWrappersList, ih]

mutual

private theorem stripSCWrappers_atomToPattern :
    ∀ a : Atom, stripSCWrappers (atomToPattern a) = atomToPattern a
  | .symbol s => by
      simp [atomToPattern, stripSCWrappers, stripSCWrappersList]
  | .var v => by
      simp [atomToPattern, stripSCWrappers, stripSCWrappersList]
  | .grounded g => by
      cases g with
      | int i =>
          cases i using Int.rec with
          | ofNat n =>
              simp [atomToPattern, groundedValueToPattern,
                stripSCWrappers, stripSCWrappersList,
                stripSCWrappers_natToPattern]
          | negSucc n =>
              simp [atomToPattern, groundedValueToPattern,
                stripSCWrappers, stripSCWrappersList,
                stripSCWrappers_natToPattern]
      | string s =>
          simp [atomToPattern, groundedValueToPattern,
            stripSCWrappers, stripSCWrappersList]
      | bool b =>
          cases b <;> simp [atomToPattern, groundedValueToPattern,
            stripSCWrappers, stripSCWrappersList]
      | custom ty data =>
          simp [atomToPattern, groundedValueToPattern,
            stripSCWrappers, stripSCWrappersList]
  | .expression es => by
      simpa [atomToPattern, stripSCWrappers, stripSCWrappersList] using
        stripSCWrappersList_atomToPatterns es
termination_by a => sizeOf a

private theorem stripSCWrappersList_atomToPatterns :
    ∀ xs : List Atom,
      stripSCWrappersList (xs.map atomToPattern) = xs.map atomToPattern
  | [] => by
      simp [stripSCWrappersList]
  | x :: xs => by
      simp [stripSCWrappersList, stripSCWrappers_atomToPattern x,
        stripSCWrappersList_atomToPatterns xs]
termination_by xs => sizeOf xs

end

private theorem stripSCWrappers_deferredPayload (payload : Atom) :
    stripSCWrappers (deferredPayload payload) = deferredPayload payload := by
  simp [deferredPayload, stripSCWrappers, stripSCWrappersList,
    stripSCWrappers_atomToPattern]

private theorem stripSCWrappers_wrappedValue (value : Atom) :
    stripSCWrappers (wrappedValue value) = wrappedValue value := by
  simp [wrappedValue, stripSCWrappers, stripSCWrappersList,
    stripSCWrappers_atomToPattern]

/-- SC-aware atom decoder candidate: first collapse administrative wrappers,
then decode the inert HE embedding. -/
private def scDecodeAtom? (p : Pattern) : Option Atom :=
  patternToAtom? (stripSCWrappers p)

/-- The nonzero stripped elements of a parallel bag/set shell. -/
private def strippedNonZeroElems (elems : List Pattern) : List Pattern :=
  (stripSCWrappersList elems).filter (fun e => e ≠ .apply "PZero" [])

/-- SC-aware deferred-payload decoder candidate: collapse administrative
wrappers, then read the exact Rhometta eval marker. -/
private def scDecodeDeferredPayload? (p : Pattern) : Option Atom :=
  match stripSCWrappers p with
  | .apply "rho:eval-payload" [.apply "quote" [q]] => patternToAtom? q
  | _ => none

private theorem strippedNonZeroElems_perm
    {elems₁ elems₂ : List Pattern} (hperm : elems₁.Perm elems₂) :
    (strippedNonZeroElems elems₁).Perm (strippedNonZeroElems elems₂) := by
  unfold strippedNonZeroElems
  simpa [stripSCWrappersList_eq_map] using
    (List.Perm.filter (p := fun e => e ≠ .apply "PZero" [])
      (hperm.map stripSCWrappers))

private theorem scDecodeAtom_atomToPattern (a : Atom) :
    scDecodeAtom? (atomToPattern a) = some a := by
  simp [scDecodeAtom?, stripSCWrappers_atomToPattern,
    patternToAtom_atomToPattern]

private theorem scDecodeDeferredPayload_deferredPayload (payload : Atom) :
    scDecodeDeferredPayload? (deferredPayload payload) = some payload := by
  rw [scDecodeDeferredPayload?, stripSCWrappers_deferredPayload]
  simp [deferredPayload, patternToAtom_atomToPattern]

private theorem scDecodeDeferredPayload_quoteDrop (payload : Atom) :
    scDecodeDeferredPayload?
      (.apply "NQuote" [.apply "PDrop" [deferredPayload payload]]) =
        some payload := by
  simp [scDecodeDeferredPayload?, stripSCWrappers]
  exact scDecodeDeferredPayload_deferredPayload payload

private theorem scDecodeDeferredPayload_singleton (payload : Atom) :
    scDecodeDeferredPayload?
      (.collection .hashBag [deferredPayload payload] none) =
        some payload := by
  simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList]
  simpa [deferredPayload] using scDecodeAtom_atomToPattern payload

private theorem scDecodeDeferredPayload_zero_left (payload : Atom) :
    scDecodeDeferredPayload?
      (.collection .hashBag [.apply "PZero" [], deferredPayload payload] none) =
        some payload := by
  simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList]
  simpa [deferredPayload] using scDecodeAtom_atomToPattern payload

private theorem scDecodeDeferredPayload_zero_right (payload : Atom) :
    scDecodeDeferredPayload?
      (.collection .hashBag [deferredPayload payload, .apply "PZero" []] none) =
        some payload := by
  simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList]
  simpa [deferredPayload] using scDecodeAtom_atomToPattern payload

private theorem scDecodeDeferredPayload_hashBag_of_strippedNonZeroElems
    {elems : List Pattern} {payload : Atom}
    (h : strippedNonZeroElems elems = [deferredPayload payload]) :
    scDecodeDeferredPayload? (.collection .hashBag elems none) = some payload := by
  unfold strippedNonZeroElems at h
  have h' :
      List.filter (fun e => !decide (e = .apply "PZero" []))
        (stripSCWrappersList elems) = [deferredPayload payload] := by
    simpa using h
  unfold scDecodeDeferredPayload?
  simp [stripSCWrappers]
  rw [h']
  simp [deferredPayload, patternToAtom_atomToPattern]

private theorem scDecodeDeferredPayload_hashSet_of_strippedNonZeroElems
    {elems : List Pattern} {payload : Atom}
    (h : strippedNonZeroElems elems = [deferredPayload payload]) :
    scDecodeDeferredPayload? (.collection .hashSet elems none) = some payload := by
  unfold strippedNonZeroElems at h
  have h' :
      List.filter (fun e => !decide (e = .apply "PZero" []))
        (stripSCWrappersList elems) = [deferredPayload payload] := by
    simpa using h
  unfold scDecodeDeferredPayload?
  simp [stripSCWrappers]
  rw [h']
  simp [deferredPayload, patternToAtom_atomToPattern]

theorem ioCount_natToPattern_zero (n : Nat) :
    ioCount (natToPattern n) = 0 := by
  induction n with
  | zero =>
      simp [natToPattern, ioCount]
  | succ n ih =>
      simp [natToPattern, ioCount, ih]

mutual

private theorem ioCount_atomToPattern_zero :
    ∀ a : Atom, ioCount (atomToPattern a) = 0
  | .symbol s => by
      simp [atomToPattern, ioCount]
  | .var v => by
      simp [atomToPattern, ioCount]
  | .grounded g => by
      cases g with
      | int i =>
          cases i using Int.rec with
          | ofNat n =>
              simpa [atomToPattern, groundedValueToPattern, ioCount] using
                ioCount_natToPattern_zero n
          | negSucc n =>
              simpa [atomToPattern, groundedValueToPattern, ioCount] using
                ioCount_natToPattern_zero n
      | string s =>
          simp [atomToPattern, groundedValueToPattern, ioCount]
      | bool b =>
          cases b <;> simp [atomToPattern, groundedValueToPattern, ioCount]
      | custom ty data =>
          simp [atomToPattern, groundedValueToPattern, ioCount]
  | .expression es => by
      simpa [atomToPattern, ioCount] using
        ioCount_atomPatterns_zero es
termination_by a => sizeOf a

private theorem ioCount_atomPatterns_zero :
    ∀ xs : List Atom, (xs.map atomToPattern |>.map ioCount).sum = 0
  | [] => by
      simp
  | x :: xs => by
      simp [ioCount_atomToPattern_zero x]
      simpa [Function.comp] using ioCount_atomPatterns_zero xs
termination_by xs => sizeOf xs

end

theorem ioCount_wrappedValue_zero (value : Atom) :
    ioCount (wrappedValue value) = 0 := by
  simpa [wrappedValue, ioCount] using ioCount_atomToPattern_zero value

theorem ioCount_deferredPayload_zero (payload : Atom) :
    ioCount (deferredPayload payload) = 0 := by
  simpa [deferredPayload, ioCount] using ioCount_atomToPattern_zero payload

/-- A certified top-level HE result for a deferred Rhometta payload.

Bindings are existential here because the current Rhometta runtime surface
returns top-level atoms after the HE evaluator drops bindings at the edge. -/
def CertifiedPayloadResult
    (space : Space) (dispatch : GroundedDispatch)
    (payload value : Atom) : Prop :=
  ∃ b, EvalAtomCertified
    space dispatch payload Atom.undefinedType Bindings.empty (value, b)

/-- Eval-at-COMM fires only on canonical shells, matching the runtime's
normalize-then-fire discipline while keeping structural-congruence wandering
available around the step itself. -/
def EvalCommCanonicalShell
    (body : Pattern) (payload : Atom) : Prop :=
  semanticNormalizeProc body = body ∧
    strictCoreCommBody body = true ∧
    semanticNormalizeProc (deferredPayload payload) = deferredPayload payload

theorem evalCommCanonicalShell_dropBody
    {payload : Atom} :
    EvalCommCanonicalShell (.apply "PDrop" [.bvar 0]) payload := by
  refine ⟨?_, ?_, semanticNormalizeProc_deferredPayload payload⟩
  · simp [semanticNormalizeProc, semanticNormalizeName]
  · native_decide

/-- Output payloads that are structurally congruent to a deferred Rhometta
payload must not take the ordinary core COMM route. This closes SC shells such
as singleton-bag wrappers around `rho:eval-payload`. -/
def DeferredPayloadLike (q : Pattern) : Prop :=
  ∃ payload, StructuralCongruence q (deferredPayload payload)

theorem deferredPayloadLike_singleton_shell (payload : Atom) :
    DeferredPayloadLike (.collection .hashBag [deferredPayload payload] none) := by
  refine ⟨payload, ?_⟩
  simpa using StructuralCongruence.par_singleton (deferredPayload payload)

theorem deferredPayloadLike_iff_of_structuralCongruence
    {p q : Pattern} (hsc : StructuralCongruence p q) :
    DeferredPayloadLike p ↔ DeferredPayloadLike q := by
  constructor
  · rintro ⟨payload, hp⟩
    exact ⟨payload,
      StructuralCongruence.trans _ _ _
        (StructuralCongruence.symm _ _ hsc) hp⟩
  · rintro ⟨payload, hq⟩
    exact ⟨payload, StructuralCongruence.trans _ _ _ hsc hq⟩

theorem deferredPayloadLike_of_output_apply_cong
    {args₁ args₂ : List Pattern}
    (hlen : args₁.length = args₂.length)
    (hpoint : ∀ i (h₁ : i < args₁.length) (h₂ : i < args₂.length),
      StructuralCongruence (args₁.get ⟨i, h₁⟩) (args₂.get ⟨i, h₂⟩))
    {n q chan : Pattern} {payload : Atom}
    (hargs₁ : args₁ = [n, q])
    (hargs₂ : args₂ = [chan, deferredPayload payload]) :
    DeferredPayloadLike q := by
  subst hargs₁ hargs₂
  have hpayload : StructuralCongruence q (deferredPayload payload) := by
    simpa using hpoint 1 (by simp) (by simp)
  exact (deferredPayloadLike_iff_of_structuralCongruence hpayload).mpr
    ⟨payload, StructuralCongruence.refl _⟩

/-- Transport structural congruence to a fixed target. -/
private theorem structuralCongruence_to_fixed_iff
    {p q r : Pattern} (hsc : StructuralCongruence p q) :
    StructuralCongruence p r ↔ StructuralCongruence q r := by
  constructor
  · intro h
    exact StructuralCongruence.trans _ _ _
      (StructuralCongruence.symm _ _ hsc) h
  · intro h
    exact StructuralCongruence.trans _ _ _ hsc h

/-- Ordinary rho core steps that would consume an explicit Rhometta eval
payload are classified separately so `RhometaReduces.core` can exclude exactly
that route while preserving unrelated core reductions. -/
inductive CoreConsumesEvalPayload :
    {p q : Pattern} → Reduction.Reduces p q → Prop where
  | comm {n body q : Pattern} {rest : List Pattern} :
      DeferredPayloadLike q →
      CoreConsumesEvalPayload
        (Reduction.Reduces.comm
          (n := n) (q := q) (p := body) (rest := rest))
  | equiv {p p' q q' : Pattern}
      {hsc₁ : StructuralCongruence p p'}
      {hred : Reduction.Reduces p' q'}
      {hsc₂ : StructuralCongruence q' q} :
      CoreConsumesEvalPayload hred →
      CoreConsumesEvalPayload
        (Reduction.Reduces.equiv
          (p := p) (p' := p') (q := q) (q' := q')
          hsc₁ hred hsc₂)
  | par {p q : Pattern} {rest : List Pattern}
      {hred : Reduction.Reduces p q} :
      CoreConsumesEvalPayload hred →
      CoreConsumesEvalPayload
        (Reduction.Reduces.par (p := p) (q := q) (rest := rest) hred)
  | par_any {p q : Pattern} {before after : List Pattern}
      {hred : Reduction.Reduces p q} :
      CoreConsumesEvalPayload hred →
      CoreConsumesEvalPayload
        (Reduction.Reduces.par_any
          (p := p) (q := q) (before := before) (after := after) hred)
  | par_set {p q : Pattern} {rest : List Pattern}
      {hred : Reduction.Reduces p q} :
      CoreConsumesEvalPayload hred →
      CoreConsumesEvalPayload
        (Reduction.Reduces.par_set (p := p) (q := q) (rest := rest) hred)
  | par_set_any {p q : Pattern} {before after : List Pattern}
      {hred : Reduction.Reduces p q} :
      CoreConsumesEvalPayload hred →
      CoreConsumesEvalPayload
        (Reduction.Reduces.par_set_any
          (p := p) (q := q) (before := before) (after := after) hred)

theorem coreConsumesEvalPayload_singleton_shell
    {n body : Pattern} {rest : List Pattern} {payload : Atom} :
    CoreConsumesEvalPayload
      (Reduction.Reduces.comm
        (n := n)
        (q := .collection .hashBag [deferredPayload payload] none)
        (p := body)
        (rest := rest)) := by
  exact CoreConsumesEvalPayload.comm (deferredPayloadLike_singleton_shell payload)

mutual

/-- Every `POutput` anywhere in the syntax tree carries a deferred Rhometta
payload marker. This is the output-side structural invariant of the
drop-observer shell. -/
private def OutputsDeferred : Pattern → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .apply "POutput" [_, q] => DeferredPayloadLike q
  | .apply "PInput" _ => True
  | .apply _ args => OutputsDeferredList args
  | .lambda _ body => OutputsDeferred body
  | .multiLambda _ _ body => OutputsDeferred body
  | .subst body repl => OutputsDeferred body ∧ OutputsDeferred repl
  | .collection _ elems _ => OutputsDeferredList elems

/-- List-level helper for `OutputsDeferred`. -/
private def OutputsDeferredList : List Pattern → Prop
  | [] => True
  | p :: ps => OutputsDeferred p ∧ OutputsDeferredList ps

end

private theorem outputsDeferredList_iff_of_pointwise
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hpoint : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      OutputsDeferred (ps.get ⟨i, h₁⟩) ↔
        OutputsDeferred (qs.get ⟨i, h₂⟩)) :
    OutputsDeferredList ps ↔ OutputsDeferredList qs := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => simp [OutputsDeferredList]
      | cons q qs =>
          simp at hlen
  | cons p ps ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q qs =>
          have hpq : OutputsDeferred p ↔ OutputsDeferred q :=
            hpoint 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hrest : OutputsDeferredList ps ↔ OutputsDeferredList qs := by
            apply ih
            · simpa using Nat.succ.inj hlen
            · intro i h₁ h₂
              simpa using hpoint (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          constructor <;> intro h
          · exact ⟨hpq.mp h.1, hrest.mp h.2⟩
          · exact ⟨hpq.mpr h.1, hrest.mpr h.2⟩

private theorem outputsDeferredList_iff_of_perm
    {ps qs : List Pattern} (hperm : ps.Perm qs) :
    OutputsDeferredList ps ↔ OutputsDeferredList qs := by
  induction hperm with
  | nil =>
      simp [OutputsDeferredList]
  | @cons p ps qs hperm ih =>
      simp [OutputsDeferredList, ih]
  | swap p q ps =>
      simp [OutputsDeferredList, and_left_comm]
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem outputsDeferredList_append_iff
    {ps qs : List Pattern} :
    OutputsDeferredList (ps ++ qs) ↔
      OutputsDeferredList ps ∧ OutputsDeferredList qs := by
  induction ps with
  | nil =>
      simp [OutputsDeferredList]
  | cons p ps ih =>
      simp [OutputsDeferredList, ih, and_assoc]

private theorem outputsDeferred_of_outputsDeferredList_middle
    {before after : List Pattern} {p : Pattern}
    (h : OutputsDeferredList (before ++ [p] ++ after)) :
    OutputsDeferred p := by
  induction before with
  | nil =>
      simpa [OutputsDeferredList] using h.1
  | cons b before ih =>
      have htail : OutputsDeferredList (before ++ [p] ++ after) := by
        simpa [OutputsDeferredList] using h.2
      exact ih htail

private theorem outputsDeferred_iff_of_structuralCongruence
    {p q : Pattern} (hsc : StructuralCongruence p q) :
    OutputsDeferred p ↔ OutputsDeferred q := by
  induction hsc with
  | alpha _ _ h =>
      subst h
      rfl
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | par_singleton p =>
      simp [OutputsDeferred, OutputsDeferredList]
  | par_nil_left p =>
      simp [OutputsDeferred, OutputsDeferredList]
  | par_nil_right p =>
      simp [OutputsDeferred, OutputsDeferredList]
  | par_comm p q =>
      simp [OutputsDeferred, OutputsDeferredList, and_comm]
  | par_assoc p q r =>
      simp [OutputsDeferred, OutputsDeferredList, and_assoc, and_comm]
  | par_cong ps qs hlen _ ih =>
      simpa [OutputsDeferred] using outputsDeferredList_iff_of_pointwise hlen ih
  | par_flatten ps qs =>
      simp [OutputsDeferred, OutputsDeferredList, outputsDeferredList_append_iff]
  | par_perm ps qs hperm =>
      simpa [OutputsDeferred] using outputsDeferredList_iff_of_perm hperm
  | set_perm ps qs hperm =>
      simpa [OutputsDeferred] using outputsDeferredList_iff_of_perm hperm
  | set_cong ps qs hlen _ ih =>
      simpa [OutputsDeferred] using outputsDeferredList_iff_of_pointwise hlen ih
  | lambda_cong _ _ _ _ ih =>
      simpa [OutputsDeferred] using ih
  | apply_cong f args₁ args₂ hlen hpt ih =>
      by_cases hfout : f = "POutput"
      · subst hfout
        cases args₁ with
        | nil =>
            cases args₂ with
            | nil =>
                simp [OutputsDeferred, OutputsDeferredList]
            | cons a as =>
                simp at hlen
        | cons a as =>
            cases as with
            | nil =>
                cases args₂ with
                | nil =>
                    simp at hlen
                | cons b bs =>
                    cases bs with
                    | nil =>
                        simpa [OutputsDeferred, OutputsDeferredList] using
                          outputsDeferredList_iff_of_pointwise hlen ih
                    | cons c cs =>
                        simp at hlen
            | cons b bs =>
                cases bs with
                | nil =>
                    cases args₂ with
                    | nil =>
                        simp at hlen
                    | cons a' as' =>
                        cases as' with
                        | nil =>
                            simp at hlen
                        | cons b' bs' =>
                            cases bs' with
                            | nil =>
                                have hq : StructuralCongruence b b' := by
                                  simpa using hpt 1 (by simp) (by simp)
                                simpa [OutputsDeferred] using
                                  (deferredPayloadLike_iff_of_structuralCongruence hq)
                            | cons c' cs' =>
                                simp at hlen
                | cons c cs =>
                    cases args₂ with
                    | nil =>
                        simp at hlen
                    | cons a' as' =>
                        cases as' with
                        | nil =>
                            simp at hlen
                        | cons b' bs' =>
                            cases bs' with
                            | nil =>
                                simp at hlen
                            | cons c' cs' =>
                                simpa [OutputsDeferred] using
                                  outputsDeferredList_iff_of_pointwise hlen ih
      · by_cases hfin : f = "PInput"
        · simp [OutputsDeferred, hfin]
        · simpa [OutputsDeferred, hfout, hfin] using
            outputsDeferredList_iff_of_pointwise hlen ih
  | collection_general_cong ct ps qs g hlen _ ih =>
      simpa [OutputsDeferred] using outputsDeferredList_iff_of_pointwise hlen ih
  | multiLambda_cong _ _ _ _ _ ih =>
      simpa [OutputsDeferred] using ih
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ =>
      simp [OutputsDeferred, ih₁, ih₂]
  | quote_drop n =>
      simp [OutputsDeferred, OutputsDeferredList]

mutual

/-- Every `POutput` anywhere in the syntax tree carries the specific deferred
payload marker from the target drop-observer shell. -/
private def OutputsPayload (payload : Atom) : Pattern → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .apply "POutput" [_, q] => StructuralCongruence q (deferredPayload payload)
  | .apply "PInput" _ => True
  | .apply _ args => OutputsPayloadList payload args
  | .lambda _ body => OutputsPayload payload body
  | .multiLambda _ _ body => OutputsPayload payload body
  | .subst body repl => OutputsPayload payload body ∧ OutputsPayload payload repl
  | .collection _ elems _ => OutputsPayloadList payload elems

/-- List-level helper for `OutputsPayload`. -/
private def OutputsPayloadList (payload : Atom) : List Pattern → Prop
  | [] => True
  | p :: ps => OutputsPayload payload p ∧ OutputsPayloadList payload ps

end

private theorem outputsPayloadList_iff_of_pointwise
    {payload : Atom} {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hpoint : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      OutputsPayload payload (ps.get ⟨i, h₁⟩) ↔
        OutputsPayload payload (qs.get ⟨i, h₂⟩)) :
    OutputsPayloadList payload ps ↔ OutputsPayloadList payload qs := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => simp [OutputsPayloadList]
      | cons q qs =>
          simp at hlen
  | cons p ps ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q qs =>
          have hpq : OutputsPayload payload p ↔ OutputsPayload payload q :=
            hpoint 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hrest : OutputsPayloadList payload ps ↔ OutputsPayloadList payload qs := by
            apply ih
            · simpa using Nat.succ.inj hlen
            · intro i h₁ h₂
              simpa using hpoint (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          constructor <;> intro h
          · exact ⟨hpq.mp h.1, hrest.mp h.2⟩
          · exact ⟨hpq.mpr h.1, hrest.mpr h.2⟩

private theorem outputsPayloadList_iff_of_perm
    {payload : Atom} {ps qs : List Pattern} (hperm : ps.Perm qs) :
    OutputsPayloadList payload ps ↔ OutputsPayloadList payload qs := by
  induction hperm with
  | nil =>
      simp [OutputsPayloadList]
  | @cons p ps qs hperm ih =>
      simp [OutputsPayloadList, ih]
  | swap p q ps =>
      simp [OutputsPayloadList, and_left_comm]
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem outputsPayloadList_append_iff
    {payload : Atom} {ps qs : List Pattern} :
    OutputsPayloadList payload (ps ++ qs) ↔
      OutputsPayloadList payload ps ∧ OutputsPayloadList payload qs := by
  induction ps with
  | nil =>
      simp [OutputsPayloadList]
  | cons p ps ih =>
      simp [OutputsPayloadList, ih, and_assoc]

private theorem outputsPayload_iff_of_structuralCongruence
    {payload : Atom} {p q : Pattern} (hsc : StructuralCongruence p q) :
    OutputsPayload payload p ↔ OutputsPayload payload q := by
  induction hsc with
  | alpha _ _ h =>
      subst h
      rfl
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | par_singleton p =>
      simp [OutputsPayload, OutputsPayloadList]
  | par_nil_left p =>
      simp [OutputsPayload, OutputsPayloadList]
  | par_nil_right p =>
      simp [OutputsPayload, OutputsPayloadList]
  | par_comm p q =>
      simp [OutputsPayload, OutputsPayloadList, and_comm]
  | par_assoc p q r =>
      simp [OutputsPayload, OutputsPayloadList, and_assoc, and_comm]
  | par_cong ps qs hlen _ ih =>
      simpa [OutputsPayload] using outputsPayloadList_iff_of_pointwise
        (payload := payload) hlen ih
  | par_flatten ps qs =>
      simp [OutputsPayload, OutputsPayloadList, outputsPayloadList_append_iff]
  | par_perm ps qs hperm =>
      simpa [OutputsPayload] using outputsPayloadList_iff_of_perm
        (payload := payload) hperm
  | set_perm ps qs hperm =>
      simpa [OutputsPayload] using outputsPayloadList_iff_of_perm
        (payload := payload) hperm
  | set_cong ps qs hlen _ ih =>
      simpa [OutputsPayload] using outputsPayloadList_iff_of_pointwise
        (payload := payload) hlen ih
  | lambda_cong _ _ _ _ ih =>
      simpa [OutputsPayload] using ih
  | apply_cong f args₁ args₂ hpt hlen ih =>
      by_cases hfout : f = "POutput"
      · subst hfout
        cases args₁ with
        | nil =>
            cases args₂ with
            | nil =>
                simp [OutputsPayload, OutputsPayloadList]
            | cons a as =>
                simp at hpt
        | cons a as =>
            cases as with
            | nil =>
                cases args₂ with
                | nil =>
                    simp at hpt
                | cons b bs =>
                    cases bs with
                    | nil =>
                        simpa [OutputsPayload, OutputsPayloadList] using
                          outputsPayloadList_iff_of_pointwise
                            (payload := payload) hpt ih
                    | cons c cs =>
                        simp at hpt
            | cons b bs =>
                cases bs with
                | nil =>
                    cases args₂ with
                    | nil =>
                        simp at hpt
                    | cons a' as' =>
                        cases as' with
                        | nil =>
                            simp at hpt
                        | cons b' bs' =>
                            cases bs' with
                            | nil =>
                                have hq : StructuralCongruence b b' := by
                                  simpa using hlen 1 (by simp) (by simp)
                                simpa [OutputsPayload] using
                                  (structuralCongruence_to_fixed_iff
                                    (r := deferredPayload payload) hq)
                            | cons c' cs' =>
                                simp at hpt
                | cons c cs =>
                    cases args₂ with
                    | nil =>
                        simp at hpt
                    | cons a' as' =>
                        cases as' with
                        | nil =>
                            simp at hpt
                        | cons b' bs' =>
                            cases bs' with
                            | nil =>
                                simp at hpt
                            | cons c' cs' =>
                                simpa [OutputsPayload] using
                                  outputsPayloadList_iff_of_pointwise
                                    (payload := payload) hpt ih
      · by_cases hfin : f = "PInput"
        · simp [OutputsPayload, hfin]
        · simpa [OutputsPayload, hfout, hfin] using
            outputsPayloadList_iff_of_pointwise
              (payload := payload) hpt ih
  | collection_general_cong ct ps qs g hlen _ ih =>
      simpa [OutputsPayload] using outputsPayloadList_iff_of_pointwise
        (payload := payload) hlen ih
  | multiLambda_cong _ _ _ _ _ ih =>
      simpa [OutputsPayload] using ih
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ =>
      simp [OutputsPayload, ih₁, ih₂]
  | quote_drop n =>
      simp [OutputsPayload, OutputsPayloadList]

mutual

/-- `EvalFree p` means `p` contains no explicit `rho:eval-payload` marker
anywhere in its syntax tree. -/
def EvalFree : Pattern → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .apply "rho:eval-payload" _ => False
  | .apply _ args => EvalFreeList args
  | .lambda _ body => EvalFree body
  | .multiLambda _ _ body => EvalFree body
  | .subst body repl => EvalFree body ∧ EvalFree repl
  | .collection _ elems _ => EvalFreeList elems

/-- List-level helper for `EvalFree`. -/
def EvalFreeList : List Pattern → Prop
  | [] => True
  | p :: ps => EvalFree p ∧ EvalFreeList ps

end

/-- Rhometta reuses rho reduction and adds one explicit eval-at-COMM rule. -/
inductive RhometaReduces
    (space : Space) (dispatch : GroundedDispatch) :
    Pattern → Pattern → Type where
  | core {p q : Pattern} :
      (hcore : Reduction.Reduces p q) →
      ¬ CoreConsumesEvalPayload hcore →
      RhometaReduces space dispatch p q
  | evalComm {n body : Pattern} {rest : List Pattern}
      {payload value : Atom} :
      EvalCommCanonicalShell body payload →
      CertifiedPayloadResult space dispatch payload value →
      RhometaReduces space dispatch
        (.collection .hashBag
          ([.apply "POutput" [n, deferredPayload payload],
            .apply "PInput" [n, .lambda none body]] ++ rest) none)
        (.collection .hashBag
          ([semanticCommSubst body (wrappedValue value)] ++ rest) none)
  | equiv {p p' q q' : Pattern} :
      StructuralCongruence p p' →
      RhometaReduces space dispatch p' q' →
      StructuralCongruence q' q →
      RhometaReduces space dispatch p q
  | par {p q : Pattern} {rest : List Pattern} :
      RhometaReduces space dispatch p q →
      RhometaReduces space dispatch
        (.collection .hashBag (p :: rest) none)
        (.collection .hashBag (q :: rest) none)
  | par_any {p q : Pattern} {before after : List Pattern} :
      RhometaReduces space dispatch p q →
      RhometaReduces space dispatch
        (.collection .hashBag (before ++ [p] ++ after) none)
        (.collection .hashBag (before ++ [q] ++ after) none)
  | par_set {p q : Pattern} {rest : List Pattern} :
      RhometaReduces space dispatch p q →
      RhometaReduces space dispatch
        (.collection .hashSet (p :: rest) none)
        (.collection .hashSet (q :: rest) none)
  | par_set_any {p q : Pattern} {before after : List Pattern} :
      RhometaReduces space dispatch p q →
      RhometaReduces space dispatch
        (.collection .hashSet (before ++ [p] ++ after) none)
        (.collection .hashSet (before ++ [q] ++ after) none)

/-- Reflexive-transitive closure of Rhometta reduction. -/
inductive RhometaReducesStar
    (space : Space) (dispatch : GroundedDispatch) :
    Pattern → Pattern → Type where
  | refl (p : Pattern) : RhometaReducesStar space dispatch p p
  | step {p q r : Pattern} :
      RhometaReduces space dispatch p q →
      RhometaReducesStar space dispatch q r →
      RhometaReducesStar space dispatch p r

/-- Rhometta may-reachability: all states reachable via zero or more
Rhometta reductions. -/
def RhometaMayReachable
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) : Set Pattern :=
  { q | Nonempty (RhometaReducesStar space dispatch p q) }

/-- A Rhometta term can step if it has at least one one-step Rhometta reduct. -/
def RhometaCanStep
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) : Prop :=
  ∃ q, Nonempty (RhometaReduces space dispatch p q)

/-- A Rhometta term is quiescent when it has no Rhometta one-step reduct. -/
def RhometaNormalForm
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) : Prop :=
  ¬ RhometaCanStep space dispatch p

/-- The quiescent outcome set for Rhometta's may-semantics. -/
def RhometaOutcomes
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) : Set Pattern :=
  { q | Nonempty (RhometaReducesStar space dispatch p q) ∧
      RhometaNormalForm space dispatch q }

/-- Single-path execution is semantically safe only when the Rhometta
quiescent outcome set is a subsingleton. -/
def RhometaSinglePathSafe
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) : Prop :=
  (RhometaOutcomes space dispatch p).Subsingleton

abbrev MayReachable := RhometaMayReachable

/-- Canonical two-party source process used to observe deferred payload COMM. -/
def evalSource (chan : Pattern) (payload : Atom) (body : Pattern)
    (rest : List Pattern := []) : Pattern :=
  .collection .hashBag
    ([.apply "POutput" [chan, deferredPayload payload],
      .apply "PInput" [chan, .lambda none body]] ++ rest) none

/-- Drop-observer source: after COMM the payload value is exposed as a process. -/
def evalDropSource (chan : Pattern) (payload : Atom) : Pattern :=
  evalSource chan payload (.apply "PDrop" [.bvar 0])

/-- Expected one-step residual for the drop-observer case. -/
def evalDropResidual (value : Atom) : Pattern :=
  .collection .hashBag [semanticNormalizeProc (wrappedValue value)] none

private theorem outputsDeferred_evalDropSource
    (chan : Pattern) (payload : Atom) :
    OutputsDeferred (evalDropSource chan payload) := by
  unfold evalDropSource evalSource
  simp [OutputsDeferred, OutputsDeferredList]
  exact ⟨payload, StructuralCongruence.refl _⟩

private theorem outputsPayload_evalDropSource
    (chan : Pattern) (payload : Atom) :
    OutputsPayload payload (evalDropSource chan payload) := by
  unfold evalDropSource evalSource
  simp [OutputsPayload, OutputsPayloadList]
  exact StructuralCongruence.refl _

private theorem deferredPayloadLike_of_commSource_SC_evalDropSource
    {n q body chan : Pattern} {rest : List Pattern}
    {payload : Atom}
    (hsc :
      StructuralCongruence
        (.collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none)
        (evalDropSource chan payload)) :
    DeferredPayloadLike q := by
  have hdef :
      OutputsDeferred
        (.collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none) :=
    (outputsDeferred_iff_of_structuralCongruence hsc).mpr
      (outputsDeferred_evalDropSource chan payload)
  simpa [OutputsDeferred, OutputsDeferredList] using hdef.1

private theorem outputPayload_of_commSource_SC_evalDropSource
    {n q body chan : Pattern} {rest : List Pattern}
    {payload : Atom}
    (hsc :
      StructuralCongruence
        (.collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none)
        (evalDropSource chan payload)) :
    StructuralCongruence q (deferredPayload payload) := by
  have hdef :
      OutputsPayload payload
        (.collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none) :=
    (outputsPayload_iff_of_structuralCongruence hsc).mpr
      (outputsPayload_evalDropSource chan payload)
  simpa [OutputsPayload, OutputsPayloadList] using hdef.1

private theorem deferredPayload_of_evalSource_SC_evalDropSource
    {n chan body : Pattern} {rest : List Pattern}
    {payload₁ payload₂ : Atom}
    (hsc :
      StructuralCongruence
        (evalSource n payload₁ body rest)
        (evalDropSource chan payload₂)) :
    StructuralCongruence (deferredPayload payload₁) (deferredPayload payload₂) := by
  simpa [evalSource] using
    (outputPayload_of_commSource_SC_evalDropSource
      (n := n) (q := deferredPayload payload₁) (body := body)
      (chan := chan) (rest := rest) (payload := payload₂) hsc)

theorem evalDrop_subst (value : Atom) :
    semanticCommSubst (.apply "PDrop" [.bvar 0]) (wrappedValue value) =
      semanticNormalizeProc (wrappedValue value) := by
  simpa [wrappedValue] using
    semanticCommSubst_collapses_bound_drop (wrappedValue value)

theorem evalSource_eq_evalDropSource_inv
    {n chan body : Pattern} {rest : List Pattern}
    {payload₁ payload₂ : Atom}
    (h :
      evalSource n payload₁ body rest =
        evalDropSource chan payload₂) :
    n = chan ∧
      body = .apply "PDrop" [.bvar 0] ∧
      rest = [] ∧
      payload₁ = payload₂ := by
  unfold evalSource evalDropSource at h
  injection h with _ hlist _
  have hlen := congrArg List.length hlist
  simp at hlen
  have hrest : rest = [] := by
    cases rest with
    | nil =>
        rfl
    | cons x xs =>
        simp at hlen
  subst hrest
  simp at hlist
  have hn : n = chan := hlist.1.1
  have hpayloadPat : deferredPayload payload₁ = deferredPayload payload₂ := hlist.1.2
  have hbody : body = .apply "PDrop" [.bvar 0] := hlist.2.2
  have hpayload : payload₁ = payload₂ := by
    simp [deferredPayload] at hpayloadPat
    exact atomToPattern_injective hpayloadPat
  exact ⟨hn, hbody, rfl, hpayload⟩

theorem commSource_eq_evalDropSource_inv
    {n chan body q : Pattern} {rest : List Pattern}
    {payload : Atom}
    (h :
      .collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none =
        evalDropSource chan payload) :
    n = chan ∧
      q = deferredPayload payload ∧
      body = .apply "PDrop" [.bvar 0] ∧
      rest = [] := by
  unfold evalDropSource evalSource at h
  injection h with _ hlist _
  have hlen := congrArg List.length hlist
  simp at hlen
  have hrest : rest = [] := by
    cases rest with
    | nil =>
        rfl
    | cons x xs =>
        simp at hlen
  subst hrest
  simp at hlist
  exact ⟨hlist.1.1, hlist.1.2, hlist.2.2, rfl⟩

theorem deferredPayloadLike_of_commSource_eq_evalDropSource
    {n chan body q : Pattern} {rest : List Pattern}
    {payload : Atom}
    (h :
      .collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none =
        evalDropSource chan payload) :
    DeferredPayloadLike q := by
  rcases commSource_eq_evalDropSource_inv h with ⟨_, hq, _, _⟩
  subst hq
  exact ⟨payload, StructuralCongruence.refl _⟩

theorem evalDropSource_evalComm_residual_exact
    {space : Space} {dispatch : GroundedDispatch}
    {n chan body : Pattern} {rest : List Pattern}
    {payload₁ payload₂ value : Atom}
    (hsource : evalSource n payload₁ body rest = evalDropSource chan payload₂)
    (hcert : CertifiedPayloadResult space dispatch payload₁ value) :
    CertifiedPayloadResult space dispatch payload₂ value ∧
      .collection .hashBag
          ([semanticCommSubst body (wrappedValue value)] ++ rest) none =
        evalDropResidual value := by
  rcases evalSource_eq_evalDropSource_inv hsource with ⟨_, hbody, hrest, hpayload⟩
  subst hbody hrest hpayload
  constructor
  · exact hcert
  · simp [evalDropResidual, evalDrop_subst]

private theorem certifiedPayloadResult_of_evalSource_eq_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {n chan body : Pattern} {rest : List Pattern}
    {payload₁ payload₂ value : Atom}
    (hsource : evalSource n payload₁ body rest = evalDropSource chan payload₂)
    (hcert : CertifiedPayloadResult space dispatch payload₁ value) :
    CertifiedPayloadResult space dispatch payload₂ value :=
  (evalDropSource_evalComm_residual_exact
    (space := space) (dispatch := dispatch)
    (n := n) (chan := chan) (body := body) (rest := rest)
    (payload₁ := payload₁) (payload₂ := payload₂) (value := value)
    hsource hcert).1

private theorem no_evalComm_from_evalDropSource_eq_of_no_certified
    {space : Space} {dispatch : GroundedDispatch}
    {n chan body : Pattern} {rest : List Pattern}
    {payload₁ payload₂ value : Atom}
    (hsource : evalSource n payload₁ body rest = evalDropSource chan payload₂)
    (hnone : ∀ v, ¬ CertifiedPayloadResult space dispatch payload₂ v)
    (hcert : CertifiedPayloadResult space dispatch payload₁ value) :
    False := by
  exact hnone value
    (certifiedPayloadResult_of_evalSource_eq_evalDropSource
      (space := space) (dispatch := dispatch)
      (n := n) (chan := chan) (body := body) (rest := rest)
      (payload₁ := payload₁) (payload₂ := payload₂) (value := value)
      hsource hcert)

theorem list_middle_eq_pair_cases
    {α : Type} {before after : List α} {p a b : α}
    (h : before ++ [p] ++ after = [a, b]) :
    (before = [] ∧ p = a ∧ after = [b]) ∨
      (before = [a] ∧ p = b ∧ after = []) := by
  have hlen := congrArg List.length h
  simp at hlen
  cases before with
  | nil =>
      left
      simp at h
      aesop
  | cons x xs =>
      cases xs with
      | nil =>
          right
          simp at h
          aesop
      | cons y ys =>
          have : False := by
            have hlen' := congrArg List.length h
            simp at hlen'
          exact False.elim this

private def shellWidth : Pattern → Nat
  | .apply "PZero" [] => 0
  | .apply "NQuote" [p] => shellWidth p
  | .apply "PDrop" [p] => shellWidth p
  | .collection _ elems _ => (elems.map shellWidth).sum
  | _ => 1

private theorem shellWidth_list_SC
    {ps qs : List Pattern} (hlen : ps.length = qs.length)
    (hsc : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      shellWidth (ps.get ⟨i, h₁⟩) = shellWidth (qs.get ⟨i, h₂⟩)) :
    (ps.map shellWidth).sum = (qs.map shellWidth).sum := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => rfl
      | cons q qs' => simp at hlen
  | cons p ps' ih =>
      cases qs with
      | nil => simp at hlen
      | cons q qs' =>
          simp only [List.map_cons, List.sum_cons]
          simp only [List.length_cons] at hlen ⊢
          have h0 : shellWidth p = shellWidth q := hsc 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have htl := ih (by omega) fun i h₁ h₂ =>
            hsc (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          omega

private theorem shellWidth_SC {p q : Pattern}
    (hsc : StructuralCongruence p q) :
    shellWidth p = shellWidth q := by
  induction hsc with
  | alpha _ _ h =>
      subst h
      rfl
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | par_singleton p =>
      simp [shellWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_nil_left p =>
      simp [shellWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_nil_right p =>
      simp [shellWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_comm p q =>
      simp [shellWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  | par_assoc p q r =>
      simp [shellWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  | par_cong ps qs hlen _ ih =>
      simp only [shellWidth]
      exact shellWidth_list_SC hlen ih
  | par_flatten ps qs =>
      simp [shellWidth, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_perm _ _ hperm =>
      simp only [shellWidth]
      exact (hperm.map shellWidth).sum_eq
  | set_perm _ _ hperm =>
      simp only [shellWidth]
      exact (hperm.map shellWidth).sum_eq
  | set_cong es₁ es₂ hlen _ ih =>
      simp only [shellWidth]
      exact shellWidth_list_SC hlen ih
  | lambda_cong _ _ _ _ =>
      simp [shellWidth]
  | apply_cong f args₁ args₂ hlen _ ih =>
      by_cases hquote : f = "NQuote"
      · subst hquote
        cases args₁ with
        | nil =>
            cases args₂ <;> simp at hlen ⊢
        | cons a as =>
            cases as with
            | nil =>
                cases args₂ with
                | nil => simp at hlen
                | cons b bs =>
                    cases bs with
                    | nil =>
                        have hab : shellWidth a = shellWidth b := by
                          simpa using ih 0 (by simp) (by simp)
                        simp [shellWidth, hab]
                    | cons b' bs' =>
                        simp at hlen
            | cons a' as' =>
                cases args₂ with
                | nil =>
                    simp at hlen
                | cons b bs =>
                    cases bs with
                    | nil =>
                        simp at hlen
                    | cons b' bs' =>
                        simp [shellWidth]
      · by_cases hdrop : f = "PDrop"
        · subst hdrop
          cases args₁ with
          | nil =>
              cases args₂ <;> simp at hlen ⊢
          | cons a as =>
              cases as with
              | nil =>
                  cases args₂ with
                  | nil => simp at hlen
                  | cons b bs =>
                      cases bs with
                      | nil =>
                          have hab : shellWidth a = shellWidth b := by
                            simpa using ih 0 (by simp) (by simp)
                          simp [shellWidth, hab]
                      | cons b' bs' =>
                          simp at hlen
              | cons a' as' =>
                  cases args₂ with
                  | nil =>
                      simp at hlen
                  | cons b bs =>
                      cases bs with
                      | nil =>
                          simp at hlen
                      | cons b' bs' =>
                          simp [shellWidth]
        · by_cases hzero : f = "PZero"
          · subst hzero
            cases args₁ with
            | nil =>
                cases args₂ with
                | nil =>
                    simp [shellWidth]
                | cons b bs =>
                    simp at hlen
            | cons a as =>
                cases args₂ with
                | nil =>
                    simp at hlen
                | cons b bs =>
                    cases bs with
                    | nil =>
                        simp [shellWidth]
                    | cons b' bs' =>
                        simp [shellWidth]
          · simp [shellWidth, hquote, hdrop, hzero]
  | collection_general_cong _ es₁ es₂ _ hlen _ ih =>
      simp only [shellWidth]
      exact shellWidth_list_SC hlen ih
  | multiLambda_cong _ _ _ _ _ =>
      simp [shellWidth]
  | subst_cong _ _ _ _ _ _ =>
      simp [shellWidth]
  | quote_drop n =>
      simp [shellWidth]

private theorem shellWidth_ge_two_of_reduces {p q : Pattern}
    (hred : Reduction.Reduces p q) :
    2 ≤ shellWidth p := by
  induction hred with
  | comm =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | @equiv p p' q q' hsc _ _ ih =>
      have hw : shellWidth p = shellWidth p' := shellWidth_SC hsc
      omega
  | par _ ih =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | par_any _ ih =>
      simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega
  | par_set _ ih =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | par_set_any _ ih =>
      simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega

private theorem output_shell_SC_irreducible
    {n payload p q : Pattern}
    (hsc : StructuralCongruence p (.apply "POutput" [n, payload]))
    (hred : Reduction.Reduces p q) : False := by
  have hw : shellWidth p = shellWidth (.apply "POutput" [n, payload]) := shellWidth_SC hsc
  have hge : 2 ≤ shellWidth p := shellWidth_ge_two_of_reduces hred
  simp [shellWidth] at hw
  omega

private theorem input_shell_SC_irreducible
    {n body p q : Pattern}
    (hsc : StructuralCongruence p (.apply "PInput" [n, .lambda none body]))
    (hred : Reduction.Reduces p q) : False := by
  have hw : shellWidth p = shellWidth (.apply "PInput" [n, .lambda none body]) := shellWidth_SC hsc
  have hge : 2 ≤ shellWidth p := shellWidth_ge_two_of_reduces hred
  simp [shellWidth] at hw
  omega

private theorem coreConsumesEvalPayload_of_outputsDeferred_shellWidth_two
    {p q : Pattern}
    (hout : OutputsDeferred p)
    (hwidth : shellWidth p = 2)
    (hred : Reduction.Reduces p q) :
    CoreConsumesEvalPayload hred := by
  revert hout hwidth
  induction hred with
  | comm =>
      intro hout hwidth
      exact CoreConsumesEvalPayload.comm (by
        simpa [OutputsDeferred, OutputsDeferredList] using hout.1)
  | @equiv p p' q q' hsc hmid hsc' ih =>
      intro hout hwidth
      have hout' : OutputsDeferred p' :=
        (outputsDeferred_iff_of_structuralCongruence hsc).mp hout
      have hwidth' : shellWidth p' = 2 := by
        calc
          shellWidth p' = shellWidth p := (shellWidth_SC hsc).symm
          _ = 2 := hwidth
      exact CoreConsumesEvalPayload.equiv (ih hout' hwidth')
  | @par pInner qInner rest hmid ih =>
      intro hout hwidth
      have hp : OutputsDeferred pInner := by
        simpa [OutputsDeferred, OutputsDeferredList] using hout.1
      have hge : 2 ≤ shellWidth pInner := shellWidth_ge_two_of_reduces hmid
      have hpwidth : shellWidth pInner = 2 := by
        simp [shellWidth, List.map_cons, List.sum_cons] at hwidth
        omega
      exact CoreConsumesEvalPayload.par (ih hp hpwidth)
  | @par_any pInner qInner before after hmid ih =>
      intro hout hwidth
      have hlist : OutputsDeferredList (before ++ [pInner] ++ after) := by
        simpa [OutputsDeferred] using hout
      have hp : OutputsDeferred pInner :=
        outputsDeferred_of_outputsDeferredList_middle hlist
      have hge : 2 ≤ shellWidth pInner := shellWidth_ge_two_of_reduces hmid
      have hpwidth : shellWidth pInner = 2 := by
        simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hwidth
        omega
      exact CoreConsumesEvalPayload.par_any (ih hp hpwidth)
  | @par_set pInner qInner rest hmid ih =>
      intro hout hwidth
      have hp : OutputsDeferred pInner := by
        simpa [OutputsDeferred, OutputsDeferredList] using hout.1
      have hge : 2 ≤ shellWidth pInner := shellWidth_ge_two_of_reduces hmid
      have hpwidth : shellWidth pInner = 2 := by
        simp [shellWidth, List.map_cons, List.sum_cons] at hwidth
        omega
      exact CoreConsumesEvalPayload.par_set (ih hp hpwidth)
  | @par_set_any pInner qInner before after hmid ih =>
      intro hout hwidth
      have hlist : OutputsDeferredList (before ++ [pInner] ++ after) := by
        simpa [OutputsDeferred] using hout
      have hp : OutputsDeferred pInner :=
        outputsDeferred_of_outputsDeferredList_middle hlist
      have hge : 2 ≤ shellWidth pInner := shellWidth_ge_two_of_reduces hmid
      have hpwidth : shellWidth pInner = 2 := by
        simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hwidth
        omega
      exact CoreConsumesEvalPayload.par_set_any (ih hp hpwidth)

private theorem coreConsumesEvalPayload_of_SC_evalDropSource
    {p q chan : Pattern} {payload : Atom}
    (hsc : StructuralCongruence p (evalDropSource chan payload))
    (hred : Reduction.Reduces p q) :
    CoreConsumesEvalPayload hred := by
  have hout : OutputsDeferred p :=
    (outputsDeferred_iff_of_structuralCongruence hsc).mpr
      (outputsDeferred_evalDropSource chan payload)
  have hwidth : shellWidth p = 2 := by
    calc
      shellWidth p = shellWidth (evalDropSource chan payload) := shellWidth_SC hsc
      _ = 2 := by
        simp [evalDropSource, evalSource, shellWidth]
  exact coreConsumesEvalPayload_of_outputsDeferred_shellWidth_two hout hwidth hred

private theorem no_rhometaCore_from_SC_evalDropSource
    {p q chan : Pattern} {payload : Atom}
    {hcore : Reduction.Reduces p q}
    (hsc : StructuralCongruence p (evalDropSource chan payload))
    (hguard : ¬ CoreConsumesEvalPayload hcore) :
    False := by
  exact hguard (coreConsumesEvalPayload_of_SC_evalDropSource hsc hcore)

private theorem shellWidth_ge_two_of_rhometaReduces
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hred : RhometaReduces space dispatch p q) :
    2 ≤ shellWidth p := by
  induction hred with
  | core hcore _ =>
      exact shellWidth_ge_two_of_reduces hcore
  | @evalComm n body rest payload value hcanon hcert =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | @equiv p p' q q' hsc hmid hsc' ih =>
      have hw : shellWidth p = shellWidth p' := shellWidth_SC hsc
      omega
  | par _ ih =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | par_any _ ih =>
      simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega
  | par_set _ ih =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | par_set_any _ ih =>
      simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega

private theorem rhometa_output_shell_SC_irreducible
    {space : Space} {dispatch : GroundedDispatch}
    {n payload p q : Pattern}
    (hsc : StructuralCongruence p (.apply "POutput" [n, payload]))
    (hred : RhometaReduces space dispatch p q) : False := by
  have hw : shellWidth p = shellWidth (.apply "POutput" [n, payload]) := shellWidth_SC hsc
  have hge : 2 ≤ shellWidth p := shellWidth_ge_two_of_rhometaReduces hred
  simp [shellWidth] at hw
  omega

private theorem rhometa_input_shell_SC_irreducible
    {space : Space} {dispatch : GroundedDispatch}
    {n body p q : Pattern}
    (hsc : StructuralCongruence p (.apply "PInput" [n, .lambda none body]))
    (hred : RhometaReduces space dispatch p q) : False := by
  have hw : shellWidth p = shellWidth (.apply "PInput" [n, .lambda none body]) := shellWidth_SC hsc
  have hge : 2 ≤ shellWidth p := shellWidth_ge_two_of_rhometaReduces hred
  simp [shellWidth] at hw
  omega

private theorem no_rhometaReduces_par_source_eq_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} {rest : List Pattern}
    {chan : Pattern} {payload : Atom}
    (hstep : RhometaReduces space dispatch p q)
    (hsrc : .collection .hashBag (p :: rest) none = evalDropSource chan payload) :
    False := by
  unfold evalDropSource evalSource at hsrc
  injection hsrc with _ hlist _
  have hlen := congrArg List.length hlist
  simp at hlen
  cases rest with
  | nil =>
      simp at hlen
  | cons r rest' =>
      cases rest' with
      | nil =>
          rcases hlist with ⟨_, _, _⟩
          exact rhometa_output_shell_SC_irreducible
            (space := space) (dispatch := dispatch)
            (n := chan) (payload := deferredPayload payload)
            (p := .apply "POutput" [chan, deferredPayload payload])
            (q := q)
            (StructuralCongruence.refl _) hstep
      | cons r' rest'' =>
          simp at hlen

private theorem no_rhometaReduces_par_any_source_eq_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} {before after : List Pattern}
    {chan : Pattern} {payload : Atom}
    (hstep : RhometaReduces space dispatch p q)
    (hsrc :
      .collection .hashBag (before ++ [p] ++ after) none =
        evalDropSource chan payload) :
    False := by
  unfold evalDropSource evalSource at hsrc
  injection hsrc with _ hlist _
  rcases list_middle_eq_pair_cases hlist with hcase | hcase
  · rcases hcase with ⟨hbefore, hp, hafter⟩
    subst hbefore hp hafter
    exact rhometa_output_shell_SC_irreducible
      (space := space) (dispatch := dispatch)
      (n := chan) (payload := deferredPayload payload)
      (p := .apply "POutput" [chan, deferredPayload payload])
      (q := q)
      (StructuralCongruence.refl _) hstep
  · rcases hcase with ⟨hbefore, hp, hafter⟩
    subst hbefore hp hafter
    exact rhometa_input_shell_SC_irreducible
      (space := space) (dispatch := dispatch)
      (n := chan) (body := .apply "PDrop" [.bvar 0])
      (p := .apply "PInput" [chan, .lambda none (.apply "PDrop" [.bvar 0])])
      (q := q)
      (StructuralCongruence.refl _) hstep

private theorem no_rhometaReduces_par_set_source_eq_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} {rest : List Pattern}
    {chan : Pattern} {payload : Atom}
    (_hstep : RhometaReduces space dispatch p q)
    (hsrc : .collection .hashSet (p :: rest) none = evalDropSource chan payload) :
    False := by
  unfold evalDropSource evalSource at hsrc
  cases hsrc

private theorem no_rhometaReduces_par_set_any_source_eq_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} {before after : List Pattern}
    {chan : Pattern} {payload : Atom}
    (_hstep : RhometaReduces space dispatch p q)
    (hsrc :
      .collection .hashSet (before ++ [p] ++ after) none =
        evalDropSource chan payload) :
    False := by
  unfold evalDropSource evalSource at hsrc
  cases hsrc

private theorem struct_output_cong_channel {n n' q : Pattern}
    (hn : StructuralCongruence n n') :
    StructuralCongruence (.apply "POutput" [n, q]) (.apply "POutput" [n', q]) := by
  refine StructuralCongruence.apply_cong "POutput" [n, q] [n', q] rfl ?_
  intro i h₁ h₂
  have hi_lt : i < 2 := by simpa using h₁
  have hi : i = 0 ∨ i = 1 := by omega
  cases hi with
  | inl hi0 =>
      subst hi0
      simpa using hn
  | inr hi1 =>
      subst hi1
      simpa using StructuralCongruence.refl q

private theorem struct_input_cong_channel {n n' body : Pattern}
    (hn : StructuralCongruence n n') :
    StructuralCongruence
      (.apply "PInput" [n, .lambda none body])
      (.apply "PInput" [n', .lambda none body]) := by
  refine StructuralCongruence.apply_cong "PInput"
    [n, .lambda none body] [n', .lambda none body] rfl ?_
  intro i h₁ h₂
  have hi_lt : i < 2 := by simpa using h₁
  have hi : i = 0 ∨ i = 1 := by omega
  cases hi with
  | inl hi0 =>
      subst hi0
      simpa using hn
  | inr hi1 =>
      subst hi1
      simpa using StructuralCongruence.refl (.lambda none body)

private theorem par_cong_cons_cons_tail
    {a₁ a₂ b₁ b₂ : Pattern} {rest : List Pattern}
    (ha : StructuralCongruence a₁ a₂)
    (hb : StructuralCongruence b₁ b₂) :
    StructuralCongruence
      (.collection .hashBag ([a₁, b₁] ++ rest) none)
      (.collection .hashBag ([a₂, b₂] ++ rest) none) := by
  refine StructuralCongruence.par_cong _ _ rfl ?_
  intro i h₁ h₂
  cases i with
  | zero =>
      simpa using ha
  | succ i =>
      cases i with
      | zero =>
          simpa using hb
      | succ i =>
          have h₁' : i < rest.length := by simpa using h₁
          have h₂' : i < rest.length := by simpa using h₂
          simpa using StructuralCongruence.refl (rest.get ⟨i, h₁'⟩)

theorem evalSource_structCongruence_normalizedChannel
    (chan : Pattern) (payload : Atom) (body : Pattern) (rest : List Pattern := []) :
    StructuralCongruence
      (evalSource chan payload body rest)
      (evalSource (semanticNormalizeName chan) payload body rest) := by
  unfold evalSource
  refine par_cong_cons_cons_tail ?_ ?_
  · exact struct_output_cong_channel
      (StructuralCongruence.symm _ _ (semanticNormalizeName_sound_struct (n := chan)))
  · exact struct_input_cong_channel
      (StructuralCongruence.symm _ _ (semanticNormalizeName_sound_struct (n := chan)))

theorem evalDrop_certified_branch
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    Nonempty (RhometaReduces space dispatch
      (evalDropSource chan payload)
      (evalDropResidual value)) := by
  have hcanon :
      EvalCommCanonicalShell (.apply "PDrop" [.bvar 0]) payload :=
    evalCommCanonicalShell_dropBody (payload := payload)
  refine ⟨?_⟩
  simpa [evalDropSource, evalSource, evalDropResidual, evalDrop_subst] using
    (RhometaReduces.evalComm (space := space) (dispatch := dispatch)
      (n := chan) (body := .apply "PDrop" [.bvar 0]) (rest := [])
      (payload := payload) (value := value) hcanon hcert)

theorem evalComm_certified_branch
    {space : Space} {dispatch : GroundedDispatch}
    {chan body : Pattern} {rest : List Pattern}
    {payload value : Atom}
    (hcanon : EvalCommCanonicalShell body payload)
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    Nonempty (RhometaReduces space dispatch
      (evalSource chan payload body rest)
      (.collection .hashBag
        ([semanticCommSubst body (wrappedValue value)] ++ rest) none)) := by
  refine ⟨?_⟩
  simpa [evalSource] using
    (RhometaReduces.evalComm (space := space) (dispatch := dispatch)
      (n := chan) (body := body) (rest := rest)
      (payload := payload) (value := value) hcanon hcert)

private theorem evalFreeList_iff_of_pointwise
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hpoint :
      ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
        EvalFree (ps.get ⟨i, h₁⟩) ↔ EvalFree (qs.get ⟨i, h₂⟩)) :
    EvalFreeList ps ↔ EvalFreeList qs := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => simp [EvalFreeList]
      | cons q qs => simp at hlen
  | cons p ps ih =>
      cases qs with
      | nil => simp at hlen
      | cons q qs =>
          have hpq : EvalFree p ↔ EvalFree q :=
            hpoint 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hrest :
              EvalFreeList ps ↔ EvalFreeList qs := by
            apply ih
            · simpa using Nat.succ.inj hlen
            · intro i h₁ h₂
              simpa using hpoint (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          simp [EvalFreeList, hpq, hrest]

private theorem evalFreeList_iff_of_perm
    {ps qs : List Pattern} (hperm : ps.Perm qs) :
    EvalFreeList ps ↔ EvalFreeList qs := by
  induction hperm with
  | nil =>
      simp [EvalFreeList]
  | @cons p ps qs hperm ih =>
      simp [EvalFreeList, ih]
  | swap p q ps =>
      simp [EvalFreeList, and_left_comm]
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem evalFreeList_append_iff
    {ps qs : List Pattern} :
    EvalFreeList (ps ++ qs) ↔ EvalFreeList ps ∧ EvalFreeList qs := by
  induction ps with
  | nil =>
      simp [EvalFreeList]
  | cons p ps ih =>
      simp [EvalFreeList, ih, and_assoc]

private theorem evalFree_of_evalFreeList_middle
    {before after : List Pattern} {p : Pattern}
    (h : EvalFreeList (before ++ [p] ++ after)) :
    EvalFree p := by
  induction before with
  | nil =>
      simpa [EvalFreeList] using h.1
  | cons b before ih =>
      have htail : EvalFreeList (before ++ [p] ++ after) := by
        simpa [EvalFreeList] using h.2
      exact ih htail

theorem evalFree_iff_of_structuralCongruence
    {p q : Pattern} (hsc : StructuralCongruence p q) :
    EvalFree p ↔ EvalFree q := by
  induction hsc with
  | alpha p q h =>
      subst h
      rfl
  | refl p =>
      rfl
  | symm p q _ ih =>
      exact ih.symm
  | trans p q r _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | par_singleton p =>
      simp [EvalFree, EvalFreeList]
  | par_nil_left p =>
      simp [EvalFree, EvalFreeList]
  | par_nil_right p =>
      simp [EvalFree, EvalFreeList]
  | par_comm p q =>
      simp [EvalFree, EvalFreeList, and_comm]
  | par_assoc p q r =>
      simp [EvalFree, EvalFreeList, and_assoc, and_comm]
  | par_cong ps qs hlen _ ih =>
      simpa [EvalFree] using evalFreeList_iff_of_pointwise hlen ih
  | par_flatten ps qs =>
      simp [EvalFree, EvalFreeList, evalFreeList_append_iff]
  | par_perm _ _ hperm =>
      simpa [EvalFree] using evalFreeList_iff_of_perm hperm
  | set_perm _ _ hperm =>
      simpa [EvalFree] using evalFreeList_iff_of_perm hperm
  | set_cong es₁ es₂ hlen _ ih =>
      simpa [EvalFree] using evalFreeList_iff_of_pointwise hlen ih
  | lambda_cong _ _ _ _ ih =>
      simpa [EvalFree] using ih
  | apply_cong f args₁ args₂ hlen _ ih =>
      by_cases hf : f = "rho:eval-payload"
      · subst hf
        simp [EvalFree]
      · simpa [EvalFree, hf] using evalFreeList_iff_of_pointwise hlen ih
  | collection_general_cong _ elems₁ elems₂ _ hlen _ ih =>
      simpa [EvalFree] using evalFreeList_iff_of_pointwise hlen ih
  | multiLambda_cong _ _ _ _ _ ih =>
      simpa [EvalFree] using ih
  | subst_cong _ _ _ _ _ _ ihBody ihRepl =>
      constructor
      · intro h
        exact ⟨ihBody.mp h.1, ihRepl.mp h.2⟩
      · intro h
        exact ⟨ihBody.mpr h.1, ihRepl.mpr h.2⟩
  | quote_drop n =>
      simp [EvalFree, EvalFreeList]

theorem not_evalFree_of_deferredPayloadLike
    {q : Pattern} (hlike : DeferredPayloadLike q) :
    ¬ EvalFree q := by
  rcases hlike with ⟨payload, hsc⟩
  intro hfree
  have htarget : EvalFree (deferredPayload payload) := by
    exact (evalFree_iff_of_structuralCongruence hsc).mp hfree
  simp [EvalFree, deferredPayload] at htarget

theorem not_evalFree_of_coreConsumesEvalPayload
    {p q : Pattern} {hred : Reduction.Reduces p q}
    (hconsume : CoreConsumesEvalPayload hred) :
    ¬ EvalFree p := by
  induction hconsume with
  | comm hlike =>
      intro hfree
      exact not_evalFree_of_deferredPayloadLike hlike
        (by simpa [EvalFree, EvalFreeList] using hfree.1.2)
  | @equiv p p' q q' hsc₁ hred hsc₂ _ ih =>
      intro hfree
      exact ih ((evalFree_iff_of_structuralCongruence hsc₁).mp hfree)
  | par _ ih =>
      intro hfree
      exact ih (by simpa [EvalFree, EvalFreeList] using hfree.1)
  | @par_any p q before after hred _ ih =>
      intro hfree
      have hlist : EvalFreeList (before ++ [p] ++ after) := by
        simpa [EvalFree] using hfree
      exact ih (evalFree_of_evalFreeList_middle hlist)
  | par_set _ ih =>
      intro hfree
      exact ih (by simpa [EvalFree, EvalFreeList] using hfree.1)
  | @par_set_any p q before after hred _ ih =>
      intro hfree
      have hlist : EvalFreeList (before ++ [p] ++ after) := by
        simpa [EvalFree] using hfree
      exact ih (evalFree_of_evalFreeList_middle hlist)

theorem rhometa_core_guard_of_evalFree
    {p q : Pattern} (hfree : EvalFree p) (hred : Reduction.Reduces p q) :
    ¬ CoreConsumesEvalPayload hred := by
  intro hconsume
  exact not_evalFree_of_coreConsumesEvalPayload hconsume hfree

theorem nonempty_reduces_of_rhometaReduces_of_evalFree
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} (hfree : EvalFree p)
    (hred : RhometaReduces space dispatch p q) :
    Nonempty (Reduction.Reduces p q) := by
  induction hred with
  | core hcore _ =>
      exact ⟨hcore⟩
  | evalComm _ hcert =>
      exfalso
      simp [EvalFree, EvalFreeList, deferredPayload] at hfree
  | equiv hsc hstep hsc' ih =>
      rcases ih ((evalFree_iff_of_structuralCongruence hsc).mp hfree) with ⟨hcore⟩
      exact ⟨Reduction.Reduces.equiv hsc hcore hsc'⟩
  | par hstep ih =>
      rcases ih (by simpa [EvalFree, EvalFreeList] using hfree.1) with ⟨hcore⟩
      exact ⟨Reduction.Reduces.par hcore⟩
  | @par_any pInner qInner before after hstep ih =>
      have hlist : EvalFreeList (before ++ [pInner] ++ after) := by
        simpa [EvalFree] using hfree
      rcases ih (evalFree_of_evalFreeList_middle hlist) with ⟨hcore⟩
      exact ⟨Reduction.Reduces.par_any (before := before) (after := after) hcore⟩
  | par_set hstep ih =>
      rcases ih (by simpa [EvalFree, EvalFreeList] using hfree.1) with ⟨hcore⟩
      exact ⟨Reduction.Reduces.par_set hcore⟩
  | @par_set_any pInner qInner before after hstep ih =>
      have hlist : EvalFreeList (before ++ [pInner] ++ after) := by
        simpa [EvalFree] using hfree
      rcases ih (evalFree_of_evalFreeList_middle hlist) with ⟨hcore⟩
      exact ⟨Reduction.Reduces.par_set_any (before := before) (after := after) hcore⟩

theorem rhometaReduces_iff_reduces_of_evalFree
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} (hfree : EvalFree p) :
    Nonempty (RhometaReduces space dispatch p q) ↔
      Nonempty (Reduction.Reduces p q) := by
  constructor
  · intro hred
    rcases hred with ⟨hred⟩
    exact nonempty_reduces_of_rhometaReduces_of_evalFree hfree hred
  · intro hred
    rcases hred with ⟨hred⟩
    exact ⟨RhometaReduces.core hred
      (rhometa_core_guard_of_evalFree hfree hred)⟩

theorem ioCount_pos_of_core_reduces {p q : Pattern}
    (hred : Reduction.Reduces p q) :
    0 < ioCount p := by
  induction hred with
  | comm =>
      simp [ioCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | @equiv p p' q q' hsc _ _ ih =>
      have hw : ioCount p = ioCount p' := ioCount_SC hsc
      omega
  | par _ ih =>
      simp [ioCount, List.map_cons, List.sum_cons]
      omega
  | par_any _ ih =>
      simp [ioCount, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega
  | par_set _ ih =>
      simp [ioCount, List.map_cons, List.sum_cons]
      omega
  | par_set_any _ ih =>
      simp [ioCount, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega

theorem ioCount_pos_of_rhometa_reduces
    {space : Space} {dispatch : GroundedDispatch} {p q : Pattern}
    (hred : RhometaReduces space dispatch p q) :
    0 < ioCount p := by
  induction hred with
  | core hcore _ =>
      exact ioCount_pos_of_core_reduces hcore
  | @evalComm n body rest payload value _ hcert =>
      have hz : ioCount (deferredPayload payload) = 0 :=
        ioCount_deferredPayload_zero payload
      simp [ioCount, hz,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | @equiv p p' q q' hsc _ _ ih =>
      have hw : ioCount p = ioCount p' := ioCount_SC hsc
      omega
  | par _ ih =>
      simp [ioCount, List.map_cons, List.sum_cons]
      omega
  | par_any _ ih =>
      simp [ioCount, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega
  | par_set _ ih =>
      simp [ioCount, List.map_cons, List.sum_cons]
      omega
  | par_set_any _ ih =>
      simp [ioCount, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega

theorem rhometaNormalForm_of_ioCount_zero
    {space : Space} {dispatch : GroundedDispatch} {p : Pattern}
    (hzero : ioCount p = 0) :
    RhometaNormalForm space dispatch p := by
  intro hstep
  rcases hstep with ⟨q, hq⟩
  rcases hq with ⟨hred⟩
  have hpos : 0 < ioCount p := ioCount_pos_of_rhometa_reduces hred
  omega

theorem evalDropResidual_normalForm
    {space : Space} {dispatch : GroundedDispatch} (value : Atom) :
    RhometaNormalForm space dispatch (evalDropResidual value) := by
  apply rhometaNormalForm_of_ioCount_zero
  simpa [evalDropResidual, semanticNormalizeProc_wrappedValue, ioCount] using
    ioCount_wrappedValue_zero value

theorem rhometaNormalForm_of_SC_evalDropResidual
    {space : Space} {dispatch : GroundedDispatch}
    {q : Pattern} {value : Atom}
    (hsc : StructuralCongruence q (evalDropResidual value)) :
    RhometaNormalForm space dispatch q := by
  apply rhometaNormalForm_of_ioCount_zero
  calc
    ioCount q = ioCount (evalDropResidual value) := ioCount_SC hsc
    _ = 0 := by
      simpa [evalDropResidual, semanticNormalizeProc_wrappedValue, ioCount] using
        ioCount_wrappedValue_zero value

theorem rhometaCanStep_iff_of_structuralCongruence
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hsc : StructuralCongruence p q) :
    RhometaCanStep space dispatch p ↔
      RhometaCanStep space dispatch q := by
  constructor
  · rintro ⟨r, ⟨hred⟩⟩
    exact ⟨r, ⟨RhometaReduces.equiv
      (StructuralCongruence.symm _ _ hsc)
      hred
      (StructuralCongruence.refl _)⟩⟩
  · rintro ⟨r, ⟨hred⟩⟩
    exact ⟨r, ⟨RhometaReduces.equiv
      hsc
      hred
      (StructuralCongruence.refl _)⟩⟩

theorem rhometaNormalForm_iff_of_structuralCongruence
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hsc : StructuralCongruence p q) :
    RhometaNormalForm space dispatch p ↔
      RhometaNormalForm space dispatch q := by
  constructor
  · intro hnf hstep
    exact hnf ((rhometaCanStep_iff_of_structuralCongruence hsc).mpr hstep)
  · intro hnf hstep
    exact hnf ((rhometaCanStep_iff_of_structuralCongruence hsc).mp hstep)

theorem rhometaReducesStar_eq_of_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hnf : RhometaNormalForm space dispatch p)
    (hstar : RhometaReducesStar space dispatch p q) :
    p = q := by
  induction hstar with
  | refl _ =>
      rfl
  | @step p q r hstep htail ih =>
      exfalso
      exact hnf ⟨q, ⟨hstep⟩⟩

theorem rhometaOutcomes_self_iff_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {p : Pattern} :
    p ∈ RhometaOutcomes space dispatch p ↔
      RhometaNormalForm space dispatch p := by
  constructor
  · intro hp
    exact hp.2
  · intro hnf
    exact ⟨⟨RhometaReducesStar.refl _⟩, hnf⟩

theorem not_mem_rhometaOutcomes_of_normalForm_ne
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hnf : RhometaNormalForm space dispatch p)
    (hneq : q ≠ p) :
    q ∉ RhometaOutcomes space dispatch p := by
  intro hq
  rcases hq with ⟨hstar, _⟩
  have hpq : p = q := rhometaReducesStar_eq_of_normalForm hnf hstar.some
  exact hneq hpq.symm

theorem mem_rhometaOutcomes_iff_eq_of_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hnf : RhometaNormalForm space dispatch p) :
    q ∈ RhometaOutcomes space dispatch p ↔ q = p := by
  constructor
  · intro hq
    by_cases hpq : q = p
    · exact hpq
    · exact False.elim (not_mem_rhometaOutcomes_of_normalForm_ne
        (space := space) (dispatch := dispatch)
        (p := p) (q := q) hnf hpq hq)
  · intro hqp
    subst hqp
    simpa using (rhometaOutcomes_self_iff_normalForm
      (space := space) (dispatch := dispatch)
      (p := q)).2 hnf

theorem evalDropSource_outcomes_iff_eq_of_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {chan q : Pattern} {payload : Atom}
    (hnf : RhometaNormalForm space dispatch (evalDropSource chan payload)) :
    q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) ↔
      q = evalDropSource chan payload := by
  exact mem_rhometaOutcomes_iff_eq_of_normalForm
    (space := space) (dispatch := dispatch)
    (p := evalDropSource chan payload) (q := q) hnf

theorem rhometaOutcomes_eq_singleton_of_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {p : Pattern}
    (hnf : RhometaNormalForm space dispatch p) :
    RhometaOutcomes space dispatch p = ({p} : Set Pattern) := by
  ext q
  simp [mem_rhometaOutcomes_iff_eq_of_normalForm
    (space := space) (dispatch := dispatch)
    (p := p) (q := q) hnf]

theorem evalDropSource_outcomes_eq_singleton_of_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hnf : RhometaNormalForm space dispatch (evalDropSource chan payload)) :
    RhometaOutcomes space dispatch (evalDropSource chan payload) =
      ({evalDropSource chan payload} : Set Pattern) := by
  exact rhometaOutcomes_eq_singleton_of_normalForm
    (space := space) (dispatch := dispatch)
    (p := evalDropSource chan payload) hnf

theorem evalDropSource_not_normalForm_of_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    ¬ RhometaNormalForm space dispatch (evalDropSource chan payload) := by
  intro hnf
  exact hnf ⟨evalDropResidual value,
    evalDrop_certified_branch
      (space := space) (dispatch := dispatch)
      (payload := payload) (value := value) hcert⟩

theorem evalDropSource_normalForm_implies_no_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hnf : RhometaNormalForm space dispatch (evalDropSource chan payload)) :
    ∀ value, ¬ CertifiedPayloadResult space dispatch payload value := by
  intro value hcert
  exact evalDropSource_not_normalForm_of_certified
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) (value := value) hcert hnf

theorem evalDropSource_outcome_implies_no_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    evalDropSource chan payload ∈
        RhometaOutcomes space dispatch (evalDropSource chan payload) →
      ∀ value, ¬ CertifiedPayloadResult space dispatch payload value := by
  intro hout
  exact evalDropSource_normalForm_implies_no_certified
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload)
    ((rhometaOutcomes_self_iff_normalForm
      (space := space) (dispatch := dispatch)
      (p := evalDropSource chan payload)).mp hout)

theorem evalDropSource_not_outcome_of_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    evalDropSource chan payload ∉
      RhometaOutcomes space dispatch (evalDropSource chan payload) := by
  intro hout
  exact evalDropSource_outcome_implies_no_certified
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hout value hcert

theorem evalDrop_certified_value_mayReachable
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    evalDropResidual value ∈ MayReachable space dispatch (evalDropSource chan payload) := by
  refine ⟨RhometaReducesStar.step ?_ (RhometaReducesStar.refl _)⟩
  exact (evalDrop_certified_branch
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) (value := value) hcert).some

theorem evalDrop_certified_value_outcome
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    evalDropResidual value ∈
      RhometaOutcomes space dispatch (evalDropSource chan payload) := by
  exact ⟨evalDrop_certified_value_mayReachable
            (space := space) (dispatch := dispatch)
            (chan := chan) (payload := payload) (value := value) hcert,
         evalDropResidual_normalForm (space := space) (dispatch := dispatch) value⟩

theorem evalDrop_preserves_all_certified_results
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload v₁ v₂ : Atom}
    (h₁ : CertifiedPayloadResult space dispatch payload v₁)
    (h₂ : CertifiedPayloadResult space dispatch payload v₂) :
    evalDropResidual v₁ ∈ MayReachable space dispatch (evalDropSource chan payload) ∧
    evalDropResidual v₂ ∈ MayReachable space dispatch (evalDropSource chan payload) := by
  exact ⟨evalDrop_certified_value_mayReachable
            (space := space) (dispatch := dispatch)
            (chan := chan) (payload := payload) (value := v₁) h₁,
         evalDrop_certified_value_mayReachable
            (space := space) (dispatch := dispatch)
            (chan := chan) (payload := payload) (value := v₂) h₂⟩

theorem evalDrop_preserves_all_certified_outcomes
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload v₁ v₂ : Atom}
    (h₁ : CertifiedPayloadResult space dispatch payload v₁)
    (h₂ : CertifiedPayloadResult space dispatch payload v₂) :
    evalDropResidual v₁ ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) ∧
    evalDropResidual v₂ ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) := by
  exact ⟨evalDrop_certified_value_outcome
            (space := space) (dispatch := dispatch)
            (chan := chan) (payload := payload) (value := v₁) h₁,
         evalDrop_certified_value_outcome
            (space := space) (dispatch := dispatch)
            (chan := chan) (payload := payload) (value := v₂) h₂⟩

theorem evalDropResidual_injective :
    Function.Injective (fun a : Atom => evalDropResidual a) := by
  intro a b h
  have hsingle :
      [semanticNormalizeProc (wrappedValue a)] =
      [semanticNormalizeProc (wrappedValue b)] := by
    injection h with hsingle
  have hnorm : semanticNormalizeProc (wrappedValue a) =
      semanticNormalizeProc (wrappedValue b) := List.cons.inj hsingle |>.1
  have hw : wrappedValue a = wrappedValue b := by
    simpa [semanticNormalizeProc_wrappedValue] using hnorm
  exact wrappedValue_injective hw

theorem evalDrop_not_singlePathSafe_of_distinct_values
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload v₁ v₂ : Atom}
    (h₁ : CertifiedPayloadResult space dispatch payload v₁)
    (h₂ : CertifiedPayloadResult space dispatch payload v₂)
    (hdistinct : v₁ ≠ v₂) :
    ¬ RhometaSinglePathSafe space dispatch (evalDropSource chan payload) := by
  intro hsafe
  have hpair := evalDrop_preserves_all_certified_outcomes
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload)
    (v₁ := v₁) (v₂ := v₂) h₁ h₂
  have hres : evalDropResidual v₁ = evalDropResidual v₂ := hsafe hpair.1 hpair.2
  exact hdistinct (evalDropResidual_injective hres)

theorem outcomes_eq_of_singlePathSafe
    {space : Space} {dispatch : GroundedDispatch} {p q r : Pattern}
    (hsafe : RhometaSinglePathSafe space dispatch p)
    (hq : q ∈ RhometaOutcomes space dispatch p)
    (hr : r ∈ RhometaOutcomes space dispatch p) :
    q = r := by
  exact hsafe hq hr

theorem chosenOutcome_lossless_iff_singlePathSafe
    {space : Space} {dispatch : GroundedDispatch} {p q : Pattern}
    (hq : q ∈ RhometaOutcomes space dispatch p) :
    RhometaSinglePathSafe space dispatch p ↔
      ∀ r, r ∈ RhometaOutcomes space dispatch p → r = q := by
  constructor
  · intro hsafe r hr
    exact hsafe hr hq
  · intro hchosen r hr s hs
    rw [hchosen r hr, hchosen s hs]

/-! ## Concurrent fold — the commuting lemma for one fixed compatible matching (the ⊗ layer)

This block is the **⊗ layer** of the full rhometta semantics
(⊔ choice over compatible matchings + ⊗ parallel fold within a matching + `;` sequential closure of
rounds): it governs ONE pairwise-compatible matching fired as a single round.  It is deliberately
*not* the whole semantics — it does not model contention (choice between alternative pairings of the
same linear send/receive) nor causal chaining (a COMM enabling a later COMM); those phenomena require
the choice and sequencing layers and have operational witnesses in `Engine.lean` (race and multi-step
tests).  Treating this fold as the whole rhometta would overclaim.

Within its scope it is exact: a payload over a frozen base is a *nondeterministic producer of
`(result, local-delta)`*, where the delta lives in a commutative merge monoid `Δ` (a semilattice /
MORK union / cost quantale).  Firing an independent frontier chooses one outcome per payload and
merges the deltas commutatively, recording results as an order-independent multiset.  Because `Δ` is
a `CommMonoid`, the outcome set is invariant under firing order (`foldOutcomes_perm`) — macro-step
soundness for one round delivered as *algebra*, not a hand diamond.  Single-path safety factors as
"every payload is deterministic" (`foldOutcomes_subsingleton_of_forall`), generalizing
`chosenOutcome_lossless_iff_singlePathSafe`.  The value-only theory above is the `Δ := PUnit`
instance.  Payload non-interference is *structural* here (payload outcome sets are fixed data); an
engine step instantiates this fold only under the engine-side conditions (quiet continuations,
copy-stable results, unique matching, transactional isolation) — that instance-hood is a separate
corollary, not this lemma. -/
section ConcurrentFold

/-- A payload over the frozen base: its set of possible `(result, local-delta)` outcomes. -/
abbrev Payload (R Δ : Type*) := Set (R × Δ)

variable {R : Type*} {Δ : Type*} [CommMonoid Δ]

/-- Outcomes of firing a frontier (list of payloads): choose one `(result, delta)` per payload, merge
the deltas by the commutative product, and record the results as an order-independent multiset. -/
def foldOutcomes : List (Payload R Δ) → Set (Multiset R × Δ)
  | [] => {(0, 1)}
  | p :: F =>
      { x | ∃ r δ rs δ', (r, δ) ∈ p ∧ (rs, δ') ∈ foldOutcomes F ∧ x = (r ::ₘ rs, δ * δ') }

theorem mem_foldOutcomes_cons {p : Payload R Δ} {F : List (Payload R Δ)}
    {x : Multiset R × Δ} :
    x ∈ foldOutcomes (p :: F) ↔
      ∃ r δ rs δ', (r, δ) ∈ p ∧ (rs, δ') ∈ foldOutcomes F ∧ x = (r ::ₘ rs, δ * δ') :=
  Iff.rfl

/-- **Macro-step soundness as algebra**: the outcome set of an independent frontier is invariant under
firing order, because the merge monoid is commutative. -/
theorem foldOutcomes_perm {F₁ F₂ : List (Payload R Δ)} (h : F₁.Perm F₂) :
    foldOutcomes F₁ = foldOutcomes F₂ := by
  induction h with
  | nil => rfl
  | cons p _ ih => ext x; simp only [mem_foldOutcomes_cons, ih]
  | swap x y l =>
      ext z
      simp only [mem_foldOutcomes_cons]
      constructor
      · rintro ⟨ry, δy, RS, D, hy, hmid, rfl⟩
        obtain ⟨rx, δx, rs, δ', hx, hrs, hpair⟩ := hmid
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        exact ⟨rx, δx, ry ::ₘ rs, δy * δ', hx, ⟨ry, δy, rs, δ', hy, hrs, rfl⟩, by
          simp only [Prod.mk.injEq]
          exact ⟨Multiset.cons_swap ry rx rs, mul_left_comm δy δx δ'⟩⟩
      · rintro ⟨rx, δx, RS, D, hx, hmid, rfl⟩
        obtain ⟨ry, δy, rs, δ', hy, hrs, hpair⟩ := hmid
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        exact ⟨ry, δy, rx ::ₘ rs, δx * δ', hy, ⟨rx, δx, rs, δ', hx, hrs, rfl⟩, by
          simp only [Prod.mk.injEq]
          exact ⟨Multiset.cons_swap rx ry rs, mul_left_comm δx δy δ'⟩⟩
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- **Factorization (⟸)**: if every payload is deterministic (a subsingleton outcome set), the whole
frontier's outcome set is a subsingleton — i.e. single-path-safe.  Generalizes the crown theorem
`chosenOutcome_lossless_iff_singlePathSafe` to the delta-carrying setting. -/
theorem foldOutcomes_subsingleton_of_forall :
    ∀ {F : List (Payload R Δ)}, (∀ p ∈ F, p.Subsingleton) → (foldOutcomes F).Subsingleton
  | [], _ => by
      rintro a ha b hb
      simp only [foldOutcomes, Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
  | p :: F, hsub => by
      rintro a ⟨r, δ, rs, δ', hr, hrs, rfl⟩ b ⟨r2, δ2, rs2, δ2', hr2, hrs2, rfl⟩
      have hp := hsub p (List.mem_cons.mpr (Or.inl rfl)) hr hr2
      have htail := foldOutcomes_subsingleton_of_forall
        (fun q hq => hsub q (List.mem_cons.mpr (Or.inr hq))) hrs hrs2
      rw [Prod.mk.injEq] at hp htail ⊢
      exact ⟨by rw [hp.1, htail.1], by rw [hp.2, htail.2]⟩

end ConcurrentFold

/-! ### Merged cost — the concurrent fold as a quantale-valued aggregate

When the merge monoid `Δ` also carries a complete lattice (e.g. the cost quantale `ℝ≥0∞` from
`Mettapedia.Algebra.QuantaleWeakness`), a payload's aggregate value is the join of its possible deltas,
and a frontier's merged cost is the commutative product of those aggregates.  This merged cost is
invariant under firing order (`foldCost_perm`) — the quantale shadow of `foldOutcomes_perm`. -/
section CostQuantale

variable {R : Type*} {Δ : Type*} [CommMonoid Δ] [CompleteLattice Δ]

/-- A payload's aggregate value: the join of its possible deltas. -/
noncomputable def payloadSup (p : Payload R Δ) : Δ := sSup {δ | ∃ r, (r, δ) ∈ p}

/-- A frontier's merged cost: the commutative product of the per-payload aggregates. -/
noncomputable def foldCost : List (Payload R Δ) → Δ
  | [] => 1
  | p :: F => payloadSup p * foldCost F

@[simp] theorem foldCost_nil : foldCost ([] : List (Payload R Δ)) = 1 := rfl

@[simp] theorem foldCost_cons (p : Payload R Δ) (F : List (Payload R Δ)) :
    foldCost (p :: F) = payloadSup p * foldCost F := rfl

/-- The merged cost of an independent frontier is invariant under firing order — the quantale shadow
of `foldOutcomes_perm`, by commutativity of the merge. -/
theorem foldCost_perm {F₁ F₂ : List (Payload R Δ)} (h : F₁.Perm F₂) :
    foldCost F₁ = foldCost F₂ := by
  induction h with
  | nil => rfl
  | cons p _ ih => simp only [foldCost_cons, ih]
  | swap x y l => simp only [foldCost_cons]; rw [mul_left_comm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

end CostQuantale

/-! ### The quantale factorization — merged cost = aggregate over outcomes

When `Δ` is a quantale (the merge `*` distributes over arbitrary joins, as for the cost quantale
`ℝ≥0∞`), the recursive merged cost `foldCost` equals the join of the deltas of *all* concurrent
outcomes (`foldCost_eq_aggregate`).  So the macro step's single merged cost faithfully aggregates the
whole outcome lattice — macro-step soundness for the cost observable, delivered by quantale
distributivity. -/
section CostAggregate

variable {R : Type*} {Δ : Type*} [CommMonoid Δ] [CompleteLattice Δ] [IsQuantale Δ]

/-- The product of two joins is the join of the pairwise products (quantale distributivity). -/
theorem sSup_mul_sSup (A B : Set Δ) :
    sSup A * sSup B = ⨆ a ∈ A, ⨆ b ∈ B, a * b := by
  rw [sSup_mul_distrib]
  simp_rw [mul_sSup_distrib]

/-- **Quantale factorization**: the frontier's recursive merged cost equals the join of the merged
deltas over every concurrent outcome.  Macro-step soundness for the cost observable. -/
theorem foldCost_eq_aggregate (F : List (Payload R Δ)) :
    foldCost F = sSup (Prod.snd '' foldOutcomes F) := by
  induction F with
  | nil =>
      rw [foldCost_nil, foldOutcomes, Set.image_singleton]
      simp
  | cons p F ih =>
      rw [foldCost_cons, ih, payloadSup, sSup_mul_sSup]
      apply le_antisymm
      · refine iSup₂_le fun a ha => iSup₂_le fun b hb => le_sSup ?_
        obtain ⟨r, hr⟩ := ha
        obtain ⟨x, hxF, rfl⟩ := hb
        exact ⟨(r ::ₘ x.1, a * x.2),
          mem_foldOutcomes_cons.mpr ⟨r, a, x.1, x.2, hr, hxF, rfl⟩, rfl⟩
      · refine sSup_le fun c hc => ?_
        obtain ⟨x, hx, rfl⟩ := hc
        rw [mem_foldOutcomes_cons] at hx
        obtain ⟨r, δ, rs, δ', hr, hrs, rfl⟩ := hx
        exact le_iSup₂_of_le δ ⟨r, hr⟩ (le_iSup₂_of_le δ' ⟨(rs, δ'), hrs, rfl⟩ le_rfl)

end CostAggregate

/-! ### Result branching factors out of the merge

The other half of the factorization: the multiset of *results* reachable is the pure result fold,
independent of the delta monoid.  Together with `foldCost_eq_aggregate`, the may-set factors as
(result branching) × (merge/cost skeleton). -/
section ResultFactor

variable {R : Type*} {Δ : Type*} [CommMonoid Δ]

/-- The pure result fold: the multisets of results from choosing one result per payload. -/
def resultOutcomes : List (Set R) → Set (Multiset R)
  | [] => {0}
  | p :: F => {x | ∃ r rs, r ∈ p ∧ rs ∈ resultOutcomes F ∧ x = r ::ₘ rs}

theorem mem_resultOutcomes_cons {p : Set R} {F : List (Set R)} {x : Multiset R} :
    x ∈ resultOutcomes (p :: F) ↔
      ∃ r rs, r ∈ p ∧ rs ∈ resultOutcomes F ∧ x = r ::ₘ rs :=
  Iff.rfl

/-- The result-multiset reachable is the pure result fold, independent of the delta monoid. -/
theorem foldOutcomes_fst (F : List (Payload R Δ)) :
    Prod.fst '' foldOutcomes F = resultOutcomes (F.map (fun p => Prod.fst '' p)) := by
  induction F with
  | nil => simp [foldOutcomes, resultOutcomes]
  | cons p F ih =>
      ext z
      simp only [List.map_cons, mem_resultOutcomes_cons, Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [mem_foldOutcomes_cons] at hx
        obtain ⟨r, δ, rs, δ', hr, hrs, rfl⟩ := hx
        refine ⟨r, rs, ⟨(r, δ), hr, rfl⟩, ?_, rfl⟩
        rw [← ih]; exact ⟨(rs, δ'), hrs, rfl⟩
      · rintro ⟨r, rs, ⟨rδ, hrδ, hrr⟩, hrs, rfl⟩
        rw [← ih] at hrs
        obtain ⟨y, hy, rfl⟩ := hrs
        refine ⟨(rδ.1 ::ₘ y.1, rδ.2 * y.2), mem_foldOutcomes_cons.mpr
          ⟨rδ.1, rδ.2, y.1, y.2, hrδ, hy, rfl⟩, ?_⟩
        simp [hrr]

end ResultFactor

/-! ### Grounding: the fold fires on real rhometta merge and on the cost quantale

These witnesses confirm the abstract theory applies to concrete rhometta data: `Δ` a bag-space delta
(`Multiset Atom` merge, via `Multiplicative`) gives order-independent residual outcomes; `Δ = ℝ≥0∞`
(the project's cost quantale) gives the merged-cost factorization. -/
section Grounding

open scoped ENNReal

/-- rhometta residuals merging bag-space deltas: the concurrent fold is order-independent. -/
example {F₁ F₂ : List (Payload Pattern (Multiplicative (Multiset Atom)))} (h : F₁.Perm F₂) :
    foldOutcomes F₁ = foldOutcomes F₂ :=
  foldOutcomes_perm h

/-- rhometta cost in the `ℝ≥0∞` quantale: merged cost = join over all concurrent outcomes. -/
example (F : List (Payload Pattern ℝ≥0∞)) :
    foldCost F = sSup (Prod.snd '' foldOutcomes F) :=
  foldCost_eq_aggregate F

end Grounding

/-! ## First-class owned exports — the Ω layer (transactional outcomes)

The engine's transactional payloads do three things: produce a result, accumulate a local delta, and
let mutated resources escape only as *owned exports* (fresh-identity spaces/state cells returned as
values).  Here exports become first-class in the outcome object: a payload outcome is
`(result, delta, exports)` with exports an order-irrelevant bag.

The crucial economy: `PayloadΩ R Δ Ω` is *definitionally* the existing `Payload` over the product
merge monoid `Δ × ExportBag Ω`, so the entire ⊗-layer theory (`foldOutcomes`, `foldOutcomes_perm`,
the factorizations) applies verbatim — nothing is re-proven (`foldOutcomesΩ_perm`).  Dropping
exports along the projection monoid hom recovers the export-free theory
(`foldOutcomesΩ_proj_delta`, via the general naturality lemma `foldOutcomes_map_hom`), so the
development above is literally the shadow of this one.

`reifyΩ` is the abstract form of what the engine does with owned results: pack result and exports
together (owned results returned as values in the residual), delta separate.  It is injective
(`reifyΩ_injective`) — reification loses nothing — and commutes with firing a round
(`reifyΩ_fold_commutes`): reify-then-fold equals fold-then-reify on aggregate observables.  The
closing example shows exports are *semantically real*: two payloads with identical result/delta
projections but different owned exports are distinguished after reification — outcome objects
without exports are too coarse for transactional rhometta. -/
section OwnedExports

/-- A bag of owned exports, as a multiplicative commutative monoid (merge = bag union). -/
abbrev ExportBag (Ω : Type*) := Multiplicative (Multiset Ω)

/-- A transactional payload: a nondeterministic producer of `(result, delta, exports)` over a frozen
base.  Definitionally a `Payload` over the product merge monoid, so the concurrent-fold theory
applies verbatim. -/
abbrev PayloadΩ (R Δ Ω : Type*) := Payload R (Δ × ExportBag Ω)

variable {R Δ Ω : Type*} [CommMonoid Δ]

/-- Outcomes of firing a frontier of transactional payloads: the existing fold over the product
monoid — deltas merge in `Δ`, export bags merge by union. -/
abbrev foldOutcomesΩ (F : List (PayloadΩ R Δ Ω)) : Set (Multiset R × (Δ × ExportBag Ω)) :=
  foldOutcomes F

/-- Order-independence of the transactional round, inherited verbatim from the ⊗ layer. -/
theorem foldOutcomesΩ_perm {F₁ F₂ : List (PayloadΩ R Δ Ω)} (h : F₁.Perm F₂) :
    foldOutcomesΩ F₁ = foldOutcomesΩ F₂ :=
  foldOutcomes_perm h

/-- **Naturality**: the concurrent fold commutes with any monoid hom on the merge — mapping every
payload along `f` and folding equals folding and then mapping the merged delta. -/
theorem foldOutcomes_map_hom {Δ' : Type*} [CommMonoid Δ'] (f : Δ →* Δ') :
    ∀ F : List (Payload R Δ),
      foldOutcomes (F.map (fun p => (fun o : R × Δ => (o.1, f o.2)) '' p)) =
        (fun x : Multiset R × Δ => (x.1, f x.2)) '' foldOutcomes F
  | [] => by
      ext x
      simp [foldOutcomes, Set.image_singleton]
  | p :: F => by
      ext x
      simp only [List.map_cons, mem_foldOutcomes_cons, Set.mem_image]
      constructor
      · rintro ⟨r, δ, rs, δ', ⟨⟨a, b⟩, hab, hg⟩, hrs, rfl⟩
        rw [foldOutcomes_map_hom f F] at hrs
        obtain ⟨⟨rs₀, d₀⟩, hd₀, hg₂⟩ := hrs
        rw [Prod.mk.injEq] at hg hg₂
        obtain ⟨rfl, rfl⟩ := hg
        obtain ⟨rfl, rfl⟩ := hg₂
        exact ⟨(a ::ₘ rs₀, b * d₀), ⟨a, b, rs₀, d₀, hab, hd₀, rfl⟩, by
          simp [map_mul]⟩
      · rintro ⟨⟨RS, D⟩, hRSD, rfl⟩
        obtain ⟨r, δ, rs, δ', hr, hrs, hpair⟩ := hRSD
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        refine ⟨r, f δ, rs, f δ', ⟨(r, δ), hr, rfl⟩, ?_, by simp [map_mul]⟩
        rw [foldOutcomes_map_hom f F]
        exact ⟨(rs, δ'), hrs, rfl⟩

/-- **Conservativity**: dropping exports (the projection monoid hom) recovers the export-free
theory — the Δ-only development is the image of the transactional one. -/
theorem foldOutcomesΩ_proj_delta (F : List (PayloadΩ R Δ Ω)) :
    foldOutcomes (F.map (fun p => (fun o : R × (Δ × ExportBag Ω) => (o.1, o.2.1)) '' p)) =
      (fun x : Multiset R × (Δ × ExportBag Ω) => (x.1, x.2.1)) '' foldOutcomesΩ F :=
  foldOutcomes_map_hom (MonoidHom.fst Δ (ExportBag Ω)) F

/-- Reify a transactional outcome into the residual-style shape the engine returns: result and
exports packed together (owned results as values in the residual), delta separate. -/
def reifyΩ (o : R × (Δ × ExportBag Ω)) : (R × Multiset Ω) × Δ :=
  ((o.1, (o.2.2 : ExportBag Ω).toAdd), o.2.1)

omit [CommMonoid Δ] in
/-- **Reification loses no information.** -/
theorem reifyΩ_injective : Function.Injective (reifyΩ (R := R) (Δ := Δ) (Ω := Ω)) := by
  rintro ⟨r₁, δ₁, ω₁⟩ ⟨r₂, δ₂, ω₂⟩ h
  simp only [reifyΩ, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, hω⟩, rfl⟩ := h
  simp only [Prod.mk.injEq, true_and]
  exact Multiplicative.toAdd.injective hω

/-- Aggregate a reified round outcome: strip per-result export attachments into one merged bag. -/
def aggregateReified (x : Multiset (R × Multiset Ω) × Δ) : Multiset R × Δ × Multiset Ω :=
  (x.1.map Prod.fst, x.2, (x.1.map Prod.snd).sum)

/-- Reshape a transactional fold outcome to the same observable type. -/
def reshapeΩ (x : Multiset R × (Δ × ExportBag Ω)) : Multiset R × Δ × Multiset Ω :=
  (x.1, x.2.1, (x.2.2 : ExportBag Ω).toAdd)

/-- **Reification commutes with the round**: reifying every payload, firing the round, and
aggregating equals firing the transactional round and reshaping — reify-then-fold =
fold-then-reify on aggregate observables. -/
theorem reifyΩ_fold_commutes :
    ∀ F : List (PayloadΩ R Δ Ω),
      aggregateReified '' foldOutcomes (F.map (Set.image reifyΩ)) =
        reshapeΩ '' foldOutcomesΩ F
  | [] => by
      ext x
      simp [foldOutcomes, Set.image_singleton, aggregateReified, reshapeΩ]
  | p :: F => by
      ext x
      simp only [List.map_cons, Set.mem_image]
      constructor
      · rintro ⟨⟨RS, D⟩, hRSD, rfl⟩
        obtain ⟨rω, δ, rs, δ', hrω, hrs, hpair⟩ := hRSD
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        obtain ⟨⟨a, b, ωm⟩, hab, hg⟩ := hrω
        have hagg : aggregateReified (rs, δ') ∈
            aggregateReified '' foldOutcomes (F.map (Set.image reifyΩ)) :=
          ⟨(rs, δ'), hrs, rfl⟩
        rw [reifyΩ_fold_commutes F] at hagg
        obtain ⟨⟨rs₀, d₀, ωs₀⟩, hmem, hsh⟩ := hagg
        refine ⟨(a ::ₘ rs₀, (b * d₀, ωm * ωs₀)),
          ⟨a, (b, ωm), rs₀, (d₀, ωs₀), hab, hmem, by simp⟩, ?_⟩
        simp only [reifyΩ] at hg
        rw [Prod.mk.injEq] at hg
        obtain ⟨hg1, rfl⟩ := hg
        simp only [reshapeΩ, aggregateReified, reshapeΩ] at hsh ⊢
        rw [Prod.mk.injEq] at hsh
        obtain ⟨h1, h2⟩ := hsh
        rw [Prod.mk.injEq] at h2
        obtain ⟨h2, h3⟩ := h2
        simp only [Multiset.map_cons, Multiset.sum_cons, ← hg1, Prod.mk.injEq]
        refine ⟨by rw [h1], by rw [h2], ?_⟩
        rw [← h3, toAdd_mul]
      · rintro ⟨⟨RS, D⟩, hRSD, rfl⟩
        obtain ⟨a, bω, rs, δω', hab, hrs, hpair⟩ := hRSD
        obtain ⟨b, ωm⟩ := bω
        obtain ⟨δ', ωs'⟩ := δω'
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        have hsh : reshapeΩ (rs, (δ', ωs')) ∈ reshapeΩ '' foldOutcomesΩ F :=
          ⟨(rs, (δ', ωs')), hrs, rfl⟩
        rw [← reifyΩ_fold_commutes F] at hsh
        obtain ⟨⟨RS₀, D₀⟩, hmem, hagg⟩ := hsh
        refine ⟨((a, ωm.toAdd) ::ₘ RS₀, b * D₀),
          ⟨(a, ωm.toAdd), b, RS₀, D₀, ⟨(a, (b, ωm)), hab, rfl⟩, hmem, rfl⟩, ?_⟩
        simp only [aggregateReified, reshapeΩ] at hagg ⊢
        rw [Prod.mk.injEq] at hagg
        obtain ⟨h1, h2⟩ := hagg
        rw [Prod.mk.injEq] at h2
        obtain ⟨h2, h3⟩ := h2
        simp only [Multiset.map_cons, Multiset.sum_cons, Prod.fst_mul, Prod.snd_mul,
          toAdd_mul, Prod.mk.injEq]
        exact ⟨by rw [h1], by rw [h2], by rw [h3]⟩

/-- Positive grounding: a singleton transactional frontier yields exactly its payload's outcome,
exports included. -/
theorem foldOutcomesΩ_singleton (r₀ : R) (δ₀ : Δ × ExportBag Ω) :
    foldOutcomesΩ [({(r₀, δ₀)} : PayloadΩ R Δ Ω)] = {(({r₀} : Multiset R), δ₀)} := by
  ext x
  simp only [foldOutcomesΩ, foldOutcomes, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, δ, rs, δ', hr, hrs, rfl⟩
    rw [Prod.mk.injEq] at hr hrs
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨rfl, rfl⟩ := hrs
    simp
  · rintro rfl
    exact ⟨r₀, δ₀, 0, 1, rfl, rfl, by simp⟩

/-- A concrete transactional round: one payload exporting an owned resource. -/
example :
    foldOutcomesΩ [({((), (2, Multiplicative.ofAdd ({true} : Multiset Bool)))} :
        PayloadΩ Unit ℕ Bool)] =
      {(({()} : Multiset Unit), (2, Multiplicative.ofAdd ({true} : Multiset Bool)))} :=
  foldOutcomesΩ_singleton _ _

/-- **Exports are semantically real** (the no-go-3 content): two payloads with identical
result/delta projections but different owned exports are distinguished after reification — outcome
objects without exports are too coarse for transactional rhometta. -/
example :
    ∃ p₁ p₂ : PayloadΩ Unit ℕ Bool,
      (fun o : Unit × (ℕ × ExportBag Bool) => (o.1, o.2.1)) '' p₁ =
        (fun o : Unit × (ℕ × ExportBag Bool) => (o.1, o.2.1)) '' p₂ ∧
      reifyΩ '' p₁ ≠ reifyΩ '' p₂ := by
  refine ⟨{((), (1, Multiplicative.ofAdd ({true} : Multiset Bool)))},
          {((), (1, Multiplicative.ofAdd ({false} : Multiset Bool)))}, ?_, ?_⟩
  · simp [Set.image_singleton]
  · simp only [Set.image_singleton, reifyΩ, ne_eq, Set.singleton_eq_singleton_iff]
    intro h
    rw [Prod.mk.injEq] at h
    have := h.1
    rw [Prod.mk.injEq] at this
    have hbag := this.2
    simp only [toAdd_ofAdd] at hbag
    exact absurd (Multiset.singleton_inj.mp hbag) (by decide)

end OwnedExports

/-! ## Event layer — the ⊔/`;` boundary vocabulary (events, compatibility, matchings)

An `EventSkeleton` is a COMM candidate: which output occurrence and which input occurrence it
would consume (as frontier indices), and the transactional payload it would run.  `Compatible` is
the MODEL-level relation — distinct consumed occurrences and disjoint export identities.  It is
deliberately weaker than the engine's macro side conditions (quiet continuations, copy-stable
results, unique matching): in the model, payload non-interference is structural, so bare
compatibility carries the abstract theorems; the engine conditions enter only as explicit
hypotheses of the engine-facing corollary.

A matching is a pairwise-compatible selection of events fired together as one round; `MatchOf` is
ALL compatible matchings over an enabled set — including the empty and singleton ones, so the
exact one-redex reducer embeds as the finest refinement and every concrete scheduler is a
refinement of this one base.

The two no-go theorems pin the boundary the round/run layers must respect:
`contention_requires_choice` — a contended enabled set is represented by NO single fold, so a
one-round semantics must branch over matchings (additive choice ⊔); and
`chaining_not_single_round` — one-round folds only produce results offered by enabled payloads,
so an outcome enabled only by a *later* COMM needs sequential closure (`;`).  The same witnesses
are pinned operationally by the race/chaining theorems in `Engine.lean` and at runtime by the
`eval:contended-pair` / `eval:chained-two-round` bridge fixtures. -/
section EventLayer

variable {R Δ Ω : Type*}

/-- A COMM candidate: the output/input occurrences it consumes (frontier indices) and the
transactional payload fired at the rendezvous. -/
structure EventSkeleton (R Δ Ω : Type*) where
  sendIdx : ℕ
  recvIdx : ℕ
  payload : PayloadΩ R Δ Ω

/-- The owned-export identities an event's payload can produce. -/
def EventSkeleton.exports (e : EventSkeleton R Δ Ω) : Set Ω :=
  { ω | ∃ o ∈ e.payload, ω ∈ ((o.2.2 : ExportBag Ω).toAdd : Multiset Ω) }

/-- Model-level compatibility: distinct consumed occurrences (no shared linear send or receive)
and disjoint export identities.  Deliberately weaker than the engine's macro conditions — see the
section header. -/
structure Compatible (e₁ e₂ : EventSkeleton R Δ Ω) : Prop where
  send_ne : e₁.sendIdx ≠ e₂.sendIdx
  recv_ne : e₁.recvIdx ≠ e₂.recvIdx
  exports_disjoint : Disjoint e₁.exports e₂.exports

theorem Compatible.symm {e₁ e₂ : EventSkeleton R Δ Ω} (h : Compatible e₁ e₂) :
    Compatible e₂ e₁ :=
  ⟨h.send_ne.symm, h.recv_ne.symm, h.exports_disjoint.symm⟩

/-- Compatibility is irreflexive: an event would consume its own send twice. -/
theorem not_compatible_self (e : EventSkeleton R Δ Ω) : ¬Compatible e e :=
  fun h => h.send_ne rfl

/-- Contention: two events consuming the same linear send are incompatible. -/
theorem not_compatible_of_shared_send {e₁ e₂ : EventSkeleton R Δ Ω}
    (h : e₁.sendIdx = e₂.sendIdx) : ¬Compatible e₁ e₂ :=
  fun hc => hc.send_ne h

/-- A matching: a pairwise-compatible selection of events, fired together as one round.  Carried
as a list (the fold's native shape); order is irrelevant by `foldOutcomesΩ_perm`, and pairwise
compatibility forces distinctness via `not_compatible_self`. -/
def IsMatching (M : List (EventSkeleton R Δ Ω)) : Prop :=
  M.Pairwise Compatible

/-- ALL compatible matchings over an enabled set — including `[]` and singletons, so the exact
one-redex reducer embeds as the finest refinement of this one base relation. -/
def MatchOf (E : Set (EventSkeleton R Δ Ω)) : Set (List (EventSkeleton R Δ Ω)) :=
  { M | (∀ e ∈ M, e ∈ E) ∧ IsMatching M }

/-- The payloads a matching fires. -/
def matchingPayloads (M : List (EventSkeleton R Δ Ω)) : List (PayloadΩ R Δ Ω) :=
  M.map (·.payload)

@[simp] theorem nil_mem_matchOf (E : Set (EventSkeleton R Δ Ω)) : [] ∈ MatchOf E :=
  ⟨by simp, List.Pairwise.nil⟩

/-- Singletons are matchings: the exact one-redex step is a legal round. -/
theorem singleton_mem_matchOf {E : Set (EventSkeleton R Δ Ω)} {e : EventSkeleton R Δ Ω}
    (he : e ∈ E) : [e] ∈ MatchOf E :=
  ⟨by simpa using he, List.pairwise_singleton _ _⟩

/-- Sub-selections of a matching are matchings: the base is closed under sub-rounds. -/
theorem matchOf_sublist {E : Set (EventSkeleton R Δ Ω)} {M M' : List (EventSkeleton R Δ Ω)}
    (hM : M ∈ MatchOf E) (hsub : List.Sublist M' M) : M' ∈ MatchOf E :=
  ⟨fun e he => hM.1 e (hsub.subset he), hM.2.sublist hsub⟩

/-- In a contended pair (shared linear send), every matching fires at most one event. -/
theorem matchOf_length_le_one_of_shared_send {e₁ e₂ : EventSkeleton R Δ Ω}
    (hsend : e₁.sendIdx = e₂.sendIdx) :
    ∀ M ∈ MatchOf {e₁, e₂}, M.length ≤ 1 := by
  rintro M ⟨hmem, hpair⟩
  match M with
  | [] => simp
  | [_] => simp
  | a :: b :: rest =>
    exfalso
    have hcab : Compatible a b := (List.pairwise_cons.mp hpair).1 b (by simp)
    have ha := hmem a (by simp)
    have hb := hmem b (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    have hsame : a.sendIdx = b.sendIdx := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        first | rfl | exact hsend | exact hsend.symm
    exact not_compatible_of_shared_send hsame hcab

variable [CommMonoid Δ]

/-- Every outcome of a frontier carries exactly one result per fired payload. -/
theorem foldOutcomes_card {F : List (Payload R Δ)} :
    ∀ x ∈ foldOutcomes F, x.1.card = F.length := by
  induction F with
  | nil =>
      rintro x hx
      simp only [foldOutcomes, Set.mem_singleton_iff] at hx
      subst hx; simp
  | cons p F ih =>
      rintro x ⟨r, δ, rs, δ', _, hrs, rfl⟩
      simp [ih (rs, δ') hrs]

/-- A frontier of nonempty payloads has a nonempty outcome set. -/
theorem foldOutcomes_nonempty {F : List (Payload R Δ)} (h : ∀ p ∈ F, p.Nonempty) :
    (foldOutcomes F).Nonempty := by
  induction F with
  | nil => exact ⟨(0, 1), rfl⟩
  | cons p F ih =>
      obtain ⟨⟨r, δ⟩, hrδ⟩ := h p (by simp)
      obtain ⟨⟨rs, δ'⟩, hrs⟩ := ih (fun q hq => h q (by simp [hq]))
      exact ⟨(r ::ₘ rs, δ * δ'), ⟨r, δ, rs, δ', hrδ, hrs, rfl⟩⟩

/-- **Provenance**: every result in a round outcome is offered by one of the fired payloads. -/
theorem foldOutcomes_results_mem {F : List (Payload R Δ)} :
    ∀ x ∈ foldOutcomes F, ∀ r ∈ x.1, ∃ p ∈ F, ∃ δ, (r, δ) ∈ p := by
  induction F with
  | nil =>
      rintro x hx r hr
      simp only [foldOutcomes, Set.mem_singleton_iff] at hx
      subst hx; simp at hr
  | cons p F ih =>
      rintro x ⟨r₀, δ₀, rs, δ', hr₀, hrs, rfl⟩ r hr
      rcases Multiset.mem_cons.mp hr with rfl | hr
      · exact ⟨p, by simp, δ₀, hr₀⟩
      · obtain ⟨q, hq, δ, hmem⟩ := ih (rs, δ') hrs r hr
        exact ⟨q, by simp [hq], δ, hmem⟩

/-- **No-go: contention requires choice (⊔).**  When two enabled events contend for the same
linear send, the raw fold over BOTH is the fold of NO legal matching: every matching of the
contended pair fires at most one event (outcomes carry ≤ 1 result), while the raw fold's outcomes
carry two.  A one-round semantics must branch over matchings — additive choice — rather than fold
the enabled set.  Operational echo: `Engine.lean` race theorem; runtime echo: the
`eval:contended-pair` bridge fixture. -/
theorem contention_requires_choice {e₁ e₂ : EventSkeleton R Δ Ω}
    (hsend : e₁.sendIdx = e₂.sendIdx)
    (h₁ : e₁.payload.Nonempty) (h₂ : e₂.payload.Nonempty) :
    ∀ M ∈ MatchOf {e₁, e₂},
      foldOutcomesΩ (matchingPayloads M) ≠ foldOutcomesΩ [e₁.payload, e₂.payload] := by
  rintro M hM heq
  have hlen : M.length ≤ 1 := matchOf_length_le_one_of_shared_send hsend M hM
  obtain ⟨x, hx⟩ : (foldOutcomesΩ [e₁.payload, e₂.payload]).Nonempty :=
    foldOutcomes_nonempty (by
      rintro p hp
      rcases List.mem_pair.mp hp with rfl | rfl
      · exact h₁
      · exact h₂)
  have hc2 : x.1.card = 2 := foldOutcomes_card x hx
  rw [← heq] at hx
  have hc1 : x.1.card = (matchingPayloads M).length := foldOutcomes_card x hx
  rw [matchingPayloads, List.length_map] at hc1
  omega

/-- **No-go: chaining requires sequence (`;`).**  A one-round fold over an enabled set only
produces results offered by the enabled payloads (provenance).  So an outcome whose result is
offered by NO initially-enabled payload — e.g. one enabled only after a first COMM exposes a new
send — is unreachable in any single round, whichever matching fires: reaching it requires
sequential closure of rounds.  Operational echo: `Engine.lean` two-step chaining theorem; runtime
echo: the `eval:chained-two-round` bridge fixture. -/
theorem chaining_not_single_round {E : Set (EventSkeleton R Δ Ω)} {target : R}
    (hno : ∀ e ∈ E, ∀ o ∈ e.payload, o.1 ≠ target) :
    ∀ M ∈ MatchOf E, ∀ x ∈ foldOutcomesΩ (matchingPayloads M), target ∉ x.1 := by
  rintro M ⟨hmem, _⟩ x hx htgt
  obtain ⟨p, hp, δ, hpδ⟩ := foldOutcomes_results_mem x hx target htgt
  obtain ⟨e, heM, rfl⟩ := List.mem_map.mp hp
  exact absurd rfl (hno e (hmem e heM) (target, δ) hpδ)

/-- Concrete contended pair: one send (occurrence 0), two receivers — no single fold represents
the round. -/
example :
    ∀ M ∈ MatchOf {(⟨0, 0, {(true, (1, 1))}⟩ : EventSkeleton Bool ℕ Empty),
                   (⟨0, 1, {(false, (1, 1))}⟩ : EventSkeleton Bool ℕ Empty)},
      foldOutcomesΩ (matchingPayloads M) ≠
        foldOutcomesΩ [{(true, (1, 1))}, {(false, (1, 1))}] :=
  contention_requires_choice rfl ⟨_, rfl⟩ ⟨_, rfl⟩

/-- Concrete chained witness: the only enabled payload offers `false`; the `true`-producing event
exists but is not yet enabled — no single round reaches `true`. -/
example :
    ∀ M ∈ MatchOf {(⟨0, 0, {(false, (1, 1))}⟩ : EventSkeleton Bool ℕ Empty)},
      ∀ x ∈ foldOutcomesΩ (matchingPayloads M), true ∉ x.1 :=
  chaining_not_single_round (by
    rintro e he o ho
    simp only [Set.mem_singleton_iff] at he
    subst he
    simp only [Set.mem_singleton_iff] at ho
    subst ho
    simp)

/-- Membership in a one-payload fold: exactly the payload's outcomes, singleton-wrapped. -/
theorem mem_foldOutcomes_singleton {p : Payload R Δ} {x : Multiset R × Δ} :
    x ∈ foldOutcomes [p] ↔ ∃ o ∈ p, x = ({o.1}, o.2) := by
  simp only [foldOutcomes, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, δ, rs, δ', hr, hrs, rfl⟩
    rw [Prod.mk.injEq] at hrs
    obtain ⟨rfl, rfl⟩ := hrs
    exact ⟨(r, δ), hr, by simp⟩
  · rintro ⟨⟨r, δ⟩, hr, rfl⟩
    exact ⟨r, δ, 0, 1, hr, rfl, by simp⟩

/-- Folds split over frontier concatenation: an outcome of `F₁ ++ F₂` is the pointwise merge of
an outcome of each part. -/
theorem mem_foldOutcomes_append {F₁ F₂ : List (Payload R Δ)} {x : Multiset R × Δ} :
    x ∈ foldOutcomes (F₁ ++ F₂) ↔
      ∃ x₁ ∈ foldOutcomes F₁, ∃ x₂ ∈ foldOutcomes F₂, x = (x₁.1 + x₂.1, x₁.2 * x₂.2) := by
  induction F₁ generalizing x with
  | nil =>
      simp only [List.nil_append, foldOutcomes, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact ⟨(0, 1), rfl, x, hx, by simp⟩
      · rintro ⟨x₁, hx₁, x₂, hx₂, rfl⟩
        subst hx₁
        simpa using hx₂
  | cons p F₁ ih =>
      simp only [List.cons_append, mem_foldOutcomes_cons]
      constructor
      · rintro ⟨r, δ, rs, δ', hr, hrs, rfl⟩
        obtain ⟨x₁, hx₁, x₂, hx₂, heq⟩ := ih.mp hrs
        rw [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨(r ::ₘ x₁.1, δ * x₁.2), ⟨r, δ, x₁.1, x₁.2, hr, hx₁, rfl⟩, x₂, hx₂, by
          simp [mul_assoc]⟩
      · rintro ⟨x₁, ⟨r, δ, rs, δ', hr, hrs, rfl⟩, x₂, hx₂, rfl⟩
        exact ⟨r, δ, rs + x₂.1, δ' * x₂.2, hr, ih.mpr ⟨(rs, δ'), hrs, x₂, hx₂, rfl⟩, by
          simp [mul_assoc]⟩

omit [CommMonoid Δ] in
/-- Matchings are duplicate-free: pairwise compatibility is irreflexive. -/
theorem IsMatching.nodup {M : List (EventSkeleton R Δ Ω)} (h : IsMatching M) : M.Nodup := by
  induction M with
  | nil => exact List.nodup_nil
  | cons e M ih =>
      rcases List.pairwise_cons.mp h with ⟨hhead, htail⟩
      exact List.nodup_cons.mpr
        ⟨fun hmem => not_compatible_self e (hhead e hmem), ih htail⟩

/-! ### B4 — the round layer (static): choice over compatible matchings -/

/-- One-round outcomes of an enabled set: additive choice (⊔) over ALL compatible matchings, each
interpreted by the commuting ⊗-fold.  This is where contention becomes branching instead of an
impossible joint firing. -/
def roundOutcomes (E : Set (EventSkeleton R Δ Ω)) : Set (Multiset R × (Δ × ExportBag Ω)) :=
  ⋃ M ∈ MatchOf E, foldOutcomesΩ (matchingPayloads M)

/-- **The exact one-redex reducer is the finest refinement**: every single enabled event's fold
contributes to the round. -/
theorem singleton_step_embeds {E : Set (EventSkeleton R Δ Ω)} {e : EventSkeleton R Δ Ω}
    (he : e ∈ E) : foldOutcomesΩ [e.payload] ⊆ roundOutcomes E := fun _ hx =>
  Set.mem_biUnion (singleton_mem_matchOf he) hx

/-- **Collapse on an independent frontier**: when a selection of enabled events is pairwise
compatible, the full ⊗-fold over it is one of the round's branches. -/
theorem independent_unique_matching_collapses_to_fold {E : Set (EventSkeleton R Δ Ω)}
    {L : List (EventSkeleton R Δ Ω)} (hmem : ∀ e ∈ L, e ∈ E) (hpair : IsMatching L) :
    foldOutcomesΩ (matchingPayloads L) ⊆ roundOutcomes E := fun _ hx =>
  Set.mem_biUnion (⟨hmem, hpair⟩ : L ∈ MatchOf E) hx

/-- **Choice is semantically load-bearing** (corollary of the contention no-go): the round of a
contended pair never fires both events jointly — its outcomes carry at most one result — so it is
NOT the raw two-event fold, whose outcomes all carry two. -/
theorem roundOutcomes_ne_rawFold {e₁ e₂ : EventSkeleton R Δ Ω}
    (hsend : e₁.sendIdx = e₂.sendIdx)
    (h₁ : e₁.payload.Nonempty) (h₂ : e₂.payload.Nonempty) :
    roundOutcomes {e₁, e₂} ≠ foldOutcomesΩ [e₁.payload, e₂.payload] := by
  intro heq
  obtain ⟨x, hx⟩ : (foldOutcomesΩ [e₁.payload, e₂.payload]).Nonempty :=
    foldOutcomes_nonempty (by
      rintro p hp
      rcases List.mem_pair.mp hp with rfl | rfl
      · exact h₁
      · exact h₂)
  have hc2 : x.1.card = 2 := foldOutcomes_card x hx
  rw [← heq] at hx
  obtain ⟨_, ⟨M, rfl⟩, _, ⟨hM, rfl⟩, hxM⟩ := hx
  have hlen := matchOf_length_le_one_of_shared_send hsend M hM
  have hc1 : x.1.card = (matchingPayloads M).length := foldOutcomes_card x hxM
  rw [matchingPayloads, List.length_map] at hc1
  omega

end EventLayer

/-! ## Run layer — sequential closure of rounds and the two crowns

`EventSystem` is the abstract transactional machine: states expose enabled COMM candidates;
firing one event advances the state.  Its single law, `enabled_persist`, is the MODEL-structural
form of transactional non-interference: a compatible sibling survives a firing.  Payload outcome
sets are data attached to skeletons, so "copy-stable results" and "transactional payload
isolation" have no separate content at this layer — they are what makes an ENGINE step
instantiate this structure at all, and they are discharged at the operational bridge, not assumed
here.  Likewise the owned-export renaming obligation vanishes at this layer: exports are data
merged by bag union, so serializing a round needs no identity bookkeeping — fresh-identity
generation is an operational-bridge concern.

`runOutcomes` is the fuel-indexed sequential closure of rounds under a *policy* (which matchings
may fire): `singletonPol` is the exact one-redex reducer, `allPol` the free all-matchings base.

**Crown 1**, `round_granularity_independence`: the two closures reach exactly the same
configurations — bigger compatible rounds add nothing and lose nothing.  This is a statement
about the MODEL; citing it as an engine guarantee without Crown 2 is precisely the overclaim this
file is structured to prevent.

**Crown 2**, `macro_collapse_corollary`: under the explicit `QuietFrontier` hypotheses mirroring
the engine's macro side conditions — `matching` (no alternative pairing), `complete` (the macro
fires the whole frontier), `quiet_consume` (linear consumption and no new enablement: quiet
continuations) — the macro's one-shot outcome set IS the quiescent may-set of the full closure.
Each hypothesis corresponds to a C-side check in the correspondence table of the two-lane TODO
(docs/plans 2026-06-11); the conditions with no formal content here (copy-stability, payload
isolation) are exactly the engine's instance-hood obligations. -/
section RunLayer

variable {R Δ Ω S : Type*} [CommMonoid Δ]

/-- An abstract transactional event system: states expose enabled COMM candidates; firing one
event advances the state.  `enabled_persist` is the model-structural form of transactional
non-interference: a compatible sibling survives a firing. -/
structure EventSystem (R Δ Ω : Type*) (S : Type*) where
  enabled : S → Set (EventSkeleton R Δ Ω)
  fireOne : S → EventSkeleton R Δ Ω → S
  enabled_persist : ∀ s e e', e ∈ enabled s → e' ∈ enabled s → Compatible e' e →
    e' ∈ enabled (fireOne s e)

/-- Fire a matching's events in list order (the reference serialization). -/
def EventSystem.fireMany (sys : EventSystem R Δ Ω S) (s : S)
    (M : List (EventSkeleton R Δ Ω)) : S :=
  M.foldl sys.fireOne s

omit [CommMonoid Δ] in
@[simp] theorem EventSystem.fireMany_nil (sys : EventSystem R Δ Ω S) (s : S) :
    sys.fireMany s [] = s := rfl

omit [CommMonoid Δ] in
@[simp] theorem EventSystem.fireMany_cons (sys : EventSystem R Δ Ω S) (s : S)
    (e : EventSkeleton R Δ Ω) (M : List (EventSkeleton R Δ Ω)) :
    sys.fireMany s (e :: M) = sys.fireMany (sys.fireOne s e) M := rfl

omit [CommMonoid Δ] in
theorem EventSystem.fireMany_append (sys : EventSystem R Δ Ω S) (s : S)
    (L M : List (EventSkeleton R Δ Ω)) :
    sys.fireMany s (L ++ M) = sys.fireMany (sys.fireMany s L) M :=
  List.foldl_append

/-- A configuration: state plus accumulated observable (results, merged delta and exports). -/
abbrev Config (R Δ Ω S : Type*) := S × (Multiset R × (Δ × ExportBag Ω))

/-- Merge accumulated observables: results append, deltas and export bags multiply. -/
def accMul (x y : Multiset R × (Δ × ExportBag Ω)) : Multiset R × (Δ × ExportBag Ω) :=
  (x.1 + y.1, x.2 * y.2)

theorem accMul_assoc (x y z : Multiset R × (Δ × ExportBag Ω)) :
    accMul (accMul x y) z = accMul x (accMul y z) := by
  simp [accMul, add_assoc, mul_assoc]

@[simp] theorem accMul_one (x : Multiset R × (Δ × ExportBag Ω)) :
    accMul x (0, 1) = x := by
  simp [accMul]

omit [CommMonoid Δ] in
/-- Firing one event of a matching keeps the rest a matching of the new state — the persistence
law, in the form the serialization induction consumes. -/
theorem matchOf_tail_fireOne (sys : EventSystem R Δ Ω S) {s : S} {e : EventSkeleton R Δ Ω}
    {M : List (EventSkeleton R Δ Ω)} (h : (e :: M) ∈ MatchOf (sys.enabled s)) :
    M ∈ MatchOf (sys.enabled (sys.fireOne s e)) := by
  obtain ⟨hmem, hpair⟩ := h
  rcases List.pairwise_cons.mp hpair with ⟨hhead, htail⟩
  refine ⟨fun a ha => ?_, htail⟩
  exact sys.enabled_persist s e a (hmem e (by simp)) (hmem a (by simp [ha]))
    ((hhead a ha).symm)

/-- One round under a policy: fire a permitted matching of the enabled set, in list order,
accumulating one of its ⊗-fold outcomes. -/
inductive RoundStep (sys : EventSystem R Δ Ω S)
    (pol : List (EventSkeleton R Δ Ω) → Prop) :
    Config R Δ Ω S → Config R Δ Ω S → Prop
  | fire {s : S} {acc : Multiset R × (Δ × ExportBag Ω)}
      {M : List (EventSkeleton R Δ Ω)} {x : Multiset R × (Δ × ExportBag Ω)}
      (hpol : pol M) (hM : M ∈ MatchOf (sys.enabled s))
      (hx : x ∈ foldOutcomesΩ (matchingPayloads M)) :
      RoundStep sys pol (s, acc) (sys.fireMany s M, accMul acc x)

/-- The exact policy: one event per round (the one-redex reducer). -/
def singletonPol (M : List (EventSkeleton R Δ Ω)) : Prop := M.length = 1

/-- The free policy: any compatible matching. -/
def allPol (_ : List (EventSkeleton R Δ Ω)) : Prop := True

/-- Fuel-indexed sequential closure: configurations reachable in at most `n` rounds. -/
def runOutcomes (sys : EventSystem R Δ Ω S) (pol : List (EventSkeleton R Δ Ω) → Prop) :
    ℕ → Config R Δ Ω S → Set (Config R Δ Ω S)
  | 0, c => {c}
  | n + 1, c => {c} ∪ ⋃ c' ∈ {c' | RoundStep sys pol c c'}, runOutcomes sys pol n c'

theorem self_mem_runOutcomes (sys : EventSystem R Δ Ω S) (pol) (n : ℕ)
    (c : Config R Δ Ω S) : c ∈ runOutcomes sys pol n c := by
  cases n <;> simp [runOutcomes]

theorem runOutcomes_succ_of_step (sys : EventSystem R Δ Ω S) {pol} {n : ℕ}
    {c d c' : Config R Δ Ω S} (hstep : RoundStep sys pol c d)
    (h : c' ∈ runOutcomes sys pol n d) : c' ∈ runOutcomes sys pol (n + 1) c := by
  simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq]
  exact Or.inr ⟨d, hstep, h⟩

theorem runOutcomes_mono_fuel (sys : EventSystem R Δ Ω S) (pol) :
    ∀ {n : ℕ} {c c' : Config R Δ Ω S},
      c' ∈ runOutcomes sys pol n c → c' ∈ runOutcomes sys pol (n + 1) c := by
  intro n
  induction n with
  | zero =>
      intro c c' h
      rw [Set.mem_singleton_iff.mp h]
      exact self_mem_runOutcomes sys pol 1 c
  | succ n ih =>
      intro c c' h
      simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq] at h
      rcases h with h | ⟨d, hd, hrest⟩
      · rw [Set.mem_singleton_iff.mp h]
        exact self_mem_runOutcomes sys pol (n + 2) c
      · exact runOutcomes_succ_of_step sys hd (ih hrest)

theorem runOutcomes_le (sys : EventSystem R Δ Ω S) (pol) {m k : ℕ} (hmk : m ≤ k) :
    ∀ {c c' : Config R Δ Ω S},
      c' ∈ runOutcomes sys pol m c → c' ∈ runOutcomes sys pol k c := by
  induction hmk with
  | refl => intro c c' h; exact h
  | step _ ih => intro c c' h; exact runOutcomes_mono_fuel sys pol (ih h)

theorem runOutcomes_trans (sys : EventSystem R Δ Ω S) (pol) :
    ∀ {n m : ℕ} {c c' c'' : Config R Δ Ω S},
      c' ∈ runOutcomes sys pol n c → c'' ∈ runOutcomes sys pol m c' →
      c'' ∈ runOutcomes sys pol (n + m) c := by
  intro n
  induction n with
  | zero =>
      intro m c c' c'' h h'
      rw [Set.mem_singleton_iff.mp h] at h'
      exact runOutcomes_le sys pol (by omega) h'
  | succ n ih =>
      intro m c c' c'' h h'
      simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq] at h
      rcases h with h | ⟨d, hd, hrest⟩
      · rw [Set.mem_singleton_iff.mp h] at h'
        exact runOutcomes_le sys pol (by omega) h'
      · have heq : n + 1 + m = (n + m) + 1 := by omega
        rw [heq]
        exact runOutcomes_succ_of_step sys hd (ih hrest h')

theorem runOutcomes_mono_pol (sys : EventSystem R Δ Ω S)
    {pol₁ pol₂ : List (EventSkeleton R Δ Ω) → Prop} (hpol : ∀ M, pol₁ M → pol₂ M) :
    ∀ {n : ℕ} {c c' : Config R Δ Ω S},
      c' ∈ runOutcomes sys pol₁ n c → c' ∈ runOutcomes sys pol₂ n c := by
  intro n
  induction n with
  | zero => intro c c' h; exact h
  | succ n ih =>
      intro c c' h
      simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq] at h
      rcases h with h | ⟨d, hd, hrest⟩
      · rw [Set.mem_singleton_iff.mp h]
        exact self_mem_runOutcomes sys pol₂ (n + 1) c
      · refine runOutcomes_succ_of_step sys ?_ (ih hrest)
        cases hd with
        | fire hp hM hx => exact RoundStep.fire (hpol _ hp) hM hx

/-- **Serialization**: a matching round decomposes into singleton rounds — same final state (the
round's own list order) and same accumulated observable, by the per-payload structure of the
⊗-fold.  Note: no export renaming is needed — exports are data merged by bag union at this layer. -/
theorem singleton_run_of_matching (sys : EventSystem R Δ Ω S) :
    ∀ (M : List (EventSkeleton R Δ Ω)) (s : S) (acc x),
      M ∈ MatchOf (sys.enabled s) → x ∈ foldOutcomesΩ (matchingPayloads M) →
      (sys.fireMany s M, accMul acc x) ∈ runOutcomes sys singletonPol M.length (s, acc)
  | [], s, acc, x, _, hx => by
      simp only [matchingPayloads, List.map_nil, foldOutcomesΩ, foldOutcomes,
        Set.mem_singleton_iff] at hx
      subst hx
      simpa using self_mem_runOutcomes sys singletonPol 0 (s, acc)
  | e :: M, s, acc, x, hM, hx => by
      simp only [matchingPayloads, List.map_cons, foldOutcomesΩ] at hx
      rw [mem_foldOutcomes_cons] at hx
      obtain ⟨r, δω, rs, δω', ho, hrest, rfl⟩ := hx
      have hstep : RoundStep sys singletonPol (s, acc)
          (sys.fireMany s [e], accMul acc ({r}, δω)) :=
        RoundStep.fire (by simp [singletonPol])
          (singleton_mem_matchOf (hM.1 e (by simp)))
          (mem_foldOutcomes_singleton.mpr ⟨(r, δω), ho, rfl⟩)
      have hrest' := singleton_run_of_matching sys M (sys.fireOne s e)
        (accMul acc ({r}, δω)) (rs, δω') (matchOf_tail_fireOne sys hM) hrest
      have hconn : accMul acc (r ::ₘ rs, δω * δω') =
          accMul (accMul acc ({r}, δω)) (rs, δω') := by
        simp only [accMul, Prod.mk.injEq]
        exact ⟨by rw [← Multiset.singleton_add, add_assoc], (mul_assoc _ _ _).symm⟩
      rw [hconn]
      exact runOutcomes_succ_of_step sys hstep hrest'

/-- Any free-policy round decomposes into a singleton run. -/
theorem roundStep_decomposes (sys : EventSystem R Δ Ω S) {c c' : Config R Δ Ω S}
    (h : RoundStep sys allPol c c') :
    ∃ n, c' ∈ runOutcomes sys singletonPol n c := by
  cases h with
  | fire hpol hM hx => exact ⟨_, singleton_run_of_matching sys _ _ _ _ hM hx⟩

/-- **Crown 1 — round-granularity independence (abstract).**  The all-matchings closure and the
singleton-only closure reach exactly the same configurations: bigger compatible rounds add
nothing and lose nothing.  This is a statement about the MODEL — payload non-interference is
structural here (payload outcome sets are fixed data, and `enabled_persist` is assumed) — and it
must NOT be cited as an engine guarantee on its own: the engine instantiates it only under the
macro side conditions, which is `macro_collapse_corollary` below. -/
theorem round_granularity_independence (sys : EventSystem R Δ Ω S) (c : Config R Δ Ω S) :
    {c' | ∃ n, c' ∈ runOutcomes sys allPol n c} =
    {c' | ∃ n, c' ∈ runOutcomes sys singletonPol n c} := by
  ext c'
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing c with
    | zero => exact ⟨0, hn⟩
    | succ n ih =>
        simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq] at hn
        rcases hn with h | ⟨d, hd, hrest⟩
        · exact ⟨0, h⟩
        · obtain ⟨m₁, h₁⟩ := roundStep_decomposes sys hd
          obtain ⟨m₂, h₂⟩ := ih d hrest
          exact ⟨m₁ + m₂, runOutcomes_trans sys singletonPol h₁ h₂⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, runOutcomes_mono_pol sys (fun _ _ => trivial) hn⟩

/-- Quiescent corollary of Crown 1: the quiescent may-sets of the two closures agree. -/
theorem quiescent_granularity_independence (sys : EventSystem R Δ Ω S)
    (c : Config R Δ Ω S) :
    {c' | (∃ n, c' ∈ runOutcomes sys allPol n c) ∧ sys.enabled c'.1 = ∅} =
    {c' | (∃ n, c' ∈ runOutcomes sys singletonPol n c) ∧ sys.enabled c'.1 = ∅} := by
  have h := Set.ext_iff.mp (round_granularity_independence sys c)
  ext c'
  simp only [Set.mem_setOf_eq] at h ⊢
  exact ⟨fun ⟨a, b⟩ => ⟨(h c').mp a, b⟩, fun ⟨a, b⟩ => ⟨(h c').mpr a, b⟩⟩

/-- **The engine macro side conditions, as explicit model hypotheses.**  Each field corresponds
to a C-side check (correspondence table, docs/plans 2026-06-11): `matching` ↔ keywise at-most-one
pairing (no contention); `complete` ↔ the macro fires the whole frontier; `quiet_consume` ↔ quiet
continuations + linear consumption (fired events leave, nothing new is exposed, compatible
siblings persist — one equation).  Copy-stable results and transactional payload isolation have
no separate content at this layer (payload outcome sets are fixed data on skeletons); they are
the engine's instance-hood obligations, discharged at the operational bridge. -/
structure QuietFrontier (sys : EventSystem R Δ Ω S) (s : S)
    (M : List (EventSkeleton R Δ Ω)) : Prop where
  matching : M ∈ MatchOf (sys.enabled s)
  complete : ∀ e ∈ sys.enabled s, e ∈ M
  quiet_consume : ∀ L : List (EventSkeleton R Δ Ω), L.Nodup → (∀ e ∈ L, e ∈ M) →
    sys.enabled (sys.fireMany s L) = {e | e ∈ sys.enabled s ∧ e ∉ L}

/-- Shape invariant of singleton runs under a quiet frontier: every reachable configuration is
"some duplicate-free part `L'` of the frontier fired, with a fold outcome of `L'` accumulated". -/
theorem QuietFrontier.singleton_run_shape {sys : EventSystem R Δ Ω S} {s : S}
    {M : List (EventSkeleton R Δ Ω)} (h : QuietFrontier sys s M)
    (acc : Multiset R × (Δ × ExportBag Ω)) :
    ∀ {n : ℕ} {L : List (EventSkeleton R Δ Ω)} {y} {c' : Config R Δ Ω S},
      L.Nodup → (∀ e ∈ L, e ∈ M) → y ∈ foldOutcomesΩ (matchingPayloads L) →
      c' ∈ runOutcomes sys singletonPol n (sys.fireMany s L, accMul acc y) →
      ∃ L' : List (EventSkeleton R Δ Ω), L'.Nodup ∧ (∀ e ∈ L', e ∈ M) ∧
        c'.1 = sys.fireMany s L' ∧
        ∃ y' ∈ foldOutcomesΩ (matchingPayloads L'), c'.2 = accMul acc y' := by
  intro n
  induction n with
  | zero =>
      rintro L y c' hnd hsub hy hc'
      rw [Set.mem_singleton_iff.mp hc']
      exact ⟨L, hnd, hsub, rfl, y, hy, rfl⟩
  | succ n ih =>
      rintro L y c' hnd hsub hy hc'
      simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq] at hc'
      rcases hc' with hc' | ⟨d, hd, hrest⟩
      · rw [Set.mem_singleton_iff.mp hc']
        exact ⟨L, hnd, hsub, rfl, y, hy, rfl⟩
      · cases hd with
        | @fire _ _ M₀ x hpol hM hx =>
          obtain ⟨e, rfl⟩ : ∃ a, M₀ = [a] := by
            rcases M₀ with _ | ⟨a, _ | ⟨b, l⟩⟩
            · exfalso; simp only [singletonPol, List.length_nil] at hpol; omega
            · exact ⟨a, rfl⟩
            · exfalso; simp only [singletonPol, List.length_cons] at hpol; omega
          have he : e ∈ sys.enabled (sys.fireMany s L) := hM.1 e (by simp)
          rw [h.quiet_consume L hnd hsub] at he
          have heM : e ∈ M := h.complete e he.1
          simp only [matchingPayloads, List.map_cons, List.map_nil, foldOutcomesΩ] at hx
          have hLe_nodup : (L ++ [e]).Nodup := by
            refine List.Nodup.append hnd (List.nodup_singleton e) ?_
            intro a haL hae
            exact he.2 ((List.mem_singleton.mp hae) ▸ haL)
          have hLe_sub : ∀ a ∈ L ++ [e], a ∈ M := by
            intro a ha
            rcases List.mem_append.mp ha with ha | ha
            · exact hsub a ha
            · rw [List.mem_singleton.mp ha]; exact heM
          have hyx : accMul y x ∈ foldOutcomesΩ (matchingPayloads (L ++ [e])) := by
            simp only [matchingPayloads, List.map_append, List.map_cons, List.map_nil,
              foldOutcomesΩ]
            exact mem_foldOutcomes_append.mpr ⟨y, hy, x, hx, rfl⟩
          have hd_eq : ((sys.fireMany (sys.fireMany s L) [e], accMul (accMul acc y) x) :
              Config R Δ Ω S) =
              (sys.fireMany s (L ++ [e]), accMul acc (accMul y x)) :=
            Prod.ext (sys.fireMany_append s L [e]).symm (accMul_assoc acc y x)
          rw [hd_eq] at hrest
          exact ih hLe_nodup hLe_sub hyx hrest

/-- **Crown 2 — the engine macro-collapse corollary.**  Under the explicit `QuietFrontier`
hypotheses (the engine's macro side conditions), the macro's one-shot outcome set IS the
quiescent may-set of the full all-matchings closure: macro-firing the frontier is semantically
invisible.  This — not Crown 1 alone — is the statement the engine may cite: Crown 1 supplies
the model fact, this corollary supplies the instance-hood under the named conditions. -/
theorem macro_collapse_corollary (sys : EventSystem R Δ Ω S) {s : S}
    {M : List (EventSkeleton R Δ Ω)} (h : QuietFrontier sys s M)
    (acc : Multiset R × (Δ × ExportBag Ω)) :
    {acc' | ∃ s', (∃ n, (s', acc') ∈ runOutcomes sys allPol n (s, acc)) ∧
        sys.enabled s' = ∅} =
    {acc' | ∃ x ∈ foldOutcomesΩ (matchingPayloads M), acc' = accMul acc x} := by
  ext acc'
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨s', ⟨n, hn⟩, hq⟩
    have h1 : ((s', acc') : Config R Δ Ω S) ∈
        {c' | ∃ n, c' ∈ runOutcomes sys singletonPol n (s, acc)} := by
      rw [← round_granularity_independence sys (s, acc)]
      exact ⟨n, hn⟩
    obtain ⟨m, hm⟩ := h1
    have hbase : ((s, acc) : Config R Δ Ω S) =
        (sys.fireMany s [], accMul acc ((0 : Multiset R), (1 : Δ × ExportBag Ω))) := by
      simp
    rw [hbase] at hm
    obtain ⟨L', hnd, hsub, hs', y', hy', hacc'⟩ :=
      h.singleton_run_shape acc List.nodup_nil (by simp) rfl hm
    have hempty : {e | e ∈ sys.enabled s ∧ e ∉ L'} = (∅ : Set (EventSkeleton R Δ Ω)) := by
      rw [← h.quiet_consume L' hnd hsub, ← hs', hq]
    have hML' : ∀ e ∈ M, e ∈ L' := by
      intro e heM
      by_contra hnot
      have : e ∈ {e | e ∈ sys.enabled s ∧ e ∉ L'} := ⟨h.matching.1 e heM, hnot⟩
      rw [hempty] at this
      exact this
    have hperm : L'.Perm M :=
      (hnd.subperm hsub).antisymm ((h.matching.2.nodup).subperm hML')
    have hfold : foldOutcomesΩ (matchingPayloads L') = foldOutcomesΩ (matchingPayloads M) :=
      foldOutcomesΩ_perm (hperm.map _)
    exact ⟨y', hfold ▸ hy', hacc'⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨sys.fireMany s M, ⟨1, ?_⟩, ?_⟩
    · exact runOutcomes_succ_of_step sys (RoundStep.fire trivial h.matching hx)
        (self_mem_runOutcomes sys allPol 0 _)
    · rw [h.quiet_consume M h.matching.2.nodup (fun _ he => he)]
      ext e
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      exact fun hes => h.complete e hes

end RunLayer

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhometaReduction
