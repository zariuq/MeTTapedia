import Mettapedia.GSLT.Meredith.GSLT
import Mettapedia.GSLT.Dynamics.PathIntegral
import Mettapedia.GSLT.Synthesis.MainConservation
import Mettapedia.GSLT.Dynamics.WeightCost
import Mettapedia.GSLT.Meredith.RhoExample
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

/-!
# Symmetric Cut Presentations

This file isolates the smallest honest interaction layer beneath continued
interactive GSLTs:

- a `SymmetricCutPresentation S` over an existing `GSLT` `S`
- an abstract contact constructor together with left/right introductions
- a one-step contraction kernel
- a generic section out of the quotient by structural equations

The wrapping / cost endofunctor layer belongs on top of this presentation once
cost-accounted terms themselves are formalized in Lean.
-/

namespace Mettapedia.GSLT.Meredith

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

variable {S : GSLT}

/-- A symmetric cut presentation for a fixed GSLT.

The intended reading is:
- `contact` is where two co-introductions meet
- `leftIntro` and `rightIntro` are the two cut-forming introductions
- `contract` performs one interaction and returns the residual pair

This is the interaction core we can state cleanly before adding wrapped terms
and graded cost accounting.
-/
structure SymmetricCutPresentation (S : GSLT) where
  contact : S.Term → S.Term → S.Term
  leftIntro : S.Term → S.Term → S.Term
  rightIntro : S.Term → S.Term → S.Term
  contract : S.Term → S.Term → S.Term → S.Term → S.Term × S.Term

/-- A wrapped term carrying explicit accounting data. -/
structure WrappedTerm (α γ : Type) where
  term : α
  grade : γ

/-- One accounted contraction step on wrapped terms. -/
structure AccountedCutStep (α γ σ : Type) where
  left : WrappedTerm α γ
  right : WrappedTerm α γ
  spent : σ

/-- A first honest continued layer over a symmetric cut presentation.

This stays abstract about the accounting grade while requiring wrapped
contraction to erase back to the underlying cut contraction.
-/
structure ContinuedCutPresentation (S : GSLT) where
  symmetricCut : SymmetricCutPresentation S
  Grade : Type
  Spent : Type
  reprSection : Quotient S.equations → S.Term
  reprSection_spec : ∀ q, Quotient.mk _ (reprSection q) = q
  contractWrapped :
    S.Term → S.Term →
      WrappedTerm S.Term Grade → WrappedTerm S.Term Grade →
        AccountedCutStep S.Term Grade Spent
  contractWrapped_fst_term :
    ∀ chan nm body payload,
      (contractWrapped chan nm body payload).left.term =
        (symmetricCut.contract chan nm body.term payload.term).1
  contractWrapped_snd_term :
    ∀ chan nm body payload,
      (contractWrapped chan nm body payload).right.term =
        (symmetricCut.contract chan nm body.term payload.term).2

/-- A generic computable section of the quotient by structural equations. -/
noncomputable def equationsSection (S : GSLT) : Quotient S.equations → S.Term :=
  Quotient.out

/-- The generic section lands back in the same quotient class. -/
theorem equationsSection_spec (S : GSLT)
    (q : Quotient S.equations) :
    Quotient.mk _ (equationsSection S q) = q := by
  unfold equationsSection
  exact Quotient.out_eq q

/-- Wrapped contraction erases to the underlying cut contraction. -/
theorem contractWrapped_erases (C : ContinuedCutPresentation S)
    (chan nm : S.Term)
    (body payload : WrappedTerm S.Term C.Grade) :
    ((C.contractWrapped chan nm body payload).left.term,
      (C.contractWrapped chan nm body payload).right.term) =
      C.symmetricCut.contract chan nm body.term payload.term := by
  cases body
  cases payload
  simp [C.contractWrapped_fst_term, C.contractWrapped_snd_term]

namespace RhoExample

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

abbrev RhoCostAccount := VectorialAccount Nat 2
abbrev RhoSignature := Multiset Pattern
abbrev RhoTemporalTrace := List RhoSignature

/-- A paper-facing cost ledger with the two monoids kept distinct:

- `spatial` is a commutative signature aggregate
- `temporal` is an ordered stack/trace of consumed signatures
-/
structure RhoLedger where
  spatial : RhoSignature
  temporal : RhoTemporalTrace

@[ext] theorem RhoLedger.ext {a b : RhoLedger}
    (hspatial : a.spatial = b.spatial)
    (htemporal : a.temporal = b.temporal) :
    a = b := by
  cases a
  cases b
  simp_all

namespace RhoLedger

instance : Zero RhoLedger where
  zero := { spatial := 0, temporal := [] }

instance : Add RhoLedger where
  add a b :=
    { spatial := a.spatial + b.spatial
      temporal := a.temporal ++ b.temporal }

instance : AddMonoid RhoLedger where
  zero := 0
  add := (· + ·)
  nsmul := nsmulRec
  zero_add a := by
    apply RhoLedger.ext
    · change (0 : RhoSignature) + a.spatial = a.spatial
      simp
    · change ([] : List RhoSignature) ++ a.temporal = a.temporal
      simp
  add_zero a := by
    apply RhoLedger.ext
    · change a.spatial + (0 : RhoSignature) = a.spatial
      simp
    · change a.temporal ++ ([] : List RhoSignature) = a.temporal
      simp
  add_assoc a b c := by
    apply RhoLedger.ext
    · change (a.spatial + b.spatial) + c.spatial = a.spatial + (b.spatial + c.spatial)
      simp [add_assoc]
    · change (a.temporal ++ b.temporal) ++ c.temporal = a.temporal ++ (b.temporal ++ c.temporal)
      simp [List.append_assoc]

def temporalList (ledger : RhoLedger) : List RhoSignature :=
  ledger.temporal

@[simp] theorem temporalList_zero :
    (0 : RhoLedger).temporalList = [] := by
  rfl

@[simp] theorem temporalList_add (left right : RhoLedger) :
    (left + right).temporalList = left.temporalList ++ right.temporalList := by
  rfl

def WellFormedSpent (ledger : RhoLedger) : Prop :=
  ledger.temporalList = [ledger.spatial]

/-- A stronger multi-step invariant: the aggregate spatial signature is exactly
the ordered sum of the temporal spent cells. -/
def TraceCoherent (ledger : RhoLedger) : Prop :=
  ledger.spatial = ledger.temporalList.sum

@[simp] theorem traceCoherent_zero :
    TraceCoherent (0 : RhoLedger) := by
  rfl

@[simp] theorem traceCoherent_add {left right : RhoLedger}
    (hleft : TraceCoherent left) (hright : TraceCoherent right) :
    TraceCoherent (left + right) := by
  dsimp [TraceCoherent] at hleft hright ⊢
  calc
    (left + right).spatial = left.spatial + right.spatial := rfl
    _ = left.temporalList.sum + right.temporalList.sum := by rw [hleft, hright]
    _ = (left.temporalList ++ right.temporalList).sum := by
      simp [List.sum_append]
    _ = (left + right).temporalList.sum := by
      simp [RhoLedger.temporalList_add]

@[simp] theorem wellFormedSpent_traceCoherent {ledger : RhoLedger}
    (h : WellFormedSpent ledger) :
    TraceCoherent ledger := by
  dsimp [WellFormedSpent, TraceCoherent] at h ⊢
  simp [h]

end RhoLedger

def rhoCostUnits (n : Nat) : RhoCostAccount :=
  fun i => if i = 0 then n else 0

@[simp] theorem rhoCostUnits_apply_zero (n : Nat) :
    rhoCostUnits n 0 = n := by
  simp [rhoCostUnits]

@[simp] theorem rhoCostUnits_apply_one (n : Nat) :
    rhoCostUnits n 1 = 0 := by
  simp [rhoCostUnits]

def rhoTemporalUnits (n : Nat) : RhoCostAccount :=
  fun i => if i = 1 then n else 0

@[simp] theorem rhoTemporalUnits_apply_zero (n : Nat) :
    rhoTemporalUnits n 0 = 0 := by
  simp [rhoTemporalUnits]

@[simp] theorem rhoTemporalUnits_apply_one (n : Nat) :
    rhoTemporalUnits n 1 = n := by
  simp [rhoTemporalUnits]

def rhoLedgerShadow (ledger : RhoLedger) : RhoCostAccount :=
  rhoCostUnits ledger.spatial.card + rhoTemporalUnits ledger.temporalList.length

@[simp] theorem rhoLedgerShadow_zero :
    rhoLedgerShadow 0 = 0 := by
  funext i
  fin_cases i
  · change (0 : Nat) = 0
    rfl
  · change (0 : Nat) = 0
    rfl

def rhoSignatureSyntaxWidth : Pattern → Nat
  | .apply "rho:cost:sig-mul" [left, right] =>
      rhoSignatureSyntaxWidth left + rhoSignatureSyntaxWidth right
  | .apply "rho:cost:sig-unit" [] => 0
  | .apply "rho:cost:stack-empty" [] => 0
  | .apply "rho:cost:sig-atom" [_] => 1
  | .apply "rho:cost:stack-cons" [head, tail] =>
      rhoSignatureSyntaxWidth head + rhoSignatureSyntaxWidth tail
  | _ => 1

def rhoSpentSyntaxWidth : Pattern → Nat
  | .apply "rho:cost:stack-empty" [] => 0
  | .apply "rho:cost:stack-cons" [head, tail] =>
      rhoSignatureSyntaxWidth head + rhoSpentSyntaxWidth tail
  | spent => rhoSignatureSyntaxWidth spent

def rhoSpentSyntaxTicks : Pattern → Nat
  | .apply "rho:cost:stack-empty" [] => 0
  | .apply "rho:cost:stack-cons" [_head, tail] =>
      1 + rhoSpentSyntaxTicks tail
  | _ => 1

def rhoSpentSyntaxAccount (spent : Pattern) : RhoCostAccount :=
  rhoCostUnits (rhoSpentSyntaxWidth spent) + rhoTemporalUnits (rhoSpentSyntaxTicks spent)

@[simp] theorem rhoSignatureSyntaxWidth_sig_mul (left right : Pattern) :
    rhoSignatureSyntaxWidth (.apply "rho:cost:sig-mul" [left, right]) =
      rhoSignatureSyntaxWidth left + rhoSignatureSyntaxWidth right := by
  rfl

@[simp] theorem rhoSignatureSyntaxWidth_sig_unit :
    rhoSignatureSyntaxWidth (.apply "rho:cost:sig-unit" []) = 0 := by
  rfl

@[simp] theorem rhoSignatureSyntaxWidth_stack_empty :
    rhoSignatureSyntaxWidth (.apply "rho:cost:stack-empty" []) = 0 := by
  rfl

@[simp] theorem rhoSignatureSyntaxWidth_sig_atom (p : Pattern) :
    rhoSignatureSyntaxWidth (.apply "rho:cost:sig-atom" [p]) = 1 := by
  rfl

@[simp] theorem rhoSpentSyntaxWidth_sig_mul (left right : Pattern) :
    rhoSpentSyntaxWidth (.apply "rho:cost:sig-mul" [left, right]) =
      rhoSignatureSyntaxWidth left + rhoSignatureSyntaxWidth right := by
  rfl

@[simp] theorem rhoSpentSyntaxWidth_stack_empty :
    rhoSpentSyntaxWidth (.apply "rho:cost:stack-empty" []) = 0 := by
  rfl

@[simp] theorem rhoSpentSyntaxWidth_stack_cons (head tail : Pattern) :
    rhoSpentSyntaxWidth (.apply "rho:cost:stack-cons" [head, tail]) =
      rhoSignatureSyntaxWidth head + rhoSpentSyntaxWidth tail := by
  rfl

@[simp] theorem rhoSpentSyntaxTicks_stack_empty :
    rhoSpentSyntaxTicks (.apply "rho:cost:stack-empty" []) = 0 := by
  rfl

@[simp] theorem rhoSpentSyntaxTicks_stack_cons (head tail : Pattern) :
    rhoSpentSyntaxTicks (.apply "rho:cost:stack-cons" [head, tail]) =
      1 + rhoSpentSyntaxTicks tail := by
  rfl

@[simp] theorem rhoSpentSyntaxAccount_apply (spent : Pattern) :
    rhoSpentSyntaxAccount spent =
      rhoCostUnits (rhoSpentSyntaxWidth spent) + rhoTemporalUnits (rhoSpentSyntaxTicks spent) := by
  rfl

@[simp] theorem rhoSpentSyntaxAccount_apply_zero (spent : Pattern) :
    rhoSpentSyntaxAccount spent 0 = rhoSpentSyntaxWidth spent := by
  change (rhoCostUnits (rhoSpentSyntaxWidth spent) 0 + rhoTemporalUnits (rhoSpentSyntaxTicks spent) 0) =
    rhoSpentSyntaxWidth spent
  simp

@[simp] theorem rhoSpentSyntaxAccount_apply_one (spent : Pattern) :
    rhoSpentSyntaxAccount spent 1 = rhoSpentSyntaxTicks spent := by
  change (rhoCostUnits (rhoSpentSyntaxWidth spent) 1 +
      rhoTemporalUnits (rhoSpentSyntaxTicks spent) 1) = rhoSpentSyntaxTicks spent
  simp

@[simp] theorem rhoSpentSyntaxAccount_sig_mul (left right : Pattern) :
    rhoSpentSyntaxAccount (.apply "rho:cost:sig-mul" [left, right]) =
      rhoCostUnits (rhoSignatureSyntaxWidth left + rhoSignatureSyntaxWidth right) + rhoTemporalUnits 1 := by
  simp [rhoSpentSyntaxAccount, rhoSpentSyntaxTicks]

@[simp] theorem rhoSpentSyntaxAccount_stack_cons (head tail : Pattern) :
    rhoSpentSyntaxAccount (.apply "rho:cost:stack-cons" [head, tail]) =
      rhoCostUnits (rhoSignatureSyntaxWidth head + rhoSpentSyntaxWidth tail) +
        rhoTemporalUnits (1 + rhoSpentSyntaxTicks tail) := by
  rfl

/-- Direct Lean signature syntax matching the CeTTa cost surface:
ground atoms, binary signature products, and the internal unit. -/
inductive RhoDirectSignature where
  | unit
  | atom (p : Pattern)
  | mul (left right : RhoDirectSignature)

/-- Direct Lean token-stack syntax matching `rho:cost:stack-empty` /
`rho:cost:stack-cons`. -/
inductive RhoDirectStack where
  | empty
  | cons (sig : RhoDirectSignature) (rest : RhoDirectStack)

/-- A direct signed rho process fragment matching `rho:cost:signed`. -/
structure RhoDirectSigned where
  body : Pattern
  sig : RhoDirectSignature

/-- Direct Lean costed rho terms matching the CeTTa surface:
signed fragments, costed parallel composition, and token stacks. -/
inductive RhoDirectTerm where
  | signed (body : Pattern) (sig : RhoDirectSignature)
  | par (items : List RhoDirectTerm)
  | stack (tokens : RhoDirectStack)

private def rhoSignatureOfList : List Pattern → RhoSignature
  | [] => 0
  | p :: rest => ({p} : RhoSignature) + rhoSignatureOfList rest

def RhoDirectSignature.toSignature : RhoDirectSignature → RhoSignature
  | .unit => 0
  | .atom p => ({p} : RhoSignature)
  | .mul left right => left.toSignature + right.toSignature

def RhoDirectSignature.toPattern : RhoDirectSignature → Pattern
  | .unit => .apply "rho:cost:sig-unit" []
  | .atom p => p
  | .mul left right => .apply "rho:cost:sig-mul" [left.toPattern, right.toPattern]

def RhoDirectSignature.toPublicPattern : RhoDirectSignature → Pattern
  | .unit => .apply "rho:cost:stack-empty" []
  | .atom p => .apply "rho:cost:sig-atom" [p]
  | .mul left right => .apply "rho:cost:sig-mul" [left.toPublicPattern, right.toPublicPattern]

private def RhoDirectSignature.ofPatternList : List Pattern → RhoDirectSignature
  | [] => .unit
  | [p] => .atom p
  | p :: rest => .mul (.atom p) (ofPatternList rest)

noncomputable def RhoDirectSignature.ofSignature (sig : RhoSignature) : RhoDirectSignature :=
  RhoDirectSignature.ofPatternList sig.toList

def RhoDirectSignature.SurfaceLike : RhoDirectSignature → Prop
  | .unit => True
  | .atom p => rhoSignatureSyntaxWidth p = 1
  | .mul left right => left.SurfaceLike ∧ right.SurfaceLike

def RhoDirectStack.toLedger : RhoDirectStack → RhoLedger
  | .empty => 0
  | .cons sig rest =>
      { spatial := sig.toSignature
        temporal := [sig.toSignature] } + rest.toLedger

def RhoDirectStack.toPattern : RhoDirectStack → Pattern
  | .empty => .apply "rho:cost:stack-empty" []
  | .cons sig rest => .apply "rho:cost:stack-cons" [sig.toPattern, rest.toPattern]

def RhoDirectStack.toPublicPattern : RhoDirectStack → Pattern
  | .empty => .apply "rho:cost:stack-empty" []
  | .cons sig rest => .apply "rho:cost:stack-cons" [sig.toPublicPattern, rest.toPublicPattern]

def RhoDirectStack.depth : RhoDirectStack → Nat
  | .empty => 0
  | .cons _ rest => 1 + rest.depth

def RhoDirectStack.append : RhoDirectStack → RhoDirectStack → RhoDirectStack
  | .empty, rest => rest
  | .cons sig rest, tail => .cons sig (append rest tail)

def RhoDirectStack.temporalTrace : RhoDirectStack → RhoTemporalTrace
  | .empty => []
  | .cons sig rest => sig.toSignature :: rest.temporalTrace

def RhoDirectStack.spatialSignature : RhoDirectStack → RhoSignature
  | .empty => 0
  | .cons sig rest => sig.toSignature + rest.spatialSignature

def RhoDirectStack.SurfaceLike : RhoDirectStack → Prop
  | .empty => True
  | .cons sig rest => sig.SurfaceLike ∧ rest.SurfaceLike

def RhoDirectStack.toTerm : RhoDirectStack → RhoDirectTerm :=
  .stack

def RhoDirectSigned.toWrapped (signed : RhoDirectSigned) : WrappedTerm Pattern RhoLedger :=
  { term := signed.body
    grade := { spatial := signed.sig.toSignature, temporal := [] } }

def RhoDirectSigned.toTerm (signed : RhoDirectSigned) : RhoDirectTerm :=
  .signed signed.body signed.sig

noncomputable def RhoDirectSigned.ofWrapped (wrapped : WrappedTerm Pattern RhoLedger) :
    RhoDirectSigned :=
  { body := wrapped.term
    sig := RhoDirectSignature.ofSignature wrapped.grade.spatial }

def RhoDirectTerm.toPattern : RhoDirectTerm → Pattern
  | .signed body sig => .apply "rho:cost:signed" [body, sig.toPattern]
  | .par items => .apply "rho:cost:par" (items.map RhoDirectTerm.toPattern)
  | .stack tokens => tokens.toPattern

noncomputable def RhoDirectStack.ofTrace : RhoTemporalTrace → RhoDirectStack
  | [] => .empty
  | sig :: rest => .cons (RhoDirectSignature.ofSignature sig) (ofTrace rest)

structure RhoDirectCutWitness where
  left : RhoDirectSigned
  right : RhoDirectSigned
  spent : RhoDirectStack

noncomputable def RhoDirectCutWitness.ofAccountedStep
    (step : AccountedCutStep Pattern RhoLedger RhoLedger) : RhoDirectCutWitness :=
  { left := RhoDirectSigned.ofWrapped step.left
    right := RhoDirectSigned.ofWrapped step.right
    spent := RhoDirectStack.ofTrace step.spent.temporalList }

@[simp] theorem rhoSignatureOfList_nil :
    rhoSignatureOfList [] = 0 := by
  rfl

@[simp] theorem rhoSignatureOfList_cons (p : Pattern) (rest : List Pattern) :
    rhoSignatureOfList (p :: rest) = ({p} : RhoSignature) + rhoSignatureOfList rest := by
  rfl

@[simp] theorem RhoDirectSignature_toSignature_unit :
    RhoDirectSignature.toSignature .unit = 0 := by
  rfl

@[simp] theorem RhoDirectSignature_toSignature_atom (p : Pattern) :
    RhoDirectSignature.toSignature (.atom p) = ({p} : RhoSignature) := by
  rfl

@[simp] theorem RhoDirectSignature_toSignature_mul
    (left right : RhoDirectSignature) :
    RhoDirectSignature.toSignature (.mul left right) =
      left.toSignature + right.toSignature := by
  rfl

@[simp] theorem RhoDirectSignature_toPattern_unit :
    RhoDirectSignature.toPattern .unit = .apply "rho:cost:sig-unit" [] := by
  rfl

@[simp] theorem RhoDirectSignature_toPattern_atom (p : Pattern) :
    RhoDirectSignature.toPattern (.atom p) = p := by
  rfl

@[simp] theorem RhoDirectSignature_toPattern_mul
    (left right : RhoDirectSignature) :
    RhoDirectSignature.toPattern (.mul left right) =
      .apply "rho:cost:sig-mul" [left.toPattern, right.toPattern] := by
  rfl

private theorem RhoDirectSignature_toSignature_ofPatternList
    (ps : List Pattern) :
    (RhoDirectSignature.ofPatternList ps).toSignature = rhoSignatureOfList ps := by
  induction ps with
  | nil =>
      simp [RhoDirectSignature.ofPatternList, rhoSignatureOfList]
  | cons p rest ih =>
      cases rest with
      | nil =>
          simp [RhoDirectSignature.ofPatternList, rhoSignatureOfList]
      | cons q rest' =>
          simp [RhoDirectSignature.ofPatternList, rhoSignatureOfList, ih]

private theorem rhoSignatureOfList_eq_coe (ps : List Pattern) :
    rhoSignatureOfList ps = (ps : Multiset Pattern) := by
  induction ps with
  | nil =>
      simp [rhoSignatureOfList]
  | cons p rest ih =>
      simp [rhoSignatureOfList, ih]

private theorem RhoDirectSignature_ofPatternList_surfaceLike
    (ps : List Pattern)
    (hall : ∀ q ∈ ps, rhoSignatureSyntaxWidth q = 1) :
    (RhoDirectSignature.ofPatternList ps).SurfaceLike := by
  induction ps with
  | nil =>
      simp [RhoDirectSignature.ofPatternList, RhoDirectSignature.SurfaceLike]
  | cons p rest ih =>
      cases rest with
      | nil =>
          simp [RhoDirectSignature.ofPatternList, RhoDirectSignature.SurfaceLike, hall p (by simp)]
      | cons q rest' =>
          have hrest : ∀ r ∈ q :: rest', rhoSignatureSyntaxWidth r = 1 := by
            intro r hr
            exact hall r (by simp [hr])
          simp [RhoDirectSignature.ofPatternList, RhoDirectSignature.SurfaceLike,
            hall p (by simp), ih hrest]

@[simp] theorem RhoDirectSignature_toSignature_ofSignature
    (sig : RhoSignature) :
    (RhoDirectSignature.ofSignature sig).toSignature = sig := by
  simpa [RhoDirectSignature.ofSignature] using
    (RhoDirectSignature_toSignature_ofPatternList sig.toList).trans
      (rhoSignatureOfList_eq_coe sig.toList)

theorem RhoDirectSignature_ofSignature_surfaceLike
    (sig : RhoSignature)
    (hall : ∀ q ∈ sig, rhoSignatureSyntaxWidth q = 1) :
    (RhoDirectSignature.ofSignature sig).SurfaceLike := by
  unfold RhoDirectSignature.ofSignature
  apply RhoDirectSignature_ofPatternList_surfaceLike
  intro q hq
  exact hall q (by simpa using hq)

@[simp] theorem RhoDirectStack_toLedger_empty :
    RhoDirectStack.toLedger .empty = 0 := by
  rfl

@[simp] theorem RhoDirectStack_toLedger_cons
    (sig : RhoDirectSignature) (rest : RhoDirectStack) :
    RhoDirectStack.toLedger (.cons sig rest) =
      { spatial := sig.toSignature, temporal := [sig.toSignature] } + rest.toLedger := by
  rfl

@[simp] theorem RhoDirectStack_depth_empty :
    RhoDirectStack.depth .empty = 0 := by
  rfl

@[simp] theorem RhoDirectStack_depth_cons
    (sig : RhoDirectSignature) (rest : RhoDirectStack) :
    RhoDirectStack.depth (.cons sig rest) = 1 + rest.depth := by
  rfl

@[simp] theorem RhoDirectStack_append_empty_left
    (rest : RhoDirectStack) :
    RhoDirectStack.append .empty rest = rest := by
  rfl

@[simp] theorem RhoDirectStack_append_cons
    (sig : RhoDirectSignature) (rest tail : RhoDirectStack) :
    RhoDirectStack.append (.cons sig rest) tail =
      .cons sig (RhoDirectStack.append rest tail) := by
  rfl

@[simp] theorem RhoDirectStack_append_empty_right
    (stack : RhoDirectStack) :
    RhoDirectStack.append stack .empty = stack := by
  induction stack with
  | empty =>
      rfl
  | cons sig rest ih =>
      simp [RhoDirectStack.append, ih]

@[simp] theorem RhoDirectStack_temporalTrace_empty :
    RhoDirectStack.temporalTrace .empty = [] := by
  rfl

@[simp] theorem RhoDirectStack_temporalTrace_cons
    (sig : RhoDirectSignature) (rest : RhoDirectStack) :
    RhoDirectStack.temporalTrace (.cons sig rest) =
      sig.toSignature :: rest.temporalTrace := by
  rfl

@[simp] theorem RhoDirectStack_spatialSignature_empty :
    RhoDirectStack.spatialSignature .empty = 0 := by
  rfl

@[simp] theorem RhoDirectStack_spatialSignature_cons
    (sig : RhoDirectSignature) (rest : RhoDirectStack) :
    RhoDirectStack.spatialSignature (.cons sig rest) =
      sig.toSignature + rest.spatialSignature := by
  rfl

@[simp] theorem RhoDirectStack_toLedger_temporalList
    (stack : RhoDirectStack) :
    (stack.toLedger).temporalList = stack.temporalTrace := by
  induction stack with
  | empty =>
      rfl
  | cons sig rest ih =>
      change [sig.toSignature] ++ rest.toLedger.temporal = sig.toSignature :: rest.temporalTrace
      simpa [RhoLedger.temporalList] using congrArg (List.cons sig.toSignature) ih

@[simp] theorem RhoDirectStack_toLedger_traceCoherent
    (stack : RhoDirectStack) :
    RhoLedger.TraceCoherent stack.toLedger := by
  induction stack with
  | empty =>
      exact RhoLedger.traceCoherent_zero
  | cons sig rest ih =>
      apply RhoLedger.traceCoherent_add
      · change sig.toSignature = ([sig.toSignature] : List RhoSignature).sum
        simp
      · exact ih

@[simp] theorem RhoDirectStack_toLedger_spatial
    (stack : RhoDirectStack) :
    (stack.toLedger).spatial = stack.spatialSignature := by
  induction stack with
  | empty =>
      rfl
  | cons sig rest ih =>
      change sig.toSignature + rest.toLedger.spatial = sig.toSignature + rest.spatialSignature
      simpa using congrArg (fun spatial => sig.toSignature + spatial) ih

@[simp] theorem RhoDirectStack_toLedger_depth_eq_temporalLength
    (stack : RhoDirectStack) :
    stack.depth = (stack.toLedger).temporalList.length := by
  induction stack with
  | empty =>
      rfl
  | cons sig rest ih =>
      calc
        RhoDirectStack.depth (RhoDirectStack.cons sig rest) = (RhoDirectStack.cons sig rest).temporalTrace.length := by
          simp [RhoDirectStack.depth, RhoDirectStack.temporalTrace, ih, Nat.add_comm]
        _ = (RhoDirectStack.toLedger (RhoDirectStack.cons sig rest)).temporalList.length := by
          rw [RhoDirectStack_toLedger_temporalList]

@[simp] theorem RhoDirectStack_toLedger_ofTrace
    (trace : RhoTemporalTrace) :
    (RhoDirectStack.ofTrace trace).toLedger =
      { spatial := trace.sum, temporal := trace } := by
  induction trace with
  | nil =>
      rfl
  | cons sig rest ih =>
      rw [RhoDirectStack.ofTrace, RhoDirectStack.toLedger, ih]
      apply RhoLedger.ext
      · change (RhoDirectSignature.ofSignature sig).toSignature + rest.sum = sig + rest.sum
        simp [RhoDirectSignature_toSignature_ofSignature]
      · change [(RhoDirectSignature.ofSignature sig).toSignature] ++ rest = sig :: rest
        simp [RhoDirectSignature_toSignature_ofSignature]

@[simp] theorem RhoDirectStack_depth_ofTrace
    (trace : RhoTemporalTrace) :
    (RhoDirectStack.ofTrace trace).depth = trace.length := by
  rw [RhoDirectStack_toLedger_depth_eq_temporalLength, RhoDirectStack_toLedger_ofTrace]
  rfl

@[simp] theorem RhoDirectStack_temporalTrace_append
    (left right : RhoDirectStack) :
    (RhoDirectStack.append left right).temporalTrace =
      left.temporalTrace ++ right.temporalTrace := by
  induction left with
  | empty =>
      rfl
  | cons sig rest ih =>
      simp [RhoDirectStack.append, RhoDirectStack.temporalTrace, ih]

@[simp] theorem RhoDirectStack_depth_append
    (left right : RhoDirectStack) :
    (RhoDirectStack.append left right).depth = left.depth + right.depth := by
  induction left with
  | empty =>
      simp only [RhoDirectStack.append, RhoDirectStack.depth, Nat.zero_add]
  | cons sig rest ih =>
      calc
        (RhoDirectStack.append (RhoDirectStack.cons sig rest) right).depth
            = 1 + (RhoDirectStack.append rest right).depth := by
                rfl
        _ = 1 + (rest.depth + right.depth) := by rw [ih]
        _ = (1 + rest.depth) + right.depth := by simp [Nat.add_assoc]
        _ = (RhoDirectStack.cons sig rest).depth + right.depth := by
              simp [RhoDirectStack.depth]

@[simp] theorem RhoDirectStack_spatialSignature_append
    (left right : RhoDirectStack) :
    (RhoDirectStack.append left right).spatialSignature =
      left.spatialSignature + right.spatialSignature := by
  induction left with
  | empty =>
      simp [RhoDirectStack.append, RhoDirectStack.spatialSignature]
  | cons sig rest ih =>
      simp [RhoDirectStack.append, RhoDirectStack.spatialSignature, ih, add_assoc]

@[simp] theorem RhoDirectStack_toLedger_append
    (left right : RhoDirectStack) :
    (RhoDirectStack.append left right).toLedger =
      left.toLedger + right.toLedger := by
  induction left with
  | empty =>
      simp [RhoDirectStack.append, RhoDirectStack.toLedger]
  | cons sig rest ih =>
      simp [RhoDirectStack.append, RhoDirectStack.toLedger, ih, add_assoc]

@[simp] theorem RhoDirectStack_surfaceLike_append
    {left right : RhoDirectStack}
    (hleft : left.SurfaceLike) (hright : right.SurfaceLike) :
    (RhoDirectStack.append left right).SurfaceLike := by
  induction left with
  | empty =>
      simpa [RhoDirectStack.append, RhoDirectStack.SurfaceLike] using hright
  | cons sig rest ih =>
      rcases hleft with ⟨hsig, hrest⟩
      simp [RhoDirectStack.append, RhoDirectStack.SurfaceLike, hsig, ih hrest]

@[simp] theorem RhoDirectStack_ofTrace_append
    (left right : RhoTemporalTrace) :
    RhoDirectStack.ofTrace (left ++ right) =
      RhoDirectStack.append (RhoDirectStack.ofTrace left) (RhoDirectStack.ofTrace right) := by
  induction left with
  | nil =>
      rfl
  | cons sig rest ih =>
      simp [RhoDirectStack.ofTrace, ih]

theorem RhoDirectStack_ofTrace_surfaceLike
    (trace : RhoTemporalTrace)
    (hall : ∀ sig ∈ trace, ∀ q ∈ sig, rhoSignatureSyntaxWidth q = 1) :
    (RhoDirectStack.ofTrace trace).SurfaceLike := by
  induction trace with
  | nil =>
      simp [RhoDirectStack.ofTrace, RhoDirectStack.SurfaceLike]
  | cons sig rest ih =>
      have hrest : ∀ sig' ∈ rest, ∀ q ∈ sig', rhoSignatureSyntaxWidth q = 1 := by
        intro sig' hsig' q hq
        exact hall sig' (by simp [hsig']) q hq
      simp [RhoDirectStack.ofTrace, RhoDirectStack.SurfaceLike,
        RhoDirectSignature_ofSignature_surfaceLike sig (hall sig (by simp)),
        ih hrest]

@[simp] theorem RhoDirectSigned_ofWrapped_body
    (wrapped : WrappedTerm Pattern RhoLedger) :
    (RhoDirectSigned.ofWrapped wrapped).body = wrapped.term := by
  rfl

@[simp] theorem RhoDirectSigned_ofWrapped_signature
    (wrapped : WrappedTerm Pattern RhoLedger) :
    (RhoDirectSigned.ofWrapped wrapped).sig.toSignature = wrapped.grade.spatial := by
  simp [RhoDirectSigned.ofWrapped]

@[simp] theorem RhoDirectSigned_ofWrapped_toWrapped_spatial
    (wrapped : WrappedTerm Pattern RhoLedger) :
    (RhoDirectSigned.ofWrapped wrapped).toWrapped.grade.spatial = wrapped.grade.spatial := by
  simp [RhoDirectSigned.toWrapped]

@[simp] theorem RhoDirectSigned_ofWrapped_toWrapped_term
    (wrapped : WrappedTerm Pattern RhoLedger) :
    (RhoDirectSigned.ofWrapped wrapped).toWrapped.term = wrapped.term := by
  rfl

@[simp] theorem RhoDirectCutWitness_ofAccountedStep_left_body
    (step : AccountedCutStep Pattern RhoLedger RhoLedger) :
    (RhoDirectCutWitness.ofAccountedStep step).left.body = step.left.term := by
  rfl

@[simp] theorem RhoDirectCutWitness_ofAccountedStep_left_signature
    (step : AccountedCutStep Pattern RhoLedger RhoLedger) :
    (RhoDirectCutWitness.ofAccountedStep step).left.sig.toSignature = step.left.grade.spatial := by
  simp [RhoDirectCutWitness.ofAccountedStep]

@[simp] theorem RhoDirectCutWitness_ofAccountedStep_right_body
    (step : AccountedCutStep Pattern RhoLedger RhoLedger) :
    (RhoDirectCutWitness.ofAccountedStep step).right.body = step.right.term := by
  rfl

@[simp] theorem RhoDirectCutWitness_ofAccountedStep_right_signature
    (step : AccountedCutStep Pattern RhoLedger RhoLedger) :
    (RhoDirectCutWitness.ofAccountedStep step).right.sig.toSignature = step.right.grade.spatial := by
  simp [RhoDirectCutWitness.ofAccountedStep]

theorem RhoDirectCutWitness_ofAccountedStep_spent_ledger
    (step : AccountedCutStep Pattern RhoLedger RhoLedger)
    (hcoh : RhoLedger.TraceCoherent step.spent) :
    (RhoDirectCutWitness.ofAccountedStep step).spent.toLedger = step.spent := by
  apply RhoLedger.ext
  · calc
      ((RhoDirectCutWitness.ofAccountedStep step).spent.toLedger).spatial =
          step.spent.temporalList.sum := by
            simp [RhoDirectCutWitness.ofAccountedStep, RhoDirectStack_toLedger_ofTrace]
      _ = step.spent.spatial := by
            simpa [RhoLedger.TraceCoherent] using hcoh.symm
  · simp [RhoDirectCutWitness.ofAccountedStep, RhoDirectStack_toLedger_ofTrace, RhoLedger.temporalList]

@[simp] theorem RhoDirectSignature_toPattern_width_eq_card
    (sig : RhoDirectSignature)
    (h : sig.SurfaceLike) :
    rhoSignatureSyntaxWidth sig.toPattern = sig.toSignature.card := by
  induction sig with
  | unit =>
      simp [RhoDirectSignature.toPattern, RhoDirectSignature.toSignature]
  | atom p =>
      simpa [RhoDirectSignature.toPattern, RhoDirectSignature.toSignature] using! h
  | mul left right ihLeft ihRight =>
      rcases h with ⟨hLeft, hRight⟩
      simp [RhoDirectSignature.toPattern, RhoDirectSignature.toSignature,
        ihLeft hLeft, ihRight hRight, Multiset.card_add]

@[simp] theorem RhoDirectStack_toPattern_ticks_eq_depth
    (stack : RhoDirectStack) :
    rhoSpentSyntaxTicks stack.toPattern = stack.depth := by
  induction stack with
  | empty =>
      simp [RhoDirectStack.toPattern, RhoDirectStack.depth]
  | cons sig rest ih =>
      simp [RhoDirectStack.toPattern, RhoDirectStack.depth, ih]

@[simp] theorem RhoDirectStack_toPattern_width_eq_spatial_card
    (stack : RhoDirectStack)
    (h : stack.SurfaceLike) :
    rhoSpentSyntaxWidth stack.toPattern = stack.spatialSignature.card := by
  induction stack with
  | empty =>
      simp [RhoDirectStack.toPattern, RhoDirectStack.spatialSignature]
  | cons sig rest ih =>
      rcases h with ⟨hsig, hrest⟩
      simp [RhoDirectStack.toPattern, RhoDirectStack.spatialSignature,
        RhoDirectSignature_toPattern_width_eq_card sig hsig, ih hrest, Multiset.card_add]

@[simp] theorem RhoDirectStack_toPattern_account_eq_shadow
    (stack : RhoDirectStack) :
    stack.SurfaceLike →
    rhoSpentSyntaxAccount stack.toPattern = rhoLedgerShadow stack.toLedger := by
  intro h
  funext i
  fin_cases i
  · simp [rhoSpentSyntaxAccount, rhoLedgerShadow,
      RhoDirectStack_toPattern_width_eq_spatial_card stack h,
      RhoDirectStack_toLedger_spatial]
  · rw [rhoSpentSyntaxAccount, rhoLedgerShadow,
      RhoDirectStack_toPattern_width_eq_spatial_card stack h,
      RhoDirectStack_toPattern_ticks_eq_depth,
      RhoDirectStack_toLedger_depth_eq_temporalLength]
    simp

private def rhoSignatureToSpentSyntaxList : List Pattern → Pattern
  | [] => .apply "rho:cost:stack-empty" []
  | [p] => .apply "rho:cost:sig-atom" [p]
  | p :: rest => .apply "rho:cost:sig-mul" [.apply "rho:cost:sig-atom" [p], rhoSignatureToSpentSyntaxList rest]

noncomputable def rhoSignatureToSpentSyntax (sig : RhoSignature) : Pattern :=
  rhoSignatureToSpentSyntaxList sig.toList

noncomputable def rhoTemporalTraceToSpentSyntax : RhoTemporalTrace → Pattern
  | [] => .apply "rho:cost:stack-empty" []
  | sig :: rest =>
      .apply "rho:cost:stack-cons" [rhoSignatureToSpentSyntax sig, rhoTemporalTraceToSpentSyntax rest]

noncomputable def rhoLedgerToSpentSyntax (ledger : RhoLedger) : Pattern :=
  rhoTemporalTraceToSpentSyntax ledger.temporalList

private theorem rhoSignatureToSpentSyntaxList_width_eq_length
    (ps : List Pattern) :
    rhoSignatureSyntaxWidth (rhoSignatureToSpentSyntaxList ps) = ps.length := by
  induction ps with
  | nil =>
      simp [rhoSignatureToSpentSyntaxList]
  | cons p rest ih =>
      cases rest with
      | nil =>
          simp [rhoSignatureToSpentSyntaxList]
      | cons q rest' =>
          simp [rhoSignatureToSpentSyntaxList, ih, Nat.add_left_comm, Nat.add_comm]

private theorem RhoDirectSignature_ofPatternList_toPublicPattern
    (ps : List Pattern) :
    (RhoDirectSignature.ofPatternList ps).toPublicPattern =
      rhoSignatureToSpentSyntaxList ps := by
  induction ps with
  | nil =>
      simp [RhoDirectSignature.ofPatternList, rhoSignatureToSpentSyntaxList,
        RhoDirectSignature.toPublicPattern]
  | cons p rest ih =>
      cases rest with
      | nil =>
          simp [RhoDirectSignature.ofPatternList, rhoSignatureToSpentSyntaxList,
            RhoDirectSignature.toPublicPattern]
      | cons q rest' =>
          simp [RhoDirectSignature.ofPatternList, rhoSignatureToSpentSyntaxList,
            RhoDirectSignature.toPublicPattern, ih]

@[simp] theorem RhoDirectSignature_ofSignature_toPublicPattern
    (sig : RhoSignature) :
    (RhoDirectSignature.ofSignature sig).toPublicPattern =
      rhoSignatureToSpentSyntax sig := by
  simp [RhoDirectSignature.ofSignature, rhoSignatureToSpentSyntax,
    RhoDirectSignature_ofPatternList_toPublicPattern]

@[simp] theorem RhoDirectStack_ofTrace_toPublicPattern
    (trace : RhoTemporalTrace) :
    (RhoDirectStack.ofTrace trace).toPublicPattern =
      rhoTemporalTraceToSpentSyntax trace := by
  induction trace with
  | nil =>
      simp [RhoDirectStack.ofTrace, rhoTemporalTraceToSpentSyntax,
        RhoDirectStack.toPublicPattern]
  | cons sig rest ih =>
      simp [RhoDirectStack.ofTrace, rhoTemporalTraceToSpentSyntax,
        RhoDirectStack.toPublicPattern, ih]

@[simp] theorem rhoSignatureToSpentSyntax_width_eq_card
    (sig : RhoSignature) :
    rhoSignatureSyntaxWidth (rhoSignatureToSpentSyntax sig) = sig.card := by
  simpa [rhoSignatureToSpentSyntax] using
    rhoSignatureToSpentSyntaxList_width_eq_length sig.toList

private theorem rhoSignatureList_sum_card
    (sigs : List RhoSignature) :
    (sigs.map Multiset.card).sum = sigs.sum.card := by
  induction sigs with
  | nil =>
      simp
  | cons sig rest ih =>
      simp [Multiset.card_add, ih]

@[simp] theorem rhoTemporalTraceToSpentSyntax_width
    (trace : RhoTemporalTrace) :
    rhoSpentSyntaxWidth (rhoTemporalTraceToSpentSyntax trace) =
      (trace.map Multiset.card).sum := by
  induction trace with
  | nil =>
      simp [rhoTemporalTraceToSpentSyntax]
  | cons sig rest ih =>
      simp [rhoTemporalTraceToSpentSyntax, rhoSignatureToSpentSyntax_width_eq_card, ih]

@[simp] theorem rhoTemporalTraceToSpentSyntax_ticks
    (trace : RhoTemporalTrace) :
    rhoSpentSyntaxTicks (rhoTemporalTraceToSpentSyntax trace) = trace.length := by
  induction trace with
  | nil =>
      simp [rhoTemporalTraceToSpentSyntax]
  | cons sig rest ih =>
      calc
        rhoSpentSyntaxTicks (rhoTemporalTraceToSpentSyntax (sig :: rest)) =
            1 + rhoSpentSyntaxTicks (rhoTemporalTraceToSpentSyntax rest) := by
              simp [rhoTemporalTraceToSpentSyntax]
        _ = 1 + rest.length := by rw [ih]
        _ = (sig :: rest).length := by simp [Nat.add_comm]

theorem rhoLedgerToSpentSyntax_shadow_of_traceCoherent
    (ledger : RhoLedger)
    (hcoh : RhoLedger.TraceCoherent ledger) :
    rhoSpentSyntaxAccount (rhoLedgerToSpentSyntax ledger) = rhoLedgerShadow ledger := by
  have hcard : (ledger.temporalList.map Multiset.card).sum = ledger.spatial.card := by
    calc
      (ledger.temporalList.map Multiset.card).sum = ledger.temporalList.sum.card := by
        exact rhoSignatureList_sum_card ledger.temporalList
      _ = ledger.spatial.card := by
        simpa [RhoLedger.TraceCoherent] using congrArg Multiset.card hcoh.symm
  funext i
  fin_cases i
  · calc
      rhoSpentSyntaxAccount (rhoLedgerToSpentSyntax ledger) 0 =
          (ledger.temporalList.map Multiset.card).sum := by
            simp [rhoLedgerToSpentSyntax, rhoTemporalTraceToSpentSyntax_width]
      _ = ledger.spatial.card := hcard
      _ = (rhoLedgerShadow ledger) 0 := by
            change ledger.spatial.card =
              rhoCostUnits ledger.spatial.card 0 +
                rhoTemporalUnits ledger.temporalList.length 0
            simp [rhoCostUnits, rhoTemporalUnits]
  · calc
      rhoSpentSyntaxAccount (rhoLedgerToSpentSyntax ledger) 1 =
          ledger.temporalList.length := by
            simp [rhoLedgerToSpentSyntax, rhoTemporalTraceToSpentSyntax_ticks]
      _ = (rhoLedgerShadow ledger) 1 := by
            change ledger.temporalList.length =
              rhoCostUnits ledger.spatial.card 1 +
                rhoTemporalUnits ledger.temporalList.length 1
            simp [rhoCostUnits, rhoTemporalUnits]

theorem RhoDirectStack_toPattern_account_eq_publicSpentSyntax
    (stack : RhoDirectStack)
    (h : stack.SurfaceLike) :
    rhoSpentSyntaxAccount stack.toPattern =
      rhoSpentSyntaxAccount (rhoLedgerToSpentSyntax stack.toLedger) := by
  calc
    rhoSpentSyntaxAccount stack.toPattern = rhoLedgerShadow stack.toLedger := by
      exact RhoDirectStack_toPattern_account_eq_shadow stack h
    _ = rhoSpentSyntaxAccount (rhoLedgerToSpentSyntax stack.toLedger) := by
      symm
      exact rhoLedgerToSpentSyntax_shadow_of_traceCoherent
        stack.toLedger
        (RhoDirectStack_toLedger_traceCoherent stack)

theorem RhoDirectStack_toPattern_width_eq_publicSpentSyntax_width
    (stack : RhoDirectStack)
    (h : stack.SurfaceLike) :
    rhoSpentSyntaxWidth stack.toPattern =
      rhoSpentSyntaxWidth (rhoLedgerToSpentSyntax stack.toLedger) := by
  have hacc := RhoDirectStack_toPattern_account_eq_publicSpentSyntax stack h
  have h0 : rhoSpentSyntaxAccount stack.toPattern 0 =
      rhoSpentSyntaxAccount (rhoLedgerToSpentSyntax stack.toLedger) 0 := by
    exact congrFun hacc 0
  simpa using h0

theorem RhoDirectStack_toPattern_ticks_eq_publicSpentSyntax_ticks
    (stack : RhoDirectStack)
    (h : stack.SurfaceLike) :
    rhoSpentSyntaxTicks stack.toPattern =
      rhoSpentSyntaxTicks (rhoLedgerToSpentSyntax stack.toLedger) := by
  have hacc := RhoDirectStack_toPattern_account_eq_publicSpentSyntax stack h
  have h1 : rhoSpentSyntaxAccount stack.toPattern 1 =
      rhoSpentSyntaxAccount (rhoLedgerToSpentSyntax stack.toLedger) 1 := by
    exact congrFun hacc 1
  simpa using h1

/-- A small structural mass model for rho terms used by the intrinsic
continued-step cost extractor.

This is the lowest-risk honest move while the full signed-term grammar is not
yet present in Lean: COMM cost is derived from the actual redex structure
rather than supplied by an external witness.
-/
def rhoPatternMass : Pattern → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .apply "PZero" [] => 0
  | .apply _ args => (args.map rhoPatternMass).sum
  | .lambda _ body => rhoPatternMass body
  | .multiLambda _ _ body => rhoPatternMass body
  | .subst body repl => rhoPatternMass body + rhoPatternMass repl
  | .collection _ elems _ => (elems.map rhoPatternMass).sum

@[simp] theorem rhoPatternMass_pzero :
    rhoPatternMass (.apply "PZero" []) = 0 := by
  simp [rhoPatternMass]

@[simp] theorem rhoPatternMass_empty_bag :
    rhoPatternMass (.collection .hashBag [] none) = 0 := by
  simp [rhoPatternMass]

/-- A commutative signature extracted structurally from a rho term.

This is still a shadow of the full signed-term grammar, but unlike plain `Nat`
width it keeps the spatial component as a genuine commutative monoid object.
-/
def rhoPatternSignature : Pattern → RhoSignature
  | .bvar n => ({.bvar n} : RhoSignature)
  | .fvar x => ({.fvar x} : RhoSignature)
  | .apply "PZero" [] => 0
  | .apply _ args => (args.map rhoPatternSignature).sum
  | .lambda _ body => rhoPatternSignature body
  | .multiLambda _ _ body => rhoPatternSignature body
  | .subst body repl => rhoPatternSignature body + rhoPatternSignature repl
  | .collection _ elems _ => (elems.map rhoPatternSignature).sum

private theorem rhoPatternSignature_card_list_of
    (ps : List Pattern)
    (hall : ∀ q ∈ ps, Multiset.card (rhoPatternSignature q) = rhoPatternMass q) :
    (ps.map rhoPatternSignature).sum.card = (ps.map rhoPatternMass).sum := by
  induction ps with
  | nil =>
      simp
  | cons p ps ihList =>
      have hp : Multiset.card (rhoPatternSignature p) = rhoPatternMass p := by
        exact hall p (by simp)
      have hps :
          (ps.map rhoPatternSignature).sum.card = (ps.map rhoPatternMass).sum := by
        apply ihList
        intro q hq
        exact hall q (by simp [hq])
      simp [hp, hps]

@[simp] theorem rhoPatternSignature_card (p : Pattern) :
    (rhoPatternSignature p).card = rhoPatternMass p := by
  induction p using Pattern.inductionOn with
  | hbvar n =>
      simp [rhoPatternSignature, rhoPatternMass]
  | hfvar x =>
      simp [rhoPatternSignature, rhoPatternMass]
  | happly head args ih =>
      have hargs := rhoPatternSignature_card_list_of args ih
      by_cases hzero : head = "PZero" ∧ args = []
      · rcases hzero with ⟨rfl, rfl⟩
        simp [rhoPatternSignature]
      · by_cases hhead : head = "PZero"
        · cases args with
          | nil =>
              cases hzero <| by simp [hhead]
          | cons a rest =>
              have ha : Multiset.card (rhoPatternSignature a) = rhoPatternMass a := by
                exact ih a (by simp)
              have hrest :
                  (rest.map rhoPatternSignature).sum.card = (rest.map rhoPatternMass).sum := by
                apply rhoPatternSignature_card_list_of
                intro q hq
                exact ih q (by simp [hq])
              simp [rhoPatternSignature, rhoPatternMass, hhead, ha, hrest]
        · simpa [rhoPatternSignature, rhoPatternMass, hhead] using hargs
  | hlambda nm body ih =>
      simpa [rhoPatternSignature, rhoPatternMass] using ih
  | hmultiLambda sort nms body ih =>
      simpa [rhoPatternSignature, rhoPatternMass] using ih
  | hsubst body repl ihBody ihRepl =>
      simp [rhoPatternSignature, rhoPatternMass, ihBody, ihRepl]
  | hcollection coll elems tail ih =>
      simpa [rhoPatternSignature, rhoPatternMass] using
        rhoPatternSignature_card_list_of elems ih

private theorem mem_sum_map_rhoPatternSignature
    {q : Pattern} {ps : List Pattern}
    (h : q ∈ (ps.map rhoPatternSignature).sum) :
    ∃ p ∈ ps, q ∈ rhoPatternSignature p := by
  induction ps with
  | nil =>
      cases h
  | cons p ps ih =>
      simp at h
      rcases h with h | h
      · exact ⟨p, by simp, h⟩
      · rcases ih h with ⟨p', hp', hq⟩
        exact ⟨p', by simp [hp'], hq⟩

theorem rhoPatternSignature_mem_width_one
    (p : Pattern) :
    ∀ {q : Pattern}, q ∈ rhoPatternSignature p → rhoSignatureSyntaxWidth q = 1 := by
  induction p using Pattern.inductionOn with
  | hbvar n =>
      intro q h
      simp [rhoPatternSignature] at h
      rcases h with rfl
      simp [rhoSignatureSyntaxWidth]
  | hfvar x =>
      intro q h
      simp [rhoPatternSignature] at h
      rcases h with rfl
      simp [rhoSignatureSyntaxWidth]
  | happly head args ih =>
      intro q h
      by_cases hzero : head = "PZero" ∧ args = []
      · rcases hzero with ⟨rfl, rfl⟩
        simp [rhoPatternSignature] at h
      · by_cases hhead : head = "PZero"
        · cases args with
          | nil =>
              cases hzero <| by simp [hhead]
          | cons a rest =>
              have h' : q ∈ ((a :: rest).map rhoPatternSignature).sum := by
                simpa [rhoPatternSignature, hhead] using h
              rcases mem_sum_map_rhoPatternSignature h' with ⟨p', hp', hq⟩
              exact ih p' (by simpa using hp') hq
        · simp [rhoPatternSignature, hhead] at h
          rcases mem_sum_map_rhoPatternSignature h with ⟨p', hp', hq⟩
          exact ih p' (by simpa using hp') hq
  | hlambda nm body ih =>
      intro q h
      have h' : q ∈ rhoPatternSignature body := by
        simpa [rhoPatternSignature] using h
      exact ih h'
  | hmultiLambda sort nms body ih =>
      intro q h
      have h' : q ∈ rhoPatternSignature body := by
        simpa [rhoPatternSignature] using h
      exact ih h'
  | hsubst body repl ihBody ihRepl =>
      intro q h
      simp [rhoPatternSignature] at h
      rcases h with h | h
      · exact ihBody h
      · exact ihRepl h
  | hcollection coll elems tail ih =>
      intro q h
      simp [rhoPatternSignature] at h
      rcases mem_sum_map_rhoPatternSignature h with ⟨p', hp', hq⟩
      exact ih p' (by simpa using hp') hq

def rhoIntrinsicCommSignature (chan payload : Pattern) : RhoSignature :=
  rhoPatternSignature chan + rhoPatternSignature payload

/-- Intrinsic accounted cost of one rho COMM redex:

- coordinate `0`: structural mass of the communicating channel and payload
- coordinate `1`: one temporal tick for the communication step itself

This is intentionally a structural redex-cost model, not yet the full paper's
signed-term grammar.
-/
def rhoIntrinsicCommAccount (chan payload : Pattern) : RhoCostAccount :=
  rhoCostUnits (rhoPatternMass chan + rhoPatternMass payload) + rhoTemporalUnits 1

@[simp] theorem rhoIntrinsicCommAccount_apply_zero (chan payload : Pattern) :
    rhoIntrinsicCommAccount chan payload 0 =
      rhoPatternMass chan + rhoPatternMass payload := by
  change (rhoCostUnits (rhoPatternMass chan + rhoPatternMass payload) 0 +
      rhoTemporalUnits 1 0) = _
  simp

@[simp] theorem rhoIntrinsicCommAccount_apply_one (chan payload : Pattern) :
    rhoIntrinsicCommAccount chan payload 1 = 1 := by
  change (rhoCostUnits (rhoPatternMass chan + rhoPatternMass payload) 1 +
      rhoTemporalUnits 1 1) = 1
  simp

def rhoIntrinsicCommLedger (chan payload : Pattern) : RhoLedger :=
  { spatial := rhoIntrinsicCommSignature chan payload
    temporal := [rhoIntrinsicCommSignature chan payload] }

@[simp] theorem rhoIntrinsicCommLedger_temporalList (chan payload : Pattern) :
    (rhoIntrinsicCommLedger chan payload).temporalList =
      [rhoIntrinsicCommSignature chan payload] := by
  rfl

@[simp] theorem rhoIntrinsicCommLedger_wellFormed (chan payload : Pattern) :
    RhoLedger.WellFormedSpent (rhoIntrinsicCommLedger chan payload) := by
  simp [RhoLedger.WellFormedSpent, RhoLedger.temporalList, rhoIntrinsicCommLedger]

@[simp] theorem rhoIntrinsicCommLedger_traceCoherent (chan payload : Pattern) :
    RhoLedger.TraceCoherent (rhoIntrinsicCommLedger chan payload) := by
  exact RhoLedger.wellFormedSpent_traceCoherent (rhoIntrinsicCommLedger_wellFormed chan payload)

theorem rhoIntrinsicCommSignature_mem_width_one
    (chan payload : Pattern) {q : Pattern}
    (h : q ∈ rhoIntrinsicCommSignature chan payload) :
    rhoSignatureSyntaxWidth q = 1 := by
  simp [rhoIntrinsicCommSignature] at h
  rcases h with h | h
  · exact rhoPatternSignature_mem_width_one chan h
  · exact rhoPatternSignature_mem_width_one payload h

@[simp] theorem rhoLedgerShadow_add (left right : RhoLedger) :
    rhoLedgerShadow (left + right) =
      rhoLedgerShadow left + rhoLedgerShadow right := by
  funext i
  fin_cases i
  · change
      rhoCostUnits ((left.spatial + right.spatial).card) 0 +
          rhoTemporalUnits ((left.temporal ++ right.temporal).length) 0 =
        (rhoCostUnits left.spatial.card 0 + rhoTemporalUnits left.temporal.length 0) +
          (rhoCostUnits right.spatial.card 0 + rhoTemporalUnits right.temporal.length 0)
    simp [Multiset.card_add]
  · change
      rhoCostUnits ((left.spatial + right.spatial).card) 1 +
          rhoTemporalUnits ((left.temporal ++ right.temporal).length) 1 =
        (rhoCostUnits left.spatial.card 1 + rhoTemporalUnits left.temporal.length 1) +
          (rhoCostUnits right.spatial.card 1 + rhoTemporalUnits right.temporal.length 1)
    simp [List.length_append]

@[simp] theorem rhoIntrinsicCommLedger_shadow (chan payload : Pattern) :
    rhoLedgerShadow (rhoIntrinsicCommLedger chan payload) =
      rhoIntrinsicCommAccount chan payload := by
  funext i
  fin_cases i
  · change (rhoIntrinsicCommSignature chan payload).card =
        rhoPatternMass chan + rhoPatternMass payload
    simp [rhoIntrinsicCommSignature, rhoPatternSignature_card, Multiset.card_add]
  · change (1 : Nat) = 1
    rfl

private def rhoContact (p q : Pattern) : Pattern :=
  .collection .hashBag [p, q] none

private def rhoIntroP (chan body : Pattern) : Pattern :=
  .apply "PInput" [chan, .lambda none body]

private def rhoIntroE (chan payload : Pattern) : Pattern :=
  .apply "POutput" [chan, payload]

private def rhoNil : Pattern :=
  .apply "PZero" []

/-- The ρ-calculus symmetric cut presentation:

- contact site: parallel composition
- left introduction: input
- right introduction: output
- contraction kernel: semantic COMM substitution, with inert sender residual
-/
def rhoSymmetricCutPresentation : SymmetricCutPresentation rhoGSLT where
  contact := rhoContact
  leftIntro := rhoIntroP
  rightIntro := rhoIntroE
  contract := fun _chan _name body payload =>
    (semanticCommSubst body payload, rhoNil)

/-- In the rho instance, contraction exposes semantic COMM substitution directly. -/
theorem rhoSymmetricCutPresentation_contract_fst (chan nm body payload : Pattern) :
    (rhoSymmetricCutPresentation.contract chan nm body payload).1 =
      semanticCommSubst body payload := by
  rfl

/-- In the rho instance, the sender residual is inert. -/
theorem rhoSymmetricCutPresentation_contract_snd (chan nm body payload : Pattern) :
    (rhoSymmetricCutPresentation.contract chan nm body payload).2 = rhoNil := by
  rfl

/-- The rho contact constructor is parallel composition. -/
theorem rhoSymmetricCutPresentation_contact (p q : Pattern) :
    rhoSymmetricCutPresentation.contact p q = .collection .hashBag [p, q] none := by
  rfl

/-- Intrinsic step-account carried by a rho reduction derivation.

The extractor peels away congruence/context closure and charges the underlying
COMM kernel structurally from the channel and payload that actually interact.
-/
def rhoIntrinsicReducesCost : {p q : Pattern} → Reduces p q → RhoCostAccount
  | _, _, .comm (n := n) (q := payload) => rhoIntrinsicCommAccount n payload
  | _, _, .equiv _ step _ => rhoIntrinsicReducesCost step
  | _, _, .par step => rhoIntrinsicReducesCost step
  | _, _, .par_any step => rhoIntrinsicReducesCost step
  | _, _, .par_set step => rhoIntrinsicReducesCost step
  | _, _, .par_set_any step => rhoIntrinsicReducesCost step

def rhoIntrinsicReducesLedger : {p q : Pattern} → Reduces p q → RhoLedger
  | _, _, .comm (n := n) (q := payload) => rhoIntrinsicCommLedger n payload
  | _, _, .equiv _ step _ => rhoIntrinsicReducesLedger step
  | _, _, .par step => rhoIntrinsicReducesLedger step
  | _, _, .par_any step => rhoIntrinsicReducesLedger step
  | _, _, .par_set step => rhoIntrinsicReducesLedger step
  | _, _, .par_set_any step => rhoIntrinsicReducesLedger step

@[simp] theorem rhoIntrinsicReducesLedger_shadow {p q : Pattern}
    (step : Reduces p q) :
    rhoLedgerShadow (rhoIntrinsicReducesLedger step) =
      rhoIntrinsicReducesCost step := by
  induction step with
  | comm =>
      exact rhoIntrinsicCommLedger_shadow _ _
  | equiv _ inner _ ih =>
      exact ih
  | par inner ih =>
      exact ih
  | par_any inner ih =>
      exact ih
  | par_set inner ih =>
      exact ih
  | par_set_any inner ih =>
      exact ih

@[simp] theorem rhoIntrinsicReducesLedger_wellFormed {p q : Pattern}
    (step : Reduces p q) :
    RhoLedger.WellFormedSpent (rhoIntrinsicReducesLedger step) := by
  induction step with
  | comm =>
      exact rhoIntrinsicCommLedger_wellFormed _ _
  | equiv _ inner _ ih =>
      exact ih
  | par inner ih =>
      exact ih
  | par_any inner ih =>
      exact ih
  | par_set inner ih =>
      exact ih
  | par_set_any inner ih =>
      exact ih

@[simp] theorem rhoIntrinsicReducesLedger_traceCoherent {p q : Pattern}
    (step : Reduces p q) :
    RhoLedger.TraceCoherent (rhoIntrinsicReducesLedger step) := by
  exact RhoLedger.wellFormedSpent_traceCoherent (rhoIntrinsicReducesLedger_wellFormed step)

/-- Intrinsic step-ledger for the rho GSLT rewrite relation. -/
noncomputable def rhoIntrinsicStepLedger {p q : Pattern} (h : rhoGSLT.Step p q) :
    RhoLedger :=
  rhoIntrinsicReducesLedger (Classical.choice h)

@[simp] theorem rhoIntrinsicStepLedger_shadow_choice {p q : Pattern}
    (h : rhoGSLT.Step p q) :
    rhoLedgerShadow (rhoIntrinsicStepLedger h) =
      rhoIntrinsicReducesCost (Classical.choice h) := by
  show rhoLedgerShadow (rhoIntrinsicReducesLedger (Classical.choice h)) =
      rhoIntrinsicReducesCost (Classical.choice h)
  simp

@[simp] theorem rhoIntrinsicStepLedger_wellFormed {p q : Pattern}
    (h : rhoGSLT.Step p q) :
    RhoLedger.WellFormedSpent (rhoIntrinsicStepLedger h) := by
  rcases h with ⟨step⟩
  simp [rhoIntrinsicStepLedger]

@[simp] theorem rhoIntrinsicStepLedger_traceCoherent {p q : Pattern}
    (h : rhoGSLT.Step p q) :
    RhoLedger.TraceCoherent (rhoIntrinsicStepLedger h) := by
  rcases h with ⟨step⟩
  simp [rhoIntrinsicStepLedger]

/-- Ordered intrinsic action along rho rewrite paths, retaining the richer
two-monoid ledger rather than only its vector shadow. -/
noncomputable def rhoIntrinsicLedgerAction : ActionMap rhoGSLT RhoLedger where
  action := fun {_ _} h => rhoIntrinsicStepLedger h

/-- Intrinsic step-account for the rho GSLT rewrite relation. -/
noncomputable def rhoIntrinsicStepCost {p q : Pattern} (h : rhoGSLT.Step p q) :
    RhoCostAccount :=
  rhoIntrinsicReducesCost (Classical.choice h)

@[simp] theorem rhoIntrinsicStepLedger_shadow {p q : Pattern}
    (h : rhoGSLT.Step p q) :
    rhoLedgerShadow (rhoIntrinsicStepLedger h) = rhoIntrinsicStepCost h := by
  show rhoLedgerShadow (rhoIntrinsicStepLedger h) =
      rhoIntrinsicReducesCost (Classical.choice h)
  exact rhoIntrinsicStepLedger_shadow_choice h

@[simp] theorem rhoIntrinsicReducesCost_apply_one {p q : Pattern}
    (step : Reduces p q) :
    rhoIntrinsicReducesCost step 1 = 1 := by
  induction step with
  | comm =>
      exact rhoIntrinsicCommAccount_apply_one _ _
  | equiv _ inner _ ih => exact ih
  | par inner ih => exact ih
  | par_any inner ih => exact ih
  | par_set inner ih => exact ih
  | par_set_any inner ih => exact ih

set_option linter.unnecessarySimpa false in
@[simp] theorem rhoIntrinsicStepCost_apply_one {p q : Pattern}
    (h : rhoGSLT.Step p q) :
    rhoIntrinsicStepCost h 1 = 1 := by
  rcases h with ⟨step⟩
  simpa [rhoIntrinsicStepCost] using rhoIntrinsicReducesCost_apply_one step

@[simp] theorem rhoIntrinsicStepLedger_temporalList_length {p q : Pattern}
    (h : rhoGSLT.Step p q) :
    (rhoIntrinsicStepLedger h).temporalList.length = 1 := by
  have hlen := congrArg List.length (rhoIntrinsicStepLedger_wellFormed h)
  simpa [RhoLedger.WellFormedSpent] using hlen

theorem rhoIntrinsicReducesLedger_temporal_mem_width_one {p q : Pattern}
    (step : Reduces p q) :
    ∀ {sig : RhoSignature} {atom : Pattern},
      sig ∈ (rhoIntrinsicReducesLedger step).temporalList →
      atom ∈ sig →
      rhoSignatureSyntaxWidth atom = 1 := by
  induction step with
  | comm =>
      intro sig atom hsig hatom
      simp [rhoIntrinsicReducesLedger] at hsig
      rcases hsig with rfl
      exact rhoIntrinsicCommSignature_mem_width_one _ _ hatom
  | equiv _ inner _ ih =>
      intro sig atom hsig hatom
      exact ih hsig hatom
  | par inner ih =>
      intro sig atom hsig hatom
      exact ih hsig hatom
  | par_any inner ih =>
      intro sig atom hsig hatom
      exact ih hsig hatom
  | par_set inner ih =>
      intro sig atom hsig hatom
      exact ih hsig hatom
  | par_set_any inner ih =>
      intro sig atom hsig hatom
      exact ih hsig hatom

theorem rhoIntrinsicStepLedger_temporal_mem_width_one {p q : Pattern}
    (h : rhoGSLT.Step p q) {sig : RhoSignature} {atom : Pattern}
    (hsig : sig ∈ (rhoIntrinsicStepLedger h).temporalList)
    (hatom : atom ∈ sig) :
    rhoSignatureSyntaxWidth atom = 1 := by
  have hsig' : sig ∈ (rhoIntrinsicReducesLedger (Classical.choice h)).temporalList := by
    simpa [rhoIntrinsicStepLedger] using hsig
  exact rhoIntrinsicReducesLedger_temporal_mem_width_one (Classical.choice h) hsig' hatom

/-- Intrinsic rho cost map over the existing `rhoGSLT` rewrite graph. -/
noncomputable def rhoIntrinsicCostMap : CostMap rhoGSLT Nat 2 where
  cost := fun {_ _} h => rhoIntrinsicStepCost h

/-- The richer ordered rho ledger projects back to the already verified
vector-cost accumulation on arbitrary rewrite paths. -/
theorem rhoIntrinsicLedgerTotalAction_shadow_eq_totalCost
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction path) =
      totalCost rhoIntrinsicCostMap path := by
  refine GSLT.RewritePath.rec
    (motive := fun {t u} path =>
      rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction path) =
        totalCost rhoIntrinsicCostMap path)
    ?_ ?_ path
  · intro t
    simp [totalAction, totalCost]
  · intro _ _ _ h rest ih
    rw [totalAction, totalCost, rhoLedgerShadow_add, ih]
    simpa [rhoIntrinsicLedgerAction, rhoIntrinsicCostMap] using
      congrArg (fun x => x + totalCost rhoIntrinsicCostMap rest)
        (rhoIntrinsicStepLedger_shadow h)

/-- The temporal component of the richer rho ledger records exactly one ordered
tick per rewrite step along any rho path. -/
theorem rhoIntrinsicLedgerTotalAction_temporalLength_eq_length
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (totalAction rhoIntrinsicLedgerAction path).temporalList.length = path.length := by
  refine GSLT.RewritePath.rec
    (motive := fun {t u} path =>
      (totalAction rhoIntrinsicLedgerAction path).temporalList.length = path.length)
    ?_ ?_ path
  · intro t
    rfl
  · intro _ _ _ h rest ih
    have ih' :
        (totalAction
          { action := fun {x y} h => rhoIntrinsicStepLedger h } rest).temporalList.length =
          GSLT.RewritePath.length rhoGSLT rest := by
      simpa [rhoIntrinsicLedgerAction] using ih
    simp [totalAction, GSLT.RewritePath.length, ih', RhoLedger.temporalList_add,
      rhoIntrinsicLedgerAction, rhoIntrinsicStepLedger_temporalList_length]

theorem rhoIntrinsicLedgerTotalAction_traceCoherent
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    RhoLedger.TraceCoherent (totalAction rhoIntrinsicLedgerAction path) := by
  refine GSLT.RewritePath.rec
    (motive := fun {t u} path =>
      RhoLedger.TraceCoherent (totalAction rhoIntrinsicLedgerAction path))
    ?_ ?_ path
  · intro t
    simp [totalAction]
  · intro _ _ _ h rest ih
    simpa [totalAction, rhoIntrinsicLedgerAction] using
      RhoLedger.traceCoherent_add (rhoIntrinsicStepLedger_traceCoherent h) ih

theorem rhoIntrinsicLedgerTotalAction_spentSyntax_eq_totalCost
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
        totalCost rhoIntrinsicCostMap path := by
  rw [rhoLedgerToSpentSyntax_shadow_of_traceCoherent
      (totalAction rhoIntrinsicLedgerAction path)
      (rhoIntrinsicLedgerTotalAction_traceCoherent path)]
  exact rhoIntrinsicLedgerTotalAction_shadow_eq_totalCost path

theorem rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_spatialCard
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
        (totalAction rhoIntrinsicLedgerAction path).spatial.card := by
  have h0 :=
    congrFun
      (rhoLedgerToSpentSyntax_shadow_of_traceCoherent
        (totalAction rhoIntrinsicLedgerAction path)
        (rhoIntrinsicLedgerTotalAction_traceCoherent path)) 0
  simpa [rhoLedgerShadow] using! h0

theorem rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_length
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
        path.length := by
  calc
    rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          (totalAction rhoIntrinsicLedgerAction path).temporalList.length := by
            simp [rhoLedgerToSpentSyntax, rhoTemporalTraceToSpentSyntax_ticks]
    _ = path.length := rhoIntrinsicLedgerTotalAction_temporalLength_eq_length path

theorem rhoIntrinsicLedgerTotalAction_spatialCard_eq_totalCost_zero
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (totalAction rhoIntrinsicLedgerAction path).spatial.card =
      totalCost rhoIntrinsicCostMap path 0 := by
  have h0 := congrFun (rhoIntrinsicLedgerTotalAction_shadow_eq_totalCost path) 0
  simpa [rhoLedgerShadow] using! h0

theorem rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_totalCost_zero
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
        totalCost rhoIntrinsicCostMap path 0 := by
  calc
    rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          (totalAction rhoIntrinsicLedgerAction path).spatial.card := by
            exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_spatialCard path
    _ = totalCost rhoIntrinsicCostMap path 0 := by
      exact rhoIntrinsicLedgerTotalAction_spatialCard_eq_totalCost_zero path

theorem rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_totalCost_one
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
        totalCost rhoIntrinsicCostMap path 1 := by
  have h1 := congrFun (rhoIntrinsicLedgerTotalAction_spentSyntax_eq_totalCost path) 1
  simpa using h1

theorem rhoIntrinsicLedgerTotalAction_publicSpentSyntax_modulus
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
        totalCost rhoIntrinsicCostMap path 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          totalCost rhoIntrinsicCostMap path 1 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          path.length := by
  constructor
  · exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_totalCost_zero path
  · constructor
    · exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_totalCost_one path
    · exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_length path

/-- Direct spent-stack witness for an intrinsic rho rewrite path. This is the
ordered stack view of the accumulated spent ledger, without routing through the
older spent-syntax projection. -/
noncomputable def rhoIntrinsicDirectSpentStack
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) : RhoDirectStack :=
  RhoDirectStack.ofTrace (totalAction rhoIntrinsicLedgerAction path).temporalList

theorem rhoIntrinsicDirectSpentStack_toLedger
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (rhoIntrinsicDirectSpentStack path).toLedger =
      totalAction rhoIntrinsicLedgerAction path := by
  unfold rhoIntrinsicDirectSpentStack
  calc
    (RhoDirectStack.ofTrace (totalAction rhoIntrinsicLedgerAction path).temporalList).toLedger =
        { spatial := (totalAction rhoIntrinsicLedgerAction path).temporalList.sum
          temporal := (totalAction rhoIntrinsicLedgerAction path).temporalList } := by
          simp [RhoDirectStack_toLedger_ofTrace]
    _ = totalAction rhoIntrinsicLedgerAction path := by
      apply RhoLedger.ext
      · simpa [RhoLedger.TraceCoherent] using
          (rhoIntrinsicLedgerTotalAction_traceCoherent path).symm
      · rfl

theorem rhoIntrinsicDirectSpentStack_shadow_eq_totalCost
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoLedgerShadow ((rhoIntrinsicDirectSpentStack path).toLedger) =
      totalCost rhoIntrinsicCostMap path := by
  rw [rhoIntrinsicDirectSpentStack_toLedger]
  exact rhoIntrinsicLedgerTotalAction_shadow_eq_totalCost path

theorem rhoIntrinsicDirectSpentStack_depth_eq_length
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (rhoIntrinsicDirectSpentStack path).depth = path.length := by
  unfold rhoIntrinsicDirectSpentStack
  rw [RhoDirectStack_depth_ofTrace, rhoIntrinsicLedgerTotalAction_temporalLength_eq_length]

theorem rhoIntrinsicLedgerTotalAction_temporal_mem_width_one
    {t u : Pattern} (path : rhoGSLT.RewritePath t u)
    :
    ∀ {sig : RhoSignature} {atom : Pattern},
      sig ∈ (totalAction rhoIntrinsicLedgerAction path).temporalList →
      atom ∈ sig →
      rhoSignatureSyntaxWidth atom = 1 := by
  refine GSLT.RewritePath.rec
    (motive := fun {t u} path =>
      ∀ {sig : RhoSignature} {atom : Pattern},
        sig ∈ (totalAction rhoIntrinsicLedgerAction path).temporalList →
        atom ∈ sig →
        rhoSignatureSyntaxWidth atom = 1)
    ?_ ?_ path
  · intro t sig atom hsig hatom
    change sig ∈ ([] : List RhoSignature) at hsig
    have hnil : sig ∈ ([] : List RhoSignature) := hsig
    cases hnil
  · intro _ _ _ h rest ih sig atom hsig hatom
    change sig ∈
        ((rhoIntrinsicStepLedger h).temporal ++
          (totalAction rhoIntrinsicLedgerAction rest).temporal) at hsig
    have hsig' :
        sig ∈ (rhoIntrinsicStepLedger h).temporal ++
          (totalAction rhoIntrinsicLedgerAction rest).temporal := hsig
    rcases List.mem_append.mp hsig' with hsig | hsig
    · exact rhoIntrinsicStepLedger_temporal_mem_width_one h hsig hatom
    · exact ih hsig hatom

theorem rhoIntrinsicDirectSpentStack_surfaceLike
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (rhoIntrinsicDirectSpentStack path).SurfaceLike := by
  unfold rhoIntrinsicDirectSpentStack
  apply RhoDirectStack_ofTrace_surfaceLike
  intro sig hsig atom hatom
  exact rhoIntrinsicLedgerTotalAction_temporal_mem_width_one path hsig hatom

theorem rhoIntrinsicDirectSpentStack_spentSyntax_eq_totalCost
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentStack path).toPattern =
      totalCost rhoIntrinsicCostMap path := by
  rw [RhoDirectStack_toPattern_account_eq_shadow
      (rhoIntrinsicDirectSpentStack path)
      (rhoIntrinsicDirectSpentStack_surfaceLike path)]
  exact rhoIntrinsicDirectSpentStack_shadow_eq_totalCost path

theorem rhoIntrinsicDirectSpentStack_ticks_eq_length
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentStack path).toPattern =
      path.length := by
  rw [RhoDirectStack_toPattern_ticks_eq_depth,
    rhoIntrinsicDirectSpentStack_depth_eq_length]

theorem rhoIntrinsicDirectSpentStack_semantics
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (rhoIntrinsicDirectSpentStack path).SurfaceLike ∧
      (rhoIntrinsicDirectSpentStack path).toLedger =
        totalAction rhoIntrinsicLedgerAction path ∧
      rhoLedgerShadow ((rhoIntrinsicDirectSpentStack path).toLedger) =
        totalCost rhoIntrinsicCostMap path ∧
      (rhoIntrinsicDirectSpentStack path).depth = path.length ∧
      rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentStack path).toPattern =
        totalCost rhoIntrinsicCostMap path ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentStack path).toPattern =
        path.length := by
  constructor
  · exact rhoIntrinsicDirectSpentStack_surfaceLike path
  · constructor
    · exact rhoIntrinsicDirectSpentStack_toLedger path
    · constructor
      · exact rhoIntrinsicDirectSpentStack_shadow_eq_totalCost path
      · constructor
        · exact rhoIntrinsicDirectSpentStack_depth_eq_length path
        · constructor
          · exact rhoIntrinsicDirectSpentStack_spentSyntax_eq_totalCost path
          · exact rhoIntrinsicDirectSpentStack_ticks_eq_length path

theorem rhoIntrinsicDirectSpentStack_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    rhoIntrinsicDirectSpentStack (rewritePathAppend left right) =
      RhoDirectStack.append
        (rhoIntrinsicDirectSpentStack left)
        (rhoIntrinsicDirectSpentStack right) := by
  unfold rhoIntrinsicDirectSpentStack
  rw [totalAction_append, RhoLedger.temporalList_add, RhoDirectStack_ofTrace_append]

@[simp] theorem rhoIntrinsicDirectSpentStack_oneStepPath
    {t u : Pattern} (step : rhoGSLT.Step t u) :
    rhoIntrinsicDirectSpentStack (oneStepPath (S := rhoGSLT) step) =
      RhoDirectStack.ofTrace (rhoIntrinsicStepLedger step).temporalList := by
  unfold rhoIntrinsicDirectSpentStack
  simp [rhoIntrinsicLedgerAction, totalAction, oneStepPath]

noncomputable def rhoIntrinsicDirectStepSpent
    {t u : Pattern} (step : rhoGSLT.Step t u) : RhoDirectStack :=
  RhoDirectStack.ofTrace (rhoIntrinsicStepLedger step).temporalList

@[simp] theorem rhoIntrinsicDirectStepSpent_eq_oneStepPath
    {t u : Pattern} (step : rhoGSLT.Step t u) :
    rhoIntrinsicDirectStepSpent step =
      rhoIntrinsicDirectSpentStack (oneStepPath (S := rhoGSLT) step) := by
  symm
  exact rhoIntrinsicDirectSpentStack_oneStepPath step

@[simp] theorem rhoIntrinsicDirectStepSpent_surfaceLike
    {t u : Pattern} (step : rhoGSLT.Step t u) :
    (rhoIntrinsicDirectStepSpent step).SurfaceLike := by
  rw [rhoIntrinsicDirectStepSpent_eq_oneStepPath]
  exact rhoIntrinsicDirectSpentStack_surfaceLike (oneStepPath (S := rhoGSLT) step)

@[simp] theorem rhoIntrinsicDirectStepSpent_spentSyntax_eq_stepCost
    {t u : Pattern} (step : rhoGSLT.Step t u) :
    rhoSpentSyntaxAccount (rhoIntrinsicDirectStepSpent step).toPattern =
      rhoIntrinsicStepCost step := by
  rw [rhoIntrinsicDirectStepSpent_eq_oneStepPath,
    rhoIntrinsicDirectSpentStack_spentSyntax_eq_totalCost]
  change totalCost rhoIntrinsicCostMap (oneStepPath (S := rhoGSLT) step) =
      rhoIntrinsicCostMap.cost step
  exact totalCost_oneStepPath (S := rhoGSLT) (A := Nat) (k := 2) rhoIntrinsicCostMap step

@[simp] theorem rhoIntrinsicDirectStepSpent_ticks_eq_one
    {t u : Pattern} (step : rhoGSLT.Step t u) :
    rhoSpentSyntaxTicks (rhoIntrinsicDirectStepSpent step).toPattern = 1 := by
  rw [rhoIntrinsicDirectStepSpent_eq_oneStepPath,
    rhoIntrinsicDirectSpentStack_ticks_eq_length]
  simp

theorem rhoIntrinsicDirectSpentStack_rewritePathAppend_steps
    {t u v : Pattern}
    (left : rhoGSLT.Step t u)
    (right : rhoGSLT.Step u v) :
    rhoIntrinsicDirectSpentStack
      (rewritePathAppend
        (oneStepPath (S := rhoGSLT) left)
        (oneStepPath (S := rhoGSLT) right)) =
          RhoDirectStack.append
            (rhoIntrinsicDirectStepSpent left)
            (rhoIntrinsicDirectStepSpent right) := by
  simpa [rhoIntrinsicDirectStepSpent_eq_oneStepPath] using
    rhoIntrinsicDirectSpentStack_rewritePathAppend
      (oneStepPath (S := rhoGSLT) left)
      (oneStepPath (S := rhoGSLT) right)

noncomputable def rhoIntrinsicDirectSpentTrace
    {t u : Pattern} : rhoGSLT.RewritePath t u → RhoDirectStack
  | .nil _ => .empty
  | .cons step rest =>
      RhoDirectStack.append
        (rhoIntrinsicDirectStepSpent step)
        (rhoIntrinsicDirectSpentTrace rest)

theorem rhoIntrinsicDirectSpentTrace_eq_stack
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoIntrinsicDirectSpentTrace path = rhoIntrinsicDirectSpentStack path := by
  refine GSLT.RewritePath.rec
    (motive := fun {t u} path =>
      rhoIntrinsicDirectSpentTrace path = rhoIntrinsicDirectSpentStack path)
    ?_ ?_ path
  · intro t
    rfl
  · intro _ _ _ step rest ih
    calc
      rhoIntrinsicDirectSpentTrace (.cons step rest) =
          RhoDirectStack.append
            (rhoIntrinsicDirectStepSpent step)
            (rhoIntrinsicDirectSpentTrace rest) := by
              rfl
      _ =
          RhoDirectStack.append
            (rhoIntrinsicDirectSpentStack (oneStepPath (S := rhoGSLT) step))
            (rhoIntrinsicDirectSpentStack rest) := by
              rw [rhoIntrinsicDirectStepSpent_eq_oneStepPath, ih]
      _ =
          rhoIntrinsicDirectSpentStack
            (rewritePathAppend (oneStepPath (S := rhoGSLT) step) rest) := by
              symm
              exact rhoIntrinsicDirectSpentStack_rewritePathAppend
                (oneStepPath (S := rhoGSLT) step) rest
      _ = rhoIntrinsicDirectSpentStack (.cons step rest) := by
            rfl

@[simp] theorem rhoIntrinsicDirectSpentTrace_oneStepPath
    {t u : Pattern} (step : rhoGSLT.Step t u) :
    rhoIntrinsicDirectSpentTrace (oneStepPath (S := rhoGSLT) step) =
      rhoIntrinsicDirectStepSpent step := by
  simp [oneStepPath, rhoIntrinsicDirectSpentTrace, rhoIntrinsicDirectStepSpent]

theorem rhoIntrinsicDirectSpentTrace_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    rhoIntrinsicDirectSpentTrace (rewritePathAppend left right) =
      RhoDirectStack.append
        (rhoIntrinsicDirectSpentTrace left)
        (rhoIntrinsicDirectSpentTrace right) := by
  rw [rhoIntrinsicDirectSpentTrace_eq_stack,
    rhoIntrinsicDirectSpentTrace_eq_stack,
    rhoIntrinsicDirectSpentTrace_eq_stack]
  exact rhoIntrinsicDirectSpentStack_rewritePathAppend left right

theorem rhoIntrinsicDirectSpentTrace_toLedger
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (rhoIntrinsicDirectSpentTrace path).toLedger =
      totalAction rhoIntrinsicLedgerAction path := by
  rw [rhoIntrinsicDirectSpentTrace_eq_stack]
  exact rhoIntrinsicDirectSpentStack_toLedger path

theorem rhoIntrinsicDirectSpentTrace_rewritePathAppend_steps
    {t u v : Pattern}
    (left : rhoGSLT.Step t u)
    (right : rhoGSLT.Step u v) :
    rhoIntrinsicDirectSpentTrace
      (rewritePathAppend
        (oneStepPath (S := rhoGSLT) left)
        (oneStepPath (S := rhoGSLT) right)) =
          RhoDirectStack.append
            (rhoIntrinsicDirectStepSpent left)
            (rhoIntrinsicDirectStepSpent right) := by
  simpa using
    rhoIntrinsicDirectSpentTrace_rewritePathAppend
      (oneStepPath (S := rhoGSLT) left)
      (oneStepPath (S := rhoGSLT) right)

theorem rhoIntrinsicDirectSpentStack_semantics_rewritePathAppend_steps
    {t u v : Pattern}
    (left : rhoGSLT.Step t u)
    (right : rhoGSLT.Step u v) :
    let path :=
      rewritePathAppend
        (oneStepPath (S := rhoGSLT) left)
        (oneStepPath (S := rhoGSLT) right)
    let stack := rhoIntrinsicDirectSpentStack path
    stack.toLedger = totalAction rhoIntrinsicLedgerAction path ∧
      rhoLedgerShadow stack.toLedger = totalCost rhoIntrinsicCostMap path ∧
      stack.depth = path.length ∧
      rhoSpentSyntaxAccount stack.toPattern = totalCost rhoIntrinsicCostMap path ∧
      rhoSpentSyntaxTicks stack.toPattern = path.length ∧
      stack =
        RhoDirectStack.append
          (rhoIntrinsicDirectSpentStack (oneStepPath (S := rhoGSLT) left))
          (rhoIntrinsicDirectSpentStack (oneStepPath (S := rhoGSLT) right)) ∧
      stack =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent left)
          (rhoIntrinsicDirectStepSpent right) ∧
      rhoIntrinsicDirectSpentTrace path =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent left)
          (rhoIntrinsicDirectStepSpent right) := by
  dsimp
  constructor
  · exact rhoIntrinsicDirectSpentStack_toLedger _
  · constructor
    · exact rhoIntrinsicDirectSpentStack_shadow_eq_totalCost _
    · constructor
      · exact rhoIntrinsicDirectSpentStack_depth_eq_length _
      · constructor
        · exact rhoIntrinsicDirectSpentStack_spentSyntax_eq_totalCost _
        · constructor
          · exact rhoIntrinsicDirectSpentStack_ticks_eq_length _
          · constructor
            · exact rhoIntrinsicDirectSpentStack_rewritePathAppend
                (oneStepPath (S := rhoGSLT) left)
                (oneStepPath (S := rhoGSLT) right)
            · constructor
              · exact rhoIntrinsicDirectSpentStack_rewritePathAppend_steps left right
              · exact rhoIntrinsicDirectSpentTrace_rewritePathAppend_steps left right

theorem rhoIntrinsicDirectSpentTrace_traceCoherent
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    RhoLedger.TraceCoherent ((rhoIntrinsicDirectSpentTrace path).toLedger) := by
  rw [rhoIntrinsicDirectSpentTrace_toLedger]
  exact rhoIntrinsicLedgerTotalAction_traceCoherent path

theorem rhoIntrinsicDirectSpentTrace_surfaceLike
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (rhoIntrinsicDirectSpentTrace path).SurfaceLike := by
  rw [rhoIntrinsicDirectSpentTrace_eq_stack]
  exact rhoIntrinsicDirectSpentStack_surfaceLike path

theorem rhoIntrinsicDirectSpentTrace_shadow_eq_totalCost
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoLedgerShadow ((rhoIntrinsicDirectSpentTrace path).toLedger) =
      totalCost rhoIntrinsicCostMap path := by
  rw [rhoIntrinsicDirectSpentTrace_toLedger]
  exact rhoIntrinsicLedgerTotalAction_shadow_eq_totalCost path

theorem rhoIntrinsicDirectSpentTrace_spentSyntax_eq_totalCost
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace path).toPattern =
      totalCost rhoIntrinsicCostMap path := by
  rw [rhoIntrinsicDirectSpentTrace_eq_stack]
  exact rhoIntrinsicDirectSpentStack_spentSyntax_eq_totalCost path

theorem rhoIntrinsicDirectSpentTrace_depth_eq_length
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (rhoIntrinsicDirectSpentTrace path).depth = path.length := by
  rw [rhoIntrinsicDirectSpentTrace_eq_stack]
  exact rhoIntrinsicDirectSpentStack_depth_eq_length path

theorem rhoIntrinsicDirectSpentTrace_ticks_eq_length
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
      path.length := by
  rw [rhoIntrinsicDirectSpentTrace_eq_stack]
  exact rhoIntrinsicDirectSpentStack_ticks_eq_length path

theorem rhoIntrinsicDirectSpentTrace_preserves_spent_coherence
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (rhoIntrinsicDirectSpentTrace path).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace path).toLedger =
        totalAction rhoIntrinsicLedgerAction path ∧
      RhoLedger.TraceCoherent ((rhoIntrinsicDirectSpentTrace path).toLedger) := by
  constructor
  · exact rhoIntrinsicDirectSpentTrace_surfaceLike path
  · constructor
    · exact rhoIntrinsicDirectSpentTrace_toLedger path
    · exact rhoIntrinsicDirectSpentTrace_traceCoherent path

theorem rhoIntrinsicDirectSpentTrace_account_eq_publicSpentSyntax
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace path).toPattern =
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) := by
  rw [← rhoIntrinsicDirectSpentTrace_toLedger]
  exact RhoDirectStack_toPattern_account_eq_publicSpentSyntax
    (rhoIntrinsicDirectSpentTrace path)
    (rhoIntrinsicDirectSpentTrace_surfaceLike path)

theorem rhoIntrinsicDirectSpentTrace_width_eq_publicSpentSyntax_width
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace path).toPattern =
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) := by
  rw [← rhoIntrinsicDirectSpentTrace_toLedger]
  exact RhoDirectStack_toPattern_width_eq_publicSpentSyntax_width
    (rhoIntrinsicDirectSpentTrace path)
    (rhoIntrinsicDirectSpentTrace_surfaceLike path)

theorem rhoIntrinsicDirectSpentTrace_ticks_eq_publicSpentSyntax_ticks
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) := by
  rw [← rhoIntrinsicDirectSpentTrace_toLedger]
  exact RhoDirectStack_toPattern_ticks_eq_publicSpentSyntax_ticks
    (rhoIntrinsicDirectSpentTrace path)
    (rhoIntrinsicDirectSpentTrace_surfaceLike path)

theorem rhoIntrinsicDirectSpentStack_toPublicPattern_eq_publicSpentSyntax
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (rhoIntrinsicDirectSpentStack path).toPublicPattern =
      rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path) := by
  unfold rhoIntrinsicDirectSpentStack rhoLedgerToSpentSyntax
  simp [RhoDirectStack_ofTrace_toPublicPattern]

theorem rhoIntrinsicDirectSpentTrace_toPublicPattern_eq_publicSpentSyntax
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (rhoIntrinsicDirectSpentTrace path).toPublicPattern =
      rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path) := by
  rw [rhoIntrinsicDirectSpentTrace_eq_stack]
  exact rhoIntrinsicDirectSpentStack_toPublicPattern_eq_publicSpentSyntax path

theorem rhoIntrinsicDirectSpentTrace_width_eq_totalCost_zero
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace path).toPattern =
      totalCost rhoIntrinsicCostMap path 0 := by
  calc
    rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace path).toPattern =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) := by
            exact rhoIntrinsicDirectSpentTrace_width_eq_publicSpentSyntax_width path
    _ = totalCost rhoIntrinsicCostMap path 0 := by
      exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_totalCost_zero path

theorem rhoIntrinsicDirectSpentTrace_ticks_eq_totalCost_one
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
      totalCost rhoIntrinsicCostMap path 1 := by
  calc
    rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) := by
            exact rhoIntrinsicDirectSpentTrace_ticks_eq_publicSpentSyntax_ticks path
    _ = totalCost rhoIntrinsicCostMap path 1 := by
      exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_totalCost_one path

theorem rhoIntrinsicDirectSpentTrace_modulus
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace path).toPattern =
      totalCost rhoIntrinsicCostMap path 0 ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
        totalCost rhoIntrinsicCostMap path 1 ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
        path.length := by
  constructor
  · exact rhoIntrinsicDirectSpentTrace_width_eq_totalCost_zero path
  · constructor
    · exact rhoIntrinsicDirectSpentTrace_ticks_eq_totalCost_one path
    · exact rhoIntrinsicDirectSpentTrace_ticks_eq_length path

theorem rhoIntrinsicLedgerPublicSpentSyntax_semantics
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
        totalCost rhoIntrinsicCostMap path ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          totalCost rhoIntrinsicCostMap path 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          totalCost rhoIntrinsicCostMap path 1 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          path.length ∧
      RhoLedger.TraceCoherent (totalAction rhoIntrinsicLedgerAction path) := by
  constructor
  · exact rhoIntrinsicLedgerTotalAction_spentSyntax_eq_totalCost path
  · constructor
    · exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_totalCost_zero path
    · constructor
      · exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_totalCost_one path
      · constructor
        · exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_length path
        · exact rhoIntrinsicLedgerTotalAction_traceCoherent path

theorem rhoIntrinsicDirectSpentTrace_semantics
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (rhoIntrinsicDirectSpentTrace path).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace path).toLedger =
        totalAction rhoIntrinsicLedgerAction path ∧
      (rhoIntrinsicDirectSpentTrace path).toPublicPattern =
        rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path) ∧
      RhoLedger.TraceCoherent ((rhoIntrinsicDirectSpentTrace path).toLedger) ∧
      rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace path).toPattern =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) ∧
      rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace path).toPattern =
        totalCost rhoIntrinsicCostMap path ∧
      rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace path).toPattern =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) ∧
      rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace path).toPattern =
        totalCost rhoIntrinsicCostMap path 0 ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
        totalCost rhoIntrinsicCostMap path 1 ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
        path.length := by
  constructor
  · exact rhoIntrinsicDirectSpentTrace_surfaceLike path
  · constructor
    · exact rhoIntrinsicDirectSpentTrace_toLedger path
    · constructor
      · exact rhoIntrinsicDirectSpentTrace_toPublicPattern_eq_publicSpentSyntax path
      · constructor
        · exact rhoIntrinsicDirectSpentTrace_traceCoherent path
        · constructor
          · exact rhoIntrinsicDirectSpentTrace_account_eq_publicSpentSyntax path
          · constructor
            · exact rhoIntrinsicDirectSpentTrace_spentSyntax_eq_totalCost path
            · constructor
              · exact rhoIntrinsicDirectSpentTrace_width_eq_publicSpentSyntax_width path
              · constructor
                · exact rhoIntrinsicDirectSpentTrace_width_eq_totalCost_zero path
                · constructor
                  · exact rhoIntrinsicDirectSpentTrace_ticks_eq_publicSpentSyntax_ticks path
                  · constructor
                    · exact rhoIntrinsicDirectSpentTrace_ticks_eq_totalCost_one path
                    · exact rhoIntrinsicDirectSpentTrace_ticks_eq_length path

theorem rhoIntrinsicLedgerTotalAction_publicSpentSyntax_account_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) := by
  calc
    rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
          totalCost rhoIntrinsicCostMap (rewritePathAppend left right) := by
            exact rhoIntrinsicLedgerTotalAction_spentSyntax_eq_totalCost
              (rewritePathAppend left right)
    _ = totalCost rhoIntrinsicCostMap left + totalCost rhoIntrinsicCostMap right := by
      exact totalCost_append (S := rhoGSLT) (A := Nat) (k := 2)
        rhoIntrinsicCostMap left right
    _ =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) := by
            rw [← rhoIntrinsicLedgerTotalAction_spentSyntax_eq_totalCost left,
              ← rhoIntrinsicLedgerTotalAction_spentSyntax_eq_totalCost right]

theorem rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) := by
  have h0 := congrFun
    (totalCost_append (S := rhoGSLT) (A := Nat) (k := 2)
      rhoIntrinsicCostMap left right) 0
  calc
    rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
          totalCost rhoIntrinsicCostMap (rewritePathAppend left right) 0 := by
            exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_totalCost_zero
              (rewritePathAppend left right)
    _ = totalCost rhoIntrinsicCostMap left 0 + totalCost rhoIntrinsicCostMap right 0 := by
      simpa using! h0
    _ =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) := by
            rw [← rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_totalCost_zero left,
              ← rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_totalCost_zero right]

theorem rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) := by
  have h1 := congrFun
    (totalCost_append (S := rhoGSLT) (A := Nat) (k := 2)
      rhoIntrinsicCostMap left right) 1
  calc
    rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
          totalCost rhoIntrinsicCostMap (rewritePathAppend left right) 1 := by
            exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_totalCost_one
              (rewritePathAppend left right)
    _ = totalCost rhoIntrinsicCostMap left 1 + totalCost rhoIntrinsicCostMap right 1 := by
      simpa using! h1
    _ =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) := by
            rw [← rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_totalCost_one left,
              ← rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_totalCost_one right]

theorem rhoIntrinsicLedgerTotalAction_publicSpentSyntax_no_leak_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) := by
  constructor
  · exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_account_rewritePathAppend
      left right
  · constructor
    · exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_rewritePathAppend
        left right
    · exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_rewritePathAppend
        left right

theorem rhoIntrinsicLedgerPublicSpentSyntax_semantics_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)) +
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right))) =
            (rewritePathAppend left right).length ∧
      RhoLedger.TraceCoherent
        (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right)) := by
  rcases rhoIntrinsicLedgerTotalAction_publicSpentSyntax_no_leak_rewritePathAppend
      left right with
    ⟨hacc, hwidth, hticks⟩
  rcases rhoIntrinsicLedgerPublicSpentSyntax_semantics (rewritePathAppend left right) with
    ⟨_, _, _, hticksLen, hcoh⟩
  constructor
  · exact hacc
  · constructor
    · exact hwidth
    · constructor
      · exact hticks
      · constructor
        · exact hticksLen
        · exact hcoh

theorem rhoIntrinsicDirectSpentTrace_account_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
        rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace left).toPattern +
        rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace right).toPattern := by
  calc
    rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
          totalCost rhoIntrinsicCostMap (rewritePathAppend left right) := by
            exact rhoIntrinsicDirectSpentTrace_spentSyntax_eq_totalCost
              (rewritePathAppend left right)
    _ = totalCost rhoIntrinsicCostMap left + totalCost rhoIntrinsicCostMap right := by
      exact totalCost_append (S := rhoGSLT) (A := Nat) (k := 2)
        rhoIntrinsicCostMap left right
    _ =
        rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace left).toPattern +
        rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace right).toPattern := by
          rw [← rhoIntrinsicDirectSpentTrace_spentSyntax_eq_totalCost left,
            ← rhoIntrinsicDirectSpentTrace_spentSyntax_eq_totalCost right]

theorem rhoIntrinsicDirectSpentTrace_width_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
        rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace left).toPattern +
        rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace right).toPattern := by
  have h0 := congrFun
    (totalCost_append (S := rhoGSLT) (A := Nat) (k := 2)
      rhoIntrinsicCostMap left right) 0
  calc
    rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
          totalCost rhoIntrinsicCostMap (rewritePathAppend left right) 0 := by
            exact rhoIntrinsicDirectSpentTrace_width_eq_totalCost_zero
              (rewritePathAppend left right)
    _ = totalCost rhoIntrinsicCostMap left 0 + totalCost rhoIntrinsicCostMap right 0 := by
      simpa using! h0
    _ =
        rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace left).toPattern +
        rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace right).toPattern := by
          rw [← rhoIntrinsicDirectSpentTrace_width_eq_totalCost_zero left,
            ← rhoIntrinsicDirectSpentTrace_width_eq_totalCost_zero right]

theorem rhoIntrinsicDirectSpentTrace_ticks_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
        rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace left).toPattern +
        rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace right).toPattern := by
  have h1 := congrFun
    (totalCost_append (S := rhoGSLT) (A := Nat) (k := 2)
      rhoIntrinsicCostMap left right) 1
  calc
    rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
          totalCost rhoIntrinsicCostMap (rewritePathAppend left right) 1 := by
            exact rhoIntrinsicDirectSpentTrace_ticks_eq_totalCost_one
              (rewritePathAppend left right)
    _ = totalCost rhoIntrinsicCostMap left 1 + totalCost rhoIntrinsicCostMap right 1 := by
      simpa using! h1
    _ =
        rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace left).toPattern +
        rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace right).toPattern := by
          rw [← rhoIntrinsicDirectSpentTrace_ticks_eq_totalCost_one left,
            ← rhoIntrinsicDirectSpentTrace_ticks_eq_totalCost_one right]

theorem rhoIntrinsicDirectSpentTrace_no_leak_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
        rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace left).toPattern +
        rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace right).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
          rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace left).toPattern +
          rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace right).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
          rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace left).toPattern +
          rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace right).toPattern ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toLedger) := by
  constructor
  · exact rhoIntrinsicDirectSpentTrace_account_rewritePathAppend left right
  · constructor
    · exact rhoIntrinsicDirectSpentTrace_width_rewritePathAppend left right
    · constructor
      · exact rhoIntrinsicDirectSpentTrace_ticks_rewritePathAppend left right
      · exact rhoIntrinsicDirectSpentTrace_traceCoherent (rewritePathAppend left right)

theorem rhoIntrinsicDirectSpentTrace_semantics_rewritePathAppend
    {t u v : Pattern}
    (left : rhoGSLT.RewritePath t u)
    (right : rhoGSLT.RewritePath u v) :
    (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toLedger =
        totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right) ∧
      (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPublicPattern =
        rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rewritePathAppend left right)) ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
          rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace left).toPattern +
          rhoSpentSyntaxAccount (rhoIntrinsicDirectSpentTrace right).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
          rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace left).toPattern +
          rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace right).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
          rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace left).toPattern +
          rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace right).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace (rewritePathAppend left right)).toPattern =
          (rewritePathAppend left right).length := by
  rcases rhoIntrinsicDirectSpentTrace_semantics (rewritePathAppend left right) with
    ⟨hsurf, hledger, hpublic, hcoh, _, _, _, _, _, _, hticksLen⟩
  rcases rhoIntrinsicDirectSpentTrace_no_leak_rewritePathAppend left right with
    ⟨hacc, hwidth, hticks, _⟩
  constructor
  · exact hsurf
  · constructor
    · exact hledger
    · constructor
      · exact hpublic
      · constructor
        · exact hcoh
        · constructor
          · exact hacc
          · constructor
            · exact hwidth
            · constructor
              · exact hticks
              · exact hticksLen

theorem rhoIntrinsicSemanticBridge_rewritePathAppend_steps
    {t u v : Pattern}
    (left : rhoGSLT.Step t u)
    (right : rhoGSLT.Step u v) :
    let path :=
      rewritePathAppend
        (oneStepPath (S := rhoGSLT) left)
        (oneStepPath (S := rhoGSLT) right)
    let stack := rhoIntrinsicDirectSpentStack path
    stack.toLedger = totalAction rhoIntrinsicLedgerAction path ∧
      rhoLedgerShadow stack.toLedger = totalCost rhoIntrinsicCostMap path ∧
      stack.depth = path.length ∧
      rhoSpentSyntaxAccount stack.toPattern = totalCost rhoIntrinsicCostMap path ∧
      rhoSpentSyntaxTicks stack.toPattern = path.length ∧
      stack =
        RhoDirectStack.append
          (rhoIntrinsicDirectSpentStack (oneStepPath (S := rhoGSLT) left))
          (rhoIntrinsicDirectSpentStack (oneStepPath (S := rhoGSLT) right)) ∧
      stack =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent left)
          (rhoIntrinsicDirectStepSpent right) ∧
      rhoIntrinsicDirectSpentTrace path =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent left)
          (rhoIntrinsicDirectStepSpent right) ∧
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) left))) +
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) right))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) left))) +
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) right))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) left))) +
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) right))) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace path).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) left)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) right)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace path).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) left)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) right)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace path).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) left)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) right)).toPattern ∧
      RhoLedger.TraceCoherent ((rhoIntrinsicDirectSpentTrace path).toLedger) := by
  dsimp
  rcases rhoIntrinsicDirectSpentStack_semantics_rewritePathAppend_steps left right with
    ⟨hLedger, hShadow, hDepth, hAccCost, hTicksLen, hAppendStack, hAppendStep, hTraceAppend⟩
  rcases rhoIntrinsicLedgerPublicSpentSyntax_semantics_rewritePathAppend
      (oneStepPath (S := rhoGSLT) left)
      (oneStepPath (S := rhoGSLT) right) with
    ⟨hPublicAcc, hPublicWidth, hPublicTicks, _, _⟩
  rcases rhoIntrinsicDirectSpentTrace_semantics_rewritePathAppend
      (oneStepPath (S := rhoGSLT) left)
      (oneStepPath (S := rhoGSLT) right) with
    ⟨_, _, _, hTraceCoherent, hDirectAcc, hDirectWidth, hDirectTicks, _⟩
  constructor
  · exact hLedger
  · constructor
    · exact hShadow
    · constructor
      · exact hDepth
      · constructor
        · exact hAccCost
        · constructor
          · exact hTicksLen
          · constructor
            · exact hAppendStack
            · constructor
              · exact hAppendStep
              · constructor
                · exact hTraceAppend
                · constructor
                  · exact hPublicAcc
                  · constructor
                    · exact hPublicWidth
                    · constructor
                      · exact hPublicTicks
                      · constructor
                        · exact hDirectAcc
                        · constructor
                          · exact hDirectWidth
                          · constructor
                            · exact hDirectTicks
                            · exact hTraceCoherent

noncomputable def rhoRewritePathOfReducesN
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) : rhoGSLT.RewritePath p q :=
  match h with
  | .zero p => GSLT.RewritePath.nil (S := rhoGSLT) p
  | .succ step rest =>
      GSLT.RewritePath.cons (S := rhoGSLT) ⟨step⟩ (rhoRewritePathOfReducesN rest)

@[simp] theorem rhoRewritePathOfReducesN_length
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) :
    (rhoRewritePathOfReducesN h).length = n := by
  induction h with
  | zero p =>
      change 0 = 0
      rfl
  | succ step rest ih =>
      change 1 + (rhoRewritePathOfReducesN rest).length = _ + 1
      simpa [Nat.add_comm] using congrArg Nat.succ ih

@[simp] theorem rhoRewritePathOfReducesN_oneStep
    {p q : Pattern} (step : Reduces p q) :
    rhoRewritePathOfReducesN (ReducesN.succ step (.zero q)) =
      oneStepPath (S := rhoGSLT) ⟨step⟩ := by
  rfl

theorem rhoIntrinsicLedgerPublicSpentSyntax_modulus_reducesN
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) :
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
          totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
            totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 1 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
            n := by
  rcases rhoIntrinsicLedgerTotalAction_publicSpentSyntax_modulus
      (rhoRewritePathOfReducesN h) with ⟨hwidth, hticksCost, hticksLen⟩
  constructor
  · exact hwidth
  · constructor
    · exact hticksCost
    · simpa [rhoRewritePathOfReducesN_length h] using hticksLen

theorem rhoIntrinsicLedgerPublicSpentSyntax_semantics_reducesN
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
          totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
            totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
            totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 1 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
            n ∧
      RhoLedger.TraceCoherent
        (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h)) := by
  rcases rhoIntrinsicLedgerPublicSpentSyntax_semantics
      (rhoRewritePathOfReducesN h) with
      ⟨hacc, hwidth, hticksCost, hticksLen, hcoh⟩
  constructor
  · exact hacc
  · constructor
    · exact hwidth
    · constructor
      · exact hticksCost
      · constructor
        · simpa [rhoRewritePathOfReducesN_length h] using hticksLen
        · exact hcoh

theorem rhoIntrinsicDirectSpentTrace_modulus_reducesN
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) :
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
        totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 0 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
          totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 1 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
          n := by
  rcases rhoIntrinsicDirectSpentTrace_modulus
      (rhoRewritePathOfReducesN h) with ⟨hwidth, hticksCost, hticksLen⟩
  constructor
  · exact hwidth
  · constructor
    · exact hticksCost
    · simpa [rhoRewritePathOfReducesN_length h] using hticksLen

theorem rhoIntrinsicDirectSpentTrace_semantics_reducesN
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) :
    (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toLedger =
        totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h) ∧
      (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPublicPattern =
        rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h)) ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
          totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
          totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 0 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
          totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 1 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
          n := by
  rcases rhoIntrinsicDirectSpentTrace_semantics
      (rhoRewritePathOfReducesN h) with
      ⟨hsurf, hledger, hpublicExact, hcoh, haccPublic, haccCost, hwidthPublic, hwidthCost,
        hticksPublic, hticksCost, hticksLen⟩
  constructor
  · exact hsurf
  · constructor
    · exact hledger
    · constructor
      · exact hpublicExact
      · constructor
        · exact hcoh
        · constructor
          · exact haccPublic
          · constructor
            · exact haccCost
            · constructor
              · exact hwidthPublic
              · constructor
                · exact hwidthCost
                · constructor
                  · exact hticksPublic
                  · constructor
                    · exact hticksCost
                    · simpa [rhoRewritePathOfReducesN_length h] using hticksLen

/-- The first continued ρ presentation uses the shared vectorial-account
carrier from `WeightCost` together with an intrinsic spent account derived
from the actual COMM redex.

This keeps the continued layer honest while the explicit cost-accounted term
grammar is still being formalized separately.
-/
noncomputable def rhoContinuedCutPresentation : ContinuedCutPresentation rhoGSLT where
  symmetricCut := rhoSymmetricCutPresentation
  Grade := RhoLedger
  Spent := RhoLedger
  reprSection := equationsSection rhoGSLT
  reprSection_spec := equationsSection_spec rhoGSLT
  contractWrapped := fun chan _name body payload =>
    { left := { term := semanticCommSubst body.term payload.term, grade := body.grade }
      right := { term := rhoNil, grade := payload.grade }
      spent := rhoIntrinsicCommLedger chan payload.term }
  contractWrapped_fst_term := by
    intro chan nm body payload
    rfl
  contractWrapped_snd_term := by
    intro chan nm body payload
    rfl

/-- The continued rho step records the intrinsic account extracted from the
COMM redex itself. -/
theorem rhoContinuedCutPresentation_spent
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    (rhoContinuedCutPresentation.contractWrapped chan nm body payload).spent =
      rhoIntrinsicCommLedger chan payload.term := by
  rfl

/-- The richer spent ledger still projects to the previously verified vectorial
shadow account. -/
theorem rhoContinuedCutPresentation_spent_shadow
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    rhoLedgerShadow
      ((rhoContinuedCutPresentation.contractWrapped chan nm body payload).spent) =
        rhoIntrinsicCommAccount chan payload.term := by
  show rhoLedgerShadow (rhoIntrinsicCommLedger chan payload.term) =
      rhoIntrinsicCommAccount chan payload.term
  simp

theorem rhoContinuedCutPresentation_spent_traceCoherent
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    RhoLedger.TraceCoherent
      ((rhoContinuedCutPresentation.contractWrapped chan nm body payload).spent) := by
  show RhoLedger.TraceCoherent (rhoIntrinsicCommLedger chan payload.term)
  simp

theorem rhoContinuedCutPresentation_preserves_direct_witness
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    let step : AccountedCutStep Pattern RhoLedger RhoLedger :=
      rhoContinuedCutPresentation.contractWrapped chan nm body payload
    let direct := RhoDirectCutWitness.ofAccountedStep step
    direct.left.body = step.left.term ∧
      direct.left.sig.toSignature = step.left.grade.spatial ∧
      direct.right.body = step.right.term ∧
      direct.right.sig.toSignature = step.right.grade.spatial ∧
      direct.spent.toLedger = step.spent ∧
      direct.spent.depth = step.spent.temporalList.length := by
  constructor
  · rfl
  · constructor
    · simp [RhoDirectCutWitness.ofAccountedStep]
    · constructor
      · rfl
      · constructor
        · simp [RhoDirectCutWitness.ofAccountedStep]
        · constructor
          · exact RhoDirectCutWitness_ofAccountedStep_spent_ledger
              (rhoContinuedCutPresentation.contractWrapped chan nm body payload)
              (rhoContinuedCutPresentation_spent_traceCoherent chan nm body payload)
          · simpa [RhoDirectCutWitness.ofAccountedStep] using
              (RhoDirectStack_depth_ofTrace
                ((rhoContinuedCutPresentation.contractWrapped chan nm body payload).spent.temporalList))

theorem rhoContinuedCutPresentation_spent_syntax_eq_shadow
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        ((rhoContinuedCutPresentation.contractWrapped chan nm body payload).spent)) =
          rhoLedgerShadow
            ((rhoContinuedCutPresentation.contractWrapped chan nm body payload).spent) := by
  refine rhoLedgerToSpentSyntax_shadow_of_traceCoherent _ ?_
  exact rhoContinuedCutPresentation_spent_traceCoherent chan nm body payload

/-- The continued rho contraction does not mutate wrapped residual grades:
all new accounting appears only in the explicit spent field, and that spent
field is itself a well-formed wrapped ledger fragment. -/
theorem rhoContinuedCutPresentation_no_leak
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    (rhoContinuedCutPresentation.contractWrapped chan nm body payload).left.grade = body.grade ∧
      (rhoContinuedCutPresentation.contractWrapped chan nm body payload).right.grade = payload.grade ∧
      (rhoContinuedCutPresentation.contractWrapped chan nm body payload).spent =
        rhoIntrinsicCommLedger chan payload.term ∧
      RhoLedger.WellFormedSpent
        ((rhoContinuedCutPresentation.contractWrapped chan nm body payload).spent) := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · exact rhoIntrinsicCommLedger_wellFormed _ _

/-- Balance-form no-leak statement over the current shared 2-coordinate carrier:
the wrapped residual grades conserve their total, and the consumed account is
recorded explicitly in the spent field while remaining a well-formed wrapped
ledger fragment. -/
theorem rhoContinuedCutPresentation_balance_no_leak
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    let step : AccountedCutStep Pattern RhoLedger RhoLedger :=
      rhoContinuedCutPresentation.contractWrapped chan nm body payload
    step.left.grade + step.right.grade = body.grade + payload.grade ∧
      step.spent = rhoIntrinsicCommLedger chan payload.term ∧
      RhoLedger.WellFormedSpent step.spent ∧
      rhoLedgerShadow step.spent = rhoIntrinsicCommAccount chan payload.term := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · exact rhoIntrinsicCommLedger_wellFormed _ _
      · exact rhoIntrinsicCommLedger_shadow _ _

/-- A stronger structural preservation theorem for the current wrapped rho layer:
residuals stay wrapped with their original grades, and the emitted spent ledger
is a well-formed one-step fragment. -/
theorem rhoContinuedCutPresentation_preserves_wrapped_structure
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    let step : AccountedCutStep Pattern RhoLedger RhoLedger :=
      rhoContinuedCutPresentation.contractWrapped chan nm body payload
    step.left.term = semanticCommSubst body.term payload.term ∧
      step.right.term = rhoNil ∧
      step.left.grade = body.grade ∧
      step.right.grade = payload.grade ∧
      RhoLedger.WellFormedSpent step.spent := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · exact rhoIntrinsicCommLedger_wellFormed _ _

private def rhoContinuedCutPresentation_contactStepWitness
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    rhoGSLT.Step
      (rhoSymmetricCutPresentation.contact
        (rhoSymmetricCutPresentation.rightIntro chan payload.term)
        (rhoSymmetricCutPresentation.leftIntro chan body.term))
      (rhoSymmetricCutPresentation.contact
        (rhoContinuedCutPresentation.contractWrapped chan nm body payload).left.term
        (rhoContinuedCutPresentation.contractWrapped chan nm body payload).right.term) := by
  let source :=
    rhoSymmetricCutPresentation.contact
      (rhoSymmetricCutPresentation.rightIntro chan payload.term)
      (rhoSymmetricCutPresentation.leftIntro chan body.term)
  let mid :=
    (.collection .hashBag [semanticCommSubst body.term payload.term] none : Pattern)
  let target :=
    rhoSymmetricCutPresentation.contact
      (rhoContinuedCutPresentation.contractWrapped chan nm body payload).left.term
      (rhoContinuedCutPresentation.contractWrapped chan nm body payload).right.term
  refine ⟨@Reduces.equiv source source target mid (StructuralCongruence.refl _) ?_ ?_⟩
  · simpa [source, mid, rhoSymmetricCutPresentation, rhoContact, rhoIntroP, rhoIntroE] using
      (@Reduces.comm chan payload.term body.term [])
  ·
    have hsingleton : StructuralCongruence mid (semanticCommSubst body.term payload.term) := by
      exact StructuralCongruence.par_singleton _
    have hnil :
        StructuralCongruence
          (semanticCommSubst body.term payload.term)
          (.collection .hashBag
            [semanticCommSubst body.term payload.term, rhoNil] none) := by
      exact StructuralCongruence.symm _ _ (StructuralCongruence.par_nil_right _)
    simpa [mid, target, rhoSymmetricCutPresentation, rhoContact, rhoContinuedCutPresentation, rhoNil] using
      StructuralCongruence.trans _ _ _ hsingleton hnil

/-- A wrapped rho communication step erases to a real `rhoGSLT.Step` at the
contact site, with the inert sender residual retained explicitly as `rhoNil`.

This is the generic one-step bridge from the continued presentation back into
the underlying rho reduction graph. -/
theorem rhoContinuedCutPresentation_contact_step
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    rhoGSLT.Step
      (rhoSymmetricCutPresentation.contact
        (rhoSymmetricCutPresentation.rightIntro chan payload.term)
        (rhoSymmetricCutPresentation.leftIntro chan body.term))
      (rhoSymmetricCutPresentation.contact
      (rhoContinuedCutPresentation.contractWrapped chan nm body payload).left.term
      (rhoContinuedCutPresentation.contractWrapped chan nm body payload).right.term) := by
  exact rhoContinuedCutPresentation_contactStepWitness chan nm body payload

/-- The wrapped rho contraction erases to the base COMM contraction. -/
theorem rhoContinuedCutPresentation_contract_erases
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    ((rhoContinuedCutPresentation.contractWrapped chan nm body payload).left.term,
      (rhoContinuedCutPresentation.contractWrapped chan nm body payload).right.term) =
      rhoSymmetricCutPresentation.contract chan nm body.term payload.term := by
  exact contractWrapped_erases rhoContinuedCutPresentation chan nm body payload

/-- The first wrapped rho residual transports to the representative residual. -/
theorem rhoContinuedCutPresentation_contract_fst_transport_to_representative
    (chan nm : Pattern) (body payload : WrappedTerm Pattern RhoLedger) :
    ProcResidualEquiv
      (rhoContinuedCutPresentation.contractWrapped chan nm body payload).left.term
      (semanticCommRepresentative body.term payload.term) := by
  simpa [rhoContinuedCutPresentation] using
    semanticCommSubst_transport_to_representative body.term payload.term

end RhoExample
end Mettapedia.GSLT.Meredith
