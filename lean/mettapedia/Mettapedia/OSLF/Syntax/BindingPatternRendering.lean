import Mettapedia.OSLF.Syntax.TermClone
import Mettapedia.OSLF.MeTTaIL.ContextSubstitution

/-!
# Rendering binding signatures into canonical patterns

A constructor rendering is required to commute with raw index shifting and
simultaneous substitution. Its recursive extension then preserves the entire
binding-clone substitution action. The hypothesis is local to each rendered
constructor; the conclusion covers arbitrary terms, binder lists, and
context changes. This compares raw syntax only. Quotient equations, source
validation, and operational firing require separate comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.PatternRendering

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution

variable {S : Signature}

/-- A constructor rendering that respects the two operations needed when a
context is extended or substituted. -/
structure Rendering (S : Signature) where
  operation : {s : S.Srt} → S.Op s → List Pattern → Pattern
  shift : ∀ {s : S.Srt} (op : S.Op s) (args : List Pattern)
      (cutoff amount : Nat),
    liftBVars cutoff amount (operation op args) =
      operation op (liftBVarsList cutoff amount args)
  bind : ∀ {s : S.Srt} (op : S.Op s) (args : List Pattern)
      (assignment : Assignment),
    substitute assignment (operation op args) =
      operation op (substituteList assignment args)

/-- The binder list is rendered in the same order as an intrinsic argument's
extended context. -/
def wrapBinders {α : Type} (binders : List α) (body : Pattern) : Pattern :=
  binders.foldr (fun _ result => .lambda none result) body

theorem wrapBinders_wellScoped {α : Type} (binders : List α)
    (body : Pattern) (depth : Nat) :
    (wrapBinders binders body).isWellScopedAt depth =
      body.isWellScopedAt (depth + binders.length) := by
  induction binders generalizing depth with
  | nil => rfl
  | cons binder rest ih =>
      change (wrapBinders rest body).isWellScopedAt (depth + 1) =
        body.isWellScopedAt (depth + (rest.length + 1))
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (depth + 1)

mutual
/-- Read an intrinsically scoped term in the authored pattern carrier. -/
def encodeTerm (R : Rendering S) : {Γ : Ctx S} → {s : S.Srt} →
    Term S Γ s → Pattern
  | _, _, .var v => .bvar (varIdx v).val
  | _, _, .op op args => R.operation op (encodeArgs R args)

/-- Read each argument beneath exactly its declared local binders. -/
def encodeArgs (R : Rendering S) :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args S arity Γ → List Pattern
  | _, _, .nil => []
  | _, _, .cons (bs := bs) head tail =>
      wrapBinders bs (encodeTerm R head) :: encodeArgs R tail
end

/-- A rendering respects the scope judgment at each constructor. -/
def ScopePreserving (R : Rendering S) : Prop :=
  ∀ {s : S.Srt} (op : S.Op s) (args : List Pattern) (depth : Nat),
    Pattern.isWellScopedListAt depth args = true →
      (R.operation op args).isWellScopedAt depth = true

mutual
/-- Every intrinsic term lowers to a well-scoped raw pattern when each
constructor respects the ordinary scope check. -/
theorem encodeTerm_wellScoped (R : Rendering S)
    (hR : ScopePreserving R) :
    ∀ {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s),
      (encodeTerm R term).isWellScopedAt Γ.length = true
  | _, _, .var v => by
      change decide ((varIdx v).val < _) = true
      exact decide_eq_true (varIdx v).isLt
  | _, _, .op op args =>
      hR op (encodeArgs R args) _ (encodeArgs_wellScoped R hR args)

theorem encodeArgs_wellScoped (R : Rendering S)
    (hR : ScopePreserving R) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args S arity Γ),
      Pattern.isWellScopedListAt Γ.length (encodeArgs R args) = true
  | _, _, .nil => rfl
  | _, Γ, .cons (bs := bs) head tail => by
      simp only [encodeArgs, Pattern.isWellScopedListAt,
        Bool.and_eq_true, wrapBinders_wellScoped]
      constructor
      · simpa [List.length_append, Nat.add_comm] using
          encodeTerm_wellScoped R hR head
      · exact encodeArgs_wellScoped R hR tail
end

/-- A source renaming is a numerical insertion at the displayed cutoff. -/
def EncodedShift {Γ Δ : Ctx S} (rho : Ren S Γ Δ)
    (cutoff amount : Nat) : Prop :=
  ∀ (s : S.Srt) (v : Var Γ s),
    (varIdx (rho s v)).val =
      if cutoff ≤ (varIdx v).val then (varIdx v).val + amount
      else (varIdx v).val

theorem encodedShift_liftRen {Γ Δ : Ctx S} (rho : Ren S Γ Δ)
    (cutoff amount : Nat) (h : EncodedShift rho cutoff amount) :
    ∀ bs : List S.Srt,
      EncodedShift (liftRen rho bs) (cutoff + bs.length) amount
  | [] => by simpa [EncodedShift, liftRen] using h
  | _ :: bs => by
      intro s v
      cases v with
      | zero => simp [liftRen, varIdx]
      | succ w =>
          have hw := encodedShift_liftRen rho cutoff amount h bs s w
          change (varIdx (liftRen rho bs s w)).val + 1 =
            if cutoff + (bs.length + 1) ≤ (varIdx w).val + 1
            then (varIdx w).val + 1 + amount else (varIdx w).val + 1
          rw [hw]
          split_ifs <;> omega

theorem liftBVars_wrapBinders {α : Type} (bs : List α)
    (pattern : Pattern) (cutoff amount : Nat) :
    liftBVars cutoff amount (wrapBinders bs pattern) =
      wrapBinders bs (liftBVars (cutoff + bs.length) amount pattern) := by
  induction bs generalizing cutoff with
  | nil => rfl
  | cons binder bs ih =>
      calc
        liftBVars cutoff amount (wrapBinders (binder :: bs) pattern) =
            .lambda none
              (liftBVars (cutoff + 1) amount (wrapBinders bs pattern)) := rfl
        _ = .lambda none
              (wrapBinders bs
                (liftBVars ((cutoff + 1) + bs.length) amount pattern)) :=
            congrArg (Pattern.lambda none) (ih (cutoff + 1))
        _ = wrapBinders (binder :: bs)
              (liftBVars (cutoff + (binder :: bs).length) amount pattern) := by
            have hlen : (cutoff + 1) + bs.length =
                cutoff + (bs.length + 1) := by omega
            rw [hlen]
            rfl

mutual
theorem encodeTerm_rename_shift (R : Rendering S) :
    ∀ {Γ Δ : Ctx S} {s : S.Srt} (rho : Ren S Γ Δ)
      (cutoff amount : Nat) (_ : EncodedShift rho cutoff amount)
      (term : Term S Γ s),
      encodeTerm R (rename rho term) =
        liftBVars cutoff amount (encodeTerm R term)
  | _, _, _, rho, cutoff, amount, h, .var v => by
      simp only [rename, encodeTerm, liftBVars]
      rw [h _ v]
      split_ifs <;> rfl
  | _, _, _, rho, cutoff, amount, h, .op op args => by
      have hargs := encodeArgs_rename_shift R rho cutoff amount h args
      simp only [rename, encodeTerm, R.shift]
      exact congrArg (R.operation op) hargs

theorem encodeArgs_rename_shift (R : Rendering S) :
    ∀ {ars : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S}
      (rho : Ren S Γ Δ) (cutoff amount : Nat)
      (_ : EncodedShift rho cutoff amount) (args : Args S ars Γ),
      encodeArgs R (renameArgs rho args) =
        liftBVarsList cutoff amount (encodeArgs R args)
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, rho, cutoff, amount, h, .cons (bs := bs) head tail => by
      simp only [renameArgs, encodeArgs, liftBVarsList]
      rw [liftBVars_wrapBinders]
      rw [encodeTerm_rename_shift R (liftRen rho bs) (cutoff + bs.length)
        amount (encodedShift_liftRen rho cutoff amount h bs) head]
      rw [encodeArgs_rename_shift R rho cutoff amount h tail]
end

theorem encodeTerm_weaken (R : Rendering S) {Γ : Ctx S} {s : S.Srt}
    (binder : S.Srt) (term : Term S Γ s) :
    encodeTerm R (weaken (t := binder) term) =
      liftBVars 0 1 (encodeTerm R term) := by
  apply encodeTerm_rename_shift R (fun _ v => Var.succ v) 0 1
  intro _ v
  simp [varIdx]

/-- An assignment represents the sorted substitution on declared source
variables; values outside that source context are unrestricted. -/
def EncodedAssignment (R : Rendering S) {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) (assignment : Assignment) : Prop :=
  ∀ (s : S.Srt) (v : Var Γ s),
    assignment (varIdx v).val = encodeTerm R (sigma s v)

theorem encodedAssignment_lift (R : Rendering S) {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) (assignment : Assignment)
    (valid : EncodedAssignment R sigma assignment) :
    ∀ binders : List S.Srt,
      EncodedAssignment R (liftSub sigma binders)
        (lift binders.length assignment)
  | [] => by simpa [EncodedAssignment, liftSub, lift_zero] using valid
  | binder :: binders => by
      intro s v
      cases v with
      | zero =>
          change lift (binder :: binders).length assignment 0 =
            Pattern.bvar 0
          simp [lift]
      | succ w =>
          have inner :=
            encodedAssignment_lift R sigma assignment valid binders s w
          change lift ((binder :: binders).length) assignment
              (varIdx w).val.succ =
            encodeTerm R (weaken (liftSub sigma binders s w))
          rw [show (binder :: binders).length = binders.length + 1 by rfl]
          rw [← lift_lift 1 binders.length assignment]
          change liftBVars 0 1
              (lift binders.length assignment (varIdx w).val) = _
          rw [inner]
          exact (encodeTerm_weaken R binder
            (liftSub sigma binders s w)).symm

theorem substitute_wrapBinders {α : Type} (binders : List α)
    (assignment : Assignment) (pattern : Pattern) :
    substitute assignment (wrapBinders binders pattern) =
      wrapBinders binders
        (substitute (lift binders.length assignment) pattern) := by
  induction binders generalizing assignment with
  | nil => simp [wrapBinders, lift_zero]
  | cons binder binders ih =>
      calc
        substitute assignment (wrapBinders (binder :: binders) pattern) =
            .lambda none (substitute (lift 1 assignment)
              (wrapBinders binders pattern)) := rfl
        _ = .lambda none (wrapBinders binders
              (substitute (lift binders.length (lift 1 assignment)) pattern)) :=
            congrArg (Pattern.lambda none) (ih (lift 1 assignment))
        _ = wrapBinders (binder :: binders)
              (substitute (lift (binder :: binders).length assignment) pattern) := by
            have hlen : 1 + binders.length = (binder :: binders).length := by
              simp [Nat.add_comm]
            rw [lift_lift, hlen]
            rfl

mutual
theorem encodeTerm_bind_of_assignment (R : Rendering S) :
    ∀ {Γ Δ : Ctx S} {s : S.Srt}
      (sigma : Sub S Γ Δ) (assignment : Assignment)
      (_ : EncodedAssignment R sigma assignment) (term : Term S Γ s),
      encodeTerm R (bind sigma term) =
        substitute assignment (encodeTerm R term)
  | _, _, _, sigma, assignment, valid, .var v => by
      simpa only [bind, encodeTerm, substitute] using (valid _ v).symm
  | _, _, _, sigma, assignment, valid, .op op args => by
      have hargs :=
        encodeArgs_bind_of_assignment R sigma assignment valid args
      simp only [bind, encodeTerm, R.bind]
      exact congrArg (R.operation op) hargs

theorem encodeArgs_bind_of_assignment (R : Rendering S) :
    ∀ {ars : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S}
      (sigma : Sub S Γ Δ) (assignment : Assignment)
      (_ : EncodedAssignment R sigma assignment) (args : Args S ars Γ),
      encodeArgs R (bindArgs sigma args) =
        substituteList assignment (encodeArgs R args)
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, sigma, assignment, valid, .cons (bs := bs) head tail => by
      simp only [bindArgs, encodeArgs, substituteList]
      rw [substitute_wrapBinders]
      rw [encodeTerm_bind_of_assignment R (liftSub sigma bs)
        (lift bs.length assignment)
        (encodedAssignment_lift R sigma assignment valid bs) head]
      rw [encodeArgs_bind_of_assignment R sigma assignment valid tail]
end

/-- Finite substitution values in the source context's de Bruijn order. -/
def encodeSubValues (R : Rendering S) :
    (Γ : Ctx S) → {Δ : Ctx S} → Sub S Γ Δ → List Pattern
  | [], _, _ => []
  | s :: Γ, _, sigma =>
      encodeTerm R (sigma s Var.zero) ::
        encodeSubValues R Γ (fun t v => sigma t (Var.succ v))

/-- Totalize the finite sorted assignment by fixing undeclared indices. -/
def encodeSub (R : Rendering S) {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) : Assignment :=
  fun index => (encodeSubValues R Γ sigma)[index]?.getD (.bvar index)

theorem encodeSubValues_length (R : Rendering S) :
    ∀ (Γ : Ctx S) {Δ : Ctx S} (sigma : Sub S Γ Δ),
      (encodeSubValues R Γ sigma).length = Γ.length
  | [], _, _ => rfl
  | _ :: Γ, _, sigma => by
      simpa [encodeSubValues] using
        congrArg Nat.succ
          (encodeSubValues_length R Γ (fun t v => sigma t (Var.succ v)))

theorem encodeSub_at_var (R : Rendering S) :
    ∀ {Γ Δ : Ctx S} (sigma : Sub S Γ Δ)
      {s : S.Srt} (v : Var Γ s),
      encodeSub R sigma (varIdx v).val = encodeTerm R (sigma s v)
  | _ :: _, _, sigma, _, .zero => rfl
  | _ :: Γ, _, sigma, _, .succ w => by
      let tailSigma : Sub S Γ _ := fun t v => sigma t (Var.succ v)
      have hi : (varIdx w).val < (encodeSubValues R Γ tailSigma).length := by
        rw [encodeSubValues_length]
        exact (varIdx w).isLt
      simpa [encodeSub, encodeSubValues, varIdx,
        List.getElem?_eq_getElem hi, tailSigma] using
        encodeSub_at_var R tailSigma w

theorem encodeSub_valid (R : Rendering S) {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) : EncodedAssignment R sigma (encodeSub R sigma) := by
  intro s v
  exact encodeSub_at_var R sigma v

/-- The generic binding-rendering square: source substitution and actual
pattern substitution agree at every intrinsically sorted term. -/
theorem encodeTerm_bind (R : Rendering S) {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) {s : S.Srt} (term : Term S Γ s) :
    encodeTerm R (bind sigma term) =
      substitute (encodeSub R sigma) (encodeTerm R term) :=
  encodeTerm_bind_of_assignment R sigma (encodeSub R sigma)
    (encodeSub_valid R sigma) term

theorem encodeArgs_bind (R : Rendering S)
    {ars : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) (args : Args S ars Γ) :
    encodeArgs R (bindArgs sigma args) =
      substituteList (encodeSub R sigma) (encodeArgs R args) :=
  encodeArgs_bind_of_assignment R sigma (encodeSub R sigma)
    (encodeSub_valid R sigma) args

theorem encodeSub_id_at_var (R : Rendering S) {Γ : Ctx S}
    {s : S.Srt} (v : Var Γ s) :
    encodeSub R (fun _ w => Term.var w : Sub S Γ Γ) (varIdx v).val =
      Pattern.bvar (varIdx v).val := by
  simpa only [encodeTerm] using
    encodeSub_at_var R (fun _ w => Term.var w : Sub S Γ Γ) v

theorem encodeSub_comp_at_var (R : Rendering S) {Γ Δ Θ : Ctx S}
    (first : Sub S Γ Δ) (second : Sub S Δ Θ)
    {s : S.Srt} (v : Var Γ s) :
    encodeSub R (fun t w => bind second (first t w)) (varIdx v).val =
      substitute (encodeSub R second)
        (encodeSub R first (varIdx v).val) := by
  rw [encodeSub_at_var, encodeSub_at_var]
  exact encodeTerm_bind R second (first s v)

#print axioms encodeTerm_bind
#print axioms encodeSub_comp_at_var

end Mettapedia.OSLF.Binding.PatternRendering
