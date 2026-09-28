import Mettapedia.OSLF.Syntax.RhoIntrinsicEncoding
import Mettapedia.OSLF.MeTTaIL.ContextSubstitution

/-!
# Scoped rho substitution in the authored pattern carrier

The intrinsic rho signature and the authored pattern syntax represent the
same de Bruijn context variables in different ways. This module translates
finite sorted substitutions to the existing total pattern assignment and
proves that the two actual substitution operations commute on every intrinsic
term and argument vector. The binder case uses the source lift and the
pattern lift, including weakening of ambient images.

The assignment's values outside its declared source context are an arbitrary
total extension. Identity and composition are stated at declared variables,
where they carry mathematical content. This is a raw-syntax theorem; passage
through canonicalization and the authored equation quotient requires the
separate support and quotation hypotheses of that layer.
-/

namespace Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution

set_option autoImplicit false

/-- The numerical action of a renaming that inserts `amount` context slots at
`cutoff`. -/
def EncodedShift {Γ Δ : Ctx sig} (rho : Ren sig Γ Δ)
    (cutoff amount : Nat) : Prop :=
  ∀ (s : Srt) (v : Var Γ s),
    (varIdx (rho s v)).val =
      if cutoff ≤ (varIdx v).val then (varIdx v).val + amount else (varIdx v).val

/-- Lifting a source renaming through an argument binder moves the insertion
cutoff past exactly those newly bound variables. -/
theorem encodedShift_liftRen {Γ Δ : Ctx sig} (rho : Ren sig Γ Δ)
    (cutoff amount : Nat) (h : EncodedShift rho cutoff amount) :
    ∀ bs : List Srt,
      EncodedShift (liftRen rho bs) (cutoff + bs.length) amount
  | [] => by simpa [EncodedShift, liftRen] using h
  | _ :: bs => by
      intro s v
      cases v with
      | zero =>
          simp [liftRen, varIdx]
      | succ w =>
          have hw := encodedShift_liftRen rho cutoff amount h bs s w
          change (varIdx (liftRen rho bs s w)).val + 1 =
            if cutoff + (bs.length + 1) ≤ (varIdx w).val + 1
            then (varIdx w).val + 1 + amount else (varIdx w).val + 1
          rw [hw]
          split_ifs <;> omega

/-- Pattern index shifting passes under the encoded binder list. -/
theorem liftBVars_wrapBinders (bs : List Srt) (pattern : Pattern)
    (cutoff amount : Nat) :
    liftBVars cutoff amount (wrapBinders bs pattern) =
      wrapBinders bs (liftBVars (cutoff + bs.length) amount pattern) := by
  induction bs generalizing cutoff with
  | nil => rfl
  | cons binder bs ih =>
      calc
        liftBVars cutoff amount (wrapBinders (binder :: bs) pattern) =
            .lambda none (liftBVars (cutoff + 1) amount (wrapBinders bs pattern)) := rfl
        _ = .lambda none (wrapBinders bs
              (liftBVars ((cutoff + 1) + bs.length) amount pattern)) :=
            congrArg (Pattern.lambda none) (ih (cutoff + 1))
        _ = wrapBinders (binder :: bs)
              (liftBVars (cutoff + (binder :: bs).length) amount pattern) := by
            have hlen : (cutoff + 1) + bs.length = cutoff + (bs.length + 1) := by
              omega
            rw [hlen]
            rfl

mutual
/-- The intrinsic encoding commutes with a context insertion, at every
operator and under the input binder. -/
theorem encodeTerm_rename_shift : ∀ {Γ Δ : Ctx sig} {s : Srt}
    (rho : Ren sig Γ Δ) (cutoff amount : Nat)
    (_ : EncodedShift rho cutoff amount) (term : Term sig Γ s),
    encodeTerm (rename rho term) =
      liftBVars cutoff amount (encodeTerm term)
  | _, _, _, rho, cutoff, amount, h, .var v => by
      simp only [rename, encodeTerm, liftBVars]
      rw [h _ v]
      split_ifs <;> rfl
  | _, _, _, rho, cutoff, amount, h, .op op args => by
      have hargs := encodeArgs_rename_shift rho cutoff amount h args
      cases op
      · rfl
      · simpa only [rename, encodeTerm, liftBVars] using
          congrArg (fun xs => Pattern.collection .hashBag xs none) hargs
      · simpa only [rename, encodeTerm, liftBVars] using
          congrArg (Pattern.apply "POutput") hargs
      · simpa only [rename, encodeTerm, liftBVars] using
          congrArg (Pattern.apply "PInput") hargs
      · simpa only [rename, encodeTerm, liftBVars] using
          congrArg (Pattern.apply "NQuote") hargs
      · simpa only [rename, encodeTerm, liftBVars] using
          congrArg (Pattern.apply "PDrop") hargs

/-- Argument-vector companion to `encodeTerm_rename_shift`. -/
theorem encodeArgs_rename_shift : ∀ {ars : List (List Srt × Srt)}
    {Γ Δ : Ctx sig} (rho : Ren sig Γ Δ) (cutoff amount : Nat)
    (_ : EncodedShift rho cutoff amount) (args : Args sig ars Γ),
    encodeArgs (renameArgs rho args) =
      liftBVarsList cutoff amount (encodeArgs args)
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, rho, cutoff, amount, h, .cons (bs := bs) head tail => by
      simp only [renameArgs, encodeArgs, liftBVarsList]
      rw [liftBVars_wrapBinders]
      rw [encodeTerm_rename_shift (liftRen rho bs) (cutoff + bs.length)
        amount (encodedShift_liftRen rho cutoff amount h bs) head]
      rw [encodeArgs_rename_shift rho cutoff amount h tail]
end

/-- One-slot weakening is exactly one-slot pattern index lifting. -/
theorem encodeTerm_weaken {Γ : Ctx sig} {s : Srt}
    (binder : Srt) (term : Term sig Γ s) :
    encodeTerm (weaken (t := binder) term) =
      liftBVars 0 1 (encodeTerm term) := by
  apply encodeTerm_rename_shift (fun _ v => Var.succ v) 0 1
  intro _ v
  simp [varIdx]

/-- A raw assignment represents a sorted substitution on every declared
source variable. Its out-of-range behavior is intentionally unconstrained. -/
def EncodedAssignment {Γ Δ : Ctx sig}
    (sigma : Sub sig Γ Δ) (assignment : Assignment) : Prop :=
  ∀ (s : Srt) (v : Var Γ s),
    assignment (varIdx v).val = encodeTerm (sigma s v)

/-- Both substitution lifts agree on every variable in the extended context. -/
theorem encodedAssignment_lift {Γ Δ : Ctx sig}
    (sigma : Sub sig Γ Δ) (assignment : Assignment)
    (valid : EncodedAssignment sigma assignment) :
    ∀ binders : List Srt,
      EncodedAssignment (liftSub sigma binders)
        (lift binders.length assignment)
  | [] => by simpa [EncodedAssignment, liftSub, lift_zero] using valid
  | binder :: binders => by
      intro s v
      cases v with
      | zero =>
          change lift (binder :: binders).length assignment 0 = Pattern.bvar 0
          simp [lift]
      | succ w =>
          have inner := encodedAssignment_lift sigma assignment valid binders s w
          change lift ((binder :: binders).length) assignment
              (varIdx w).val.succ =
            encodeTerm (weaken (liftSub sigma binders s w))
          rw [show (binder :: binders).length = binders.length + 1 by rfl]
          rw [← lift_lift 1 binders.length assignment]
          change liftBVars 0 1
              (lift binders.length assignment (varIdx w).val) = _
          rw [inner]
          exact (encodeTerm_weaken binder (liftSub sigma binders s w)).symm

/-- The consumer's simultaneous substitution moves beneath the exact number
of binders emitted by the intrinsic argument encoder. -/
theorem substitute_wrapBinders (binders : List Srt)
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
/-- Any assignment representing a sorted substitution commutes with raw term
encoding; the proof uses the actual pattern substitution function. -/
theorem encodeTerm_bind_of_assignment : ∀ {Γ Δ : Ctx sig} {s : Srt}
    (sigma : Sub sig Γ Δ) (assignment : Assignment)
    (_ : EncodedAssignment sigma assignment) (term : Term sig Γ s),
    encodeTerm (bind sigma term) =
      substitute assignment (encodeTerm term)
  | _, _, _, sigma, assignment, valid, .var v => by
      simpa only [bind, encodeTerm, substitute] using (valid _ v).symm
  | _, _, _, sigma, assignment, valid, .op op args => by
      have hargs := encodeArgs_bind_of_assignment sigma assignment valid args
      cases op
      · rfl
      · simpa only [bind, encodeTerm, substitute] using
          congrArg (fun xs => Pattern.collection .hashBag xs none) hargs
      · simpa only [bind, encodeTerm, substitute] using
          congrArg (Pattern.apply "POutput") hargs
      · simpa only [bind, encodeTerm, substitute] using
          congrArg (Pattern.apply "PInput") hargs
      · simpa only [bind, encodeTerm, substitute] using
          congrArg (Pattern.apply "NQuote") hargs
      · simpa only [bind, encodeTerm, substitute] using
          congrArg (Pattern.apply "PDrop") hargs

/-- Argument-vector companion to `encodeTerm_bind_of_assignment`. -/
theorem encodeArgs_bind_of_assignment : ∀ {ars : List (List Srt × Srt)}
    {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ) (assignment : Assignment)
    (_ : EncodedAssignment sigma assignment) (args : Args sig ars Γ),
    encodeArgs (bindArgs sigma args) =
      substituteList assignment (encodeArgs args)
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, sigma, assignment, valid, .cons (bs := bs) head tail => by
      simp only [bindArgs, encodeArgs, substituteList]
      rw [substitute_wrapBinders]
      rw [encodeTerm_bind_of_assignment (liftSub sigma bs)
        (lift bs.length assignment)
        (encodedAssignment_lift sigma assignment valid bs) head]
      rw [encodeArgs_bind_of_assignment sigma assignment valid tail]
end

/-- Encode the values of a sorted substitution in context order. -/
def encodeSubValues : (Γ : Ctx sig) → {Δ : Ctx sig} → Sub sig Γ Δ → List Pattern
  | [], _, _ => []
  | s :: Γ, _, sigma =>
      encodeTerm (sigma s Var.zero) ::
        encodeSubValues Γ (fun t v => sigma t (Var.succ v))

/-- Extend the finite sorted substitution to a total raw-pattern assignment;
indices outside its source context are left as variables. -/
def encodeSub {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ) : Assignment :=
  fun index => (encodeSubValues Γ sigma)[index]?.getD (.bvar index)

/-- The encoded assignment has one stored value per declared source slot. -/
theorem encodeSubValues_length : ∀ (Γ : Ctx sig) {Δ : Ctx sig}
    (sigma : Sub sig Γ Δ),
    (encodeSubValues Γ sigma).length = Γ.length
  | [], _, _ => rfl
  | _ :: Γ, _, sigma => by
      simpa [encodeSubValues] using
        congrArg Nat.succ
          (encodeSubValues_length Γ (fun t v => sigma t (Var.succ v)))

/-- Looking up a well-sorted source variable returns its encoded image. -/
theorem encodeSub_at_var : ∀ {Γ Δ : Ctx sig}
    (sigma : Sub sig Γ Δ) {s : Srt} (v : Var Γ s),
    encodeSub sigma (varIdx v).val = encodeTerm (sigma s v)
  | _ :: _, _, sigma, _, .zero => rfl
  | _ :: Γ, _, sigma, _, .succ w => by
      let tailSigma : Sub sig Γ _ := fun t v => sigma t (Var.succ v)
      have hi : (varIdx w).val < (encodeSubValues Γ tailSigma).length := by
        rw [encodeSubValues_length]
        exact (varIdx w).isLt
      simpa [encodeSub, encodeSubValues, varIdx,
        List.getElem?_eq_getElem hi, tailSigma] using
        encodeSub_at_var tailSigma w

/-- The constructed finite assignment represents the supplied substitution. -/
theorem encodeSub_valid {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ) :
    EncodedAssignment sigma (encodeSub sigma) := by
  intro s v
  exact encodeSub_at_var sigma v

/-- Intrinsic substitution and the executable pattern-context substitution
commute exactly, for every sorted rho term and every context change. -/
theorem encodeTerm_bind {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    {s : Srt} (term : Term sig Γ s) :
    encodeTerm (bind sigma term) =
      substitute (encodeSub sigma) (encodeTerm term) :=
  encodeTerm_bind_of_assignment sigma (encodeSub sigma) (encodeSub_valid sigma) term

/-- The same exact comparison on argument vectors, including input bodies. -/
theorem encodeArgs_bind {ars : List (List Srt × Srt)}
    {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ) (args : Args sig ars Γ) :
    encodeArgs (bindArgs sigma args) =
      substituteList (encodeSub sigma) (encodeArgs args) :=
  encodeArgs_bind_of_assignment sigma (encodeSub sigma) (encodeSub_valid sigma) args

/-- The finite-context image of the intrinsic identity substitution is the
identity raw-pattern assignment at every declared variable. -/
theorem encodeSub_id_at_var {Γ : Ctx sig} {s : Srt} (v : Var Γ s) :
    encodeSub (fun _ w => Term.var w : Sub sig Γ Γ) (varIdx v).val =
      Pattern.bvar (varIdx v).val := by
  simpa only [encodeTerm] using
    encodeSub_at_var (fun _ w => Term.var w : Sub sig Γ Γ) v

/-- Substitution composition is respected on the finite, sorted source
context; no assertion is made about arbitrary out-of-range raw indices. -/
theorem encodeSub_comp_at_var {Γ Δ Θ : Ctx sig}
    (first : Sub sig Γ Δ) (second : Sub sig Δ Θ)
    {s : Srt} (v : Var Γ s) :
    encodeSub (fun t w => bind second (first t w)) (varIdx v).val =
      substitute (encodeSub second) (encodeSub first (varIdx v).val) := by
  rw [encodeSub_at_var, encodeSub_at_var]
  exact encodeTerm_bind second (first s v)

/-- The substitution square composes through two actual context changes. -/
theorem encodeTerm_bind_twice {Γ Δ Θ : Ctx sig}
    (first : Sub sig Γ Δ) (second : Sub sig Δ Θ)
    {s : Srt} (term : Term sig Γ s) :
    encodeTerm (bind second (bind first term)) =
      substitute (encodeSub second)
        (substitute (encodeSub first) (encodeTerm term)) := by
  rw [encodeTerm_bind second, encodeTerm_bind first]

/-- An input whose body refers to an enclosing name, rather than the name
bound by that input. The distinction is visible in the encoded indices. -/
def openInputDropsAmbient : Term sig [Srt.nm] Srt.pr :=
  .op Op.inp (.cons (.var Var.zero)
    (.cons (.op Op.drp (.cons (.var (Var.succ Var.zero)) .nil)) .nil))

/-- Close only the ambient name; the input binder is introduced by the term. -/
def closeInputAmbient : Sub sig [Srt.nm] []
  | _, .zero => chan

/-- The existing pattern substitution puts the closed channel below the input
binder without turning it into the newly bound variable. -/
theorem openInput_bind_encodes_without_capture :
    substitute (encodeSub closeInputAmbient) (encodeTerm openInputDropsAmbient) =
      .apply "PInput" [encodeTerm chan,
        .lambda none (.apply "PDrop" [encodeTerm chan])] := by
  calc
    substitute (encodeSub closeInputAmbient) (encodeTerm openInputDropsAmbient) =
        encodeTerm (bind closeInputAmbient openInputDropsAmbient) :=
      (encodeTerm_bind closeInputAmbient openInputDropsAmbient).symm
    _ = _ := rfl

/-- Replacing the outer name by the input's bound index is a different,
capturing result. -/
theorem openInput_captured_result_is_wrong :
    substitute (encodeSub closeInputAmbient) (encodeTerm openInputDropsAmbient) ≠
      .apply "PInput" [encodeTerm chan,
        .lambda none (.apply "PDrop" [.bvar 0])] := by
  rw [openInput_bind_encodes_without_capture]
  decide +kernel

end Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
