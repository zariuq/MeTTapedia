import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.Encoding

/-!
# Scoped substitution and the represented raw index algorithms

These laws connect the existing native raw renaming, shifting and substitution
algorithms to the scoped terms represented by the hosted codec. They do not
identify object substitution with the host language's metavariable assignment.
No hosted evaluator or search policy is chosen here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation

theorem ofTm_rename {Head : Type} {n m : Nat} (rho : Ren n m) (term : Tm Head n) :
    ATm.ofTm (rename rho term) = (ATm.ofTm term).rename rho := by
  induction term generalizing m <;> simp_all only [rename, ATm.ofTm, ATm.rename]

theorem ofTm_liftSub {Head : Type} {n m : Nat} (substitution : Sub Head n m) :
    (fun index => ATm.ofTm (liftSub substitution index)) =
      ATm.liftSub (fun index => ATm.ofTm (substitution index)) := by
  funext index
  refine Fin.cases ?_ (fun outer => ?_) index
  · rfl
  · simp only [liftSub, ATm.liftSub, Fin.cases_succ, ofTm_rename]

theorem ofTm_subst {Head : Type} {n m : Nat} (substitution : Sub Head n m) (term : Tm Head n) :
    ATm.ofTm (subst substitution term) =
      (ATm.ofTm term).subst (fun index => ATm.ofTm (substitution index)) := by
  induction term generalizing m <;>
    simp_all only [subst, ATm.ofTm, ATm.subst, ofTm_liftSub]

theorem ofTm_subst0 {Head : Type} {n : Nat} (argument : Tm Head n) :
    (fun index => ATm.ofTm (subst0 argument index)) = ATm.subst0 (ATm.ofTm argument) := by
  funext index
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

theorem ofTm_inst0 {Head : Type} {n : Nat} (argument : Tm Head n) (body : Tm Head (n + 1)) :
    ATm.ofTm (inst0 argument body) = ATm.inst0 (ATm.ofTm argument) (ATm.ofTm body) := by
  unfold inst0 ATm.inst0
  rw [ofTm_subst, ofTm_subst0]

theorem rawTm_rename {n m : Nat} (rho : Ren n m) (raw : Nat → Nat)
    (agrees : ∀ index : Fin n, raw index.val = (rho index).val) (term : Tower.Tm n) :
    rawTm (rename rho term) = NativeSyntax.renameRaw raw (rawTm term) := by
  unfold rawTm
  rw [ofTm_rename]
  exact NativeSyntax.encode_rename rho raw agrees (ATm.ofTm term)

theorem rawTm_subst {n m : Nat} (substitution : Sub Tower.Head n m)
    (raw : Nat → NativeSyntax.Raw Tower.Head)
    (agrees : ∀ index : Fin n, raw index.val = rawTm (substitution index)) (term : Tower.Tm n) :
    rawTm (subst substitution term) = NativeSyntax.substRaw raw (rawTm term) := by
  unfold rawTm
  rw [ofTm_subst]
  exact NativeSyntax.encode_subst (fun index => ATm.ofTm (substitution index)) raw agrees (ATm.ofTm term)

theorem shift_rawTm {n : Nat} (amount : Nat) (term : Tower.Tm n) :
    NativeSyntax.shift amount 0 (rawTm term) =
      rawTm (rename (NativeSyntax.weakenRen amount) term) := by
  unfold rawTm
  rw [NativeSyntax.shift_encode, ofTm_rename]

theorem substituteZero_rawTm {n : Nat} (argument : Tower.Tm n) (body : Tower.Tm (n + 1)) :
    NativeSyntax.substituteZero (rawTm argument) 0 (rawTm body) = rawTm (inst0 argument body) := by
  unfold rawTm
  rw [NativeSyntax.substituteZero_encode, ofTm_inst0]

theorem quoteRaw_rename {n m : Nat} (rho : Ren n m) (raw : Nat → Nat)
    (agrees : ∀ index : Fin n, raw index.val = (rho index).val) (term : Tower.Tm n) :
    quoteRaw (NativeSyntax.renameRaw raw (rawTm term)) = encodeTm (rename rho term) := by
  rw [← rawTm_rename rho raw agrees, quoteRaw_rawTm]

theorem quoteRaw_subst {n m : Nat} (substitution : Sub Tower.Head n m)
    (raw : Nat → NativeSyntax.Raw Tower.Head)
    (agrees : ∀ index : Fin n, raw index.val = rawTm (substitution index)) (term : Tower.Tm n) :
    quoteRaw (NativeSyntax.substRaw raw (rawTm term)) = encodeTm (subst substitution term) := by
  rw [← rawTm_subst substitution raw agrees, quoteRaw_rawTm]

theorem quoteRaw_shift {n : Nat} (amount : Nat) (term : Tower.Tm n) :
    quoteRaw (NativeSyntax.shift amount 0 (rawTm term)) =
      encodeTm (rename (NativeSyntax.weakenRen amount) term) := by
  rw [shift_rawTm, quoteRaw_rawTm]

theorem quoteRaw_substituteZero {n : Nat} (argument : Tower.Tm n) (body : Tower.Tm (n + 1)) :
    quoteRaw (NativeSyntax.substituteZero (rawTm argument) 0 (rawTm body)) =
      encodeTm (inst0 argument body) := by
  rw [substituteZero_rawTm, quoteRaw_rawTm]

/-- Inserting a free variable beneath a lambda shifts it past that lambda. -/
theorem substitution_retains_free_variable :
    NativeSyntax.substituteZero (rawTm (.var 0 : Tower.Tm 1)) 0
      (rawTm (.lam (.var 1) : Tower.Tm 2)) = rawTm (.lam (.var 1) : Tower.Tm 1) ∧
      quoteRaw (NativeSyntax.substituteZero (rawTm (.var 0 : Tower.Tm 1)) 0
        (rawTm (.lam (.var 1) : Tower.Tm 2))) ≠ encodeTm (.lam (.var 0) : Tower.Tm 1) := by
  constructor
  · rfl
  · rw [substituteZero_rawTm, quoteRaw_rawTm]
    exact Ne.symm capture_sensitive_terms_distinct

/-- Substitution traverses the dependent codomain at one greater depth. -/
theorem dependent_codomain_keeps_its_binder :
    NativeSyntax.substituteZero (rawTm (.var 0 : Tower.Tm 1)) 0
      (rawTm (.pi (.var 0) (.pair (.var 0) (.var 1)) : Tower.Tm 2)) =
        rawTm (.pi (.var 0) (.pair (.var 0) (.var 1)) : Tower.Tm 1) := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
