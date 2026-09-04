import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionSemantics

/-!
# Naturality of scoped-to-first-order erasure

The declaration-aware first-order term algebra is an operational shadow of
the intrinsically scoped tower syntax.  This module proves that forgetting
scope commutes with weakening and simultaneous substitution.  Root
single-variable substitution follows as a derived case.

The result is independent of typing and of any selected calculus instance.  It
is the structural commuting square needed before a first-order checker result
can be identified with a scoped substitution result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace DeclarationAwareErasureNaturality

open Presentation
open DeclarationAwareSubstitutionSemantics

variable {Head : Type}
variable {n m : Nat}

/-! ## Weakening naturality -/

/-- Lifting insertion past a new binder moves the insertion position by one. -/
private theorem liftRen_succAbove (position : Fin (n + 1)) :
    Presentation.liftRen position.succAbove =
      position.succ.succAbove := by
  funext index
  refine Fin.cases ?_ (fun prior => ?_) index
  · simp [Presentation.liftRen]
  · simp [Presentation.liftRen]

/-- Erasure sends insertion at a scoped position to first-order weakening at
the corresponding natural-number cutoff. -/
theorem erase_rename_succAbove (position : Fin (n + 1))
    (term : Presentation.Tm Head n) :
    erase (Presentation.rename position.succAbove term) =
      weakenAt position.val (erase term) := by
  induction term with
  | var index =>
      by_cases below : index.val < position.val
      · have finBelow : index.castSucc < position := below
        rw [Presentation.rename, erase,
          Fin.succAbove_of_castSucc_lt position index finBelow]
        change
          RawTm.var index.val =
            weakenAt position.val (RawTm.var index.val)
        simp [weakenAt, below]
      · have finLe : position ≤ index.castSucc :=
          Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt below)
        rw [Presentation.rename, erase,
          Fin.succAbove_of_le_castSucc position index finLe]
        change
          RawTm.var (index.val + 1) =
            weakenAt position.val (RawTm.var index.val)
        simp [weakenAt, below]
  | const name => rfl
  | head head => rfl
  | pi domain body domainInduction bodyInduction =>
      simp only [Presentation.rename, erase, weakenAt, domainInduction]
      rw [liftRen_succAbove]
      congr 1
      simpa using bodyInduction position.succ
  | sigma domain body domainInduction bodyInduction =>
      simp only [Presentation.rename, erase, weakenAt, domainInduction]
      rw [liftRen_succAbove]
      congr 1
      simpa using bodyInduction position.succ
  | id type left right typeInduction leftInduction rightInduction =>
      simp only [Presentation.rename, erase, weakenAt, typeInduction,
        leftInduction, rightInduction]
  | lam body bodyInduction =>
      simp only [Presentation.rename, erase, weakenAt]
      rw [liftRen_succAbove]
      congr 1
      simpa using bodyInduction position.succ
  | app function argument functionInduction argumentInduction =>
      simp only [Presentation.rename, erase, weakenAt, functionInduction,
        argumentInduction]
  | pair first second firstInduction secondInduction =>
      simp only [Presentation.rename, erase, weakenAt, firstInduction,
        secondInduction]
  | fst pair pairInduction =>
      simp only [Presentation.rename, erase, weakenAt, pairInduction]
  | snd pair pairInduction =>
      simp only [Presentation.rename, erase, weakenAt, pairInduction]
  | refl term termInduction =>
      simp only [Presentation.rename, erase, weakenAt, termInduction]

/-- Ordinary scoped weakening erases to first-order weakening at cutoff zero. -/
@[simp]
theorem erase_rename_wk (term : Presentation.Tm Head n) :
    erase (Presentation.rename Presentation.wk term) =
      weakenAt 0 (erase term) := by
  change
    erase (Presentation.rename Fin.succ term) =
      weakenAt 0 (erase term)
  exact erase_rename_succAbove (position := (0 : Fin (n + 1))) term

/-! ## Simultaneous substitution on the raw algebra -/

/-- A total first-order simultaneous substitution.  Values outside the scope
of an erased term are harmless because scoped erasure never produces them. -/
abbrev RawSubstitution (Head : Type) := Nat → RawTm Head

/-- Lift a raw simultaneous substitution under one binder. -/
def liftRawSubstitution (substitution : RawSubstitution Head) :
    RawSubstitution Head
  | 0 => .var 0
  | index + 1 => weakenAt 0 (substitution index)

/-- Apply a raw simultaneous substitution structurally. -/
def substituteAll (substitution : RawSubstitution Head) :
    RawTm Head → RawTm Head
  | .var index => substitution index
  | .const name => .const name
  | .head head => .head head
  | .pi domain body =>
      .pi (substituteAll substitution domain)
        (substituteAll (liftRawSubstitution substitution) body)
  | .sigma domain body =>
      .sigma (substituteAll substitution domain)
        (substituteAll (liftRawSubstitution substitution) body)
  | .id type left right =>
      .id (substituteAll substitution type)
        (substituteAll substitution left)
        (substituteAll substitution right)
  | .lam body => .lam (substituteAll (liftRawSubstitution substitution) body)
  | .app function argument =>
      .app (substituteAll substitution function)
        (substituteAll substitution argument)
  | .pair first second =>
      .pair (substituteAll substitution first)
        (substituteAll substitution second)
  | .fst pair => .fst (substituteAll substitution pair)
  | .snd pair => .snd (substituteAll substitution pair)
  | .refl term => .refl (substituteAll substitution term)

/-- A scoped substitution and a raw substitution agree on every scoped
variable after erasure. -/
def SubstitutionErases
    (scopedSubstitution : Presentation.Sub Head n m)
    (raw : RawSubstitution Head) : Prop :=
  ∀ index, erase (scopedSubstitution index) = raw index.val

/-- Agreement is preserved when both substitutions cross a binder. -/
theorem SubstitutionErases.lift
    {scopedSubstitution : Presentation.Sub Head n m}
    {raw : RawSubstitution Head}
    (agreement : SubstitutionErases scopedSubstitution raw) :
    SubstitutionErases (Presentation.liftSub scopedSubstitution)
      (liftRawSubstitution raw) := by
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · change
      erase (Presentation.rename Presentation.wk
        (scopedSubstitution prior)) = weakenAt 0 (raw prior.val)
    rw [erase_rename_wk, agreement prior]

/-- Scoped simultaneous substitution commutes with first-order erasure. -/
theorem erase_subst
    {scopedSubstitution : Presentation.Sub Head n m}
    {raw : RawSubstitution Head}
    (agreement : SubstitutionErases scopedSubstitution raw)
    (term : Presentation.Tm Head n) :
    erase (Presentation.subst scopedSubstitution term) =
      substituteAll raw (erase term) := by
  induction term generalizing m raw with
  | var index => exact agreement index
  | const name => rfl
  | head head => rfl
  | pi domain body domainInduction bodyInduction =>
      simp only [Presentation.subst, erase, substituteAll]
      rw [domainInduction agreement, bodyInduction agreement.lift]
  | sigma domain body domainInduction bodyInduction =>
      simp only [Presentation.subst, erase, substituteAll]
      rw [domainInduction agreement, bodyInduction agreement.lift]
  | id type left right typeInduction leftInduction rightInduction =>
      simp only [Presentation.subst, erase, substituteAll]
      rw [typeInduction agreement, leftInduction agreement,
        rightInduction agreement]
  | lam body bodyInduction =>
      simp only [Presentation.subst, erase, substituteAll]
      rw [bodyInduction agreement.lift]
  | app function argument functionInduction argumentInduction =>
      simp only [Presentation.subst, erase, substituteAll]
      rw [functionInduction agreement, argumentInduction agreement]
  | pair first second firstInduction secondInduction =>
      simp only [Presentation.subst, erase, substituteAll]
      rw [firstInduction agreement, secondInduction agreement]
  | fst pair pairInduction =>
      simp only [Presentation.subst, erase, substituteAll]
      rw [pairInduction agreement]
  | snd pair pairInduction =>
      simp only [Presentation.subst, erase, substituteAll]
      rw [pairInduction agreement]
  | refl term termInduction =>
      simp only [Presentation.subst, erase, substituteAll]
      rw [termInduction agreement]

/-! ## Single-variable substitution as a derived case -/

/-- The total raw substitution that removes one de Bruijn position. -/
def singleRawSubstitution (index : Nat) (replacement : RawTm Head) :
    RawSubstitution Head :=
  fun variableIndex =>
    if variableIndex = index then replacement
    else if variableIndex < index then .var variableIndex
    else .var (variableIndex - 1)

/-- Lifting the single-variable substitution increments its selected index and
weakens its replacement. -/
theorem liftRawSubstitution_single (index : Nat)
    (replacement : RawTm Head) :
    liftRawSubstitution (singleRawSubstitution index replacement) =
      singleRawSubstitution (index + 1) (weakenAt 0 replacement) := by
  funext variableIndex
  cases variableIndex with
  | zero => simp [liftRawSubstitution, singleRawSubstitution]
  | succ prior =>
      by_cases equal : prior = index
      · subst prior
        simp [liftRawSubstitution, singleRawSubstitution]
      · by_cases below : prior < index
        · simp [liftRawSubstitution, singleRawSubstitution, equal, below]
        · have indexLePrior : index ≤ prior := Nat.le_of_not_gt below
          have indexNePrior : index ≠ prior := Ne.symm equal
          have indexLtPrior : index < prior :=
            lt_of_le_of_ne indexLePrior indexNePrior
          have oneLePrior : 1 ≤ prior :=
            Nat.succ_le_iff.mpr
              (lt_of_le_of_lt (Nat.zero_le index) indexLtPrior)
          simp [liftRawSubstitution, singleRawSubstitution, equal, below,
            Nat.sub_add_cancel oneLePrior]

/-- The structural simultaneous operation specializes exactly to the
independently defined first-order single-variable operation. -/
theorem substituteAll_single (index : Nat) (replacement term : RawTm Head) :
    substituteAll (singleRawSubstitution index replacement) term =
      substituteAt index replacement term := by
  induction term generalizing index replacement with
  | var variableIndex =>
      simp [substituteAll, singleRawSubstitution, substituteAt]
  | const name => rfl
  | head head => rfl
  | pi domain body domainInduction bodyInduction =>
      simp only [substituteAll, substituteAt]
      rw [domainInduction, liftRawSubstitution_single, bodyInduction]
  | sigma domain body domainInduction bodyInduction =>
      simp only [substituteAll, substituteAt]
      rw [domainInduction, liftRawSubstitution_single, bodyInduction]
  | id type left right typeInduction leftInduction rightInduction =>
      simp only [substituteAll, substituteAt]
      rw [typeInduction, leftInduction, rightInduction]
  | lam body bodyInduction =>
      simp only [substituteAll, substituteAt]
      rw [liftRawSubstitution_single, bodyInduction]
  | app function argument functionInduction argumentInduction =>
      simp only [substituteAll, substituteAt]
      rw [functionInduction, argumentInduction]
  | pair first second firstInduction secondInduction =>
      simp only [substituteAll, substituteAt]
      rw [firstInduction, secondInduction]
  | fst pair pairInduction =>
      simp only [substituteAll, substituteAt]
      rw [pairInduction]
  | snd pair pairInduction =>
      simp only [substituteAll, substituteAt]
      rw [pairInduction]
  | refl term termInduction =>
      simp only [substituteAll, substituteAt]
      rw [termInduction]

/-- The scoped newest-variable substitution agrees with the raw
single-variable substitution at zero. -/
theorem subst0_erases (argument : Presentation.Tm Head n) :
    SubstitutionErases (Presentation.subst0 argument)
      (singleRawSubstitution 0 (erase argument)) := by
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · simp [Presentation.subst0, singleRawSubstitution, erase]

/-- Root instantiation commutes exactly with scoped-to-first-order erasure. -/
@[simp]
theorem erase_inst0 (argument : Presentation.Tm Head n)
    (body : Presentation.Tm Head (n + 1)) :
    erase (Presentation.inst0 argument body) =
      substituteAt 0 (erase argument) (erase body) := by
  unfold Presentation.inst0
  rw [erase_subst (subst0_erases argument), substituteAll_single]

/-! ## Discriminating controls -/

/-- Positive: removing the newest variable returns its replacement. -/
example (argument : Presentation.Tm Head n) :
    erase (Presentation.inst0 argument (.var 0)) = erase argument := by
  simp

/-- Negative: a variable above the removed position cannot retain its old
index after erasure. -/
theorem erased_successor_changes (argument : Presentation.Tm Head n)
    (index : Fin n) :
    erase (Presentation.inst0 argument (.var index.succ)) ≠
      RawTm.var index.succ.val := by
  rw [erase_inst0]
  simp only [substituteAt, erase, Fin.val_succ]
  intro equality
  injection equality with impossible
  exact (Nat.ne_of_lt (Nat.lt_succ_self index.val)) impossible

#print axioms erase_rename_succAbove
#print axioms erase_rename_wk
#print axioms SubstitutionErases.lift
#print axioms erase_subst
#print axioms liftRawSubstitution_single
#print axioms substituteAll_single
#print axioms erase_inst0
#print axioms erased_successor_changes

end DeclarationAwareErasureNaturality
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
