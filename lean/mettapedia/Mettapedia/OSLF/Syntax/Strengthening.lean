import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# Strengthening: removing a variable a term does not use

Several constructions need the same operation and none of them had it.  Deciding
whether a one-hole context is structurally linear needs it, because the
arguments away from the hole have to be moved out of the hole's scope.
Enumerating a redex position whose hole sits under a binder needs it, because the
subterm plugged there is scoped outside the binder.  Both were left open with the
same sentence, and both are waiting on this.

The operation is partial: a term that *does* use the variable has no preimage.
Rather than make the caller supply a junk value to fill the impossible case --
which is impossible in general, since the sort may have no closed inhabitant --
it is written as an option, and its correctness is the statement that a returned
preimage renames back to the term it came from.

It is stated for an arbitrary renaming rather than for weakening alone, because
the recursion under a binder needs the lifted renaming and lifting a weakening is
not a weakening.  What the caller supplies is a *partial inverse* to the
renaming, and the construction that lifts one past a binder prefix is given here
so no clause of the recursion carries a context equation.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature}

/-- A **partial inverse** to a renaming: it recognises the variables in the
renaming's image and says which variable each came from. -/
structure Strengthener {Γ Δ : Ctx S} (rho : Ren S Γ Δ) where
  /-- Recognise a variable of the larger context. -/
  un : (s : S.Srt) → Var Δ s → Option (Var Γ s)
  /-- Everything in the image is recognised, correctly. -/
  un_rho : ∀ (s : S.Srt) (w : Var Γ s), un s (rho s w) = some w
  /-- And nothing else is recognised. -/
  rho_un : ∀ (s : S.Srt) (v : Var Δ s) (w : Var Γ s), un s v = some w → rho s w = v

namespace Strengthener

/-- One binder's worth of lifting, as a top-level recursion so that its
equations reduce: a match written inside the record field would be stuck on the
sort index as well as on the variable. -/
def liftUnStep {Γ' Δ' : Ctx S} {b : S.Srt}
    (rec : (s : S.Srt) → Var Δ' s → Option (Var Γ' s)) :
    (s : S.Srt) → Var (b :: Δ') s → Option (Var (b :: Γ') s)
  | _, .zero => some .zero
  | s, .succ w =>
      match rec s w with
      | none => none
      | some u => some (Var.succ u)

/-- **A partial inverse lifts past a binder prefix.**  The bound variables are
their own preimages; the free ones are handled by the given inverse. -/
def liftS {Γ Δ : Ctx S} {rho : Ren S Γ Δ} (St : Strengthener rho) :
    (bs : List S.Srt) → Strengthener (liftRen rho bs)
  | [] => St
  | _ :: bs =>
    { un := liftUnStep (St.liftS bs).un
      un_rho := by
        intro s w
        cases w with
        | zero => rfl
        | succ w' =>
            show liftUnStep (St.liftS bs).un s (Var.succ (liftRen rho bs s w')) = _
            simp only [liftUnStep, (St.liftS bs).un_rho s w']
      rho_un := by
        intro s v w hw
        cases v with
        | zero =>
            simp only [liftUnStep] at hw
            injection hw with h1
            rw [← h1]
            rfl
        | succ v' =>
            simp only [liftUnStep] at hw
            cases hcase : (St.liftS bs).un s v' with
            | none => rw [hcase] at hw; exact absurd hw (by simp)
            | some u =>
                rw [hcase] at hw
                injection hw with h1
                rw [← h1]
                show Var.succ (liftRen rho bs s u) = Var.succ v'
                rw [(St.liftS bs).rho_un s v' u hcase] }

/-- The partial inverse to weakening: the new variable has no preimage. -/
def ofWeaken (S : Signature) {Γ : Ctx S} (c : S.Srt) :
    Strengthener (fun (_ : S.Srt) (v : Var Γ _) => (Var.succ v : Var (c :: Γ) _)) where
  un := fun _ v =>
    match v with
    | .zero => none
    | .succ w => some w
  un_rho := fun _ _ => rfl
  rho_un := by
    intro s v w hw
    cases v with
    | zero => exact absurd hw (by simp)
    | succ v' =>
        have : (some v' : Option (Var _ s)) = some w := hw
        injection this with h
        exact h ▸ rfl

end Strengthener

/-- One step of inverting a weakening by a whole prefix, as a top-level
recursion so that its equations reduce. -/
def weakenUnStep {Γ' Δ : Ctx S} {b : S.Srt}
    (rec : (s : S.Srt) → Var Δ s → Option (Var Γ' s)) :
    (s : S.Srt) → Var (b :: Δ) s → Option (Var Γ' s)
  | _, .zero => none
  | s, .succ w => rec s w

/-- **The partial inverse to weakening by a whole binder prefix.**  A term in
the extended scope comes from the original exactly when it mentions none of the
prefix's variables, and this is what recognises that. -/
def Strengthener.ofWeakenPrefix (S : Signature) {Γ : Ctx S} :
    (bs : List S.Srt) →
      Strengthener (fun (_ : S.Srt) (v : Var Γ _) => weakenVar bs v)
  | [] =>
    { un := fun _ v => some v
      un_rho := fun _ _ => rfl
      rho_un := by
        intro s v w hw
        injection hw with h
        rw [← h]
        rfl }
  | _ :: bs =>
    { un := weakenUnStep (Strengthener.ofWeakenPrefix S bs).un
      un_rho := by
        intro s w
        show weakenUnStep (Strengthener.ofWeakenPrefix S bs).un s
          (Var.succ (weakenVar bs w)) = some w
        simp only [weakenUnStep]
        exact (Strengthener.ofWeakenPrefix S bs).un_rho s w
      rho_un := by
        intro s v w hw
        cases v with
        | zero => exact absurd hw (by simp [weakenUnStep])
        | succ u =>
            simp only [weakenUnStep] at hw
            show Var.succ (weakenVar bs w) = Var.succ u
            exact congrArg Var.succ
              ((Strengthener.ofWeakenPrefix S bs).rho_un s u w hw) }

/-! ## The operation -/

mutual
/-- Remove the variables outside the renaming's image, when the term uses
none of them. -/
def strengthenT {Γ Δ : Ctx S} {rho : Ren S Γ Δ} (St : Strengthener rho) :
    {s : S.Srt} → Term S Δ s → Option (Term S Γ s)
  | _, .var v => (St.un _ v).map Term.var
  | _, .op o args => (strengthenA St args).map (Term.op o)

def strengthenA {Γ Δ : Ctx S} {rho : Ren S Γ Δ} (St : Strengthener rho) :
    {as : List (List S.Srt × S.Srt)} → Args S as Δ → Option (Args S as Γ)
  | _, .nil => some .nil
  | _, .cons (bs := bs) head tail =>
      match strengthenT (St.liftS bs) head, strengthenA St tail with
      | some h, some t => some (.cons h t)
      | _, _ => none
end

/-! ## Correctness -/

mutual
/-- **A preimage renames back to the term it came from.** -/
theorem rename_strengthenT : ∀ {Γ Δ : Ctx S} {rho : Ren S Γ Δ}
    (St : Strengthener rho) {s : S.Srt} (t : Term S Δ s) (t' : Term S Γ s),
    strengthenT St t = some t' → rename rho t' = t
  | _, _, rho, St, _, .var v, t', h => by
      simp only [strengthenT] at h
      cases hcase : St.un _ v with
      | none => rw [hcase] at h; exact absurd h (by simp)
      | some w =>
          rw [hcase] at h
          simp only [Option.map_some] at h
          injection h with h'
          rw [← h', rename]
          exact congrArg Term.var (St.rho_un _ v w hcase)
  | _, _, rho, St, _, .op o args, t', h => by
      simp only [strengthenT] at h
      cases hcase : strengthenA St args with
      | none => rw [hcase] at h; exact absurd h (by simp)
      | some a =>
          rw [hcase] at h
          simp only [Option.map_some] at h
          injection h with h'
          rw [← h', rename, renameArgs_strengthenA St args a hcase]

theorem renameArgs_strengthenA : ∀ {Γ Δ : Ctx S} {rho : Ren S Γ Δ}
    (St : Strengthener rho) {as : List (List S.Srt × S.Srt)} (args : Args S as Δ)
    (args' : Args S as Γ), strengthenA St args = some args' →
    renameArgs rho args' = args
  | _, _, _, _, _, .nil, args', h => by
      simp only [strengthenA] at h
      injection h with h'
      rw [← h', renameArgs]
  | _, _, rho, St, _, .cons (bs := bs) head tail, args', h => by
      simp only [strengthenA] at h
      cases hh : strengthenT (St.liftS bs) head with
      | none => rw [hh] at h; exact absurd h (by simp)
      | some hv =>
          cases ht : strengthenA St tail with
          | none => rw [hh, ht] at h; exact absurd h (by simp)
          | some tv =>
              rw [hh, ht] at h
              injection h with h'
              rw [← h', renameArgs,
                rename_strengthenT (St.liftS bs) head hv hh,
                renameArgs_strengthenA St tail tv ht]
end

/-! ## Strengthening is a left inverse to renaming

A partial inverse recognises exactly the image, so strengthening a renamed term
returns the term it came from.  That makes renaming injective wherever a partial
inverse exists, which is every renaming this development performs, and it proves
it without inverting a constructor of an inductive family -- the comparison
happens in `Option`, whose constructors carry no indices. -/

mutual
/-- **Strengthening undoes renaming.** -/
theorem strengthenT_rename : ∀ {Γ Δ : Ctx S} {rho : Ren S Γ Δ}
    (St : Strengthener rho) {s : S.Srt} (t : Term S Γ s),
    strengthenT St (rename rho t) = some t
  | _, _, _, St, _, .var v => by
      simp only [rename, strengthenT, St.un_rho, Option.map_some]
  | _, _, _, St, _, .op _ args => by
      simp only [rename, strengthenT, strengthenA_renameArgs St args, Option.map_some]

theorem strengthenA_renameArgs : ∀ {Γ Δ : Ctx S} {rho : Ren S Γ Δ}
    (St : Strengthener rho) {as : List (List S.Srt × S.Srt)} (args : Args S as Γ),
    strengthenA St (renameArgs rho args) = some args
  | _, _, _, _, _, .nil => rfl
  | _, _, _, St, _, .cons (bs := bs) head tail => by
      simp only [renameArgs, strengthenA,
        strengthenT_rename (St.liftS bs) head, strengthenA_renameArgs St tail]
end

/-- **A renaming with a partial inverse is injective.** -/
theorem rename_injective {Γ Δ : Ctx S} {rho : Ren S Γ Δ} (St : Strengthener rho)
    {s : S.Srt} {t u : Term S Γ s} (h : rename rho t = rename rho u) : t = u := by
  have ht := strengthenT_rename St t
  have hu := strengthenT_rename St u
  rw [h] at ht
  have : (some t : Option (Term S Γ s)) = some u := ht.symm.trans hu
  injection this

/-- And so is renaming of argument lists. -/
theorem renameArgs_injective {Γ Δ : Ctx S} {rho : Ren S Γ Δ} (St : Strengthener rho)
    {as : List (List S.Srt × S.Srt)} {args args' : Args S as Γ}
    (h : renameArgs rho args = renameArgs rho args') : args = args' := by
  have ha := strengthenA_renameArgs St args
  have hb := strengthenA_renameArgs St args'
  rw [h] at ha
  have : (some args : Option (Args S as Γ)) = some args' := ha.symm.trans hb
  injection this

/-! ## Strengthening succeeds exactly where it should

The recursion under a binder passes from a partial inverse to its own lift, so
the statement is made for an arbitrary partial inverse and the induction is
self-similar; stating it for weakening alone would force a binder prefix to be
concatenated at every step, and every clause would carry a context equation. -/

/-- A variable the lifted inverse does not recognise is a free one the original
does not recognise. -/
theorem Strengthener.liftS_un_eq_none {Γ Δ : Ctx S} {rho : Ren S Γ Δ}
    (St : Strengthener rho) :
    ∀ (bs : List S.Srt) (r : S.Srt) (w : Var (bs ++ Δ) r),
      (St.liftS bs).un r w = none → ∃ v : Var Δ r, w = weakenVar bs v ∧ St.un r v = none
  | [], r, w, h => ⟨w, rfl, h⟩
  | _ :: bs, r, w, h => by
      cases w with
      | zero => exact absurd h (by simp [Strengthener.liftS, Strengthener.liftUnStep])
      | succ w' =>
          have h'' : (St.liftS bs).un r w' = none := by
            simp only [Strengthener.liftS, Strengthener.liftUnStep] at h
            cases hcase : (St.liftS bs).un r w' with
            | none => rfl
            | some _ => rw [hcase] at h; exact absurd h (by simp)
          obtain ⟨v, hv, hun⟩ := St.liftS_un_eq_none bs r w' h''
          exact ⟨v, by rw [hv]; rfl, hun⟩

mutual
/-- **A term whose variables are all recognised has a preimage.** -/
theorem strengthenT_isSome : ∀ {Γ Δ : Ctx S} {rho : Ren S Γ Δ}
    (St : Strengthener rho) {s : S.Srt} (t : Term S Δ s),
    (∀ (r : S.Srt) (v : Var Δ r), St.un r v = none → countVar v t = 0) →
    ∃ t', strengthenT St t = some t'
  | _, _, _, St, _, .var v, h => by
      cases hcase : St.un _ v with
      | none =>
          exact absurd (h _ v hcase) (by simp only [countVar, sameVar_self]; simp)
      | some w => exact ⟨Term.var w, by simp only [strengthenT, hcase, Option.map_some]⟩
  | _, _, _, St, _, .op o args, h => by
      obtain ⟨a, ha⟩ := strengthenA_isSome St args (by
        intro r v hv
        have := h r v hv
        simpa only [countVar] using this)
      exact ⟨Term.op o a, by simp only [strengthenT, ha, Option.map_some]⟩

theorem strengthenA_isSome : ∀ {Γ Δ : Ctx S} {rho : Ren S Γ Δ}
    (St : Strengthener rho) {as : List (List S.Srt × S.Srt)} (args : Args S as Δ),
    (∀ (r : S.Srt) (v : Var Δ r), St.un r v = none → countVarArgs v args = 0) →
    ∃ args', strengthenA St args = some args'
  | _, _, _, _, _, .nil, _ => ⟨Args.nil, rfl⟩
  | _, _, _, St, _, .cons (bs := bs) head tail, h => by
      have hhead : ∀ (r : S.Srt) (w : Var (bs ++ _) r),
          (St.liftS bs).un r w = none → countVar w head = 0 := by
        intro r w hw
        obtain ⟨v, hv, hun⟩ := St.liftS_un_eq_none bs r w hw
        have := h r v hun
        simp only [countVarArgs] at this
        rw [hv]
        omega
      have htail : ∀ (r : S.Srt) (v : Var _ r),
          St.un r v = none → countVarArgs v tail = 0 := by
        intro r v hv
        have := h r v hv
        simp only [countVarArgs] at this
        omega
      obtain ⟨hv, hhv⟩ := strengthenT_isSome (St.liftS bs) head hhead
      obtain ⟨t, ht⟩ := strengthenA_isSome St tail htail
      exact ⟨Args.cons hv t, by simp only [strengthenA, hhv, ht]⟩
end

/-! ## Weakening, inverted -/

/-- The partial inverse to weakening, named for use. -/
abbrev unweaken (S : Signature) {Γ : Ctx S} (c : S.Srt) :
    Strengthener (fun (_ : S.Srt) (v : Var Γ _) => (Var.succ v : Var (c :: Γ) _)) :=
  Strengthener.ofWeaken S c

/-- **A term that does not use its outermost variable is a weakening**, and the
witness is computed rather than asserted. -/
theorem exists_unweaken {Γ : Ctx S} {c s : S.Srt} (t : Term S (c :: Γ) s)
    (h : countVar (Var.zero : Var (c :: Γ) c) t = 0) :
    ∃ t' : Term S Γ s, strengthenT (unweaken S c) t = some t' ∧ weaken t' = t := by
  obtain ⟨t', ht'⟩ := strengthenT_isSome (unweaken S c) t (by
    intro r v hv
    cases v with
    | zero => exact h
    | succ w => exact absurd hv (by simp [unweaken, Strengthener.ofWeaken]))
  exact ⟨t', ht', rename_strengthenT (unweaken S c) t t' ht'⟩

/-- The inverse to a prefix weakening, named for use. -/
abbrev unweakenPrefix (S : Signature) {Γ : Ctx S} (bs : List S.Srt) :
    Strengthener (fun (_ : S.Srt) (v : Var Γ _) => weakenVar bs v) :=
  Strengthener.ofWeakenPrefix S bs

/-- A variable the prefix inverse does not recognise is one of the prefix's
own. -/
theorem unweakenPrefix_un_eq_none {Γ : Ctx S} :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var (bs ++ Γ) s),
      (unweakenPrefix S (Γ := Γ) bs).un s v = none → ∀ w : Var Γ s, v ≠ weakenVar bs w
  | [], _, _, h, _ => by simp [unweakenPrefix, Strengthener.ofWeakenPrefix] at h
  | b :: bs, s, v, h, w => by
      intro hv
      have := (unweakenPrefix S (Γ := Γ) (b :: bs)).un_rho s w
      rw [← hv, h] at this
      exact absurd this (by simp)

/-- **A term that uses none of a binder prefix's variables comes from outside
it**, and the witness is computed. -/
theorem exists_unweakenPrefix {Γ : Ctx S} (bs : List S.Srt) {s : S.Srt}
    (t : Term S (bs ++ Γ) s)
    (h : ∀ (r : S.Srt) (v : Var (bs ++ Γ) r),
      (unweakenPrefix S (Γ := Γ) bs).un r v = none → countVar v t = 0) :
    ∃ t' : Term S Γ s, rename (fun _ v => weakenVar bs v) t' = t := by
  obtain ⟨t', ht'⟩ := strengthenT_isSome (unweakenPrefix S bs) t h
  exact ⟨t', rename_strengthenT (unweakenPrefix S bs) t t' ht'⟩

/-- And conversely a weakening does not use it, so the two conditions are the
same condition. -/
theorem countVar_zero_of_weaken {Γ : Ctx S} {c s : S.Srt} (t : Term S Γ s) :
    countVar (Var.zero : Var (c :: Γ) c) (weaken t) = 0 := holeCount_weaken t

/-- **A one-hole context is a weakening exactly when it ignores its hole.** -/
theorem exists_unweaken_iff {Γ : Ctx S} {c s : S.Srt} (t : Term S (c :: Γ) s) :
    (∃ t' : Term S Γ s, weaken t' = t) ↔ holeCount t = 0 := by
  constructor
  · rintro ⟨t', rfl⟩
    exact countVar_zero_of_weaken t'
  · intro h
    obtain ⟨t', -, hw⟩ := exists_unweaken t h
    exact ⟨t', hw⟩

end Mettapedia.OSLF.Binding
