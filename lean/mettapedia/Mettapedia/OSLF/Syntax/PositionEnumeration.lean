import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# The structural derivative: enumerating one-hole contexts

The generator's first step is to enumerate the chosen subterm occurrences of a
left-hand side.  Chapter 17 of Finding Mind calls the resulting object a context
derivative and asks that it be the structural derivative of the term rather than
a list of syntactic paths.  That is what this module builds, once, for every
signature: the derivative of a term is the list of its one-hole contexts, each
carrying the subterm that was removed and the proof that plugging it back
returns the term.

A one-hole context is a term with a distinguished free variable, so the hole may
sit under binders -- the hole variable is simply shifted -- and plugging lifts
the substitution, which is why the term that goes into the hole is scoped in the
*outer* context.  The enumerator here returns exactly the occurrences that are
not under a binder, which is a class this representation characterises
internally: the number of occurrences of the hole under at least one binder is
counted by `deepCount`, and a context is shallow when that count is zero.

Soundness is by typing: every entry is a linear redex position of the term it
was computed from, because that is the type the enumerator returns.
Completeness is proved: every shallow linear redex position of a term is in its
derivative.  A negative control exhibits a position that is linear but not
shallow, so the characterisation is not vacuous.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature}

/-! ## Occurrences of the hole that sit under a binder -/

mutual
/-- How many occurrences of the hole sit under at least one binder. -/
def deepCount {Γ : Ctx S} {c : S.Srt} : {s : S.Srt} → Term S (c :: Γ) s → Nat
  | _, .var _ => 0
  | _, .op _ args => deepCountArgs args

def deepCountArgs {Γ : Ctx S} {c : S.Srt} :
    {as : List (List S.Srt × S.Srt)} → Args S as (c :: Γ) → Nat
  | _, .nil => 0
  | ([], _) :: _, .cons hd tl => deepCount hd + deepCountArgs tl
  | (b :: bs, _) :: _, .cons hd tl =>
      countVar (weakenVar (b :: bs) (Var.zero : Var (c :: Γ) c)) hd + deepCountArgs tl
end

/-- A context whose hole never sits under a binder. -/
abbrev Shallow {Γ : Ctx S} {c s : S.Srt} (K : Term S (c :: Γ) s) : Prop := deepCount K = 0

mutual
/-- Deep occurrences are occurrences. -/
theorem deepCount_le : ∀ {Γ : Ctx S} {c s : S.Srt} (K : Term S (c :: Γ) s),
    deepCount K ≤ countVar (Var.zero : Var (c :: Γ) c) K
  | _, _, _, .var _ => by
      simp only [deepCount]
      exact Nat.zero_le _
  | _, _, _, .op _ args => by
      simp only [deepCount, countVar]
      exact deepCountArgs_le args

theorem deepCountArgs_le : ∀ {Γ : Ctx S} {c : S.Srt} {as : List (List S.Srt × S.Srt)}
    (T : Args S as (c :: Γ)),
    deepCountArgs T ≤ countVarArgs (Var.zero : Var (c :: Γ) c) T
  | _, _, _, .nil => by
      simp only [deepCountArgs, countVarArgs]
      exact Nat.le_refl _
  | _, _, ([], _) :: _, .cons hd tl => by
      simp only [deepCountArgs, countVarArgs, weakenVar]
      exact Nat.add_le_add (deepCount_le hd) (deepCountArgs_le tl)
  | _, _, (_ :: _, _) :: _, .cons hd tl => by
      simp only [deepCountArgs, countVarArgs]
      exact Nat.add_le_add (Nat.le_refl _) (deepCountArgs_le tl)
end

/-! ## Weakening a term past the hole -/

theorem liftSub_extend_liftRen_succ {Γ : Ctx S} {c : S.Srt} (r : Term S Γ c) :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var (bs ++ Γ) s),
      liftSub (extend r) bs s (liftRen (fun _ w => Var.succ w) bs s v) = Term.var v
  | [], _, _ => rfl
  | b :: bs, s, v => by
      cases v with
      | zero => rfl
      | succ w =>
          show weaken (liftSub (extend r) bs s
            (liftRen (fun _ w => Var.succ w) bs s w)) = _
          rw [liftSub_extend_liftRen_succ r bs s w]
          rfl

theorem bind_rename_liftRen_succ {Γ : Ctx S} {c : S.Srt} (r : Term S Γ c) (bs : List S.Srt)
    {s : S.Srt} (t : Term S (bs ++ Γ) s) :
    bind (liftSub (extend r) bs) (rename (liftRen (fun _ w => Var.succ w) bs) t) = t := by
  rw [bind_rename]
  have h : (fun (s : S.Srt) (v : Var (bs ++ Γ) s) =>
      liftSub (extend r) bs s (liftRen (fun _ w => Var.succ w) bs s v))
      = fun _ v => Term.var v := by
    funext s v
    exact liftSub_extend_liftRen_succ r bs s v
  rw [h, bind_id]

theorem bindArgs_renameArgs_succ {Γ : Ctx S} {c : S.Srt} (r : Term S Γ c)
    {as : List (List S.Srt × S.Srt)} (T : Args S as Γ) :
    bindArgs (extend r) (renameArgs (fun _ v => Var.succ v) T) = T := by
  rw [bindArgs_rename]
  have h : (fun (s : S.Srt) (v : Var Γ s) => extend r s (Var.succ v))
      = fun _ v => Term.var v := rfl
  rw [h, bindArgs_id]

theorem countVar_rename_liftRen_succ {Γ : Ctx S} {c : S.Srt} (bs : List S.Srt)
    {s : S.Srt} (t : Term S (bs ++ Γ) s) :
    countVar (weakenVar bs (Var.zero : Var (c :: Γ) c))
        (rename (liftRen (fun _ w => Var.succ w) bs) t) = 0 :=
  countVar_rename_of_miss _ _
    (sameVar_weakenVar_liftRen (fun _ w => Var.succ w) Var.zero (fun _ _ => rfl) bs) t

theorem countVarArgs_renameArgs_succ {Γ : Ctx S} {c : S.Srt}
    {as : List (List S.Srt × S.Srt)} (T : Args S as Γ) :
    countVarArgs (Var.zero : Var (c :: Γ) c)
        (renameArgs (fun _ v => Var.succ v) T) = 0 :=
  countVarArgs_rename_of_miss (fun _ v => Var.succ v) Var.zero (fun _ _ => rfl) T

/-! ## Positions inside an argument list -/

/-- A one-hole context for an argument list: the hole's sort, the list with a
hole in one slot, the subterm removed, and the plugging equation. -/
structure ArgsPosition (S : Signature) (as : List (List S.Srt × S.Srt)) (Γ : Ctx S)
    (args : Args S as Γ) where
  carrier : S.Srt
  ctxt : Args S as (carrier :: Γ)
  redex : Term S Γ carrier
  plugs : bindArgs (extend redex) ctxt = args
  linear : countVarArgs (Var.zero : Var (carrier :: Γ) carrier) ctxt = 1

/-- The whole term, in the bare hole. -/
def rootPosition {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s) : LinearRedexPosition S Γ s t where
  carrier := s
  ctxt := Term.var Var.zero
  redex := t
  plugs := rfl
  linear := rfl

/-- A position inside the arguments is a position inside the term. -/
def opPosition {Γ : Ctx S} {s : S.Srt} (o : S.Op s) {args : Args S (S.arity o) Γ}
    (Q : ArgsPosition S (S.arity o) Γ args) :
    LinearRedexPosition S Γ s (Term.op o args) where
  carrier := Q.carrier
  ctxt := Term.op o Q.ctxt
  redex := Q.redex
  plugs := congrArg (fun a => Term.op o a) Q.plugs
  linear := Q.linear

/-- A position in the head of a non-binding argument. -/
def argsHere {Γ : Ctx S} {s' : S.Srt} {hd : Term S ([] ++ Γ) s'}
    {as : List (List S.Srt × S.Srt)} (P : LinearRedexPosition S Γ s' hd)
    (tl : Args S as Γ) : ArgsPosition S (([], s') :: as) Γ (Args.cons hd tl) where
  carrier := P.carrier
  ctxt := Args.cons P.ctxt (renameArgs (fun _ v => Var.succ v) tl)
  redex := P.redex
  plugs := by
    show Args.cons (bind (liftSub (extend P.redex) []) P.ctxt)
        (bindArgs (extend P.redex) (renameArgs (fun _ v => Var.succ v) tl)) = _
    rw [bindArgs_renameArgs_succ]
    exact congrArg (fun u => Args.cons u tl) P.plugs
  linear := by
    show countVar (weakenVar [] (Var.zero : Var (P.carrier :: Γ) P.carrier)) P.ctxt
        + countVarArgs Var.zero (renameArgs (fun _ v => Var.succ v) tl) = 1
    rw [countVarArgs_renameArgs_succ, Nat.add_zero]
    exact P.linear

/-- A position in the tail, with the head weakened past the hole. -/
def argsThere {Γ : Ctx S} {bs : List S.Srt} {s' : S.Srt} (hd : Term S (bs ++ Γ) s')
    {as : List (List S.Srt × S.Srt)} {tl : Args S as Γ} (Q : ArgsPosition S as Γ tl) :
    ArgsPosition S ((bs, s') :: as) Γ (Args.cons hd tl) where
  carrier := Q.carrier
  ctxt := Args.cons (rename (liftRen (fun _ v => Var.succ v) bs) hd) Q.ctxt
  redex := Q.redex
  plugs := by
    show Args.cons (bind (liftSub (extend Q.redex) bs)
        (rename (liftRen (fun _ v => Var.succ v) bs) hd))
        (bindArgs (extend Q.redex) Q.ctxt) = _
    rw [bind_rename_liftRen_succ]
    exact congrArg (fun u => Args.cons hd u) Q.plugs
  linear := by
    show countVar (weakenVar bs (Var.zero : Var (Q.carrier :: Γ) Q.carrier))
          (rename (liftRen (fun _ v => Var.succ v) bs) hd)
        + countVarArgs Var.zero Q.ctxt = 1
    rw [countVar_rename_liftRen_succ, Nat.zero_add]
    exact Q.linear

/-! ## The derivative -/

mutual
/-- **The structural derivative**: every one-hole context of a term whose hole
is not under a binder, each with the subterm it removed. -/
def deriv : {Γ : Ctx S} → {s : S.Srt} → (t : Term S Γ s) →
    List (LinearRedexPosition S Γ s t)
  | _, _, .var v => [rootPosition (Term.var v)]
  | _, _, .op o args =>
      rootPosition (Term.op o args) :: (derivArgs args).map (fun Q => opPosition o Q)

def derivArgs : {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} → (args : Args S as Γ) →
    List (ArgsPosition S as Γ args)
  | _, _, .nil => []
  | ([], _) :: _, _, .cons hd tl =>
      (deriv hd).map (fun P => argsHere P tl)
        ++ (derivArgs tl).map (fun Q => argsThere hd Q)
  | (_ :: _, _) :: _, _, .cons hd tl => (derivArgs tl).map (fun Q => argsThere hd Q)
end

mutual
/-- Everything the derivative returns is shallow. -/
theorem deriv_shallow : ∀ {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s),
    ∀ P ∈ deriv t, Shallow P.ctxt
  | _, _, .var _, P, hP => by
      simp only [deriv, List.mem_singleton] at hP
      subst hP
      simp only [rootPosition, Shallow, deepCount]
  | _, _, .op o args, P, hP => by
      simp only [deriv, List.mem_cons, List.mem_map] at hP
      rcases hP with hP | ⟨Q, hQ, hPQ⟩
      · subst hP
        simp only [rootPosition, Shallow, deepCount]
      · subst hPQ
        simp only [opPosition, Shallow, deepCount]
        exact derivArgs_shallow args Q hQ

theorem derivArgs_shallow : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (args : Args S as Γ), ∀ Q ∈ derivArgs args, deepCountArgs Q.ctxt = 0
  | _, _, .nil, Q, hQ => by simp [derivArgs] at hQ
  | ([], _) :: _, _, .cons hd tl, Q, hQ => by
      simp only [derivArgs, List.mem_append, List.mem_map] at hQ
      rcases hQ with ⟨P, hP, hPQ⟩ | ⟨Q', hQ', hQQ⟩
      · subst hPQ
        simp only [argsHere, deepCountArgs]
        rw [deriv_shallow hd P hP, Nat.zero_add]
        exact Nat.le_zero.mp
          ((deepCountArgs_le _).trans (Nat.le_of_eq (countVarArgs_renameArgs_succ tl)))
      · subst hQQ
        simp only [argsThere, deepCountArgs]
        rw [derivArgs_shallow tl Q' hQ', Nat.add_zero]
        exact Nat.le_zero.mp
          ((deepCount_le _).trans (Nat.le_of_eq (countVar_rename_liftRen_succ [] hd)))
  | (b :: bs, _) :: _, _, .cons hd tl, Q, hQ => by
      simp only [derivArgs, List.mem_map] at hQ
      obtain ⟨Q', hQ', hQQ⟩ := hQ
      subst hQQ
      simp only [argsThere, deepCountArgs]
      rw [countVar_rename_liftRen_succ, Nat.zero_add]
      exact derivArgs_shallow tl Q' hQ'
end

/-! ## Strengthening: a context that does not use its hole is a weakening

The completeness proof needs to recognise, at every argument the hole is not
in, that the argument is the plugged term weakened -- otherwise the enumerator's
output and the given position would be two different terms that happen to plug
to the same thing.  The statement is proved once, for an arbitrary renaming and
substitution that invert each other away from a chosen variable, so that the
recursion under a binder instantiates it at the lifted pair rather than needing
an equation between contexts. -/

theorem sameVar_eq_false_of_countVar_zero {Δ : Ctx S} {c s : S.Srt} (x : Var Δ c)
    (v : Var Δ s) (h : countVar x (Term.var v) = 0) : sameVar x v = false := by
  cases hb : sameVar x v with
  | false => rfl
  | true => rw [countVar, hb] at h; exact absurd h (by decide)

theorem liftSub_inv_of_miss {Δ Δ' : Ctx S} (rho : Ren S Δ Δ') (sigma : Sub S Δ' Δ)
    {c : S.Srt} (x : Var Δ' c)
    (hinv : ∀ (s : S.Srt) (v : Var Δ' s), sameVar x v = false →
      rename rho (sigma s v) = Term.var v) :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var (bs ++ Δ') s),
      sameVar (weakenVar bs x) v = false →
      rename (liftRen rho bs) (liftSub sigma bs s v) = Term.var v
  | [], s, v, h => hinv s v h
  | _ :: bs, s, v, h => by
      cases v with
      | zero => rfl
      | succ w =>
          have h' : sameVar (weakenVar bs x) w = false := h
          have ih := liftSub_inv_of_miss rho sigma x hinv bs s w h'
          show rename (liftRen rho (_ :: bs)) (weaken (liftSub sigma bs s w)) = _
          rw [weaken, rename_comp]
          show rename (fun r y => Var.succ (liftRen rho bs r y)) (liftSub sigma bs s w) = _
          rw [← rename_comp (liftRen rho bs) (fun _ v => Var.succ v), ih]
          rfl

mutual
/-- A term in which `x` does not occur is the image of the term `sigma` sends it
to under `rho`. -/
theorem eq_rename_of_miss : ∀ {Δ Δ' : Ctx S} (rho : Ren S Δ Δ') (sigma : Sub S Δ' Δ)
    {c : S.Srt} (x : Var Δ' c)
    (_ : ∀ (s : S.Srt) (v : Var Δ' s), sameVar x v = false →
      rename rho (sigma s v) = Term.var v)
    {s : S.Srt} (K : Term S Δ' s), countVar x K = 0 → K = rename rho (bind sigma K)
  | _, _, _, _, _, x, hinv, _, .var v, h => by
      rw [bind]
      exact (hinv _ v (sameVar_eq_false_of_countVar_zero x v h)).symm
  | _, _, rho, sigma, _, x, hinv, _, .op o args, h => by
      rw [bind, rename]
      exact congrArg (fun a => Term.op o a) (eqArgs_rename_of_miss rho sigma x hinv args h)

theorem eqArgs_rename_of_miss : ∀ {Δ Δ' : Ctx S} (rho : Ren S Δ Δ') (sigma : Sub S Δ' Δ)
    {c : S.Srt} (x : Var Δ' c)
    (_ : ∀ (s : S.Srt) (v : Var Δ' s), sameVar x v = false →
      rename rho (sigma s v) = Term.var v)
    {as : List (List S.Srt × S.Srt)} (T : Args S as Δ'),
    countVarArgs x T = 0 → T = renameArgs rho (bindArgs sigma T)
  | _, _, _, _, _, _, _, _, .nil, _ => rfl
  | _, _, rho, sigma, _, x, hinv, _, .cons (bs := bs) hd tl, h => by
      have hsum : countVar (weakenVar bs x) hd + countVarArgs x tl = 0 := h
      have h1 : countVar (weakenVar bs x) hd = 0 := by omega
      have h2 : countVarArgs x tl = 0 := by omega
      rw [bindArgs, renameArgs,
        ← eq_rename_of_miss (liftRen rho bs) (liftSub sigma bs) (weakenVar bs x)
          (liftSub_inv_of_miss rho sigma x hinv bs) hd h1,
        ← eqArgs_rename_of_miss rho sigma x hinv tl h2]
end

/-- The plugging substitution inverts weakening away from the hole. -/
theorem hole_inv {Γ : Ctx S} {c : S.Srt} (r : Term S Γ c) :
    ∀ (s : S.Srt) (v : Var (c :: Γ) s),
      sameVar (Var.zero : Var (c :: Γ) c) v = false →
      rename (fun _ w => Var.succ w) (extend r s v) = Term.var v
  | _, .zero, h => Bool.noConfusion h
  | _, .succ _, _ => rfl

/-! ## Completeness -/

theorem rootPosition_mem : ∀ {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s),
    rootPosition t ∈ deriv t
  | _, _, .var _ => by simp [deriv]
  | _, _, .op _ _ => by simp [deriv]

mutual
/-- **Every shallow one-hole context of a term is in its derivative.** -/
theorem mem_deriv : ∀ {Γ : Ctx S} {c s : S.Srt} (K : Term S (c :: Γ) s) (r : Term S Γ c)
    (t : Term S Γ s) (hplug : inst K r = t)
    (hlin : holeCount K = 1) (_ : deepCount K = 0),
    ({ carrier := c, ctxt := K, redex := r, plugs := hplug, linear := hlin } :
      LinearRedexPosition S Γ s t) ∈ deriv t
  | _, _, _, .var v, r, t, hplug, hlin, _ => by
      cases v with
      | zero =>
          subst hplug
          exact rootPosition_mem r
      | succ w => simp [holeCount, countVar, sameVar] at hlin
  | _, _, _, .op o Kargs, r, t, hplug, hlin, hsh => by
      subst hplug
      have hlin' : countVarArgs (Var.zero : Var _ _) Kargs = 1 := hlin
      have hsh' : deepCountArgs Kargs = 0 := by simpa only [deepCount] using hsh
      show ({ carrier := _, ctxt := Term.op o Kargs, redex := r, plugs := rfl, linear := hlin } :
          LinearRedexPosition S _ _ (Term.op o (bindArgs (extend r) Kargs)))
        ∈ deriv (Term.op o (bindArgs (extend r) Kargs))
      simp only [deriv, List.mem_cons, List.mem_map]
      exact Or.inr ⟨{ carrier := _, ctxt := Kargs, redex := r, plugs := rfl, linear := hlin' },
        memArgs_deriv Kargs r _ rfl hlin' hsh', rfl⟩

theorem memArgs_deriv : ∀ {Γ : Ctx S} {c : S.Srt} {as : List (List S.Srt × S.Srt)}
    (T : Args S as (c :: Γ)) (r : Term S Γ c) (args : Args S as Γ)
    (hplug : bindArgs (extend r) T = args)
    (hlin : countVarArgs (Var.zero : Var (c :: Γ) c) T = 1) (_ : deepCountArgs T = 0),
    ({ carrier := c, ctxt := T, redex := r, plugs := hplug, linear := hlin } :
      ArgsPosition S as Γ args) ∈ derivArgs args
  | _, _, _, .nil, _, _, _, hlin, _ => by simp [countVarArgs] at hlin
  | _, _, ([], _) :: _, .cons hd tl, r, args, hplug, hlin, hsh => by
      cases args with
      | cons a1 a2 =>
          injection hplug with _ _ _ _ hX hY
          have hsum : countVar (Var.zero : Var _ _) hd
              + countVarArgs (Var.zero : Var _ _) tl = 1 := hlin
          have hdeep : deepCount hd + deepCountArgs tl = 0 := by
            simpa only [deepCountArgs] using hsh
          rcases (by omega :
              countVar (Var.zero : Var _ _) hd = 1
                ∧ countVarArgs (Var.zero : Var _ _) tl = 0
              ∨ countVar (Var.zero : Var _ _) hd = 0
                ∧ countVarArgs (Var.zero : Var _ _) tl = 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have htl : tl = renameArgs (fun _ v => Var.succ v) a2 := by
              rw [← hY]
              exact eqArgs_rename_of_miss _ _ _ (hole_inv r) tl h2
            subst htl
            simp only [derivArgs, List.mem_append, List.mem_map]
            exact Or.inl ⟨{ carrier := _, ctxt := hd, redex := r, plugs := hX, linear := h1 },
              mem_deriv hd r a1 hX h1 (by omega), rfl⟩
          · have hhd : hd = rename (fun _ v => Var.succ v) a1 := by
              rw [← hX]
              exact eq_rename_of_miss _ _ _ (hole_inv r) hd h1
            subst hhd
            simp only [derivArgs, List.mem_append, List.mem_map]
            exact Or.inr ⟨{ carrier := _, ctxt := tl, redex := r, plugs := hY, linear := h2 },
              memArgs_deriv tl r a2 hY h2 (by omega), rfl⟩
  | _, _, (b :: bs, _) :: _, .cons hd tl, r, args, hplug, hlin, hsh => by
      cases args with
      | cons a1 a2 =>
          injection hplug with _ _ _ _ hX hY
          have hdeep : countVar (weakenVar (b :: bs) (Var.zero : Var _ _)) hd
              + deepCountArgs tl = 0 := by simpa only [deepCountArgs] using hsh
          have h1 : countVar (weakenVar (b :: bs) (Var.zero : Var _ _)) hd = 0 := by omega
          have hsum : countVar (weakenVar (b :: bs) (Var.zero : Var _ _)) hd
              + countVarArgs (Var.zero : Var _ _) tl = 1 := hlin
          have h2 : countVarArgs (Var.zero : Var _ _) tl = 1 := by omega
          have hhd : hd = rename (liftRen (fun _ v => Var.succ v) (b :: bs)) a1 := by
            rw [← hX]
            exact eq_rename_of_miss _ _ _
              (liftSub_inv_of_miss _ _ _ (hole_inv r) (b :: bs)) hd h1
          subst hhd
          simp only [derivArgs, List.mem_map]
          exact ⟨{ carrier := _, ctxt := tl, redex := r, plugs := hY, linear := h2 },
            memArgs_deriv tl r a2 hY h2 (by omega), rfl⟩
end

/-- **Completeness of the enumeration.**  Every shallow linear redex position of
a term is one the derivative returns. -/
theorem deriv_complete {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s)
    (P : LinearRedexPosition S Γ s t) (hsh : Shallow P.ctxt) : P ∈ deriv t := by
  obtain ⟨⟨c, K, r, hplug⟩, hlin⟩ := P
  exact mem_deriv K r t hplug hlin hsh

/-! ## A worked enumeration, and what it leaves out

The characterisation is not vacuous in either direction: a term with no binders
has all of its occurrences enumerated, and a term with a binder has a position
that is linear, genuinely decomposes it, and is not returned -- because its hole
sits under the binder, so the term in it would have to be scoped outside while
the occurrence it replaces is inside. -/

namespace BinderControl

inductive Srt1 where
  | tm
  deriving DecidableEq

inductive Op1 : Srt1 → Type where
  | lam : Op1 Srt1.tm
  | app : Op1 Srt1.tm
  | cst : Op1 Srt1.tm

/-- One sort, one binder, one binary former, one constant. -/
abbrev lsig : Signature where
  Srt := Srt1
  Op := Op1
  arity := fun {_} o => match o with
    | .lam => [([Srt1.tm], Srt1.tm)]
    | .app => [([], Srt1.tm), ([], Srt1.tm)]
    | .cst => []

def cst : Term lsig [] Srt1.tm := Term.op (S := lsig) Op1.cst Args.nil

/-- `app(c, c)`: no binders anywhere. -/
def appcc : Term lsig [] Srt1.tm :=
  Term.op (S := lsig) Op1.app (.cons cst (.cons cst .nil))

/-- **Three occurrences, three positions**: the whole term and each argument. -/
theorem deriv_appcc_length : (deriv appcc).length = 3 := by
  simp [appcc, cst, deriv, derivArgs]

/-- The position at the left argument, written out. -/
def leftPosition : LinearRedexPosition lsig [] Srt1.tm appcc where
  carrier := Srt1.tm
  ctxt := Term.op (S := lsig) Op1.app (.cons (Term.var Var.zero) (.cons (weaken cst) .nil))
  redex := cst
  plugs := rfl
  linear := rfl

/-- **Completeness finds it**, without inspecting the enumeration. -/
theorem leftPosition_enumerated : leftPosition ∈ deriv appcc :=
  deriv_complete appcc leftPosition (by
    simp [Shallow, leftPosition, deepCount, deepCountArgs, cst, weaken, rename,
      renameArgs, lsig])

/-- `lam(y. c)`. -/
def lamc : Term lsig [] Srt1.tm :=
  Term.op (S := lsig) Op1.lam (.cons (weaken cst) .nil)

/-- A one-hole context whose hole sits under the binder. -/
def deepCtxt : Term lsig [Srt1.tm] Srt1.tm :=
  Term.op (S := lsig) Op1.lam (.cons (Term.var (Var.succ Var.zero)) .nil)

/-- It is a genuine position: it decomposes `lam(y. c)` and uses its hole once. -/
def deepPosition : LinearRedexPosition lsig [] Srt1.tm lamc where
  carrier := Srt1.tm
  ctxt := deepCtxt
  redex := cst
  plugs := rfl
  linear := rfl

/-- Whether a position's one-hole context is the bare hole. -/
def ctxtIsHole {Γ : Ctx lsig} {s : Srt1} {t : Term lsig Γ s}
    (P : LinearRedexPosition lsig Γ s t) : Bool :=
  match P.ctxt with
  | .var _ => true
  | .op _ _ => false

/-- **So the enumeration does not return it.**  Under the binder there is only
one position at all -- the whole term -- and this is not it. -/
theorem deepPosition_not_enumerated : deepPosition ∉ deriv lamc := by
  intro h
  simp only [lamc, deriv, derivArgs, List.map_nil] at h
  rcases List.mem_cons.mp h with he | he
  · have hc := congrArg ctxtIsHole he
    simp [ctxtIsHole, deepPosition, deepCtxt, rootPosition] at hc
  · cases he

/-- **And therefore it is not shallow** -- read off from completeness rather
than computed, which is the sharper statement: were its hole not under the
binder, the enumeration would have had to return it. -/
theorem deepPosition_not_shallow : ¬ Shallow deepPosition.ctxt := fun hs =>
  deepPosition_not_enumerated (deriv_complete lamc deepPosition hs)

/-- Only the root, in a term whose single argument binds. -/
theorem deriv_lamc_length : (deriv lamc).length = 1 := by
  simp [lamc, deriv, derivArgs]

end BinderControl

end Mettapedia.OSLF.Binding
