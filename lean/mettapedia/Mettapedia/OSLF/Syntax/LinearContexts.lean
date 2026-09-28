import Mettapedia.OSLF.Syntax.ContextCategory
import Mettapedia.OSLF.Syntax.Strengthening
import Mettapedia.OSLF.Syntax.PositionEnumeration

/-!
# One-hole contexts whose linearity is structural

A one-hole context can be represented in two ways, and they trade off.

Writing it as a term with a distinguished free variable makes substitution and
the category laws come for free -- they are the unit and associativity of
substitution, read again -- but it makes *linearity* a side condition: nothing
in the type prevents the hole from occurring twice or not at all, so every use
carries a `holeCount = 1` hypothesis and composing two cuts requires a theorem
about how occurrence counts multiply through a substitution.

Writing it as an inductive shape with a `hole` constructor makes linearity a
fact about the type: there is exactly one hole because there is exactly one
place the constructor can sit.  Composition is then a definition, and the law
that was hard in the other representation -- linear cuts compose to a linear cut
-- is immediate.

Both are worth having, and this module supplies the second together with the
translation to the first, so no result proved about either has to be reproved
for the other.

The hole may sit under binders, which the position enumerator's class does not
allow.  That costs one thing: reading such a context as a term has to carry the
hole *past* the binders it sits under, which is an exchange, and an exchange
neither creates nor destroys occurrences only because a renaming that reflects
sameness preserves occurrence counts.  That is the one lemma the construction
rests on, and it is stated for an arbitrary renaming rather than at the point of
use.  Composition then has to weaken the context being plugged in, into whatever
binders the hole sits under, which is why renaming of structural contexts is
developed alongside.
-/

namespace Mettapedia.OSLF.Binding

open CategoryTheory

set_option autoImplicit false

variable {S : Signature}

mutual
/-- A one-hole context with the hole at top level or inside a non-binding
argument.  Exactly one `hole` occurs, by construction. -/
inductive LinCtx (S : Signature) (c : S.Srt) : Ctx S → S.Srt → Type where
  | hole {Γ : Ctx S} : LinCtx S c Γ c
  | op {Γ : Ctx S} {s : S.Srt} (o : S.Op s) (args : LinArgs S c Γ (S.arity o)) :
      LinCtx S c Γ s

/-- An argument list with the hole in exactly one of its non-binding slots. -/
inductive LinArgs (S : Signature) (c : S.Srt) :
    Ctx S → List (List S.Srt × S.Srt) → Type where
  | here {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt} {as : List (List S.Srt × S.Srt)}
      (K : LinCtx S c (bs ++ Γ) s) (rest : Args S as Γ) :
      LinArgs S c Γ ((bs, s) :: as)
  | there {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt}
      {as : List (List S.Srt × S.Srt)}
      (head : Term S (bs ++ Γ) s) (rest : LinArgs S c Γ as) :
      LinArgs S c Γ ((bs, s) :: as)
end

namespace LinCtx

/-- The weakening that makes room for the hole. -/
abbrev shift (S : Signature) (c : S.Srt) {Γ : Ctx S} : Ren S Γ (c :: Γ) :=
  fun _ v => Var.succ v

/-- **Carrying the hole past the binders it sits under.**  A context whose hole
is under `bs` binders is built with the hole at the front of its own scope; as a
term of the ambient scope the hole sits after those binders, and this is the
exchange that moves it. -/
def exch (c : S.Srt) {Γ : Ctx S} :
    (bs : List S.Srt) → Ren S (c :: (bs ++ Γ)) (bs ++ (c :: Γ))
  | bs, _, .zero => weakenVar bs (Var.zero : Var (c :: Γ) c)
  | bs, _, .succ v => liftRen (shift S c) bs _ v

/-- The exchange sends the hole to the hole. -/
theorem exch_zero (c : S.Srt) {Γ : Ctx S} (bs : List S.Srt) :
    exch c (Γ := Γ) bs c Var.zero = weakenVar bs (Var.zero : Var (c :: Γ) c) := rfl

/-- **The exchange reflects sameness at the hole**, so it neither creates nor
destroys occurrences of it. -/
theorem sameVar_exch (c : S.Srt) {Γ : Ctx S} (bs : List S.Srt) :
    ∀ (s : S.Srt) (v : Var (c :: (bs ++ Γ)) s),
      sameVar (exch c (Γ := Γ) bs c Var.zero) (exch c bs s v)
        = sameVar (Var.zero : Var (c :: (bs ++ Γ)) c) v := by
  intro s v
  cases v with
  | zero => exact sameVar_self _
  | succ w =>
      exact sameVar_weakenVar_liftRen (shift S c) (Var.zero : Var (c :: Γ) c)
        (fun _ _ => rfl) bs s w

mutual
/-- Read a structural context as a term with a distinguished free variable. -/
def toTerm {c : S.Srt} : {Γ : Ctx S} → {s : S.Srt} → LinCtx S c Γ s →
    Term S (c :: Γ) s
  | _, _, .hole => Term.var Var.zero
  | _, _, .op o args => Term.op o (toArgs args)

def toArgs {c : S.Srt} : {Γ : Ctx S} → {as : List (List S.Srt × S.Srt)} →
    LinArgs S c Γ as → Args S as (c :: Γ)
  | _, _, .here (bs := bs) K rest =>
      .cons (rename (exch c bs) (toTerm K)) (renameArgs (shift S c) rest)
  | _, _, .there (bs := bs) head rest =>
      .cons (rename (liftRen (shift S c) bs) head) (toArgs rest)
end

mutual
/-- **Linearity is a fact about the type.**  A structural context has exactly
one occurrence of its hole, with no side condition to carry. -/
theorem countVar_toTerm : ∀ {Γ : Ctx S} {c s : S.Srt} (K : LinCtx S c Γ s),
    countVar (Var.zero : Var (c :: Γ) c) (toTerm K) = 1
  | _, _, _, .hole => by simp only [toTerm]; rfl
  | _, _, _, .op _ args => by
      simp only [toTerm, countVar, countVarArgs_toArgs args]

theorem countVarArgs_toArgs : ∀ {Γ : Ctx S} {c : S.Srt}
    {as : List (List S.Srt × S.Srt)} (args : LinArgs S c Γ as),
    countVarArgs (Var.zero : Var (c :: Γ) c) (toArgs args) = 1
  | _, _, _, .here (bs := bs) K rest => by
      have hK : countVar (weakenVar bs (Var.zero : Var (_ :: _) _))
          (rename (exch _ bs) (toTerm K)) = 1 := by
        have h := countVar_rename_of_reflect (exch _ bs) Var.zero (sameVar_exch _ bs)
          (toTerm K)
        rw [countVar_toTerm K] at h
        exact h
      simp only [toArgs, countVarArgs, hK, countVarArgs_renameArgs_succ rest,
        Nat.add_zero]
  | _, _, _, .there (bs := bs) head rest => by
      simp only [toArgs, countVarArgs, countVar_rename_liftRen_succ bs head,
        countVarArgs_toArgs rest, Nat.zero_add]
end

theorem holeCount_toTerm {Γ : Ctx S} {c s : S.Srt} (K : LinCtx S c Γ s) :
    holeCount (toTerm K) = 1 := countVar_toTerm K

/-! ## The exchange is invertible

Carrying the hole past a binder prefix is a bijection on variables, so it has an
inverse rather than merely a partial one.  Writing that inverse down and proving
both round trips is what lets two exchanged contexts be compared: renaming along
it is injective, by the left-inverse argument, without inverting a constructor of
an inductive family. -/

/-- The inverse exchange: bring the hole back to the front. -/
def unexch (c : S.Srt) {Γ : Ctx S} :
    (bs : List S.Srt) → Ren S (bs ++ (c :: Γ)) (c :: (bs ++ Γ))
  | [], _, v => v
  | _ :: _, _, .zero => Var.succ Var.zero
  | _ :: bs, s, .succ u =>
      match unexch c bs s u with
      | .zero => Var.zero
      | .succ w => Var.succ (Var.succ w)

theorem unexch_exch (c : S.Srt) {Γ : Ctx S} :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var (c :: (bs ++ Γ)) s),
      unexch c bs s (exch c bs s v) = v
  | [], _, v => by cases v <;> simp only [unexch, exch, weakenVar, liftRen]
  | _ :: bs, s, v => by
      cases v with
      | zero =>
          have h := unexch_exch c bs c (Var.zero : Var (c :: (bs ++ Γ)) c)
          simp only [exch, weakenVar] at h ⊢
          simp only [unexch, h]
      | succ w =>
          cases w with
          | zero => simp only [exch, liftRen, unexch]
          | succ u =>
              have h := unexch_exch c bs _ (Var.succ u)
              simp only [exch, liftRen] at h ⊢
              simp only [unexch, h]

theorem exch_unexch (c : S.Srt) {Γ : Ctx S} :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var (bs ++ (c :: Γ)) s),
      exch c bs s (unexch c bs s v) = v
  | [], _, v => by cases v <;> simp only [unexch, exch, weakenVar, liftRen]
  | _ :: bs, s, v => by
      cases v with
      | zero => simp only [unexch, exch, liftRen]
      | succ u =>
          have h := exch_unexch c bs s u
          simp only [unexch]
          cases hcase : unexch c bs s u with
          | zero =>
              rw [hcase] at h
              simp only [exch, weakenVar]
              simp only [exch] at h
              exact congrArg Var.succ h
          | succ w =>
              rw [hcase] at h
              simp only [exch, liftRen]
              simp only [exch] at h
              exact congrArg Var.succ h

/-- The exchange therefore has a partial inverse, so renaming along it is
injective. -/
def exchStrengthener (c : S.Srt) {Γ : Ctx S} (bs : List S.Srt) :
    Mettapedia.OSLF.Binding.Strengthener (exch c (Γ := Γ) bs) where
  un := fun s v => some (unexch c bs s v)
  un_rho := fun s w => congrArg some (unexch_exch c bs s w)
  rho_un := by
    intro s v w hw
    injection hw with h
    rw [← h]
    exact exch_unexch c bs s v

/-! ## Renaming

A context whose hole is under binders has to receive the context plugged into it
*inside* those binders, so composition needs to weaken.  Renaming a structural
context is the operation that does it, and it is structural itself. -/

mutual
def renameLin {c : S.Srt} : {Γ Δ : Ctx S} → {s : S.Srt} → Ren S Γ Δ →
    LinCtx S c Γ s → LinCtx S c Δ s
  | _, _, _, _, .hole => .hole
  | _, _, _, rho, .op o args => .op o (renameLinArgs rho args)

def renameLinArgs {c : S.Srt} : {Γ Δ : Ctx S} → {as : List (List S.Srt × S.Srt)} →
    Ren S Γ Δ → LinArgs S c Γ as → LinArgs S c Δ as
  | _, _, _, rho, .here (bs := bs) K rest =>
      .here (renameLin (liftRen rho bs) K) (renameArgs rho rest)
  | _, _, _, rho, .there (bs := bs) head rest =>
      .there (rename (liftRen rho bs) head) (renameLinArgs rho rest)
end

mutual
theorem renameLin_renameLin : ∀ {Γ Δ Θ : Ctx S} {c s : S.Srt}
    (rho : Ren S Γ Δ) (rho' : Ren S Δ Θ) (K : LinCtx S c Γ s),
    renameLin rho' (renameLin rho K) = renameLin (fun t v => rho' t (rho t v)) K
  | _, _, _, _, _, _, _, .hole => by simp only [renameLin]
  | _, _, _, _, _, rho, rho', .op _ args => by
      simp only [renameLin, renameLinArgs_renameLinArgs rho rho' args]

theorem renameLinArgs_renameLinArgs : ∀ {Γ Δ Θ : Ctx S} {c : S.Srt}
    {as : List (List S.Srt × S.Srt)} (rho : Ren S Γ Δ) (rho' : Ren S Δ Θ)
    (args : LinArgs S c Γ as),
    renameLinArgs rho' (renameLinArgs rho args)
      = renameLinArgs (fun t v => rho' t (rho t v)) args
  | _, _, _, _, _, rho, rho', .here (bs := bs) K rest => by
      simp only [renameLinArgs, renameLin_renameLin (liftRen rho bs) (liftRen rho' bs) K,
        liftRen_comp rho rho' bs, renameArgs_comp rho rho' rest]
  | _, _, _, _, _, rho, rho', .there (bs := bs) head rest => by
      simp only [renameLinArgs, rename_comp (liftRen rho bs) (liftRen rho' bs) head,
        liftRen_comp rho rho' bs, renameLinArgs_renameLinArgs rho rho' rest]
end

/-! ## Composition -/

/-- The weakening into a binder prefix. -/
abbrev under (S : Signature) {Γ : Ctx S} (bs : List S.Srt) : Ren S Γ (bs ++ Γ) :=
  fun _ v => weakenVar bs v

mutual
/-- Plug a structural context into another's hole, weakening it into whatever
binders that hole sits under. -/
def comp {c d : S.Srt} : {Γ : Ctx S} → {s : S.Srt} →
    LinCtx S c Γ s → LinCtx S d Γ c → LinCtx S d Γ s
  | _, _, .hole, L => L
  | _, _, .op o args, L => .op o (compArgs args L)

def compArgs {c d : S.Srt} : {Γ : Ctx S} → {as : List (List S.Srt × S.Srt)} →
    LinArgs S c Γ as → LinCtx S d Γ c → LinArgs S d Γ as
  | _, _, .here (bs := bs) K rest, L =>
      .here (comp K (renameLin (under S bs) L)) rest
  | _, _, .there head rest, L => .there head (compArgs rest L)
end

mutual
theorem renameLin_comp : ∀ {Γ Δ : Ctx S} {c d s : S.Srt} (rho : Ren S Γ Δ)
    (K : LinCtx S c Γ s) (L : LinCtx S d Γ c),
    renameLin rho (comp K L) = comp (renameLin rho K) (renameLin rho L)
  | _, _, _, _, _, _, .hole, _ => by simp only [comp, renameLin]
  | _, _, _, _, _, rho, .op _ args, L => by
      simp only [comp, renameLin, renameLinArgs_compArgs rho args L]

theorem renameLinArgs_compArgs : ∀ {Γ Δ : Ctx S} {c d : S.Srt}
    {as : List (List S.Srt × S.Srt)} (rho : Ren S Γ Δ)
    (args : LinArgs S c Γ as) (L : LinCtx S d Γ c),
    renameLinArgs rho (compArgs args L)
      = compArgs (renameLinArgs rho args) (renameLin rho L)
  | _, _, _, _, _, rho, .here (bs := bs) K rest, L => by
      have hswap : renameLin (liftRen rho bs) (renameLin (under S bs) L)
          = renameLin (under S bs) (renameLin rho L) := by
        rw [renameLin_renameLin, renameLin_renameLin]
        exact congrArg (fun r => renameLin r L)
          (funext fun t => funext fun v => liftRen_weakenVar rho v bs)
      simp only [compArgs, renameLinArgs,
        renameLin_comp (liftRen rho bs) K (renameLin (under S bs) L), hswap]
  | _, _, _, _, _, rho, .there head rest, L => by
      simp only [compArgs, renameLinArgs, renameLinArgs_compArgs rho rest L]
end

mutual
theorem comp_hole : ∀ {Γ : Ctx S} {c s : S.Srt} (K : LinCtx S c Γ s),
    comp K (LinCtx.hole : LinCtx S c Γ c) = K
  | _, _, _, .hole => by simp only [comp]
  | _, _, _, .op _ args => by simp only [comp, compArgs_hole args]

theorem compArgs_hole : ∀ {Γ : Ctx S} {c : S.Srt}
    {as : List (List S.Srt × S.Srt)} (args : LinArgs S c Γ as),
    compArgs args (LinCtx.hole : LinCtx S c Γ c) = args
  | _, _, _, .here (bs := bs) K rest => by
      simp only [compArgs, renameLin, comp_hole K]
  | _, _, _, .there head rest => by simp only [compArgs, compArgs_hole rest]
end

theorem hole_comp {Γ : Ctx S} {c d : S.Srt} (L : LinCtx S d Γ c) :
    comp (LinCtx.hole : LinCtx S c Γ c) L = L := by simp only [comp]

mutual
theorem comp_assoc : ∀ {Γ : Ctx S} {b c d s : S.Srt} (K : LinCtx S c Γ s)
    (L : LinCtx S b Γ c) (M : LinCtx S d Γ b),
    comp (comp K L) M = comp K (comp L M)
  | _, _, _, _, _, .hole, _, _ => by simp only [comp]
  | _, _, _, _, _, .op _ args, L, M => by
      simp only [comp, compArgs_assoc args L M]

theorem compArgs_assoc : ∀ {Γ : Ctx S} {b c d : S.Srt}
    {as : List (List S.Srt × S.Srt)} (args : LinArgs S c Γ as)
    (L : LinCtx S b Γ c) (M : LinCtx S d Γ b),
    compArgs (compArgs args L) M = compArgs args (comp L M)
  | _, _, _, _, _, .here (bs := bs) K rest, L, M => by
      simp only [compArgs, comp_assoc K (renameLin (under S bs) L)
        (renameLin (under S bs) M), renameLin_comp (under S bs) L M]
  | _, _, _, _, _, .there head rest, L, M => by
      simp only [compArgs, compArgs_assoc rest L M]
end

/-- **Linear cuts compose to a linear cut**, with nothing to prove about how
occurrence counts multiply: the composite has one hole because its type says so.
This is the law the variable representation makes hard and this one makes
free. -/
theorem holeCount_comp {Γ : Ctx S} {c d s : S.Srt}
    (K : LinCtx S c Γ s) (L : LinCtx S d Γ c) :
    holeCount (toTerm (comp K L)) = 1 := holeCount_toTerm (comp K L)

/-- Lifting a renaming past the hole commutes with lifting it past a binder
prefix: the two ways of making room for both arrive at the same variable. -/
theorem liftRen_shift_commute (c : S.Srt) {Γ Δ : Ctx S} (rho : Ren S Γ Δ)
    (bs : List S.Srt) :
    (fun (t : S.Srt) (v : Var (bs ++ Γ) t) =>
        liftRen (shift S c) bs t (liftRen rho bs t v))
      = fun t v => liftRen (liftRen rho [c]) bs t (liftRen (shift S c) bs t v) := by
  rw [← liftRen_comp rho (shift S c) bs,
    ← liftRen_comp (shift S c) (liftRen rho [c]) bs]
  rfl

mutual
/-- **Renaming a structural context is renaming the term it denotes**, with the
hole left where it is. -/
theorem toTerm_renameLin : ∀ {Γ Δ : Ctx S} {c s : S.Srt} (rho : Ren S Γ Δ)
    (K : LinCtx S c Γ s),
    toTerm (renameLin rho K) = rename (liftRen rho [c]) (toTerm K)
  | _, _, _, _, _, .hole => by simp only [renameLin, toTerm, rename, liftRen]
  | _, _, _, _, rho, .op _ args => by
      simp only [renameLin, toTerm, rename, toArgs_renameLinArgs rho args]

theorem toArgs_renameLinArgs : ∀ {Γ Δ : Ctx S} {c : S.Srt}
    {as : List (List S.Srt × S.Srt)} (rho : Ren S Γ Δ) (args : LinArgs S c Γ as),
    toArgs (renameLinArgs rho args) = renameArgs (liftRen rho [c]) (toArgs args)
  | _, _, c, _, rho, .here (bs := bs) K rest => by
      have hcommute : (fun (t : S.Srt) (v : Var (c :: (bs ++ _)) t) =>
          exch c bs t (liftRen (liftRen rho bs) [c] t v))
            = fun t v => liftRen (liftRen rho [c]) bs t (exch c bs t v) := by
        funext t v
        cases v with
        | zero => simp only [liftRen, exch, liftRen_weakenVar]
        | succ w =>
            exact congrFun (congrFun (liftRen_shift_commute c rho bs) t) w
      simp only [renameLinArgs, toArgs, renameArgs,
        toTerm_renameLin (liftRen rho bs) K, rename_comp, renameArgs_comp]
      congr 1
      exact congrArg (fun f => rename f (toTerm K)) hcommute
  | _, _, c, _, rho, .there (bs := bs) head rest => by
      simp only [renameLinArgs, toArgs, renameArgs,
        toArgs_renameLinArgs rho rest, rename_comp,
        liftRen_shift_commute c rho bs]
end

/-! ## The translation is a functor

Composition in the structural representation is nesting in the variable one, so
no result proved about either representation has to be reproved for the other.
-/

mutual
/-- **The translation carries composition to nesting.** -/
theorem toTerm_comp : ∀ {Γ : Ctx S} {c d s : S.Srt} (K : LinCtx S c Γ s)
    (L : LinCtx S d Γ c),
    toTerm (comp K L) = ContextCat.comp (toTerm K) (toTerm L)
  | _, _, _, _, .hole, L => by
      simp only [comp, toTerm, ContextCat.comp, bind, ContextCat.holeSub]
  | _, _, _, _, .op o args, L => by
      simp only [comp, toTerm, ContextCat.comp, bind, toArgs_compArgs args L]

theorem toArgs_compArgs : ∀ {Γ : Ctx S} {c d : S.Srt}
    {as : List (List S.Srt × S.Srt)} (args : LinArgs S c Γ as)
    (L : LinCtx S d Γ c),
    toArgs (compArgs args L)
      = bindArgs (ContextCat.holeSub (toTerm L)) (toArgs args)
  | Γ, c, d, _, .here (bs := bs) K rest, L => by
      have h : (fun (r : S.Srt) (y : Var Γ r) =>
          ContextCat.holeSub (toTerm L) r (shift S c r y))
            = fun r y => Term.var (S := S) (shift S d r y) := rfl
      have hrest : bindArgs (ContextCat.holeSub (toTerm L))
          (renameArgs (shift S c) rest) = renameArgs (shift S d) rest := by
        rw [bindArgs_rename, h, bindArgs_var_eq_renameArgs]
      -- the exchange undoes the weakening that put the inner context under `bs`
      have hunder : (fun (t : S.Srt) (v : Var (d :: Γ) t) =>
          exch d bs t (liftRen (under S bs) [d] t v)) = under S (Γ := d :: Γ) bs := by
        funext t v
        cases v with
        | zero => rfl
        | succ w =>
            show liftRen (shift S d) bs t (weakenVar bs w) = weakenVar bs (Var.succ w)
            exact liftRen_weakenVar (shift S d) w bs
      -- the two substitutions agree pointwise on the hole and on everything else
      have hsub : (fun (t : S.Srt) (v : Var (c :: (bs ++ Γ)) t) =>
          rename (exch d bs)
            (ContextCat.holeSub (toTerm (renameLin (under S bs) L)) t v))
            = fun t v => liftSub (ContextCat.holeSub (toTerm L)) bs t (exch c bs t v) := by
        funext t v
        cases v with
        | zero =>
            show rename (exch d bs) (toTerm (renameLin (under S bs) L))
              = liftSub (ContextCat.holeSub (toTerm L)) bs c
                  (weakenVar bs (Var.zero : Var (c :: Γ) c))
            rw [liftSub_weakenVar, toTerm_renameLin, rename_comp]
            exact congrArg (fun f => rename f (toTerm L)) hunder
        | succ w =>
            show Term.var (exch d bs t (Var.succ w))
              = liftSub (ContextCat.holeSub (toTerm L)) bs t (exch c bs t (Var.succ w))
            show Term.var (liftRen (shift S d) bs t w)
              = liftSub (ContextCat.holeSub (toTerm L)) bs t (liftRen (shift S c) bs t w)
            have hls := congrFun (congrFun
              ((liftSub_liftRen (shift S c) (ContextCat.holeSub (toTerm L)) bs).trans
                (congrArg (fun f => liftSub f bs) h)) t) w
            rw [hls]
            exact (liftSub_var_comp (shift S d) bs t w).symm
      simp only [compArgs, toArgs, bindArgs, hrest,
        toTerm_comp K (renameLin (under S bs) L), ContextCat.comp,
        rename_bind, bind_rename, hsub]
  | Γ, c, d, _, .there (bs := bs) head rest, L => by
      have h : (fun (r : S.Srt) (y : Var Γ r) =>
          ContextCat.holeSub (toTerm L) r (shift S c r y))
            = fun r y => Term.var (S := S) (shift S d r y) := rfl
      have h2 : liftSub
            (fun (r : S.Srt) (y : Var Γ r) => Term.var (S := S) (shift S d r y)) bs
          = fun r y => Term.var (S := S) (liftRen (shift S d) bs r y) :=
        funext fun r => funext fun y => liftSub_var_comp (shift S d) bs r y
      have hhead : bind (liftSub (ContextCat.holeSub (toTerm L)) bs)
          (rename (liftRen (shift S c) bs) head)
            = rename (liftRen (shift S d) bs) head := by
        rw [bind_rename, liftSub_liftRen, h, h2, bind_var_eq_rename]
      simp only [compArgs, toArgs, toArgs_compArgs rest L, hhead, bindArgs]
end

/-! ## The translation is faithful

Two structural contexts that read as the same term are the same context.  The
comparison happens through the exchange and the weakening, and both are inverted
rather than having their constructors taken apart. -/

mutual
/-- **`toTerm` is injective.** -/
theorem toTerm_injective : ∀ {Γ : Ctx S} {c s : S.Srt} (K L : LinCtx S c Γ s),
    toTerm K = toTerm L → K = L
  | _, _, _, .hole, .hole, _ => rfl
  | _, _, _, .hole, .op _ _, h => by simp [toTerm] at h
  | _, _, _, .op _ _, .hole, h => by simp [toTerm] at h
  | _, _, _, .op o args, .op o' args', h => by
      simp only [toTerm] at h
      injection h with _ _ ho hargs
      subst ho
      exact congrArg (LinCtx.op o) (toArgs_injective args args' (eq_of_heq hargs))

theorem toArgs_injective : ∀ {Γ : Ctx S} {c : S.Srt}
    {as : List (List S.Srt × S.Srt)} (args args' : LinArgs S c Γ as),
    toArgs args = toArgs args' → args = args'
  | _, c, _, .here (bs := bs) K rest, .here K' rest', h => by
      simp only [toArgs] at h
      injection h with _ _ _ _ hhead htail
      exact congrArg₂ LinArgs.here
        (toTerm_injective K K'
          (Mettapedia.OSLF.Binding.rename_injective (exchStrengthener c bs) hhead))
        (Mettapedia.OSLF.Binding.renameArgs_injective
          (Mettapedia.OSLF.Binding.unweaken S c) htail)
  | _, c, _, .there (bs := bs) head rest, .there head' rest', h => by
      simp only [toArgs] at h
      injection h with _ _ _ _ hhead htail
      exact congrArg₂ LinArgs.there
        (Mettapedia.OSLF.Binding.rename_injective
          ((Mettapedia.OSLF.Binding.unweaken S c).liftS bs) hhead)
        (toArgs_injective rest rest' htail)
  | _, c, _, .here (bs := bs) K rest, .there head' rest', h => by
      exfalso
      simp only [toArgs] at h
      injection h with _ _ _ _ hhead _
      have h1 : countVar (weakenVar bs (Var.zero : Var (c :: _) c))
          (rename (exch c bs) (toTerm K)) = 1 := by
        have hK := countVar_rename_of_reflect (exch c bs) Var.zero (sameVar_exch c bs)
          (toTerm K)
        rw [countVar_toTerm K] at hK
        exact hK
      rw [hhead, countVar_rename_liftRen_succ bs head'] at h1
      exact absurd h1 (by decide)
  | _, c, _, .there (bs := bs) head rest, .here K' rest', h => by
      exfalso
      simp only [toArgs] at h
      injection h with _ _ _ _ hhead _
      have h1 : countVar (weakenVar bs (Var.zero : Var (c :: _) c))
          (rename (exch c bs) (toTerm K')) = 1 := by
        have hK := countVar_rename_of_reflect (exch c bs) Var.zero (sameVar_exch c bs)
          (toTerm K')
        rw [countVar_toTerm K'] at hK
        exact hK
      rw [← hhead, countVar_rename_liftRen_succ bs head] at h1
      exact absurd h1 (by decide)
end

/-! ## The translation is full

Every one-hole context of the variable representation, in the sense that its
hole occurs exactly once, is the reading of a structural one.  With faithfulness
this identifies the structural representation with the linear contexts, so the
side condition and the constructor are two descriptions of one thing.

The recursion is on the structural measure rather than on the term, because the
argument that carries the hole is examined through the exchange that brings the
hole to the front, and a renamed subterm is not a subterm.  Renaming does not
change the measure, which is what licenses the step. -/

mutual
theorem exists_linCtx (n : Nat) {Γ : Ctx S} {c s : S.Srt} (K : Term S (c :: Γ) s)
    (hn : termSize K ≤ n) (hc : countVar (Var.zero : Var (c :: Γ) c) K = 1) :
    ∃ L : LinCtx S c Γ s, toTerm L = K := by
  match K, hn, hc with
  | .var v, _, hc =>
      cases v with
      | zero => exact ⟨LinCtx.hole, by simp only [toTerm]⟩
      | succ w => simp [countVar, sameVar] at hc
  | .op o args, hn, hc =>
      simp only [termSize] at hn
      simp only [countVar] at hc
      have hpos : 1 ≤ n := by omega
      obtain ⟨L, hL⟩ := exists_linArgs (n - 1) args (by omega) hc
      exact ⟨LinCtx.op o L, by simp only [toTerm, hL]⟩
termination_by 2 * n
decreasing_by omega

theorem exists_linArgs (n : Nat) {Γ : Ctx S} {c : S.Srt}
    {as : List (List S.Srt × S.Srt)} (args : Args S as (c :: Γ))
    (hn : argsSize args ≤ n) (hc : countVarArgs (Var.zero : Var (c :: Γ) c) args = 1) :
    ∃ L : LinArgs S c Γ as, toArgs L = args := by
  match args, hn, hc with
  | .nil, _, hc => simp [countVarArgs] at hc
  | .cons (bs := bs) head tail, hn, hc =>
      simp only [argsSize] at hn
      simp only [countVarArgs] at hc
      have hheadpos := termSize_pos head
      have hpos : 1 ≤ n := by omega
      by_cases hhead : countVar (weakenVar bs (Var.zero : Var (c :: Γ) c)) head = 1
      · have htail : countVarArgs (Var.zero : Var (c :: Γ) c) tail = 0 := by omega
        have hback : rename (exch c bs) (rename (unexch c bs) head) = head := by
          rw [rename_comp]
          rw [show (fun (r : S.Srt) (v : Var (bs ++ (c :: Γ)) r) =>
              exch c bs r (unexch c bs r v)) = fun _ v => v from
            funext fun r => funext fun v => exch_unexch c bs r v, rename_id]
        have hcount : countVar (Var.zero : Var (c :: (bs ++ Γ)) c)
            (rename (unexch c bs) head) = 1 := by
          have hrefl := countVar_rename_of_reflect (exch c bs) Var.zero
            (sameVar_exch c bs) (rename (unexch c bs) head)
          rw [hback] at hrefl
          exact hrefl.symm.trans hhead
        obtain ⟨K, hK⟩ := exists_linCtx n (rename (unexch c bs) head)
          (by rw [termSize_rename]; omega) hcount
        obtain ⟨t, ht⟩ := strengthenA_isSome (unweaken S c) tail (by
          intro r v hv
          cases v with
          | zero => exact htail
          | succ _ => exact absurd hv (by simp [unweaken, Strengthener.ofWeaken]))
        refine ⟨LinArgs.here K t, ?_⟩
        simp only [toArgs, hK, hback,
          renameArgs_strengthenA (unweaken S c) tail t ht]
      · have hhead0 : countVar (weakenVar bs (Var.zero : Var (c :: Γ) c)) head = 0 := by
          omega
        have htail : countVarArgs (Var.zero : Var (c :: Γ) c) tail = 1 := by omega
        obtain ⟨h', hh'⟩ := strengthenT_isSome ((unweaken S c).liftS bs) head (by
          intro r w hw
          obtain ⟨v, hv, hun⟩ := (unweaken S c).liftS_un_eq_none bs r w hw
          cases v with
          | zero => rw [hv]; exact hhead0
          | succ _ => exact absurd hun (by simp [unweaken, Strengthener.ofWeaken]))
        obtain ⟨rest, hrest⟩ := exists_linArgs (n - 1) tail (by omega) htail
        refine ⟨LinArgs.there h' rest, ?_⟩
        simp only [toArgs, hrest,
          rename_strengthenT ((unweaken S c).liftS bs) head h' hh']
termination_by 2 * n + 1
decreasing_by
  · omega
  · omega
end

/-- **`toTerm` is onto the linear contexts.** -/
theorem exists_linCtx_of_holeCount {Γ : Ctx S} {c s : S.Srt} (K : Term S (c :: Γ) s)
    (h : holeCount K = 1) : ∃ L : LinCtx S c Γ s, toTerm L = K :=
  exists_linCtx (termSize K) K (Nat.le_refl _) h

/-- **The two representations of a one-hole context agree.**  A term with a
distinguished variable occurring exactly once is the same thing as a structural
context, and the identification is by the translation. -/
theorem toTerm_surjective_onto_linear {Γ : Ctx S} {c s : S.Srt} :
    ∀ K : Term S (c :: Γ) s, holeCount K = 1 ↔ ∃ L : LinCtx S c Γ s, toTerm L = K := by
  intro K
  constructor
  · exact exists_linCtx_of_holeCount K
  · rintro ⟨L, rfl⟩
    exact holeCount_toTerm L

/-! ## The category of structurally linear contexts -/

/-- An object: a sort, in the role of the type of a hole. -/
structure Obj (S : Signature) (_Γ : Ctx S) where
  /-- The sort a hole of this kind accepts. -/
  sort : S.Srt

instance linearContextCategory (S : Signature) (Γ : Ctx S) : Category (Obj S Γ) where
  Hom c s := LinCtx S c.sort Γ s.sort
  id _ := LinCtx.hole
  comp f g := LinCtx.comp g f
  id_comp f := comp_hole f
  comp_id f := hole_comp f
  assoc f g h := (comp_assoc h g f).symm

/-- **The functor on contexts is faithful.**  Two structural contexts with the
same reading are the same context, so the structural representation embeds in the
variable one rather than merely mapping into it. -/
theorem toTerm_hom_injective {Γ : Ctx S} {a b : Obj S Γ} (f g : a ⟶ b)
    (h : toTerm f = toTerm g) : f = g :=
  toTerm_injective f g h

/-- **The translation is a functor on the nose**: identities to identities and
composites to composites, with no coherence to check. -/
theorem toTerm_id {Γ : Ctx S} (c : Obj S Γ) :
    toTerm (𝟙 c) = (𝟙 (⟨c.sort⟩ : ContextCat.Hole S Γ) :
      (⟨c.sort⟩ : ContextCat.Hole S Γ) ⟶ ⟨c.sort⟩) := by
  show toTerm (LinCtx.hole : LinCtx S c.sort Γ c.sort)
    = Term.var (Var.zero : Var (c.sort :: Γ) c.sort)
  simp only [toTerm]

theorem toTerm_comp_hom {Γ : Ctx S} {a b c : Obj S Γ} (f : a ⟶ b) (g : b ⟶ c) :
    toTerm (f ≫ g) = ContextCat.comp (toTerm g) (toTerm f) :=
  toTerm_comp g f

/-! ## Negative controls -/

/-- The structural representation does not admit a context that ignores its
hole: every one of them has an occurrence, which a weakened term does not. -/
theorem no_vacuous_linCtx {Γ : Ctx S} {c s : S.Srt} (K : LinCtx S c Γ s)
    (u : Term S Γ s) : toTerm K ≠ weaken u := by
  intro h
  have h1 : holeCount (toTerm K) = 1 := holeCount_toTerm K
  rw [h, holeCount_weaken] at h1
  exact absurd h1 (by decide)

/-- And the variable representation does: the side condition is doing work, so
the two representations are genuinely different and the translation is not onto
without it. -/
theorem variable_representation_admits_vacuous {Γ : Ctx S} {c s : S.Srt}
    (u : Term S Γ s) : holeCount (weaken (t := c) u) = 0 := holeCount_weaken u

/-! ### The hole really may sit under a binder

A witness on the smallest signature that has one, so that the generality is
exhibited rather than asserted.  The position enumerator covers the contexts
whose hole is at top level in every slot it passes through; this one is not among
them, and it is still a context of this type. -/

namespace DeepHole

inductive Srt where
  | tm
  deriving DecidableEq

inductive Op : Srt → Type where
  | lam : Op Srt.tm
  | unit : Op Srt.tm

/-- One binding former and one constant. -/
abbrev sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} o => match o with
    | .lam => [([Srt.tm], Srt.tm)]
    | .unit => []

/-- The context that binds and then holds: its hole is under the binder. -/
def underBinder : LinCtx sig Srt.tm [] Srt.tm :=
  LinCtx.op (S := sig) (c := Srt.tm) (Γ := []) (s := Srt.tm) Op.lam
    (LinArgs.here (S := sig) (c := Srt.tm) (Γ := []) (bs := [Srt.tm])
      (s := Srt.tm) (as := [])
      (LinCtx.hole (S := sig) (c := Srt.tm) (Γ := [Srt.tm])) Args.nil)

/-- Its linearity is still a fact about the type. -/
theorem underBinder_linear : holeCount (toTerm underBinder) = 1 :=
  holeCount_toTerm underBinder

/-- **And its hole genuinely sits under a binder**, so the class represented
here strictly contains the one the position enumerator covers. -/
theorem underBinder_not_shallow : ¬ Shallow (toTerm underBinder) := by
  intro h
  simp only [Shallow, underBinder, toTerm, toArgs, deepCount, deepCountArgs,
    exch, rename, renameArgs, countVar, weakenVar] at h
  exact absurd h (by decide)

end DeepHole

end LinCtx

/-- Composing a structurally linear outer context with the occurrence context
of a rewrite preserves the contextual firing. This is the general law needed
for congruence rules such as rho's parallel closure. -/
theorem step_under_linear_context {M : List (MetaArity S)}
    (rule : PositionedRewrite (withMetas S M))
    {s : S.Srt} (outer : LinCtx S rule.sort [] s)
    {source target : Term S [] rule.sort}
    (fires : Step rule source target) :
    Step rule (inst (LinCtx.toTerm outer) source)
      (inst (LinCtx.toTerm outer) target) := by
  obtain ⟨inner, redex, reduct, linear, root, sourceEq, targetEq⟩ := fires
  obtain ⟨innerLinear, innerEq⟩ :=
    LinCtx.exists_linCtx_of_holeCount inner linear
  refine ⟨LinCtx.toTerm (LinCtx.comp outer innerLinear), redex, reduct,
    LinCtx.holeCount_toTerm _, root, ?_, ?_⟩
  · rw [LinCtx.toTerm_comp, innerEq]
    have composition := congrFun (ContextCat.act_comp
      (S := S) (Γ := [])
      (a := ⟨rule.sort⟩) (b := ⟨rule.sort⟩) (c := ⟨s⟩)
      (f := inner) (g := LinCtx.toTerm outer)) redex
    change inst (ContextCat.comp (LinCtx.toTerm outer) inner) redex =
      inst (LinCtx.toTerm outer) (inst inner redex) at composition
    rw [composition, sourceEq]
  · rw [LinCtx.toTerm_comp, innerEq]
    have composition := congrFun (ContextCat.act_comp
      (S := S) (Γ := [])
      (a := ⟨rule.sort⟩) (b := ⟨rule.sort⟩) (c := ⟨s⟩)
      (f := inner) (g := LinCtx.toTerm outer)) reduct
    change inst (ContextCat.comp (LinCtx.toTerm outer) inner) reduct =
      inst (LinCtx.toTerm outer) (inst inner reduct) at composition
    rw [composition, targetEq]

end Mettapedia.OSLF.Binding
