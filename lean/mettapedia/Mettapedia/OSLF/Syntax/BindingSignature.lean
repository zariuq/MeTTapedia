import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Relation

/-!
# Binding signatures and their term algebra

The syntactic component of a language definition `(Sigma, E, R)`.  The
signature is presented so that each operator declares, per argument, which
sorts that argument binds and what sort it has; binding is therefore part of
the signature rather than a property of particular constructors.

Terms are intrinsically sorted and intrinsically scoped. Renaming and
substitution use explicit lifts under each argument's declared binders; the
laws below give the presheaf action and substitution algebra. Scope indices
prevent references outside the context, but do not uniquely determine a
binder-preserving map: same-sort variables can still be exchanged by a
well-typed renaming. The defined lifts fix newly bound variables and weaken
the images of enclosing variables.

The laws proved below -- functoriality of renaming, unit and associativity of
substitution, and the two compatibility laws relating them -- hold for every
signature at once, rather than once per calculus.

A redex position is recorded at the end as a *factorisation*: a one-hole
context is a term with a distinguished free variable, and plugging is
substitution.  The sort of that variable is the carrier at which a generated
modality would live.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

/-- A **many-sorted binding signature**.  Each operator declares, per argument,
which sorts that argument binds and what sort the argument itself has; the
operator then has a result sort.

This is the datum the sorted term algebra reads. Writing
`lambda : ([A], B) ⟶ A⇒B` says "one argument, binding one variable of sort `A`,
whose body has sort `B`".  An `n`-ary application binds nothing.  Associativity
and commutativity of a parallel operator live in the equations, never here. -/
structure Signature where
  Srt : Type
  /-- Operators, indexed by the sort they produce.  Carrying the result sort as
  an index rather than a separate function means a term's sort is determined by
  its head constructor, so terms can be inverted. -/
  Op : Srt → Type
  /-- Per argument: the sorts it binds, then the sort of the argument itself. -/
  arity : {s : Srt} → Op s → List (List Srt × Srt)

variable {S : Signature}

/-- A typing context is a list of sorts; position is identity. -/
abbrev Ctx (S : Signature) : Type := List S.Srt

/-- A variable is a position in a list of sorts, carrying that position's sort.
It cannot be given a sort the context does not assign it.  Variables do not
depend on the operators, so a signature and any extension of it share them. -/
inductive Var {Srt : Type} : List Srt → Srt → Type where
  | zero {Γ : List Srt} {s : Srt} : Var (s :: Γ) s
  | succ {Γ : List Srt} {s t : Srt} : Var Γ s → Var (t :: Γ) s

mutual
/-- Terms, intrinsically sorted and intrinsically scoped. -/
inductive Term (S : Signature) : Ctx S → S.Srt → Type where
  | var {Γ : Ctx S} {s : S.Srt} : Var Γ s → Term S Γ s
  | op {Γ : Ctx S} {s : S.Srt} (o : S.Op s) : Args S (S.arity o) Γ → Term S Γ s

/-- The arguments of an operator, each opened under the sorts it binds. -/
inductive Args (S : Signature) : List (List S.Srt × S.Srt) → Ctx S → Type where
  | nil {Γ : Ctx S} : Args S [] Γ
  | cons {bs : List S.Srt} {s : S.Srt} {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} :
      Term S (bs ++ Γ) s → Args S as Γ → Args S ((bs, s) :: as) Γ
end

/-! ## Renaming — the functorial action -/

/-- A renaming is a sort-preserving map on variables. -/
abbrev Ren (S : Signature) (Γ Δ : Ctx S) : Type := (s : S.Srt) → Var Γ s → Var Δ s

/-- Lift a renaming under the sorts bound by one argument. -/
def liftRen {Srt : Type} {Γ Δ : List Srt} (rho : (s : Srt) → Var Γ s → Var Δ s) :
    (bs : List Srt) → (s : Srt) → Var (bs ++ Γ) s → Var (bs ++ Δ) s
  | [], s, v => rho s v
  | _ :: bs, _, .zero => .zero
  | _ :: bs, s, .succ w => .succ (liftRen rho bs s w)

mutual
def rename : {Γ Δ : Ctx S} → {s : S.Srt} → Ren S Γ Δ → Term S Γ s → Term S Δ s
  | _, _, _, rho, .var v => .var (rho _ v)
  | _, _, _, rho, .op o args => .op o (renameArgs rho args)

def renameArgs : {as : List (List S.Srt × S.Srt)} → {Γ Δ : Ctx S} →
    Ren S Γ Δ → Args S as Γ → Args S as Δ
  | _, _, _, _, .nil => .nil
  | _, _, _, rho, .cons (bs := bs) head tail =>
      .cons (rename (liftRen rho bs) head) (renameArgs rho tail)
end

/-- Weakening by one sort: the context grows, the term does not change. -/
def weaken {Γ : Ctx S} {s t : S.Srt} (u : Term S Γ s) : Term S (t :: Γ) s :=
  rename (fun _ v => .succ v) u

/-! ## Substitution — the monoid multiplication -/

/-- A substitution sends each variable to a term of the same sort. -/
abbrev Sub (S : Signature) (Γ Δ : Ctx S) : Type := (s : S.Srt) → Var Γ s → Term S Δ s

/-- Lift a substitution under the sorts bound by one argument. -/
def liftSub {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) : (bs : List S.Srt) → Sub S (bs ++ Γ) (bs ++ Δ)
  | [], s, v => sigma s v
  | _ :: bs, _, .zero => .var .zero
  | _ :: bs, s, .succ w => weaken (liftSub sigma bs s w)

mutual
/-- Substitution uses `liftSub` under each argument's declared binders. This
lift fixes newly bound variables and weakens the images of enclosing variables;
scope-correctness alone does not force this choice. -/
def bind : {Γ Δ : Ctx S} → {s : S.Srt} → Sub S Γ Δ → Term S Γ s → Term S Δ s
  | _, _, _, sigma, .var v => sigma _ v
  | _, _, _, sigma, .op o args => .op o (bindArgs sigma args)

def bindArgs : {as : List (List S.Srt × S.Srt)} → {Γ Δ : Ctx S} →
    Sub S Γ Δ → Args S as Γ → Args S as Δ
  | _, _, _, _, .nil => .nil
  | _, _, _, sigma, .cons (bs := bs) head tail =>
      .cons (bind (liftSub sigma bs) head) (bindArgs sigma tail)
end

/-! ## The presheaf laws -/

theorem liftRen_id {Γ : Ctx S} : ∀ (bs : List S.Srt),
    liftRen (Srt := S.Srt) (Γ := Γ) (Δ := Γ) (fun _ v => v) bs = fun _ v => v
  | [] => rfl
  | _ :: bs => by
      funext s v
      cases v with
      | zero => rfl
      | succ w => simp only [liftRen, liftRen_id bs]

mutual
theorem rename_id : ∀ {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s),
    rename (fun _ v => v) t = t
  | _, _, .var _ => rfl
  | _, _, .op o args => by simp only [rename, renameArgs_id args]

theorem renameArgs_id : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args S as Γ),
    renameArgs (fun _ v => v) args = args
  | _, _, .nil => rfl
  | _, _, .cons (bs := bs) head tail => by
      simp only [renameArgs, liftRen_id bs, rename_id head, renameArgs_id tail]
end

theorem liftRen_comp {Γ Δ Θ : Ctx S} (rho : Ren S Γ Δ) (rho' : Ren S Δ Θ) :
    ∀ (bs : List S.Srt), liftRen (fun s v => rho' s (rho s v)) bs
      = fun s v => liftRen rho' bs s (liftRen rho bs s v)
  | [] => rfl
  | _ :: bs => by
      funext s v
      cases v with
      | zero => rfl
      | succ w => simp only [liftRen, liftRen_comp rho rho' bs]

mutual
theorem rename_comp : ∀ {Γ Δ Θ : Ctx S} {s : S.Srt} (rho : Ren S Γ Δ) (rho' : Ren S Δ Θ)
    (t : Term S Γ s), rename rho' (rename rho t) = rename (fun s v => rho' s (rho s v)) t
  | _, _, _, _, _, _, .var _ => rfl
  | _, _, _, _, rho, rho', .op o args => by
      simp only [rename, renameArgs_comp rho rho' args]

theorem renameArgs_comp : ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ Θ : Ctx S}
    (rho : Ren S Γ Δ) (rho' : Ren S Δ Θ) (args : Args S as Γ),
    renameArgs rho' (renameArgs rho args)
      = renameArgs (fun s v => rho' s (rho s v)) args
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, rho, rho', .cons (bs := bs) head tail => by
      simp only [renameArgs, renameArgs_comp rho rho' tail,
        rename_comp (liftRen rho bs) (liftRen rho' bs) head, liftRen_comp rho rho' bs]
end

/-! ## The identity substitution -/

theorem liftSub_var {Γ : Ctx S} : ∀ (bs : List S.Srt),
    liftSub (S := S) (Γ := Γ) (Δ := Γ) (fun _ v => .var v) bs = fun _ v => .var v
  | [] => rfl
  | _ :: bs => by
      funext s v
      cases v with
      | zero => rfl
      | succ w => simp only [liftSub, liftSub_var bs, weaken, rename]

mutual
theorem bind_id : ∀ {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s),
    bind (fun _ v => .var v) t = t
  | _, _, .var _ => rfl
  | _, _, .op o args => by simp only [bind, bindArgs_id args]

theorem bindArgs_id : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args S as Γ),
    bindArgs (fun _ v => .var v) args = args
  | _, _, .nil => rfl
  | _, _, .cons (bs := bs) head tail => by
      simp only [bindArgs, liftSub_var bs, bind_id head, bindArgs_id tail]
end

/-! ## Renaming and substitution commute -/

theorem liftSub_liftRen {Γ Δ Θ : Ctx S} (rho : Ren S Γ Δ) (sigma : Sub S Δ Θ) :
    ∀ (bs : List S.Srt), (fun s v => liftSub sigma bs s (liftRen rho bs s v))
      = liftSub (fun s v => sigma s (rho s v)) bs
  | [] => rfl
  | _ :: bs => by
      funext s v
      cases v with
      | zero => simp only [liftRen, liftSub]
      | succ w => simp only [liftRen, liftSub, ← liftSub_liftRen rho sigma bs]

mutual
theorem bind_rename : ∀ {Γ Δ Θ : Ctx S} {s : S.Srt} (rho : Ren S Γ Δ) (sigma : Sub S Δ Θ)
    (t : Term S Γ s), bind sigma (rename rho t) = bind (fun s v => sigma s (rho s v)) t
  | _, _, _, _, _, _, .var _ => rfl
  | _, _, _, _, rho, sigma, .op o args => by
      simp only [rename, bind, bindArgs_rename rho sigma args]

theorem bindArgs_rename : ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ Θ : Ctx S}
    (rho : Ren S Γ Δ) (sigma : Sub S Δ Θ) (args : Args S as Γ),
    bindArgs sigma (renameArgs rho args) = bindArgs (fun s v => sigma s (rho s v)) args
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, rho, sigma, .cons (bs := bs) head tail => by
      simp only [renameArgs, bindArgs, bindArgs_rename rho sigma tail,
        bind_rename (liftRen rho bs) (liftSub sigma bs) head, liftSub_liftRen rho sigma bs]
end

theorem liftSub_rename {Γ Δ Θ : Ctx S} (sigma : Sub S Γ Δ) (rho : Ren S Δ Θ) :
    ∀ (bs : List S.Srt), (fun s v => rename (liftRen rho bs) (liftSub sigma bs s v))
      = liftSub (fun s v => rename rho (sigma s v)) bs
  | [] => rfl
  | _ :: bs => by
      funext s v
      cases v with
      | zero => simp only [liftSub, rename, liftRen]
      | succ w =>
          simp only [liftSub, weaken, rename_comp, liftRen,
            ← liftSub_rename sigma rho bs]
          rfl

mutual
theorem rename_bind : ∀ {Γ Δ Θ : Ctx S} {s : S.Srt} (sigma : Sub S Γ Δ) (rho : Ren S Δ Θ)
    (t : Term S Γ s), rename rho (bind sigma t) = bind (fun s v => rename rho (sigma s v)) t
  | _, _, _, _, _, _, .var _ => rfl
  | _, _, _, _, sigma, rho, .op o args => by
      simp only [bind, rename, renameArgs_bind sigma rho args]

theorem renameArgs_bind : ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ Θ : Ctx S}
    (sigma : Sub S Γ Δ) (rho : Ren S Δ Θ) (args : Args S as Γ),
    renameArgs rho (bindArgs sigma args) = bindArgs (fun s v => rename rho (sigma s v)) args
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, sigma, rho, .cons (bs := bs) head tail => by
      simp only [bindArgs, renameArgs, renameArgs_bind sigma rho tail,
        rename_bind (liftSub sigma bs) (liftRen rho bs) head, liftSub_rename sigma rho bs]
end

/-! ## Substitution composes: the monoid law -/

theorem liftSub_comp {Γ Δ Θ : Ctx S} (sigma : Sub S Γ Δ) (sigma' : Sub S Δ Θ) :
    ∀ (bs : List S.Srt), (fun s v => bind (liftSub sigma' bs) (liftSub sigma bs s v))
      = liftSub (fun s v => bind sigma' (sigma s v)) bs
  | [] => rfl
  | _ :: bs => by
      funext s v
      cases v with
      | zero => simp only [liftSub, bind]
      | succ w =>
          simp only [liftSub, weaken, bind_rename, rename_bind,
            ← liftSub_comp sigma sigma' bs]
          rfl

mutual
/-- **Associativity of substitution** — `Term S` is a monoid in the presheaf
category over sorted contexts and renamings.  This is the law a per-constructor
substitution gets wrong. -/
theorem bind_comp : ∀ {Γ Δ Θ : Ctx S} {s : S.Srt} (sigma : Sub S Γ Δ) (sigma' : Sub S Δ Θ)
    (t : Term S Γ s), bind sigma' (bind sigma t) = bind (fun s v => bind sigma' (sigma s v)) t
  | _, _, _, _, _, _, .var _ => rfl
  | _, _, _, _, sigma, sigma', .op o args => by
      simp only [bind, bindArgs_comp sigma sigma' args]

theorem bindArgs_comp : ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ Θ : Ctx S}
    (sigma : Sub S Γ Δ) (sigma' : Sub S Δ Θ) (args : Args S as Γ),
    bindArgs sigma' (bindArgs sigma args) = bindArgs (fun s v => bind sigma' (sigma s v)) args
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, sigma, sigma', .cons (bs := bs) head tail => by
      simp only [bindArgs, bindArgs_comp sigma sigma' tail,
        bind_comp (liftSub sigma bs) (liftSub sigma' bs) head, liftSub_comp sigma sigma' bs]
end

/-! ## Redex positions as factorizations

A one-hole context is a term with one distinguished free variable; plugging is
substitution.  So a redex position in `L` is a *factorization* of `L` through
the hole's sort, and the sort of the hole is the carrier at which the generated
modality lives. -/

/-- The substitution sending the top variable to `t` and every other variable
to itself. -/
def extend {Γ : Ctx S} {c : S.Srt} (t : Term S Γ c) : Sub S (c :: Γ) Γ
  | _, .zero => t
  | _, .succ w => .var w

/-- Plug a term into the hole of a one-hole context. -/
def inst {Γ : Ctx S} {c s : S.Srt} (K : Term S (c :: Γ) s) (t : Term S Γ c) :
    Term S Γ s :=
  bind (extend t) K

/-- A **redex position** in `L`: a one-hole context together with the subterm
occupying the hole, and a proof that plugging recovers `L`.

This records the data of a chosen subterm occurrence `t` of `L` with carrier
`c`, determining a one-hole context `K` with `K[t] = L`. -/
structure RedexPosition (S : Signature) (Γ : Ctx S) (s : S.Srt) (L : Term S Γ s) where
  /-- The sort of the hole: the carrier at which the generated modality sits. -/
  carrier : S.Srt
  /-- The one-hole context, as a term whose top variable is the hole. -/
  ctxt : Term S (carrier :: Γ) s
  /-- The subterm occupying the hole. -/
  redex : Term S Γ carrier
  /-- Plugging the redex back into the context recovers the left-hand side. -/
  plugs : inst ctxt redex = L

/-- Plugging into a context that ignores its hole returns the context. -/
theorem inst_weaken {Γ : Ctx S} {c s : S.Srt} (u : Term S Γ s) (t : Term S Γ c) :
    inst (weaken u) t = u := by
  simp only [inst, weaken, bind_rename, extend, bind_id]


/-- Do two variables occupy the same position?  A position determines its sort,
so this compares across sorts. -/
def sameVar : {Δ : Ctx S} → {c s : S.Srt} → Var Δ c → Var Δ s → Bool
  | _, _, _, .zero, .zero => true
  | _, _, _, .succ x, .succ y => sameVar x y
  | _, _, _, _, _ => false

/-- Shift a variable under the sorts bound by one argument. -/
def weakenVar {Δ : Ctx S} {c : S.Srt} : (bs : List S.Srt) → Var Δ c → Var (bs ++ Δ) c
  | [], x => x
  | _ :: bs, x => .succ (weakenVar bs x)

mutual
/-- The number of occurrences of a given variable in a term. -/
def countVar : {Δ : Ctx S} → {c s : S.Srt} → Var Δ c → Term S Δ s → Nat
  | _, _, _, x, .var v => if sameVar x v then 1 else 0
  | _, _, _, x, .op _ args => countVarArgs x args

def countVarArgs : {as : List (List S.Srt × S.Srt)} → {Δ : Ctx S} → {c : S.Srt} →
    Var Δ c → Args S as Δ → Nat
  | _, _, _, _, .nil => 0
  | _, _, _, x, .cons (bs := bs) head tail =>
      countVar (weakenVar bs x) head + countVarArgs x tail
end

/-- The number of occurrences of the hole in a one-hole context. -/
def holeCount {Γ : Ctx S} {c s : S.Srt} (K : Term S (c :: Γ) s) : Nat :=
  countVar (Var.zero : Var (c :: Γ) c) K

/-- A redex position at which the hole really is an *occurrence*: it appears,
and it appears once.  This is the condition the plugging equation does not
supply, and without it the redex at a position need not be determined. -/
structure LinearRedexPosition (S : Signature) (Γ : Ctx S) (s : S.Srt) (L : Term S Γ s)
    extends RedexPosition S Γ s L where
  /-- The hole occurs exactly once in the context. -/
  linear : holeCount ctxt = 1

/-! ## A renaming that misses a variable leaves no occurrence of it -/

/-- Missing a variable is preserved by lifting. -/
theorem sameVar_weakenVar_liftRen {Δ Δ' : Ctx S} {c : S.Srt}
    (rho : Ren S Δ Δ') (x : Var Δ' c)
    (hmiss : ∀ (s : S.Srt) (v : Var Δ s), sameVar x (rho s v) = false) :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var (bs ++ Δ) s),
      sameVar (weakenVar bs x) (liftRen rho bs s v) = false
  | [], s, v => hmiss s v
  | _ :: bs, s, v => by
      cases v with
      | zero => rfl
      | succ w =>
          simp only [weakenVar, liftRen, sameVar]
          exact sameVar_weakenVar_liftRen rho x hmiss bs s w

mutual
theorem countVar_rename_of_miss : ∀ {Δ Δ' : Ctx S} {c : S.Srt} (rho : Ren S Δ Δ')
    (x : Var Δ' c) (_ : ∀ (s : S.Srt) (v : Var Δ s), sameVar x (rho s v) = false)
    {s : S.Srt} (t : Term S Δ s), countVar x (rename rho t) = 0
  | _, _, _, rho, x, hmiss, _, .var v => by
      simp [rename, countVar, hmiss]
  | _, _, _, rho, x, hmiss, _, .op o args => by
      simp only [rename, countVar, countVarArgs_rename_of_miss rho x hmiss args]

theorem countVarArgs_rename_of_miss : ∀ {Δ Δ' : Ctx S} {c : S.Srt} (rho : Ren S Δ Δ')
    (x : Var Δ' c) (_ : ∀ (s : S.Srt) (v : Var Δ s), sameVar x (rho s v) = false)
    {as : List (List S.Srt × S.Srt)} (args : Args S as Δ),
    countVarArgs x (renameArgs rho args) = 0
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, rho, x, hmiss, _, .cons (bs := bs) head tail => by
      simp only [renameArgs, countVarArgs,
        countVar_rename_of_miss (liftRen rho bs) (weakenVar bs x)
          (sameVar_weakenVar_liftRen rho x hmiss bs) head,
        countVarArgs_rename_of_miss rho x hmiss tail]
end

/-! ### A structural measure

The term type is an inductive family whose indices are not variables, so
structural recursion is unavailable on it wherever a recursive call goes through
a renaming rather than into a subterm.  Every such construction needs the same
measure and the same fact about it -- that renaming does not change it -- so
both are given once here rather than per signature. -/

mutual
/-- The number of nodes of a term. -/
def termSize : {Γ : Ctx S} → {s : S.Srt} → Term S Γ s → Nat
  | _, _, .var _ => 1
  | _, _, .op _ args => argsSize args + 1

def argsSize : {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} → Args S as Γ → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => termSize head + argsSize tail
end

theorem termSize_pos : ∀ {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s), 0 < termSize t
  | _, _, .var _ => Nat.zero_lt_one
  | _, _, .op _ _ => Nat.succ_pos _

mutual
/-- **Renaming does not change the measure**, which is what lets a recursion
pass through one. -/
theorem termSize_rename : ∀ {Γ Δ : Ctx S} (rho : Ren S Γ Δ) {s : S.Srt}
    (t : Term S Γ s), termSize (rename rho t) = termSize t
  | _, _, _, _, .var _ => rfl
  | _, _, rho, _, .op _ args => by
      simp only [rename, termSize, argsSize_renameArgs rho args]

theorem argsSize_renameArgs : ∀ {Γ Δ : Ctx S} (rho : Ren S Γ Δ)
    {as : List (List S.Srt × S.Srt)} (args : Args S as Γ),
    argsSize (renameArgs rho args) = argsSize args
  | _, _, _, _, .nil => rfl
  | _, _, rho, _, .cons (bs := bs) head tail => by
      simp only [renameArgs, argsSize, termSize_rename (liftRen rho bs) head,
        argsSize_renameArgs rho tail]
end

/-- A term is bigger than any argument of its head. -/
theorem termSize_cons_head {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt}
    {as : List (List S.Srt × S.Srt)} (head : Term S (bs ++ Γ) s)
    (tail : Args S as Γ) : termSize head < argsSize (Args.cons head tail) + 1 := by
  simp only [argsSize]
  omega

theorem argsSize_cons_tail {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt}
    {as : List (List S.Srt × S.Srt)} (head : Term S (bs ++ Γ) s)
    (tail : Args S as Γ) : argsSize tail < argsSize (Args.cons head tail) + 1 := by
  have := termSize_pos head
  simp only [argsSize]
  omega

/-! ### Counting under a renaming that reflects sameness

The lemmas above say a renaming that *misses* a variable leaves no occurrence of
it.  The dual is needed wherever a context is moved rather than weakened -- in
particular wherever a hole is carried past a binder -- and it is the statement
that a renaming which reflects sameness preserves occurrence counts exactly.
Every route to holes under binders needs it, which is why it is stated here for
an arbitrary renaming rather than at the point of use. -/

/-- A lifted substitution at a weakened variable is the original value, weakened.
This is what lets a hole under binders be plugged from outside them. -/
theorem liftSub_weakenVar {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) {c : S.Srt} (x : Var Γ c) :
    ∀ (bs : List S.Srt), liftSub sigma bs c (weakenVar bs x)
      = rename (fun _ v => weakenVar bs v) (sigma c x)
  | [] => (rename_id _).symm
  | _ :: bs => by
      simp only [weakenVar, liftSub, liftSub_weakenVar sigma x bs, weaken,
        rename_comp]

/-- A variable is the same as itself. -/
theorem sameVar_self {Δ : Ctx S} {c : S.Srt} : ∀ (x : Var Δ c), sameVar x x = true
  | .zero => rfl
  | .succ w => by simp only [sameVar]; exact sameVar_self w

/-- Lifting commutes with weakening a variable. -/
theorem liftRen_weakenVar {Δ Δ' : Ctx S} {c : S.Srt} (rho : Ren S Δ Δ') (x : Var Δ c) :
    ∀ (bs : List S.Srt), liftRen rho bs c (weakenVar bs x) = weakenVar bs (rho c x)
  | [] => rfl
  | _ :: bs => by simp only [weakenVar, liftRen, liftRen_weakenVar rho x bs]

/-- Reflecting sameness is preserved by lifting. -/
theorem sameVar_weakenVar_liftRen_reflect {Δ Δ' : Ctx S} {c : S.Srt}
    (rho : Ren S Δ Δ') (x : Var Δ c)
    (hrefl : ∀ (s : S.Srt) (v : Var Δ s), sameVar (rho c x) (rho s v) = sameVar x v) :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var (bs ++ Δ) s),
      sameVar (weakenVar bs (rho c x)) (liftRen rho bs s v) = sameVar (weakenVar bs x) v
  | [], s, v => hrefl s v
  | _ :: bs, s, v => by
      cases v with
      | zero => rfl
      | succ w =>
          simp only [weakenVar, liftRen, sameVar]
          exact sameVar_weakenVar_liftRen_reflect rho x hrefl bs s w

mutual
/-- **A renaming that reflects sameness preserves occurrence counts.**  So
moving a context -- as opposed to weakening it -- neither creates nor destroys
occurrences of its hole. -/
theorem countVar_rename_of_reflect : ∀ {Δ Δ' : Ctx S} {c : S.Srt} (rho : Ren S Δ Δ')
    (x : Var Δ c)
    (_ : ∀ (s : S.Srt) (v : Var Δ s), sameVar (rho c x) (rho s v) = sameVar x v)
    {s : S.Srt} (t : Term S Δ s), countVar (rho c x) (rename rho t) = countVar x t
  | _, _, _, _, _, hrefl, _, .var v => by
      simp only [rename, countVar, hrefl]
  | _, _, _, rho, x, hrefl, _, .op _ args => by
      simp only [rename, countVar, countVarArgs_rename_of_reflect rho x hrefl args]

theorem countVarArgs_rename_of_reflect : ∀ {Δ Δ' : Ctx S} {c : S.Srt}
    (rho : Ren S Δ Δ') (x : Var Δ c)
    (_ : ∀ (s : S.Srt) (v : Var Δ s), sameVar (rho c x) (rho s v) = sameVar x v)
    {as : List (List S.Srt × S.Srt)} (args : Args S as Δ),
    countVarArgs (rho c x) (renameArgs rho args) = countVarArgs x args
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, rho, x, hrefl, _, .cons (bs := bs) head tail => by
      have hlift : ∀ (s : S.Srt) (v : Var (bs ++ _) s),
          sameVar (liftRen rho bs _ (weakenVar bs x)) (liftRen rho bs s v)
            = sameVar (weakenVar bs x) v := by
        intro s v
        rw [liftRen_weakenVar rho x bs]
        exact sameVar_weakenVar_liftRen_reflect rho x hrefl bs s v
      have hhead := countVar_rename_of_reflect (liftRen rho bs) (weakenVar bs x)
        hlift head
      rw [liftRen_weakenVar rho x bs] at hhead
      simp only [renameArgs, countVarArgs, hhead,
        countVarArgs_rename_of_reflect rho x hrefl tail]
end

/-- **A context that was merely weakened never uses its hole.**  So the vacuous
positions are exactly excluded by the linearity condition. -/
theorem holeCount_weaken {Γ : Ctx S} {c s : S.Srt} (u : Term S Γ s) :
    holeCount (c := c) (weaken u) = 0 := by
  refine countVar_rename_of_miss (fun _ v => Var.succ v) Var.zero ?_ u
  intro _ _
  rfl


/-! ## Metavariables -/

/-- A metavariable declaration: the sorts of the arguments it is applied to,
and its own sort.  A first-order metavariable takes no arguments. -/
abbrev MetaArity (S : Signature) : Type := List S.Srt × S.Srt

/-- The adjoined metavariables, as operators indexed by the sort they produce. -/
inductive MetaOp {S : Signature} (M : List (MetaArity S)) : S.Srt → Type where
  | mk (i : Fin M.length) : MetaOp M (M.get i).2

/-- Adjoin metavariables to a signature **as operators**.  A metavariable of
arity `(bs, s)` becomes an operator taking one non-binding argument for each
sort in `bs` and returning `s`.

Because metavariables are operators, a rule schema is an ordinary term, and it
inherits renaming, substitution and every law proved for them.  No separate
syntax of schemas, and no second substitution, is needed. -/
abbrev withMetas (S : Signature) (M : List (MetaArity S)) : Signature where
  Srt := S.Srt
  Op := fun s => S.Op s ⊕ MetaOp M s
  arity := fun {_} o => match o with
    | .inl f => S.arity f
    | .inr (.mk i) => (M.get i).1.map (fun b => ([], b))

/-- Sorts are unchanged by adjoining metavariables. -/
theorem withMetas_Srt (M : List (MetaArity S)) : (withMetas S M).Srt = S.Srt := rfl

/-- Adjoining no metavariables changes no operator's arity. -/
theorem withMetas_nil_arity {s : S.Srt} (f : S.Op s) :
    (withMetas S []).arity (Sum.inl f) = S.arity f := rfl

/-! ## Positioned rewrites: the generator's input -/

/-- A base rewrite together with the redex position chosen inside it.

The source's base rewrites carry an empty premise slot, so there is no premise
field here: a rule is a variable context, two sides of one sort, and a
position.  Carrying the position in the rule -- rather than alongside it -- is
what makes the data the generator reads be the data the rule supplies. -/
structure PositionedRewrite (S : Signature) where
  /-- The rule's variable context. -/
  ctx : Ctx S
  /-- The sort of both sides. -/
  sort : S.Srt
  lhs : Term S ctx sort
  rhs : Term S ctx sort
  /-- The chosen redex occurrence. -/
  position : LinearRedexPosition S ctx sort lhs

namespace PositionedRewrite

variable (P : PositionedRewrite S)

/-- The carrier of the generated modality: the sort of the chosen hole. -/
abbrev carrier : S.Srt := P.position.carrier

/-- A **rely parameter**: a rule variable the one-hole context uses and the
redex does not.  Read off the factorization rather than by subtracting
free-variable sets after the fact. -/
def RelyParameter {s : S.Srt} (x : Var P.ctx s) : Prop :=
  0 < countVar (Var.succ x) P.position.ctxt ∧ countVar x P.position.redex = 0

/-- Dually: a rule variable the redex uses and the context does not. -/
def LocalParameter {s : S.Srt} (x : Var P.ctx s) : Prop :=
  countVar (Var.succ x) P.position.ctxt = 0 ∧ 0 < countVar x P.position.redex

/-- The two families are disjoint, by construction rather than by argument. -/
theorem rely_not_local {s : S.Srt} (x : Var P.ctx s) :
    P.RelyParameter x → ¬ P.LocalParameter x := by
  rintro ⟨h₁, -⟩ ⟨h₂, -⟩
  omega

/-- The hole is used exactly once, so a positioned rewrite always has a genuine
occurrence to be a position at. -/
theorem hole_occurs : holeCount P.position.ctxt = 1 := P.position.linear

end PositionedRewrite


mutual
/-- Whether a term mentions any adjoined metavariable.  A term for which this
is `false` is a term of the base signature wearing the extended signature's
type: it is a closed instance, not a schema. -/
def usesMeta {M : List (MetaArity S)} : {Γ : Ctx (withMetas S M)} → {s : S.Srt} →
    Term (withMetas S M) Γ s → Bool
  | _, _, .var _ => false
  | _, _, .op (Sum.inl _) args => usesMetaArgs args
  | _, _, .op (Sum.inr _) _ => true

def usesMetaArgs {M : List (MetaArity S)} :
    {as : List (List S.Srt × S.Srt)} → {Γ : Ctx (withMetas S M)} →
    Args (withMetas S M) as Γ → Bool
  | _, _, .nil => false
  | _, _, .cons head tail => usesMeta head || usesMetaArgs tail
end

mutual
/-- With no metavariables adjoined, nothing can mention one. -/
theorem usesMeta_nil : ∀ {Γ : Ctx (withMetas S [])} {s : S.Srt}
    (t : Term (withMetas S []) Γ s), usesMeta t = false
  | _, _, .var _ => rfl
  | _, _, .op (Sum.inl _) args => by
      simp only [usesMeta, usesMetaArgs_nil args]
  | _, _, .op (Sum.inr (.mk i)) _ => i.elim0

theorem usesMetaArgs_nil : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx (withMetas S [])}
    (args : Args (withMetas S []) as Γ), usesMetaArgs args = false
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [usesMetaArgs, usesMeta_nil head, usesMetaArgs_nil tail, Bool.or_self]
end


/-! ## Embedding the base signature into an extended one -/

mutual
/-- Every term of the base signature is a term of the extended one. -/
def embed {M : List (MetaArity S)} : {Γ : Ctx S} → {s : S.Srt} →
    Term S Γ s → Term (withMetas S M) Γ s
  | _, _, .var v => .var v
  | _, _, .op f args =>
      Term.op (S := withMetas S M) (Sum.inl f) (embedArgs (M := M) (as := S.arity f) args)

def embedArgs {M : List (MetaArity S)} :
    {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args S as Γ → Args (withMetas S M) as Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (embed (M := M) head) (embedArgs (M := M) tail)
end

/-! ## Instantiating the metavariables -/

/-- The arguments of a metavariable, read as a substitution for the context its
body is open in. -/
def argsToSub : {bs : List S.Srt} → {Γ : Ctx S} →
    Args S (bs.map (fun b => ([], b))) Γ → Sub S bs Γ
  | [], _, .nil => fun _ v => nomatch v
  | _ :: _, _, .cons head tail => fun _ v => match v with
      | .zero => head
      | .succ w => argsToSub tail _ w

mutual
/-- Instantiate every metavariable by the body supplied for it, applying that
body to the arguments the schema gave it.  This is the signature morphism that
turns a rule schema into a rule. -/
def instantiate {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    {Γ : Ctx S} → {s : S.Srt} → Term (withMetas S M) Γ s → Term S Γ s
  | _, _, .var v => .var v
  | _, _, .op (Sum.inl f) args => .op f (instantiateArgs body args)
  | _, _, .op (Sum.inr (.mk i)) args =>
      bind (argsToSub (instantiateArgs body args)) (body i)

def instantiateArgs {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args (withMetas S M) as Γ → Args S as Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (instantiate body head) (instantiateArgs body tail)
end

mutual
/-- Instantiation undoes embedding: a term that mentions no metavariable is
returned unchanged, whatever bodies are supplied. -/
theorem instantiate_embed {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    ∀ {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s),
      instantiate body (embed (M := M) t) = t
  | _, _, .var _ => rfl
  | _, _, .op f args => by
      simp only [embed, instantiate, instantiateArgs_embedArgs body args]

theorem instantiateArgs_embedArgs {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args S as Γ),
      instantiateArgs body (embedArgs (M := M) args) = args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [embedArgs, instantiateArgs, instantiate_embed body head,
        instantiateArgs_embedArgs body tail]
end


/-! ## What a positioned rewrite denotes -/

/-- A closed instance of a rule: a body for each metavariable, and a closed
term for each of the rule's own variables.  The two are genuinely different
roles -- the metavariables are what the rule is parametric in, the context
variables are the ones a redex position can be taken at, since a hole must be
pluggable. -/
structure RuleInstance (M : List (MetaArity S))
    (P : PositionedRewrite (withMetas S M)) where
  /-- The continuation supplied for each metavariable. -/
  body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2
  /-- Closed terms for the rule's own variables. -/
  close : Sub S P.ctx []

/-- The root-level step relation a positioned rewrite denotes: `t` rewrites to
`u` when some instance of the rule has `t` on the left and `u` on the right.

This is also the specification a matcher must meet: a matcher is correct
exactly when the assignment it returns makes this hold. -/
def RootStep {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M))
    (t u : Term S [] P.sort) : Prop :=
  ∃ I : RuleInstance M P,
    bind I.close (instantiate I.body P.lhs) = t ∧
    bind I.close (instantiate I.body P.rhs) = u

/-- Exhibiting an instance is exactly exhibiting a step. -/
theorem rootStep_of_instance {M : List (MetaArity S)}
    (P : PositionedRewrite (withMetas S M)) (I : RuleInstance M P) :
    RootStep P (bind I.close (instantiate I.body P.lhs))
      (bind I.close (instantiate I.body P.rhs)) :=
  ⟨I, rfl, rfl⟩

/-- Every step comes from an instance, and its source *is* that instance's
left-hand side.  For a concrete rule the right-hand side of this equation
computes to a term with a known head, which is what a negative control needs. -/
theorem rootStep_lhs_shape {M : List (MetaArity S)}
    (P : PositionedRewrite (withMetas S M)) {t u : Term S [] P.sort}
    (h : RootStep P t u) :
    ∃ I : RuleInstance M P, t = bind I.close (instantiate I.body P.lhs) := by
  obtain ⟨I, hl, -⟩ := h
  exact ⟨I, hl.symm⟩

/-- Dually for the target. -/
theorem rootStep_rhs_shape {M : List (MetaArity S)}
    (P : PositionedRewrite (withMetas S M)) {t u : Term S [] P.sort}
    (h : RootStep P t u) :
    ∃ I : RuleInstance M P, u = bind I.close (instantiate I.body P.rhs) := by
  obtain ⟨I, -, hr⟩ := h
  exact ⟨I, hr.symm⟩


/-! ## Firing below the root -/

/-- The contextual closure of a positioned rewrite: `t` steps to `u` when some
one-hole context has a root step in its hole.

The context is required to *use* its hole.  Without that requirement the
closure would be reflexive on every term -- see `unconditioned_closure_is_reflexive`
below -- so the occurrence condition is load-bearing here for the second time,
having already been what distinguishes a redex position from a decomposition
that selects nothing. -/
def Step {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M))
    {s : S.Srt} (t u : Term S [] s) : Prop :=
  ∃ (K : Term S [P.sort] s) (a b : Term S [] P.sort),
    holeCount K = 1 ∧ RootStep P a b ∧ inst K a = t ∧ inst K b = u

/-- Plugging into the bare hole returns the plugged term. -/
theorem inst_hole {Γ : Ctx S} {c : S.Srt} (t : Term S Γ c) :
    inst (Term.var (Var.zero : Var (c :: Γ) c)) t = t := rfl

/-- The bare hole uses its hole once. -/
theorem holeCount_hole {Γ : Ctx S} {c : S.Srt} :
    holeCount (Term.var (Var.zero : Var (c :: Γ) c)) = 1 := rfl

/-- A root step is a step. -/
theorem step_of_rootStep {M : List (MetaArity S)}
    (P : PositionedRewrite (withMetas S M)) {t u : Term S [] P.sort}
    (h : RootStep P t u) : Step P t u :=
  ⟨Term.var Var.zero, t, u, holeCount_hole, h, inst_hole t, inst_hole u⟩

/-- **Why the occurrence condition is needed here too.**  Drop it, and a
context that ignores its hole relates every term to itself, provided the rule
fires anywhere at all.  A step relation with that property says nothing. -/
theorem unconditioned_closure_is_reflexive {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)}
    (hP : ∃ a b, RootStep P a b) {s : S.Srt} (t : Term S [] s) :
    ∃ (K : Term S [P.sort] s) (a b : Term S [] P.sort),
      RootStep P a b ∧ inst K a = t ∧ inst K b = t := by
  obtain ⟨a, b, hab⟩ := hP
  exact ⟨weaken t, a, b, hab, inst_weaken t a, inst_weaken t b⟩


/-! ## The possibility generated at a chosen position

For each base rewrite and each chosen redex position the source's algorithm
introduces a primitive modality at the position's carrier, read as a
*rely-possibly* specification: under assumptions on the rely parameters,
placing a term into the one-hole context takes one step to a right-hand side
inhabiting the target predicate.

What is built here is the possibility half of that: the rule's own instances
supply the step, and everything is generated from the rule and its position
rather than written per calculus.  The rely parameters are not yet *indexed*,
so this is weaker than the source's modality, and the name says so.  Indexing
them requires the rely and local parameters to partition the rule's variables,
which they do not do in general -- see `Separated` below. -/

/-- `StepsFromPosition P B t` holds when placing `t` at the rule's chosen position takes a
step whose right-hand side satisfies `B`. -/
def StepsFromPosition {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M))
    (B : Term S [] P.sort → Prop) (t : Term S [] P.position.carrier) : Prop :=
  ∃ I : RuleInstance M P,
    bind I.close (instantiate I.body P.position.redex) = t ∧
    B (bind I.close (instantiate I.body P.rhs))

/-- **M-INTRO.**  An instance whose redex is `t` and whose right-hand side
satisfies `B` inhabits the modality at `t`. -/
theorem stepsFromPosition_intro {M : List (MetaArity S)} {P : PositionedRewrite (withMetas S M)}
    {B : Term S [] P.sort → Prop} (I : RuleInstance M P)
    (hB : B (bind I.close (instantiate I.body P.rhs))) :
    StepsFromPosition P B (bind I.close (instantiate I.body P.position.redex)) :=
  ⟨I, rfl, hB⟩

/-- **M-STEP.**  Inhabiting the modality produces an actual step of the
generated relation, whose target satisfies `B`.  The modality delivers an
operational step, not a conversion. -/
theorem stepsFromPosition_step {M : List (MetaArity S)} {P : PositionedRewrite (withMetas S M)}
    {B : Term S [] P.sort → Prop} {t : Term S [] P.position.carrier}
    (h : StepsFromPosition P B t) :
    ∃ a b : Term S [] P.sort, RootStep P a b ∧ B b := by
  obtain ⟨I, -, hB⟩ := h
  exact ⟨_, _, rootStep_of_instance P I, hB⟩

/-- **M-ELIM.**  The step the modality delivers is the rule firing below
whatever context one places it in, so it is a step of the contextual closure
too. -/
theorem stepsFromPosition_elim {M : List (MetaArity S)} {P : PositionedRewrite (withMetas S M)}
    {B : Term S [] P.sort → Prop} {t : Term S [] P.position.carrier}
    (h : StepsFromPosition P B t) :
    ∃ a b : Term S [] P.sort, Step P a b ∧ B b := by
  obtain ⟨a, b, hstep, hB⟩ := stepsFromPosition_step h
  exact ⟨a, b, step_of_rootStep P hstep, hB⟩

/-- The modality is monotone in its target predicate, which is what makes the
propositional layer above it well behaved. -/
theorem stepsFromPosition_mono {M : List (MetaArity S)} {P : PositionedRewrite (withMetas S M)}
    {B C : Term S [] P.sort → Prop} (hBC : ∀ x, B x → C x)
    {t : Term S [] P.position.carrier} (h : StepsFromPosition P B t) : StepsFromPosition P C t := by
  obtain ⟨I, ht, hB⟩ := h
  exact ⟨I, ht, hBC _ hB⟩

/-- The freely added empty-context possibility: a step with no rely
assumptions at all. -/
def Poss {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M))
    (B : Term S [] P.sort → Prop) (t : Term S [] P.sort) : Prop :=
  ∃ u : Term S [] P.sort, RootStep P t u ∧ B u

/-- Possibility is monotone too. -/
theorem poss_mono {M : List (MetaArity S)} {P : PositionedRewrite (withMetas S M)}
    {B C : Term S [] P.sort → Prop} (hBC : ∀ x, B x → C x)
    {t : Term S [] P.sort} (h : Poss P B t) : Poss P C t := by
  obtain ⟨u, hst, hB⟩ := h
  exact ⟨u, hst, hBC _ hB⟩

/-! ## When the rely and local parameters partition the rule's variables

The source defines the rely parameters as the context's variables minus the
redex's, and their duals as the redex's minus the context's.  A variable
occurring in *both* is therefore in neither, so the two families need not cover
the rule's variables.  Indexing a modality by typed rely assumptions needs them
to, so the condition is named rather than assumed. -/

/-- Every variable of the rule is either a rely parameter or a local one. -/
def Separated {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M)) : Prop :=
  ∀ (s : S.Srt) (x : Var P.ctx s), P.RelyParameter x ∨ P.LocalParameter x

/-- Under separation the two families are complementary, not merely disjoint. -/
theorem local_of_not_rely {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} (hsep : Separated P)
    {s : S.Srt} (x : Var P.ctx s) (h : ¬ P.RelyParameter x) : P.LocalParameter x :=
  (hsep s x).resolve_left h

/-- And a variable used by both the context and the redex witnesses failure of
separation, so the condition has content. -/
theorem not_separated_of_shared {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt} (x : Var P.ctx s)
    (hK : 0 < countVar (Var.succ x) P.position.ctxt)
    (ht : 0 < countVar x P.position.redex) : ¬ Separated P := by
  intro hsep
  rcases hsep s x with ⟨-, h⟩ | ⟨h, -⟩
  · omega
  · omega


/-! ## The rely-indexed modality

The source's modality at a chosen position is a *rely-possibly* specification:
under typed assumptions on the rely parameters, placing a term at the position
takes one step to a right-hand side inhabiting the target predicate.  The
quantifier structure is therefore mixed -- universal over the rely environment,
existential over everything the rule still gets to choose. -/

/-- A typing of the rule's variables: a predicate on closed terms for each. -/
abbrev RelyTyping {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M)) :
    Type :=
  (s : S.Srt) → Var P.ctx s → Term S [] s → Prop

/-- Two closing substitutions agree wherever the rule relies. -/
def AgreesOnRely {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M))
    (sigma tau : Sub S P.ctx []) : Prop :=
  ∀ (s : S.Srt) (x : Var P.ctx s), P.RelyParameter x → sigma s x = tau s x

/-- A **rely environment**: closed terms for the rule's rely parameters, and for
nothing else.  This is the index the modality carries -- the rule's reliance set,
read off the factorization -- and quantifying over anything larger changes what
the modality says.  Quantifying over closing substitutions of the whole variable
context, in particular, makes the modality hold for want of an environment
whenever a variable the rule does *not* rely on happens to have a sort with no
closed inhabitant; that is a statement about the sort, not about the rule. -/
abbrev RelyEnv {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M)) : Type :=
  (s : S.Srt) → (x : Var P.ctx s) → P.RelyParameter x → Term S [] s

/-- A closing substitution **realises** a rely environment when the two agree
wherever the rule relies.  What the substitution does elsewhere is the rule's own
business, which is exactly the asymmetry the reliance set expresses. -/
def Realises {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M))
    (sigma : Sub S P.ctx []) (env : RelyEnv P) : Prop :=
  ∀ (s : S.Srt) (x : Var P.ctx s) (hx : P.RelyParameter x), sigma s x = env s x hx

/-- Every closing substitution restricts to a rely environment. -/
def relyEnvOf {M : List (MetaArity S)} {P : PositionedRewrite (withMetas S M)}
    (sigma : Sub S P.ctx []) : RelyEnv P := fun s x _ => sigma s x

/-- ... and realises the one it restricts to. -/
theorem realises_relyEnvOf {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} (sigma : Sub S P.ctx []) :
    Realises P sigma (relyEnvOf sigma) := fun _ _ _ => rfl

/-- Agreement between two closing substitutions is realisation of the restriction
of the second, so the coarser notion is recovered from the finer one. -/
theorem agreesOnRely_iff_realises {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} (sigma tau : Sub S P.ctx []) :
    AgreesOnRely P sigma tau ↔ Realises P sigma (relyEnvOf tau) :=
  ⟨fun h s x hx => h s x hx, fun h s x hx => h s x hx⟩

/-- **The modality at a chosen position.**  For every rely environment meeting
the rely assumptions, the rule has an instance realising it, placing `t` at the
chosen position, and stepping to a right-hand side in `B`.  The carrier of the
modality is the sort of the chosen hole, which is what the type of `t` records. -/
def RelyPossibly {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M))
    (A : RelyTyping P) (B : Term S [] P.sort → Prop)
    (t : Term S [] P.position.carrier) : Prop :=
  ∀ env : RelyEnv P,
    (∀ (s : S.Srt) (x : Var P.ctx s) (hx : P.RelyParameter x), A s x (env s x hx)) →
    ∃ I : RuleInstance M P,
      Realises P I.close env ∧
      bind I.close (instantiate I.body P.position.redex) = t ∧
      B (bind I.close (instantiate I.body P.rhs))

/-- **M-INTRO.**  An instance whose right-hand side satisfies the target
inhabits the modality, at the rely typing that instance's own closure pins.
The premises are the rule's data -- an instance and an inhabitant of the target
-- rather than the conclusion restated. -/
theorem relyPossibly_intro {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)}
    {B : Term S [] P.sort → Prop} (I : RuleInstance M P)
    (hB : B (bind I.close (instantiate I.body P.rhs))) :
    RelyPossibly P (fun s x u => u = I.close s x) B
      (bind I.close (instantiate I.body P.position.redex)) := by
  intro env henv
  exact ⟨I, fun s x hx => (henv s x hx).symm, rfl, hB⟩

/-- **M-STEP.**  Given one admissible environment, the modality delivers an
actual step of the generated relation whose target satisfies `B`.  It is an
operational step, not a conversion. -/
theorem relyPossibly_step {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {A : RelyTyping P}
    {B : Term S [] P.sort → Prop} {t : Term S [] P.position.carrier}
    (h : RelyPossibly P A B t) (env : RelyEnv P)
    (henv : ∀ (s : S.Srt) (x : Var P.ctx s) (hx : P.RelyParameter x),
      A s x (env s x hx)) :
    ∃ a b : Term S [] P.sort, RootStep P a b ∧ B b := by
  obtain ⟨I, -, -, hB⟩ := h env henv
  exact ⟨_, _, rootStep_of_instance P I, hB⟩

/-- **M-ELIM.**  That step is a step of the contextual closure too. -/
theorem relyPossibly_elim {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {A : RelyTyping P}
    {B : Term S [] P.sort → Prop} {t : Term S [] P.position.carrier}
    (h : RelyPossibly P A B t) (env : RelyEnv P)
    (henv : ∀ (s : S.Srt) (x : Var P.ctx s) (hx : P.RelyParameter x),
      A s x (env s x hx)) :
    ∃ a b : Term S [] P.sort, Step P a b ∧ B b := by
  obtain ⟨a, b, hstep, hB⟩ := relyPossibly_step h env henv
  exact ⟨a, b, step_of_rootStep P hstep, hB⟩

/-- Monotone in the target predicate. -/
theorem relyPossibly_mono_target {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {A : RelyTyping P}
    {B C : Term S [] P.sort → Prop} (hBC : ∀ x, B x → C x)
    {t : Term S [] P.position.carrier} (h : RelyPossibly P A B t) :
    RelyPossibly P A C t := by
  intro env henv
  obtain ⟨I, hag, ht, hB⟩ := h env henv
  exact ⟨I, hag, ht, hBC _ hB⟩

/-- Antitone in the rely assumptions: strengthening what one relies on can only
make the specification easier to meet. -/
theorem relyPossibly_mono_rely {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {A A' : RelyTyping P}
    (hAA : ∀ s x u, A' s x u → A s x u)
    {B : Term S [] P.sort → Prop} {t : Term S [] P.position.carrier}
    (h : RelyPossibly P A B t) : RelyPossibly P A' B t := by
  intro env henv
  exact h env (fun s x hx => hAA s x (env s x hx) (henv s x hx))

/-- With any admissible environment in hand, the rely-indexed modality refines
the unindexed possibility. -/
theorem stepsFromPosition_of_relyPossibly {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {A : RelyTyping P}
    {B : Term S [] P.sort → Prop} {t : Term S [] P.position.carrier}
    (h : RelyPossibly P A B t) (env : RelyEnv P)
    (henv : ∀ (s : S.Srt) (x : Var P.ctx s) (hx : P.RelyParameter x),
      A s x (env s x hx)) :
    StepsFromPosition P B t := by
  obtain ⟨I, -, ht, hB⟩ := h env henv
  exact ⟨I, ht, hB⟩


/-! ## The structural layer

For each term former the algorithm freely adds a type former.  Nothing here is
written per calculus: the family is indexed by the signature's operators, and
each former's argument slots are indexed by that operator's binding arity, so
an argument that opens binders carries a predicate at the opened context. -/

/-- A predicate on terms at a given context and sort. -/
abbrev Pred (S : Signature) (Γ : Ctx S) (s : S.Srt) : Type := Term S Γ s → Prop

/-- One predicate per argument of an operator, each at the context that
argument opens.  A binding argument therefore carries a predicate about terms
in scope of what it binds, not about closed terms. -/
inductive PredArgs (S : Signature) : List (List S.Srt × S.Srt) → Ctx S → Type where
  | nil {Γ : Ctx S} : PredArgs S [] Γ
  | cons {bs : List S.Srt} {s : S.Srt} {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} :
      Pred S (bs ++ Γ) s → PredArgs S as Γ → PredArgs S ((bs, s) :: as) Γ

/-- Each argument satisfies the predicate at its slot. -/
def SatArgs : {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    PredArgs S as Γ → Args S as Γ → Prop
  | _, _, .nil, .nil => True
  | _, _, .cons A As, .cons a as => A a ∧ SatArgs As as

/-- **The structural type former generated at `o`.**  A term inhabits it when
its head is `o` and its arguments inhabit the predicates at their slots. -/
def structural {Γ : Ctx S} {s : S.Srt} (o : S.Op s) (As : PredArgs S (S.arity o) Γ) :
    Pred S Γ s :=
  fun t => ∃ args : Args S (S.arity o) Γ, t = Term.op o args ∧ SatArgs As args

/-- Introduction: build at the head, and the structural type holds. -/
theorem structural_intro {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    {As : PredArgs S (S.arity o) Γ} {args : Args S (S.arity o) Γ}
    (h : SatArgs As args) : structural o As (Term.op o args) :=
  ⟨args, rfl, h⟩

/-- Elimination: inhabiting a structural type exposes the head and the
arguments. -/
theorem structural_elim {Γ : Ctx S} {s : S.Srt} {o : S.Op s}
    {As : PredArgs S (S.arity o) Γ} {t : Term S Γ s} (h : structural o As t) :
    ∃ args : Args S (S.arity o) Γ, t = Term.op o args ∧ SatArgs As args := h

/-- A variable inhabits no structural type: the layer classifies constructed
terms only. -/
theorem structural_not_var {Γ : Ctx S} {s : S.Srt} {o : S.Op s}
    {As : PredArgs S (S.arity o) Γ} (v : Var Γ s) :
    ¬ structural o As (Term.var v) := by
  rintro ⟨args, ht, -⟩
  simp at ht

/-- **The structural types separate the term formers.**  A term cannot inhabit
the types of two different heads, so the layer is a genuine classification and
not an overlapping family. -/
theorem structural_head_unique {Γ : Ctx S} {s : S.Srt} {o o' : S.Op s}
    {As : PredArgs S (S.arity o) Γ} {As' : PredArgs S (S.arity o') Γ}
    {t : Term S Γ s} (h : structural o As t) (h' : structural o' As' t) :
    o = o' := by
  obtain ⟨args, ht, -⟩ := h
  obtain ⟨args', ht', -⟩ := h'
  rw [ht] at ht'
  simp only [Term.op.injEq] at ht'
  exact ht'.1

/-! ## The propositional layer, stratified by categorical strength

Finite limits supply a terminal object and pullbacks, hence a top predicate and
conjunction -- and nothing else.  Disjunction, falsity and implication need
strictly more than finite limits, so they are not added here; adding them would
be claiming structure the base does not supply. -/

/-- The top predicate, available at finite-limit strength. -/
def PredTop (S : Signature) (Γ : Ctx S) (s : S.Srt) : Pred S Γ s := fun _ => True

/-- Conjunction, available at finite-limit strength. -/
def PredAnd {Γ : Ctx S} {s : S.Srt} (A B : Pred S Γ s) : Pred S Γ s :=
  fun t => A t ∧ B t

theorem predTop_intro {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s) :
    PredTop S Γ s t := trivial

theorem predAnd_intro {Γ : Ctx S} {s : S.Srt} {A B : Pred S Γ s} {t : Term S Γ s}
    (ha : A t) (hb : B t) : PredAnd A B t := ⟨ha, hb⟩

theorem predAnd_left {Γ : Ctx S} {s : S.Srt} {A B : Pred S Γ s} {t : Term S Γ s}
    (h : PredAnd A B t) : A t := h.1

theorem predAnd_right {Γ : Ctx S} {s : S.Srt} {A B : Pred S Γ s} {t : Term S Γ s}
    (h : PredAnd A B t) : B t := h.2


/-! ## Equations

The third component of a language definition.  An axiom is two sides of one
sort in one variable context; the theory it generates is the least equivalence
closed under instantiation and under the term formers.

The same construction exists on the older pattern carrier in the language
definition layer -- authored equations, context closure, then the equivalence
closure, with a step relation modulo it.  This is that construction on the
binding-signature carrier, where closure under the term formers can be stated
once, argument by argument, because the arity says what each argument opens. -/

/-- An equation axiom: two sides of one sort in one variable context. -/
structure EqAxiom (S : Signature) (M : List (MetaArity S)) where
  ctx : Ctx S
  sort : S.Srt
  lhs : Term (withMetas S M) ctx sort
  rhs : Term (withMetas S M) ctx sort

mutual
/-- The equational theory generated by a set of axioms. -/
inductive EqClosure {M : List (MetaArity S)} (E : List (EqAxiom S M)) :
    {Γ : Ctx S} → {s : S.Srt} → Term S Γ s → Term S Γ s → Prop where
  | ax (i : Fin E.length) {Γ : Ctx S}
      (body : (k : Fin M.length) → Term S (M.get k).1 (M.get k).2)
      (close : Sub S (E.get i).ctx Γ) :
      EqClosure E (bind close (instantiate body (E.get i).lhs))
                  (bind close (instantiate body (E.get i).rhs))
  | refl {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s) : EqClosure E t t
  | symm {Γ : Ctx S} {s : S.Srt} {t u : Term S Γ s} :
      EqClosure E t u → EqClosure E u t
  | trans {Γ : Ctx S} {s : S.Srt} {t u v : Term S Γ s} :
      EqClosure E t u → EqClosure E u v → EqClosure E t v
  | cong {Γ : Ctx S} {s : S.Srt} (o : S.Op s) {as as' : Args S (S.arity o) Γ} :
      EqArgs E as as' → EqClosure E (Term.op o as) (Term.op o as')

/-- Closure under the term formers, argument by argument.  A binding argument
is related at the context it opens, so the closure passes under binders. -/
inductive EqArgs {M : List (MetaArity S)} (E : List (EqAxiom S M)) :
    {ars : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args S ars Γ → Args S ars Γ → Prop where
  | nil {Γ : Ctx S} : EqArgs E (Args.nil (S := S) (Γ := Γ)) Args.nil
  | cons {bs : List S.Srt} {s : S.Srt} {ars : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {h h' : Term S (bs ++ Γ) s} {t t' : Args S ars Γ} :
      EqClosure E h h' → EqArgs E t t' → EqArgs E (.cons h t) (.cons h' t')
end

/-- The bare axiom instances of a presentation, before any closure: the rung-0
relation of the observation ladder for this theory. -/
def AxInstance {M : List (MetaArity S)} (E : List (EqAxiom S M)) {Γ : Ctx S}
    {s : S.Srt} (t u : Term S Γ s) : Prop :=
  ∃ (i : Fin E.length) (h : (E.get i).sort = s)
    (body : (k : Fin M.length) → Term S (M.get k).1 (M.get k).2)
    (close : Sub S (E.get i).ctx Γ),
      t = h ▸ bind close (instantiate body (E.get i).lhs)
        ∧ u = h ▸ bind close (instantiate body (E.get i).rhs)

/-- **The equivalence closure of the bare axiom instances lands inside the
presentation's congruence closure.**  A presentation's equality is a *congruence*
closure -- it adjoins `cong` -- so it is a rung above the equivalence closure of
its own axiom instances, and only this inclusion holds without a contextual
step.  Stability checked against `EqClosure` therefore descends to the ladder;
the converse does not follow from the ladder alone. -/
theorem eqvGen_axInstance_le_eqClosure {M : List (MetaArity S)}
    (E : List (EqAxiom S M)) {Γ : Ctx S} {s : S.Srt} {t u : Term S Γ s}
    (h : Relation.EqvGen (AxInstance E (Γ := Γ) (s := s)) t u) :
    EqClosure E t u := by
  induction h with
  | rel a b hab =>
      obtain ⟨i, hs, body, close, rfl, rfl⟩ := hab
      cases hs
      exact EqClosure.ax i body close
  | refl a => exact EqClosure.refl a
  | symm a b _ ih => exact EqClosure.symm ih
  | trans a b c _ _ ih₁ ih₂ => exact EqClosure.trans ih₁ ih₂

/-- Arguments are related to themselves. -/
theorem eqArgs_refl {M : List (MetaArity S)} {E : List (EqAxiom S M)} :
    ∀ {ars : List (List S.Srt × S.Srt)} {Γ : Ctx S} (as : Args S ars Γ), EqArgs E as as
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (.refl h) (eqArgs_refl t)

/-! ## Stepping modulo the equations -/

/-- A step of the generated relation, up to the equational theory on both
sides.  This is the relation the operational semantics of a presentation with
equations actually denotes. -/
def StepModE {M : List (MetaArity S)} (E : List (EqAxiom S M))
    (P : PositionedRewrite (withMetas S M)) {s : S.Srt} (t u : Term S [] s) : Prop :=
  ∃ t' u' : Term S [] s, EqClosure E t t' ∧ Step P t' u' ∧ EqClosure E u' u

/-- A step is a step modulo the equations. -/
theorem stepModE_of_step {M : List (MetaArity S)} {E : List (EqAxiom S M)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt} {t u : Term S [] s}
    (h : Step P t u) : StepModE E P t u :=
  ⟨t, u, .refl t, h, .refl u⟩

/-- The relation respects the equational theory on the left. -/
theorem stepModE_resp_left {M : List (MetaArity S)} {E : List (EqAxiom S M)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt} {t t' u : Term S [] s}
    (he : EqClosure E t t') (h : StepModE E P t' u) : StepModE E P t u := by
  obtain ⟨a, b, h1, h2, h3⟩ := h
  exact ⟨a, b, .trans he h1, h2, h3⟩

/-- And on the right. -/
theorem stepModE_resp_right {M : List (MetaArity S)} {E : List (EqAxiom S M)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt} {t u u' : Term S [] s}
    (h : StepModE E P t u) (he : EqClosure E u u') : StepModE E P t u' := by
  obtain ⟨a, b, h1, h2, h3⟩ := h
  exact ⟨a, b, h1, h2, .trans h3 he⟩


/-! ## Sort slots, the equational center, and the hypercube

Each generated type former carries finitely many sort slots: one for each rely
input, and one for the output.  Filling each slot two ways yields a raw Boolean
cube.  Equational axioms and rewrite laws force certain slots to agree, and only
the assignments stable under those identifications survive; those form the
equational center, and the hypercube's vertices are its elements.

The slots are not postulated.  They are read off the rule -- its rely
parameters and its output -- which is what the definition below records. -/

/-- The sort slots of the modality generated at a rule's chosen position: one
for each rely parameter of the rule, and one for the output. -/
inductive Slot {M : List (MetaArity S)} (P : PositionedRewrite (withMetas S M)) : Type where
  | rely (s : S.Srt) (x : Var P.ctx s) (h : P.RelyParameter x) : Slot P
  | out : Slot P

/-- A filling raises each slot or leaves it at the origin. -/
abbrev Filling (Slot : Type) : Type := Slot → Bool

/-- The identifications that equations and rewrite laws force between slots. -/
abbrev SlotLaws (Slot : Type) : Type := Slot → Slot → Prop

/-- **The equational center.**  The fillings stable under the identifications;
the hypercube's vertices are exactly these. -/
def Center {Slot : Type} (L : SlotLaws Slot) : Set (Filling Slot) :=
  {f | ∀ a b, L a b → f a = f b}

/-- The origin assignment leaves every slot unraised. -/
def origin (Slot : Type) : Filling Slot := fun _ => false

/-- The origin is a vertex of every hypercube: it satisfies every
identification, whatever the laws are. -/
theorem origin_mem_center {Slot : Type} (L : SlotLaws Slot) :
    origin Slot ∈ Center L := fun _ _ _ => rfl

/-- **With no identifications the center is the whole raw cube.**  This is the
situation of the Lambda Cube: no built-in equations, so nothing relates the
sorts, and the distinction between the raw cube and the center never arises. -/
theorem center_of_no_laws (Slot : Type) :
    Center (fun _ _ : Slot => False) = Set.univ := by
  ext f
  simp [Center]

/-- **And an identification genuinely cuts the cube down.**  As soon as two
distinct slots are forced to agree, some filling of the raw cube is excluded,
so the center is a proper part and the distinction has content. -/
theorem center_ne_univ_of_identification {Slot : Type} [DecidableEq Slot]
    {a b : Slot} (hab : a ≠ b) :
    Center (fun x y => x = a ∧ y = b) ≠ Set.univ := by
  intro h
  have hmem : (fun x => decide (x = a)) ∈ Center (fun x y : Slot => x = a ∧ y = b) := by
    rw [h]; trivial
  have := hmem a b ⟨rfl, rfl⟩
  simp [hab.symm] at this

/-! ### Counting the cube

With `n` slots there are `2 ^ n` fillings, and every nonempty set of slots
lifted from the origin is a local axis, so there are `2 ^ n - 1` of them. -/

/-- The raw cube on `n` slots. -/
abbrev Cube (n : Nat) : Type := Fin n → Bool

/-- The raw cube has `2 ^ n` fillings. -/
theorem card_cube (n : Nat) : Fintype.card (Cube n) = 2 ^ n := by
  rw [Fintype.card_pi_const, Fintype.card_bool]

/-- Every nonempty set of slots lifted from the origin is a local axis, so
there are `2 ^ n - 1` of them. -/
theorem card_axes (n : Nat) :
    (Finset.univ.filter (fun f : Cube n => f ≠ origin (Fin n))).card = 2 ^ n - 1 := by
  classical
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    card_cube]

/-! ### The worked example's geometry

A modality with two rely parameters carries three slots: one per rely input and
one for the output.  Relative to the origin every nonempty set of slots can be
raised, and holding one slot at the origin leaves the remaining two-slot
subgeometry -- a square. -/

/-- Three slots: eight vertices. -/
theorem card_cube_three : Fintype.card (Cube 3) = 8 := by
  rw [card_cube]
  decide

/-- Three slots: seven local axes. -/
theorem card_axes_three :
    (Finset.univ.filter (fun f : Cube 3 => f ≠ origin (Fin 3))).card = 7 := by
  rw [card_axes]
  decide

/-- Holding the first slot at the origin leaves four vertices. -/
theorem card_square :
    (Finset.univ.filter (fun f : Cube 3 => f 0 = false)).card = 4 := by decide

/-- And those four are exactly a two-slot cube: the subgeometry on the
remaining slots. -/
theorem square_is_two_slot_cube :
    (Finset.univ.filter (fun f : Cube 3 => f 0 = false)).card = Fintype.card (Cube 2) := by
  rw [card_cube, card_square]
  decide


/-! ## Positions whose hole carries a binding arity

A redex position whose hole is a variable can only select a term.  The source's
worked example selects an *abstraction*, and gives that position a carrier
which is an exponential -- which is why the classifying theory there must be
cartesian closed.

A hole that binds is a metavariable.  Plugging is then metavariable
instantiation, which already exists, so an abstraction position needs no new
machinery and the object language needs no function sorts.

One consequence is structural rather than convenient.  The redex of such a
position is open only in what the hole binds; it cannot mention the ambient
variables at all, because its type does not let it.  So the source's
subtraction -- the context's variables minus the redex's -- has nothing to
subtract, and the failure mode recorded for the variable case, where a variable
occurring in both belongs to neither family, cannot arise here. -/

/-- The body of the single adjoined hole. -/
def soleBody {a : MetaArity S} (redex : Term S a.1 a.2) :
    (i : Fin [a].length) → Term S ([a].get i).1 ([a].get i).2
  | ⟨0, _⟩ => redex

/-- A position whose hole carries the binding arity `a`.  The context is a term
over the signature with the hole adjoined as its one metavariable; the redex is
open in exactly what the hole binds; plugging is instantiation. -/
structure AbstractionPosition (S : Signature) (a : MetaArity S)
    (Γ : Ctx S) (s : S.Srt) (L : Term S Γ s) where
  /-- The one-hole context, with the hole as the adjoined metavariable. -/
  ctxt : Term (withMetas S [a]) Γ s
  /-- The selected abstraction, open in the sorts the hole binds. -/
  redex : Term S a.1 a.2
  /-- Instantiating the hole by the redex recovers the left-hand side. -/
  plugs : instantiate (soleBody redex) ctxt = L

namespace AbstractionPosition

variable {a : MetaArity S} {Γ : Ctx S} {s : S.Srt} {L : Term S Γ s}

/-- The carrier of the modality generated here is the hole's binding arity --
what the worked example writes as an exponential. -/
abbrev carrier (_ : AbstractionPosition S a Γ s L) : MetaArity S := a

/-- An ambient variable the context uses.  No subtraction is performed,
because the redex cannot mention ambient variables. -/
def RelyParameter (P : AbstractionPosition S a Γ s L) {c : S.Srt} (x : Var Γ c) :
    Prop :=
  0 < countVar (S := withMetas S [a]) x P.ctxt

/-- The sort slots of the modality generated at an abstraction position: one
for each ambient variable the context uses, and one for the output. -/
inductive Slot (P : AbstractionPosition S a Γ s L) : Type where
  | rely (c : S.Srt) (x : Var Γ c) (h : P.RelyParameter x) : Slot P
  | out : Slot P

end AbstractionPosition


/-! ## Adjoining and forgetting

Adjoining metavariables to a signature is a free construction, and reading a
term of the extension back down by supplying bodies is the operation that
undoes it.  The two facts below say how the original theory sits inside its
free extension: it is there, and it is exactly the metavariable-free part. -/

mutual
/-- The inclusion lands in the metavariable-free part. -/
theorem usesMeta_embed {M : List (MetaArity S)} :
    ∀ {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s), usesMeta (embed (M := M) t) = false
  | _, _, .var _ => rfl
  | _, _, .op f args => by
      simp only [embed, usesMeta, usesMetaArgs_embedArgs (M := M) args]

theorem usesMetaArgs_embedArgs {M : List (MetaArity S)} :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args S as Γ),
      usesMetaArgs (embedArgs (M := M) args) = false
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [embedArgs, usesMetaArgs, usesMeta_embed (M := M) head,
        usesMetaArgs_embedArgs (M := M) tail, Bool.or_self]
end

mutual
/-- **And the metavariable-free part is exactly the inclusion's image.**  So
the underlying theory of the free extension contains the original, and contains
nothing else that mentions no adjoined operator. -/
theorem exists_embed_of_not_usesMeta {M : List (MetaArity S)} :
    ∀ {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S M) Γ s),
      usesMeta t = false → ∃ t' : Term S Γ s, embed (M := M) t' = t
  | _, _, .var v, _ => ⟨.var v, rfl⟩
  | _, _, .op (Sum.inl f) args, h => by
      obtain ⟨args', hargs⟩ := exists_embedArgs_of_not_usesMetaArgs args (by
        simpa only [usesMeta] using h)
      exact ⟨.op f args', by
        simp only [embed, hargs]⟩
  | _, _, .op (Sum.inr _) _, h => by
      simp [usesMeta] at h

theorem exists_embedArgs_of_not_usesMetaArgs {M : List (MetaArity S)} :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args (withMetas S M) as Γ),
      usesMetaArgs args = false → ∃ args' : Args S as Γ, embedArgs (M := M) args' = args
  | _, _, .nil, _ => ⟨.nil, rfl⟩
  | _, _, .cons head tail, h => by
      simp only [usesMetaArgs, Bool.or_eq_false_iff] at h
      obtain ⟨head', hhead⟩ := exists_embed_of_not_usesMeta head h.1
      obtain ⟨tail', htail⟩ := exists_embedArgs_of_not_usesMetaArgs tail h.2
      exact ⟨.cons head' tail', by simp only [embedArgs, hhead, htail]⟩
end

/-- The inclusion is injective: supplying any bodies recovers the term, so no
two terms of the original theory become equal in the free extension. -/
theorem embed_injective {M : List (MetaArity S)} {Γ : Ctx S} {s : S.Srt}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {t u : Term S Γ s} (h : embed (M := M) t = embed (M := M) u) : t = u := by
  have ht := instantiate_embed body t
  have hu := instantiate_embed body u
  rw [← ht, ← hu, h]


/-! ## The three dials

The generated logic is fixed by a language specification together with a choice
of connectives, so a user can select fragments to trade expressivity for
checkability.  There are three axes -- the language fragment, the connective
fragment, and the cube vertex -- and they are independent. -/

/-- **Dial one: the language fragment.**  Which operators properties may be
stated over. -/
def LanguageFragment (S : Signature) : Type := (s : S.Srt) → S.Op s → Prop

mutual
/-- A term lies in a fragment when every head it uses does.  Variables are
always available; restricting the signature restricts the constructions. -/
inductive InFragment (F : LanguageFragment S) :
    {Γ : Ctx S} → {s : S.Srt} → Term S Γ s → Prop where
  | var {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) : InFragment F (Term.var v)
  | op {Γ : Ctx S} {s : S.Srt} (o : S.Op s) (h : F s o)
      {args : Args S (S.arity o) Γ} :
      InFragmentArgs F args → InFragment F (Term.op o args)

inductive InFragmentArgs (F : LanguageFragment S) :
    {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} → Args S as Γ → Prop where
  | nil {Γ : Ctx S} : InFragmentArgs F (Args.nil (S := S) (Γ := Γ))
  | cons {bs : List S.Srt} {s : S.Srt} {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {h : Term S (bs ++ Γ) s} {t : Args S as Γ} :
      InFragment F h → InFragmentArgs F t → InFragmentArgs F (.cons h t)
end

/-- The whole signature. -/
def fullFragment (S : Signature) : LanguageFragment S := fun _ _ => True

/-- No operators at all. -/
def emptyFragment (S : Signature) : LanguageFragment S := fun _ _ => False

mutual
/-- Widening the fragment admits more terms. -/
theorem inFragment_mono {F G : LanguageFragment S} (hFG : ∀ s (o : S.Op s), F s o → G s o) :
    ∀ {Γ : Ctx S} {s : S.Srt} {t : Term S Γ s}, InFragment F t → InFragment G t
  | _, _, _, .var v => .var v
  | _, _, _, .op o h hargs => .op o (hFG _ o h) (inFragmentArgs_mono hFG hargs)

theorem inFragmentArgs_mono {F G : LanguageFragment S}
    (hFG : ∀ s (o : S.Op s), F s o → G s o) :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} {args : Args S as Γ},
      InFragmentArgs F args → InFragmentArgs G args
  | _, _, _, .nil => .nil
  | _, _, _, .cons hh ht => .cons (inFragment_mono hFG hh) (inFragmentArgs_mono hFG ht)
end

/-- **The empty fragment admits no constructed term.**  Restricting the
language really does cost expressivity; the trade is not nominal. -/
theorem not_inFragment_empty {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : Args S (S.arity o) Γ) : ¬ InFragment (emptyFragment S) (Term.op o args) := by
  intro h
  cases h with
  | op _ hf _ => exact hf

/-- Whereas variables are in every fragment, including the empty one. -/
theorem inFragment_var {Γ : Ctx S} {s : S.Srt} (F : LanguageFragment S) (v : Var Γ s) :
    InFragment F (Term.var v) := .var v

/-! ### Dial two: the connective fragment

Which of the generated connectives are in play.  There is no flag for
implication or negation: the propositional layer is stratified by what the
classifying theory supplies, and finite limits supply conjunction and the top
predicate only. -/

/-- Which generated connectives a specification admits. -/
structure ConnectiveFragment where
  top : Bool
  conj : Bool
  structural : Bool
  modal : Bool
  possibility : Bool
  deriving DecidableEq, Repr

/-- Everything the stratification permits. -/
def fullConnectives : ConnectiveFragment :=
  ⟨true, true, true, true, true⟩

/-- The conjunctive-modal fragment: no structural layer. -/
def conjunctiveModal : ConnectiveFragment :=
  ⟨true, true, false, true, false⟩

theorem conjunctiveModal_ne_full : conjunctiveModal ≠ fullConnectives := by decide

/-! ### The three axes together -/

/-- A configuration of the three dials: a language fragment, a connective
fragment, and a vertex of the hypercube. -/
structure Dials (S : Signature) (Slot : Type) where
  language : LanguageFragment S
  connectives : ConnectiveFragment
  vertex : Filling Slot

/-- **The axes are independent.**  Fixing any two leaves the third free: two
configurations agreeing on language and connectives can differ at the vertex,
and two agreeing on connectives and vertex can differ in the language. -/
theorem dials_independent {Slot : Type} (L : LanguageFragment S)
    (C : ConnectiveFragment) (v w : Filling Slot) (hvw : v ≠ w) :
    (Dials.mk L C v).language = (Dials.mk L C w).language
      ∧ (Dials.mk L C v).connectives = (Dials.mk L C w).connectives
      ∧ (Dials.mk L C v).vertex ≠ (Dials.mk L C w).vertex :=
  ⟨rfl, rfl, hvw⟩


/-! ## Deciding equality of terms

A matcher must compare terms: a pattern mentioning the same variable twice
matches only when both positions carry equal subterms.  The operator case is
where this is delicate -- two terms of the same sort may be headed by different
operators, whose argument lists then have different types -- and it is handled
by settling the operators first, so that the argument lists become comparable
rather than transported. -/

/-- Variables are positions, so their equality is decidable. -/
def decEqVar : {Γ : Ctx S} → {s : S.Srt} → (x y : Var Γ s) → Decidable (x = y)
  | _, _, .zero, .zero => isTrue rfl
  | _, _, .zero, .succ _ => isFalse (fun h => by cases h)
  | _, _, .succ _, .zero => isFalse (fun h => by cases h)
  | _, _, .succ x, .succ y =>
      match decEqVar x y with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (fun hh => by
          injection hh with _ _ _ hx
          exact h hx)

instance {Γ : Ctx S} {s : S.Srt} : DecidableEq (Var Γ s) := decEqVar

variable [opDec : ∀ s : S.Srt, DecidableEq (S.Op s)]

mutual
/-- Equality of terms is decidable. -/
def decEqTerm : {Γ : Ctx S} → {s : S.Srt} → (t u : Term S Γ s) → Decidable (t = u)
  | _, _, .var x, .var y =>
      match decEqVar x y with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (fun hh => by injection hh with _ _ hx; exact h hx)
  | _, _, .var _, .op _ _ => isFalse (fun h => by cases h)
  | _, _, .op _ _, .var _ => isFalse (fun h => by cases h)
  | _, _, .op o args, .op o' args' =>
      if ho : o = o' then by
        subst ho
        exact match decEqArgs args args' with
          | isTrue h => isTrue (by rw [h])
          | isFalse h => isFalse (fun hh => by
              injection hh with _ _ _ ha
              exact h ha)
      else isFalse (fun hh => by
        injection hh with _ _ hoo _
        exact ho hoo)

/-- And so is equality of argument lists. -/
def decEqArgs : {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    (a b : Args S as Γ) → Decidable (a = b)
  | _, _, .nil, .nil => isTrue rfl
  | _, _, .cons h t, .cons h' t' =>
      match decEqTerm h h' with
      | isFalse hh => isFalse (fun e => by
          injection e with _ _ _ _ eh _
          exact hh eh)
      | isTrue hh =>
          match decEqArgs t t' with
          | isFalse ht => isFalse (fun e => by
              injection e with _ _ _ _ _ et
              exact ht et)
          | isTrue ht => isTrue (by rw [hh, ht])
end

instance {Γ : Ctx S} {s : S.Srt} : DecidableEq (Term S Γ s) := decEqTerm

instance {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} : DecidableEq (Args S as Γ) :=
  decEqArgs

section Matching

variable [DecidableEq S.Srt]

/-! ## Matching

First-order matching of a pattern -- a term whose free variables are the rule's
-- against a closed term.

The matcher threads a partial substitution rather than collecting a list of
bindings and concatenating.  That is not a style choice: with concatenation, a
binding from an earlier sibling shadows a later one, so agreeing with the
concatenated result does not imply agreeing with each part, and soundness of
the recursion does not follow.  Threading removes the possibility: a variable
already bound is checked against its existing value rather than re-bound. -/

/-- A partial closing substitution. -/
abbrev PSub (S : Signature) (Γ : Ctx S) : Type :=
  (s : S.Srt) → Var Γ s → Option (Term S [] s)

/-- Nothing bound yet. -/
def emptyPSub {Γ : Ctx S} : PSub S Γ := fun _ _ => none

/-- Bind one more variable. -/
def updatePSub {Γ : Ctx S} {c : S.Srt} (acc : PSub S Γ) (x : Var Γ c)
    (t : Term S [] c) : PSub S Γ := fun s y =>
  if h : c = s then (if h ▸ x = y then some (h ▸ t) else acc s y) else acc s y

omit opDec in
/-- Updating binds what it was given. -/
theorem updatePSub_self {Γ : Ctx S} {c : S.Srt} (acc : PSub S Γ) (x : Var Γ c)
    (t : Term S [] c) : updatePSub acc x t c x = some t := by
  simp [updatePSub]

omit opDec in
/-- And leaves everything it already said alone. -/
theorem updatePSub_mono {Γ : Ctx S} {c : S.Srt} (acc : PSub S Γ) (x : Var Γ c)
    (t : Term S [] c) (hx : acc c x = none) :
    ∀ (s : S.Srt) (y : Var Γ s) (u : Term S [] s),
      acc s y = some u → updatePSub acc x t s y = some u := by
  intro s y u hu
  simp only [updatePSub]
  by_cases h : c = s
  · subst h
    by_cases hxy : x = y
    · subst hxy; rw [hx] at hu; exact absurd hu (by simp)
    · simp [hxy, hu]
  · simp [h, hu]


/-- A variable of a bound prefix, seen in the opened context. -/
def reScope : (bs : List S.Srt) → {Γ : Ctx S} → {c : S.Srt} →
    Var (bs ++ []) c → Var (bs ++ Γ) c
  | [], _, _, v => nomatch v
  | _ :: _, _, _, .zero => .zero
  | _ :: bs, _, _, .succ w => .succ (reScope bs w)

/-- A term of the bound prefix, seen in the opened context. -/
def weakenInto (bs : List S.Srt) {Γ : Ctx S} {s : S.Srt}
    (t : Term S (bs ++ []) s) : Term S (bs ++ Γ) s :=
  rename (fun _ v => reScope bs v) t

omit opDec [DecidableEq S.Srt] in
/-- Lifting a closing substitution leaves the bound prefix alone. -/
theorem liftSub_reScope {Γ : Ctx S} (sigma : Sub S Γ []) :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var (bs ++ []) s),
      liftSub sigma bs s (reScope bs v) = Term.var v
  | [], _, v => nomatch v
  | _ :: bs, s, v => by
      cases v with
      | zero => rfl
      | succ w =>
          simp only [reScope, liftSub, liftSub_reScope sigma bs s w, weaken, rename]

omit opDec [DecidableEq S.Srt] in
/-- So a body that is merely the target's, seen in the opened context, is
carried back to the target by any closing substitution. -/
theorem bind_weakenInto {Γ : Ctx S} (sigma : Sub S Γ []) (bs : List S.Srt)
    {s : S.Srt} (t : Term S (bs ++ []) s) :
    bind (liftSub sigma bs) (weakenInto (Γ := Γ) bs t) = t := by
  simp only [weakenInto, bind_rename, liftSub_reScope sigma bs, bind_id]

mutual
/-- Match a pattern against a closed term, threading the bindings found. -/
def matchT : {Γ : Ctx S} → {s : S.Srt} →
    PSub S Γ → Term S Γ s → Term S [] s → Option (PSub S Γ)
  | _, _, acc, .var x, t =>
      match acc _ x with
      | none => some (updatePSub acc x t)
      | some u => if u = t then some acc else none
  | _, _, acc, .op o args, .op o' args' =>
      if h : o = o' then matchA acc (h ▸ args) args' else none
  | _, _, _, .op _ _, .var v => nomatch v

/-- Match argument lists.  A binding argument is not descended into: its body
lives under binders the closed term does not share, so first-order matching
stops there and that slot belongs to the metavariable layer. -/
def matchA : {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    PSub S Γ → Args S as Γ → Args S as [] → Option (PSub S Γ)
  | _, _, acc, .nil, .nil => some acc
  | (bs, _) :: _, _, acc, .cons h t, .cons h' t' =>
      match bs with
      | [] =>
          match matchT acc h h' with
          | none => none
          | some acc' => matchA acc' t t'
      | b :: rest =>
          if h = weakenInto (b :: rest) h' then matchA acc t t' else none
end

/-- A closing substitution realises a partial one when it agrees with every
binding it has made. -/
def PExtends {Γ : Ctx S} (sigma : Sub S Γ []) (acc : PSub S Γ) : Prop :=
  ∀ (s : S.Srt) (x : Var Γ s) (t : Term S [] s), acc s x = some t → sigma s x = t

mutual
/-- Matching only ever adds bindings. -/
theorem matchT_mono : ∀ {Γ : Ctx S} {s : S.Srt} (acc acc' : PSub S Γ)
    (p : Term S Γ s) (t : Term S [] s), matchT acc p t = some acc' →
    ∀ (r : S.Srt) (y : Var Γ r) (u : Term S [] r), acc r y = some u → acc' r y = some u
  | _, _, acc, acc', .var x, t, hm => by
      simp only [matchT] at hm
      cases hx : acc _ x with
      | none =>
          rw [hx] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          exact updatePSub_mono acc x t hx
      | some u =>
          rw [hx] at hm
          by_cases hu : u = t
          · simp only [if_pos hu, Option.some.injEq] at hm
            subst hm
            exact fun _ _ _ h => h
          · simp [if_neg hu] at hm
  | _, _, acc, acc', .op o args, .op o' args', hm => by
      simp only [matchT] at hm
      by_cases h : o = o'
      · rw [dif_pos h] at hm
        subst h
        exact matchA_mono acc acc' _ args' hm
      · simp [dif_neg h] at hm
  | _, _, _, _, .op _ _, .var v, _ => nomatch v

theorem matchA_mono : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (acc acc' : PSub S Γ) (p : Args S as Γ) (t : Args S as []),
    matchA acc p t = some acc' →
    ∀ (r : S.Srt) (y : Var Γ r) (u : Term S [] r), acc r y = some u → acc' r y = some u
  | _, _, acc, acc', .nil, .nil, hm => by
      simp only [matchA, Option.some.injEq] at hm
      subst hm
      exact fun _ _ _ h => h
  | (bs, _) :: _, _, acc, acc', .cons hd tl, .cons hd' tl', hm => by
      match bs with
      | [] =>
          simp only [matchA] at hm
          cases h1 : matchT acc hd hd' with
          | none => rw [h1] at hm; exact absurd hm (by simp)
          | some acc₁ =>
              rw [h1] at hm
              intro r y u hu
              exact matchA_mono acc₁ acc' tl tl' hm r y u
                (matchT_mono acc acc₁ hd hd' h1 r y u hu)
      | b :: rest =>
          simp only [matchA] at hm
          by_cases heq : hd = weakenInto (b :: rest) hd'
          · rw [if_pos heq] at hm
            exact matchA_mono acc acc' tl tl' hm
          · rw [if_neg heq] at hm
            exact absurd hm (by simp)
end

mutual
/-- **The matcher is sound.**  Any closing substitution realising its result
carries the pattern to the target. -/
theorem matchT_sound : ∀ {Γ : Ctx S} {s : S.Srt} (acc acc' : PSub S Γ)
    (p : Term S Γ s) (t : Term S [] s), matchT acc p t = some acc' →
    ∀ sigma : Sub S Γ [], PExtends sigma acc' → bind sigma p = t
  | _, _, acc, acc', .var x, t, hm, sigma, he => by
      simp only [matchT] at hm
      cases hx : acc _ x with
      | none =>
          rw [hx] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          exact he _ x t (updatePSub_self acc x t)
      | some u =>
          rw [hx] at hm
          by_cases hu : u = t
          · simp only [if_pos hu, Option.some.injEq] at hm
            subst hm
            exact he _ x t (by rw [hx, hu])
          · simp [if_neg hu] at hm
  | _, _, acc, acc', .op o args, .op o' args', hm, sigma, he => by
      simp only [matchT] at hm
      by_cases h : o = o'
      · rw [dif_pos h] at hm
        subst h
        simp only [bind, matchA_sound acc acc' args args' hm sigma he]
      · simp [dif_neg h] at hm
  | _, _, _, _, .op _ _, .var v, _, _, _ => nomatch v

theorem matchA_sound : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (acc acc' : PSub S Γ) (p : Args S as Γ) (t : Args S as []),
    matchA acc p t = some acc' →
    ∀ sigma : Sub S Γ [], PExtends sigma acc' → bindArgs sigma p = t
  | _, _, _, _, .nil, .nil, _, _, _ => rfl
  | (bs, _) :: _, _, acc, acc', .cons hd tl, .cons hd' tl', hm, sigma, he => by
      match bs with
      | [] =>
          simp only [matchA] at hm
          cases h1 : matchT acc hd hd' with
          | none => rw [h1] at hm; exact absurd hm (by simp)
          | some acc₁ =>
              rw [h1] at hm
              have he1 : PExtends sigma acc₁ := by
                intro r y u hu
                exact he r y u (matchA_mono acc₁ acc' tl tl' hm r y u hu)
              simp only [bindArgs, liftSub,
                matchT_sound acc acc₁ hd hd' h1 sigma he1,
                matchA_sound acc₁ acc' tl tl' hm sigma he]
      | b :: rest =>
          simp only [matchA] at hm
          by_cases heq : hd = weakenInto (b :: rest) hd'
          · rw [if_pos heq] at hm
            subst heq
            simp only [bindArgs, bind_weakenInto sigma (b :: rest) hd',
              matchA_sound acc acc' tl tl' hm sigma he]
          · rw [if_neg heq] at hm
            exact absurd hm (by simp)
end

end Matching


/-! ## The construction composes

Reading a term of an extension back down by supplying bodies lands in the base
signature, so it cannot be iterated.  Letting the bodies themselves carry
metavariables gives the operation that can be: it takes a term over one
extension to a term over another, and it is the multiplication the monad
needs. -/

/-- The arguments a metavariable is applied to when it stands for itself: each
variable of its own context, in order. -/
def idArgs {M : List (MetaArity S)} :
    (bs : List S.Srt) → Args (withMetas S M) (bs.map (fun b => ([], b))) bs
  | [] => .nil
  | _ :: rest => .cons (.var .zero) (renameArgs (fun _ v => .succ v) (idArgs rest))

/-- The unit: a metavariable, applied to its own variables, read as a term. -/
def metaVar {M : List (MetaArity S)} (i : Fin M.length) :
    Term (withMetas S M) (M.get i).1 (M.get i).2 :=
  Term.op (Sum.inr (MetaOp.mk i)) (idArgs (M := M) (M.get i).1)

mutual
/-- **Instantiation into an extension.**  Each metavariable is replaced by the
body supplied for it, applied to the arguments the term gave it; the bodies may
themselves mention metavariables, so this composes. -/
def instInto {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) :
    {Γ : Ctx S} → {s : S.Srt} →
    Term (withMetas S M) Γ s → Term (withMetas S N) Γ s
  | _, _, .var v => .var v
  | _, _, .op (Sum.inl f) args =>
      Term.op (S := withMetas S N) (Sum.inl f)
        (instIntoArgs (N := N) body (as := S.arity f) args)
  | _, _, .op (Sum.inr (.mk i)) args =>
      bind (argsToSub (instIntoArgs body args)) (body i)

def instIntoArgs {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) :
    {as : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args (withMetas S M) as Γ → Args (withMetas S N) as Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (instInto body head) (instIntoArgs body tail)
end

/-! ### The unit laws -/

/-- Reading a substitution off renamed arguments renames what it reads. -/
theorem argsToSub_renameArgs {T : Signature} {Γ Δ : Ctx T} (rho : Ren T Γ Δ) :
    ∀ (bs : List T.Srt) (args : Args T (bs.map (fun b => ([], b))) Γ)
      (s : T.Srt) (v : Var bs s),
      argsToSub (renameArgs rho args) s v = rename rho (argsToSub args s v)
  | [], _, _, v => nomatch v
  | _ :: rest, .cons head tail, s, v => by
      cases v with
      | zero => rfl
      | succ w => exact argsToSub_renameArgs rho rest tail s w

omit opDec in
/-- A metavariable applied to its own variables reads off as the identity. -/
theorem argsToSub_idArgs {M : List (MetaArity S)} :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var bs s),
      argsToSub (idArgs (M := M) bs) s v = Term.var (S := withMetas S M) v
  | [], _, v => nomatch v
  | _ :: rest, s, v => by
      cases v with
      | zero => rfl
      | succ w =>
          simp only [idArgs, argsToSub, argsToSub_renameArgs, argsToSub_idArgs rest s w,
            rename]

omit opDec in
mutual
/-- Instantiation commutes with renaming. -/
theorem instInto_rename {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) :
    ∀ {Γ Δ : Ctx S} {s : S.Srt} (rho : Ren S Γ Δ) (t : Term (withMetas S M) Γ s),
      instInto body (rename (S := withMetas S M) rho t)
        = rename (S := withMetas S N) rho (instInto body t)
  | _, _, _, rho, .var v => rfl
  | _, _, _, rho, .op (Sum.inl f) args => by
      simp only [rename, instInto, instIntoArgs_renameArgs body rho args]
  | _, _, _, rho, .op (Sum.inr (.mk i)) args => by
      simp only [rename, instInto, instIntoArgs_renameArgs body rho args, rename_bind]
      congr 1
      funext s v
      simp only [argsToSub_renameArgs]

theorem instIntoArgs_renameArgs {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S} (rho : Ren S Γ Δ)
      (args : Args (withMetas S M) as Γ),
      instIntoArgs body (renameArgs (S := withMetas S M) rho args)
        = renameArgs (S := withMetas S N) rho (instIntoArgs body args)
  | _, _, _, _, .nil => rfl
  | _, _, _, rho, .cons (bs := bs) head tail => by
      simp only [renameArgs, instIntoArgs, instIntoArgs_renameArgs body rho tail]
      congr 1
      exact instInto_rename body (liftRen rho bs) head
end

omit opDec in
/-- Instantiation leaves a metavariable's own variables alone. -/
theorem instIntoArgs_idArgs {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) :
    ∀ (bs : List S.Srt),
      instIntoArgs body (idArgs (M := M) bs) = idArgs (M := N) bs
  | [] => rfl
  | _ :: rest => by
      simp only [idArgs, instIntoArgs, instInto, instIntoArgs_renameArgs,
        instIntoArgs_idArgs body rest]

omit opDec in
/-- **Left unit.**  Instantiating the unit at a metavariable returns the body
supplied for it. -/
theorem instInto_metaVar {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (i : Fin M.length) : instInto body (metaVar i) = body i := by
  simp only [metaVar, instInto, instIntoArgs_idArgs body]
  have : argsToSub (idArgs (M := N) (M.get i).1) = fun s v => Term.var (S := withMetas S N) v := by
    funext s v
    exact argsToSub_idArgs (M := N) _ s v
  rw [this, bind_id]


omit opDec in
/-- Substituting a metavariable's own variables by the reading of its arguments
returns those arguments. -/
theorem bindArgs_argsToSub_idArgs {M : List (MetaArity S)} :
    ∀ (bs : List S.Srt) {Γ : Ctx S}
      (args : Args (withMetas S M) (bs.map (fun b => ([], b))) Γ),
      bindArgs (argsToSub args) (idArgs (M := M) bs) = args
  | [], _, args => by cases args; rfl
  | _ :: rest, _, args => by
      cases args with
      | cons head tail =>
          simp only [idArgs, bindArgs, liftSub, bind, argsToSub, bindArgs_rename,
            bindArgs_argsToSub_idArgs rest tail]

omit opDec in
mutual
/-- **Right unit.**  Instantiating every metavariable by itself is the
identity. -/
theorem instInto_metaVar_id {M : List (MetaArity S)} :
    ∀ {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S M) Γ s),
      instInto (metaVar (M := M)) t = t
  | _, _, .var _ => rfl
  | _, _, .op (Sum.inl f) args => by
      simp only [instInto, instIntoArgs_metaVar_id args]
  | _, _, .op (Sum.inr (.mk i)) args => by
      simp only [instInto, instIntoArgs_metaVar_id args, metaVar, bind,
        bindArgs_argsToSub_idArgs]

theorem instIntoArgs_metaVar_id {M : List (MetaArity S)} :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args (withMetas S M) as Γ),
      instIntoArgs (metaVar (M := M)) args = args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [instIntoArgs, instInto_metaVar_id head,
        instIntoArgs_metaVar_id tail]
end


omit opDec in
/-- Reading a substitution off substituted arguments substitutes what it reads. -/
theorem argsToSub_bindArgs {T : Signature} {Γ Δ : Ctx T} (sigma : Sub T Γ Δ) :
    ∀ (bs : List T.Srt) (args : Args T (bs.map (fun b => ([], b))) Γ)
      (s : T.Srt) (v : Var bs s),
      argsToSub (bindArgs sigma args) s v = bind sigma (argsToSub args s v)
  | [], _, _, v => nomatch v
  | _ :: rest, .cons head tail, s, v => by
      cases v with
      | zero => rfl
      | succ w => exact argsToSub_bindArgs sigma rest tail s w

omit opDec in
/-- And reading it off instantiated arguments instantiates what it reads. -/
theorem argsToSub_instIntoArgs {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) :
    ∀ (bs : List S.Srt) {Γ : Ctx S}
      (args : Args (withMetas S M) (bs.map (fun b => ([], b))) Γ)
      (s : S.Srt) (v : Var bs s),
      argsToSub (instIntoArgs body args) s v = instInto body (argsToSub args s v)
  | [], _, _, _, v => nomatch v
  | _ :: rest, _, .cons head tail, s, v => by
      cases v with
      | zero => rfl
      | succ w => exact argsToSub_instIntoArgs body rest tail s w

omit opDec in
/-- Instantiation commutes with the lifting of a substitution past binders. -/
theorem instInto_liftSub {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    {Γ Δ : Ctx S} (sigma : Sub (withMetas S M) Γ Δ) :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var (bs ++ Γ) s),
      instInto body (liftSub sigma bs s v)
        = liftSub (fun r y => instInto body (sigma r y)) bs s v
  | [], _, _ => rfl
  | _ :: bs, s, v => by
      cases v with
      | zero => rfl
      | succ w =>
          simp only [liftSub, weaken, instInto_rename body,
            instInto_liftSub body sigma bs s w]

omit opDec in
mutual
/-- Instantiation commutes with substitution. -/
theorem instInto_bind {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) :
    ∀ {Γ Δ : Ctx S} {s : S.Srt} (sigma : Sub (withMetas S M) Γ Δ)
      (t : Term (withMetas S M) Γ s),
      instInto body (bind sigma t)
        = bind (fun r y => instInto body (sigma r y)) (instInto body t)
  | _, _, _, _, .var _ => rfl
  | _, _, _, sigma, .op (Sum.inl f) args => by
      simp only [bind, instInto, instIntoArgs_bindArgs body sigma args]
  | _, _, _, sigma, .op (Sum.inr (.mk i)) args => by
      simp only [bind, instInto, instIntoArgs_bindArgs body sigma args, bind_comp]
      congr 1
      funext r y
      simp only [argsToSub_bindArgs]

theorem instIntoArgs_bindArgs {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S} (sigma : Sub (withMetas S M) Γ Δ)
      (args : Args (withMetas S M) as Γ),
      instIntoArgs body (bindArgs sigma args)
        = bindArgs (fun r y => instInto body (sigma r y)) (instIntoArgs body args)
  | _, _, _, _, .nil => rfl
  | _, _, _, sigma, .cons (bs := bs) head tail => by
      have h : (fun r y => instInto body (liftSub sigma bs r y))
             = liftSub (fun r y => instInto body (sigma r y)) bs := by
        funext r y
        exact instInto_liftSub body sigma bs r y
      simp only [bindArgs, instIntoArgs, instIntoArgs_bindArgs body sigma tail,
        instInto_bind body (liftSub sigma bs) head, h]
end

omit opDec in
mutual
/-- **Associativity.**  Instantiating twice is instantiating once along the
composite, so the construction is a monad. -/
theorem instInto_instInto {M N P : List (MetaArity S)}
    (body₁ : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (body₂ : (j : Fin N.length) → Term (withMetas S P) (N.get j).1 (N.get j).2) :
    ∀ {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S M) Γ s),
      instInto body₂ (instInto body₁ t)
        = instInto (fun i => instInto body₂ (body₁ i)) t
  | _, _, .var _ => rfl
  | _, _, .op (Sum.inl f) args => by
      simp only [instInto, instIntoArgs_instIntoArgs body₁ body₂ args]
  | _, _, .op (Sum.inr (.mk i)) args => by
      have h : (fun r y => instInto body₂ (argsToSub (instIntoArgs body₁ args) r y))
             = argsToSub (instIntoArgs (fun i => instInto body₂ (body₁ i)) args) := by
        funext r y
        rw [← argsToSub_instIntoArgs body₂ _ (instIntoArgs body₁ args) r y,
          instIntoArgs_instIntoArgs body₁ body₂ args]
      simp only [instInto, instInto_bind body₂, h]

theorem instIntoArgs_instIntoArgs {M N P : List (MetaArity S)}
    (body₁ : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (body₂ : (j : Fin N.length) → Term (withMetas S P) (N.get j).1 (N.get j).2) :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args (withMetas S M) as Γ),
      instIntoArgs body₂ (instIntoArgs body₁ args)
        = instIntoArgs (fun i => instInto body₂ (body₁ i)) args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [instIntoArgs, instInto_instInto body₁ body₂ head,
        instIntoArgs_instIntoArgs body₁ body₂ tail]
end


/-! ## Carrying a position along an instantiation

The source displays the action of the construction on a morphism as transport:
the modality at a one-hole context goes to the modality at the transported
context.  Instantiation is the morphism that arises here, so the question is
what it does to a position. -/

omit opDec in
/-- Instantiation commutes with plugging the hole. -/
theorem instInto_extend {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    {Γ : Ctx S} {c : S.Srt} (t : Term (withMetas S M) Γ c) :
    (fun r y => instInto body (extend t r y)) = extend (instInto body t) := by
  funext r y
  cases y with
  | zero => rfl
  | succ w => rfl

omit opDec in
/-- **Plugging transports.**  Instantiating a context and its redex separately,
then plugging, is instantiating the plugged term. -/
theorem instInto_inst {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    {Γ : Ctx S} {c s : S.Srt} (K : Term (withMetas S M) (c :: Γ) s)
    (t : Term (withMetas S M) Γ c) :
    instInto body (inst K t) = inst (instInto body K) (instInto body t) := by
  simp only [inst, instInto_bind body, instInto_extend]


/-! ## Reading a slot back one scope down

A binding slot whose pattern is a bare metavariable applied to the variables it
binds is solvable: the metavariable takes the target's body, read in the scope
the hole binds rather than in the target's own. This is the full-prefix case;
`ScopedMatching` also recognizes injective subsets and permutations using the
existing strengthening operation.

Everything it needs is already here.  Reading down and injecting back is the
identity the checking case uses, so binding the metavariable this way is sound
for the same reason that checking a non-metavariable slot is. -/

/-- A variable of the bound prefix, read in the prefix alone. -/
def unScopeVar : (bs : List S.Srt) → {c : S.Srt} → Var (bs ++ []) c → Var bs c
  | [], _, v => nomatch v
  | _ :: _, _, .zero => .zero
  | _ :: bs, _, .succ w => .succ (unScopeVar bs w)

/-- A term of the opened target scope, read in the prefix alone.  This is what
a metavariable slot is bound to. -/
def unScope (bs : List S.Srt) {s : S.Srt} (t : Term S (bs ++ []) s) : Term S bs s :=
  rename (fun _ v => unScopeVar bs v) t

/-- A variable of the prefix, injected into the opened pattern scope. -/
def injPrefix : (bs : List S.Srt) → {Γ : Ctx S} → {c : S.Srt} → Var bs c → Var (bs ++ Γ) c
  | [], _, _, v => nomatch v
  | _ :: _, _, _, .zero => .zero
  | _ :: bs, _, _, .succ w => .succ (injPrefix bs w)

omit opDec in
/-- Reading down and injecting back is reading across. -/
theorem injPrefix_unScopeVar {Γ : Ctx S} :
    ∀ (bs : List S.Srt) {c : S.Srt} (v : Var (bs ++ []) c),
      injPrefix (Γ := Γ) bs (unScopeVar bs v) = reScope bs v
  | [], _, v => nomatch v
  | _ :: bs, _, v => by
      cases v with
      | zero => rfl
      | succ w => simp only [unScopeVar, injPrefix, reScope, injPrefix_unScopeVar bs w]

omit opDec in
/-- So is it on terms. -/
theorem rename_injPrefix_unScope {Γ : Ctx S} (bs : List S.Srt) {s : S.Srt}
    (t : Term S (bs ++ []) s) :
    rename (fun _ v => injPrefix (Γ := Γ) bs v) (unScope bs t) = weakenInto bs t := by
  simp only [unScope, weakenInto, rename_comp]
  congr 1
  funext r v
  exact injPrefix_unScopeVar bs v

omit opDec in
/-- **Binding a metavariable slot to the target's body, read one scope down, is
sound**: closing the rule afterwards carries it back to that body exactly.  So
the pattern-fragment case of a second-order slot is settled by the same lemma
that settles a first-order one. -/
theorem bind_reads_slot_back {Γ : Ctx S} (sigma : Sub S Γ []) (bs : List S.Srt)
    {s : S.Srt} (t : Term S (bs ++ []) s) :
    bind (liftSub sigma bs) (rename (fun _ v => injPrefix (Γ := Γ) bs v) (unScope bs t))
      = t := by
  rw [rename_injPrefix_unScope bs t, bind_weakenInto]


/-! ## The condition a solvable metavariable slot satisfies

A metavariable applied to all variables its slot binds, in order, is a
particularly direct solvable profile. This section names
those arguments, shows what substitution they read off as, and proves that a
slot of that shape, filled by the target's body read one scope down, is carried
back to that body by any closing substitution. -/

omit opDec in
/-- Substituting variables for variables is renaming, under a lifted
substitution. -/
theorem liftSub_var_comp {Γ Δ : Ctx S} (rho : Ren S Γ Δ) :
    ∀ (bs : List S.Srt) (s : S.Srt) (v : Var (bs ++ Γ) s),
      liftSub (fun r y => Term.var (S := S) (rho r y)) bs s v
        = Term.var (liftRen rho bs s v)
  | [], _, _ => rfl
  | _ :: bs, s, v => by
      cases v with
      | zero => rfl
      | succ w =>
          simp only [liftSub, liftRen, liftSub_var_comp rho bs s w, weaken, rename]

omit opDec in
mutual
/-- Substituting variables for variables is renaming. -/
theorem bind_var_eq_rename : ∀ {Γ Δ : Ctx S} {s : S.Srt} (rho : Ren S Γ Δ)
    (t : Term S Γ s), bind (fun r y => Term.var (rho r y)) t = rename rho t
  | _, _, _, _, .var _ => rfl
  | _, _, _, rho, .op o args => by
      simp only [bind, rename, bindArgs_var_eq_renameArgs rho args]

theorem bindArgs_var_eq_renameArgs : ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S}
    (rho : Ren S Γ Δ) (args : Args S as Γ),
    bindArgs (fun r y => Term.var (rho r y)) args = renameArgs rho args
  | _, _, _, _, .nil => rfl
  | _, _, _, rho, .cons (bs := bs) head tail => by
      have h : (fun (r : S.Srt) (y : Var (bs ++ _) r) =>
          Term.var (S := S) (liftRen rho bs r y))
            = liftSub (fun r y => Term.var (S := S) (rho r y)) bs := by
        funext r y
        exact (liftSub_var_comp rho bs r y).symm
      simp only [bindArgs, renameArgs, ← bind_var_eq_rename (liftRen rho bs) head,
        bindArgs_var_eq_renameArgs rho tail, h]
end

/-- The arguments a metavariable is applied to when it is applied to exactly
the variables its slot binds. -/
def prefixArgs {T : Signature} : (bs : List T.Srt) → {Γ : Ctx T} →
    Args T (bs.map (fun b => ([], b))) (bs ++ Γ)
  | [], _ => .nil
  | _ :: rest, _ => .cons (.var .zero) (renameArgs (fun _ v => .succ v) (prefixArgs rest))

omit opDec in
/-- They read off as the injection of the prefix. -/
theorem argsToSub_prefixArgs {T : Signature} {Γ : Ctx T} :
    ∀ (bs : List T.Srt) (s : T.Srt) (v : Var bs s),
      argsToSub (prefixArgs (T := T) (Γ := Γ) bs) s v
        = Term.var (S := T) (injPrefix (Γ := Γ) bs v)
  | [], _, v => nomatch v
  | _ :: rest, s, v => by
      cases v with
      | zero => rfl
      | succ w =>
          simp only [prefixArgs, argsToSub, argsToSub_renameArgs,
            argsToSub_prefixArgs rest s w, rename, injPrefix]

omit opDec in
/-- **A metavariable slot in the pattern fragment is solved by the target's
body read one scope down.**  Filling the slot with that body and closing the
rule carries it back to exactly that body, so the assignment the fragment
forces is the right one.  The substitution appearing here is the one the slot's
arguments read off as, by `argsToSub_prefixArgs`. -/
theorem bind_prefix_slot {Γ : Ctx S} (sigma : Sub S Γ []) (bs : List S.Srt)
    {s : S.Srt} (t : Term S (bs ++ []) s) :
    bind (liftSub sigma bs)
        (bind (fun _ y => Term.var (S := S) (injPrefix (Γ := Γ) bs y)) (unScope bs t))
      = t := by
  rw [bind_var_eq_rename, rename_injPrefix_unScope, bind_weakenInto]


omit opDec in
/-- Instantiation leaves a slot's own bound variables alone, since they are
variables and instantiation touches only metavariables.  With
`argsToSub_prefixArgs` and `bind_prefix_slot` this is everything the
pattern-fragment slot case needs: its arguments survive instantiation, they
read off as the injection of the prefix, and filling the slot with the target's
body read one scope down is carried back to that body. -/
theorem instIntoArgs_prefixArgs {M N : List (MetaArity S)}
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) :
    ∀ (bs : List S.Srt) {Γ : Ctx S},
      instIntoArgs body (prefixArgs (T := withMetas S M) (Γ := Γ) bs)
        = prefixArgs (T := withMetas S N) (Γ := Γ) bs
  | [], _ => rfl
  | _ :: rest, _ => by
      simp only [prefixArgs, instIntoArgs, instInto, instIntoArgs_renameArgs,
        instIntoArgs_prefixArgs body rest]


/-! ## Splitting a variable at a binder prefix

Matching a schema under binders has to tell the slot's own bound variables from
the rule's: the first must match themselves in the target, the second are what
the match binds.  The two are distinguished by where they sit, which is a
decision the context already records. -/

/-- A variable of an opened context is either one the prefix binds or one the
ambient context does. -/
def splitVar : (bs : List S.Srt) → {Γ : Ctx S} → {c : S.Srt} →
    Var (bs ++ Γ) c → Sum (Var bs c) (Var Γ c)
  | [], _, _, x => .inr x
  | _ :: _, _, _, .zero => .inl .zero
  | _ :: rest, _, _, .succ w =>
      match splitVar rest w with
      | .inl v => .inl (.succ v)
      | .inr v => .inr v

omit opDec in
/-- A prefix variable splits to the left. -/
theorem splitVar_injPrefix {Γ : Ctx S} :
    ∀ (bs : List S.Srt) {c : S.Srt} (v : Var bs c),
      splitVar bs (injPrefix (Γ := Γ) bs v) = .inl v
  | [], _, v => nomatch v
  | _ :: rest, _, v => by
      cases v with
      | zero => rfl
      | succ w => simp only [injPrefix, splitVar, splitVar_injPrefix rest w]

omit opDec in
/-- An ambient variable splits to the right. -/
theorem splitVar_weakenVar {Γ : Ctx S} :
    ∀ (bs : List S.Srt) {c : S.Srt} (y : Var Γ c),
      splitVar bs (weakenVar bs y) = .inr y
  | [], _, _ => rfl
  | _ :: rest, _, y => by
      simp only [weakenVar, splitVar, splitVar_weakenVar rest y]

omit opDec in
/-- So the two injections are disjoint: no variable is both. -/
theorem injPrefix_ne_weakenVar {Γ : Ctx S} (bs : List S.Srt) {c : S.Srt}
    (v : Var bs c) (y : Var Γ c) : injPrefix bs v ≠ weakenVar bs y := by
  intro h
  have h1 : splitVar bs (injPrefix (Γ := Γ) bs v) = .inl v := splitVar_injPrefix bs v
  have h2 : splitVar bs (weakenVar (Δ := Γ) bs y) = .inr y := splitVar_weakenVar bs y
  rw [h, h2] at h1
  simp at h1


/-! ## Comparing argument lists that are variables

A metavariable slot in the pattern fragment is applied to variables, so
checking that it is applied to the right ones needs no equality on operators --
only on variables.  That matters: adjoining a metavariable makes the extended
signature's operator set a family indexed by the metavariable's own sort, and
two such at one sort cannot be eliminated together, so an equality instance
there is not available.  Comparing variables sidesteps it entirely. -/

/-- Compare two terms expected to be variables.  Anything else fails rather
than descends, which is what keeps this free of operator equality. -/
def varEqB {T : Signature} {Γ : Ctx T} {s : T.Srt} : Term T Γ s → Term T Γ s → Bool
  | .var x, .var y => decide (x = y)
  | _, _ => false

omit opDec in
/-- Sound: when it succeeds the two really are the same variable. -/
theorem varEqB_sound {T : Signature} {Γ : Ctx T} {s : T.Srt} :
    ∀ (a b : Term T Γ s), varEqB a b = true → a = b
  | .var x, .var y, h => by
      simp only [varEqB, decide_eq_true_eq] at h
      rw [h]
  | .var _, .op _ _, h => by simp [varEqB] at h
  | .op _ _, .var _, h => by simp [varEqB] at h
  | .op _ _, .op _ _, h => by simp [varEqB] at h

/-- Compare argument lists that are expected to be variables. -/
def varArgsEq {T : Signature} : {as : List (List T.Srt × T.Srt)} → {Γ : Ctx T} →
    Args T as Γ → Args T as Γ → Bool
  | _, _, .nil, .nil => true
  | _, _, .cons h₁ t₁, .cons h₂ t₂ => varEqB h₁ h₂ && varArgsEq t₁ t₂

omit opDec in
/-- Sound in the same way. -/
theorem varArgsEq_sound {T : Signature} :
    ∀ {as : List (List T.Srt × T.Srt)} {Γ : Ctx T} (a b : Args T as Γ),
      varArgsEq a b = true → a = b
  | _, _, .nil, .nil, _ => rfl
  | _, _, .cons h₁ t₁, .cons h₂ t₂, hb => by
      simp only [varArgsEq, Bool.and_eq_true] at hb
      rw [varEqB_sound h₁ h₂ hb.1, varArgsEq_sound t₁ t₂ hb.2]

section SchemaComparison

variable {M : List (MetaArity S)}

/-! ## Comparing a schema against a term of the base signature

A binding slot whose pattern is not a metavariable has to be checked against
the target's body.  Comparing two terms of the *extended* signature would need
equality on its operators, which is unavailable; comparing a pattern against a
*base* term does not, because the only operators ever compared are the base
ones.  A metavariable makes the comparison fail rather than descend, which is
correct: such a slot is the metavariable layer's to solve, not this one's. -/

mutual
/-- Compare a schema against a term of the base signature. -/
def patEqB : {Δ : Ctx S} → {s : S.Srt} →
    Term (withMetas S M) Δ s → Term S Δ s → Bool
  | _, _, .var x, .var y => decide (x = y)
  | _, _, .op (Sum.inl f) args, .op f' args' =>
      if h : f = f' then patArgsEqB (h ▸ args) args' else false
  | _, _, .op (Sum.inr _) _, _ => false
  | _, _, .var _, .op _ _ => false
  | _, _, .op (Sum.inl _) _, .var _ => false

def patArgsEqB : {as : List (List S.Srt × S.Srt)} → {Δ : Ctx S} →
    Args (withMetas S M) as Δ → Args S as Δ → Bool
  | _, _, .nil, .nil => true
  | _, _, .cons h₁ t₁, .cons h₂ t₂ => patEqB h₁ h₂ && patArgsEqB t₁ t₂
end

mutual
/-- **Sound**: when the comparison succeeds the schema is the inclusion of the
term, so it mentions no metavariable and agrees with it everywhere. -/
theorem patEqB_sound : ∀ {Δ : Ctx S} {s : S.Srt}
    (p : Term (withMetas S M) Δ s) (t : Term S Δ s),
    patEqB p t = true → p = embed (M := M) t
  | _, _, .var x, .var y, h => by
      simp only [patEqB, decide_eq_true_eq] at h
      rw [h]; rfl
  | _, _, .op (Sum.inl f) args, .op f' args', h => by
      simp only [patEqB] at h
      by_cases hf : f = f'
      · subst hf
        rw [dif_pos rfl] at h
        simp only [embed, patArgsEqB_sound args args' h]
      · rw [dif_neg hf] at h
        exact absurd h (by simp)
  | _, _, .op (Sum.inr _) _, _, h => by simp [patEqB] at h
  | _, _, .var _, .op _ _, h => by simp [patEqB] at h
  | _, _, .op (Sum.inl _) _, .var _, h => by simp [patEqB] at h

theorem patArgsEqB_sound : ∀ {as : List (List S.Srt × S.Srt)} {Δ : Ctx S}
    (a : Args (withMetas S M) as Δ) (b : Args S as Δ),
    patArgsEqB a b = true → a = embedArgs (M := M) b
  | _, _, .nil, .nil, _ => rfl
  | _, _, .cons h₁ t₁, .cons h₂ t₂, hb => by
      simp only [patArgsEqB, Bool.and_eq_true] at hb
      simp only [embedArgs, patEqB_sound h₁ h₂ hb.1, patArgsEqB_sound t₁ t₂ hb.2]
end

end SchemaComparison


/-! ## Instantiation into the base signature is natural too -/

omit opDec in
mutual
/-- Reading a schema down commutes with renaming. -/
theorem instantiate_rename {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    ∀ {Γ Δ : Ctx S} {s : S.Srt} (rho : Ren S Γ Δ) (t : Term (withMetas S M) Γ s),
      instantiate body (rename (S := withMetas S M) rho t)
        = rename (S := S) rho (instantiate body t)
  | _, _, _, _, .var _ => rfl
  | _, _, _, rho, .op (Sum.inl f) args => by
      simp only [rename, instantiate, instantiateArgs_renameArgs body rho args]
  | _, _, _, rho, .op (Sum.inr (.mk i)) args => by
      simp only [rename, instantiate, instantiateArgs_renameArgs body rho args, rename_bind]
      congr 1
      funext r v
      simp only [argsToSub_renameArgs]

theorem instantiateArgs_renameArgs {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S} (rho : Ren S Γ Δ)
      (args : Args (withMetas S M) as Γ),
      instantiateArgs body (renameArgs (S := withMetas S M) rho args)
        = renameArgs (S := S) rho (instantiateArgs body args)
  | _, _, _, _, .nil => rfl
  | _, _, _, rho, .cons (bs := bs) head tail => by
      simp only [renameArgs, instantiateArgs,
        instantiateArgs_renameArgs body rho tail]
      congr 1
      exact instantiate_rename body (liftRen rho bs) head
end

omit opDec in
/-- And it leaves a slot's own bound variables alone. -/
theorem instantiateArgs_prefixArgs {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    ∀ (bs : List S.Srt) {Γ : Ctx S},
      instantiateArgs body (prefixArgs (T := withMetas S M) (Γ := Γ) bs)
        = prefixArgs (T := S) (Γ := Γ) bs
  | [], _ => rfl
  | _ :: rest, _ => by
      simp only [prefixArgs, instantiateArgs, instantiate, instantiateArgs_renameArgs,
        instantiateArgs_prefixArgs body rest]

section SchemaMatching

variable [DecidableEq S.Srt] {M : List (MetaArity S)}

/-! ## Matching a schema -/

/-- Move an argument list along an equality of arities. -/
def castArgsArity {T : Signature} {as bs : List (List T.Srt × T.Srt)} (h : as = bs)
    {Γ : Ctx T} (a : Args T as Γ) : Args T bs Γ := h ▸ a

/-- Move a term along an equality of contexts. -/
def castTermCtx {T : Signature} {Γ Δ : Ctx T} (h : Γ = Δ) {s : T.Srt}
    (t : Term T Γ s) : Term T Δ s := h ▸ t

end SchemaMatching

/-! ## Coherence of explicit context transports -/

omit opDec in
theorem termSize_castTermCtx {Γ Δ : Ctx S} (h : Γ = Δ) {s : S.Srt} (t : Term S Γ s) :
    termSize (castTermCtx h t) = termSize t := by cases h; rfl

omit opDec in
theorem argsSize_castArgsArity {as bs : List (List S.Srt × S.Srt)} (h : as = bs)
    {Γ : Ctx S} (args : Args S as Γ) : argsSize (castArgsArity h args) = argsSize args := by
  cases h; rfl

omit opDec in
theorem instantiate_castTermCtx {M : List (MetaArity S)}
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {Γ Δ : Ctx S} (h : Γ = Δ) {s : S.Srt} (t : Term (withMetas S M) Γ s) :
    instantiate body (castTermCtx (T := withMetas S M) h t) = castTermCtx h (instantiate body t) := by
  cases h; rfl

omit opDec in
theorem castTermCtx_var {Γ Δ : Ctx S} (h : Γ = Δ) {s : S.Srt} (v : Var Γ s) :
    castTermCtx h (Term.var (S := S) v) = Term.var (h ▸ v) := by cases h; rfl

omit opDec in
theorem castTermCtx_weaken {Γ Δ : Ctx S} (h : Γ = Δ) {s b : S.Srt} (t : Term S Γ s) :
    castTermCtx (congrArg (List.cons b) h) (weaken t) = weaken (castTermCtx h t) := by
  cases h; rfl

omit opDec in
theorem eqRec_var_zero {Γ Δ : Ctx S} (h : Γ = Δ) (b : S.Srt) :
    (congrArg (List.cons b) h) ▸ (Var.zero : Var (b :: Γ) b) =
      (Var.zero : Var (b :: Δ) b) := by cases h; rfl

omit opDec in
theorem eqRec_var_succ {Γ Δ : Ctx S} (h : Γ = Δ) {s b : S.Srt} (v : Var Γ s) :
    (congrArg (List.cons b) h) ▸ (Var.succ v) = Var.succ (t := b) (h ▸ v) := by
  cases h; rfl

omit opDec in
/-- Lifting by two binder lists agrees with lifting by their concatenation,
with parentheses transported explicitly and no variable permutation. -/
theorem liftSub_append {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) :
    ∀ (bs β : Ctx S) (s : S.Srt) (v : Var (bs ++ (β ++ Γ)) s),
      liftSub sigma (bs ++ β) s ((List.append_assoc bs β Γ).symm ▸ v) =
        castTermCtx (List.append_assoc bs β Δ).symm
          (liftSub (liftSub sigma β) bs s v)
  | [], _, _, _ => rfl
  | b :: bs, β, s, v => by
      cases v with
      | zero =>
          change liftSub sigma (b :: (bs ++ β)) b
            (((congrArg (List.cons b) (List.append_assoc bs β Γ).symm) ▸
              (Var.zero : Var (b :: (bs ++ (β ++ Γ))) b)) : Var (b :: ((bs ++ β) ++ Γ)) b) = _
          rw [eqRec_var_zero (S := S) (List.append_assoc bs β Γ).symm b]
          change Term.var Var.zero = castTermCtx
            (congrArg (List.cons b) (List.append_assoc bs β Δ).symm) (Term.var Var.zero)
          rw [castTermCtx_var,
            eqRec_var_zero (S := S) (List.append_assoc bs β Δ).symm b]
      | succ w =>
          change liftSub sigma (b :: (bs ++ β)) s
            (((congrArg (List.cons b) (List.append_assoc bs β Γ).symm) ▸
              (Var.succ w : Var (b :: (bs ++ (β ++ Γ))) s)) : Var (b :: ((bs ++ β) ++ Γ)) s) = _
          rw [eqRec_var_succ (S := S) (List.append_assoc bs β Γ).symm w]
          change weaken (liftSub sigma (bs ++ β) s ((List.append_assoc bs β Γ).symm ▸ w)) =
            castTermCtx (congrArg (List.cons b) (List.append_assoc bs β Δ).symm)
              (weaken (liftSub (liftSub sigma β) bs s w))
          rw [liftSub_append sigma bs β s w, castTermCtx_weaken]

omit opDec in
theorem bind_castTermCtx {Γ Γ' Δ Δ' : Ctx S} (h : Γ = Γ') (k : Δ = Δ')
    (sigma : Sub S Γ Δ) {s : S.Srt} (t : Term S Γ s) :
    bind (fun sort v => castTermCtx k (sigma sort (h.symm ▸ v))) (castTermCtx h t) =
      castTermCtx k (bind sigma t) := by
  cases h; cases k; rfl

omit opDec in
theorem bind_liftSub_append {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) (bs β : Ctx S)
    {s : S.Srt} (t : Term S (bs ++ (β ++ Γ)) s) :
    bind (liftSub sigma (bs ++ β)) (castTermCtx (List.append_assoc bs β Γ).symm t) =
      castTermCtx (List.append_assoc bs β Δ).symm (bind (liftSub (liftSub sigma β) bs) t) := by
  have equality : liftSub sigma (bs ++ β) = fun sort v =>
      castTermCtx (List.append_assoc bs β Δ).symm
        (liftSub (liftSub sigma β) bs sort (List.append_assoc bs β Γ ▸ v)) := by
    funext sort v
    have h := liftSub_append sigma bs β sort (List.append_assoc bs β Γ ▸ v)
    have cancel : ∀ {Ξ Ξ' : Ctx S} (e : Ξ = Ξ') (w : Var Ξ sort), e.symm ▸ (e ▸ w) = w := by
      intro Ξ Ξ' e w
      cases e
      rfl
    simpa only [cancel] using h
  rw [equality]
  exact bind_castTermCtx _ _ _ t

omit opDec in
theorem castTermCtx_injective {Γ Δ : Ctx S} (h : Γ = Δ) {s : S.Srt} :
    Function.Injective (castTermCtx (T := S) (s := s) h) := by
  cases h
  intro left right equality
  exact equality

omit opDec in
theorem liftSub_injPrefix {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) :
    ∀ (bs : Ctx S) {s : S.Srt} (v : Var bs s),
      liftSub sigma bs s (injPrefix (Γ := Γ) bs v) =
        Term.var (injPrefix (Γ := Δ) bs v)
  | [], _, v => nomatch v
  | _ :: _, _, .zero => rfl
  | _ :: bs, _, .succ v => by
      simp only [injPrefix, liftSub, liftSub_injPrefix sigma bs v, weaken, rename]

end Mettapedia.OSLF.Binding
