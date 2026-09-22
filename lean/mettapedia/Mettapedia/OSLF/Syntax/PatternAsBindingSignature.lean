import Mettapedia.OSLF.Syntax.BindingSignature
import Mettapedia.OSLF.MeTTaIL.ScopedSyntax

/-!
# The pattern language, presented as a binding signature

The language definition layer's term carrier is `Pattern`, and the scoped
refinement `Scoped n` already in the tree gives it its binding structure in the
type.  What `Scoped` does not have is the laws: renaming is declared to be a
functorial action and substitution a monoid multiplication, but neither is
proved, and the operations are written out constructor by constructor.

This module presents the same language as a binding signature, so that its laws
are instances of laws proved once for every signature rather than seven more
hand-written inductions.  Nothing here changes an existing definition.

Two facts about the presentation are read off the existing semantics rather than
chosen.  Each binder's arity is what `instantiateBVarAt` descends by: one for
`lambda`, `arity` for `multiLambda`, and -- the one that is easy to get wrong --
one for the *first* argument of `subst` and none for its second, since that
function traverses the body at `depth + 1` and the replacement at `depth`.  And
the binder annotations are carried in the operator rather than dropped, because
`Scoped` is already de Bruijn: the names are inert labels that renaming and
substitution copy unchanged, so keeping them makes the translation a bijection
and costs nothing, while dropping them would identify terms the carrier
distinguishes.

`apply` and `collection` are variadic.  An operator is any element of a type, so
they are families indexed by their length; this keeps a translated argument list
an argument list of the same shape, which is what makes erasure agree.
-/

namespace Mettapedia.OSLF.Binding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedSyntax
open Mettapedia.OSLF.MeTTaIL.Substitution

set_option autoImplicit false

namespace PatternPresentation

/-- The pattern language is untyped: one sort. -/
inductive PatSrt where
  | pat
  deriving DecidableEq

/-- One operator per term former, with the variadic ones indexed by their
length and the binder annotations carried along. -/
inductive PatOp : PatSrt → Type where
  | fvarOp (name : String) : PatOp PatSrt.pat
  | applyOp (label : String) (k : Nat) : PatOp PatSrt.pat
  | lamOp (name : Option String) : PatOp PatSrt.pat
  | multiLamOp (arity : Nat) (names : List String) : PatOp PatSrt.pat
  | substOp : PatOp PatSrt.pat
  | collOp (kind : CollType) (k : Nat) (rest : Option String) : PatOp PatSrt.pat

/-- The signature.  Binding is declared here and nowhere else. -/
abbrev patSig : Signature where
  Srt := PatSrt
  Op := PatOp
  arity := fun {_} o => match o with
    | .fvarOp _ => []
    | .applyOp _ k => List.replicate k ([], PatSrt.pat)
    | .lamOp _ => [([PatSrt.pat], PatSrt.pat)]
    | .multiLamOp ar _ => [(List.replicate ar PatSrt.pat, PatSrt.pat)]
    | .substOp => [([PatSrt.pat], PatSrt.pat), ([], PatSrt.pat)]
    | .collOp _ k _ => List.replicate k ([], PatSrt.pat)

/-- A scope of `n` levels is a context of `n` copies of the one sort. -/
abbrev ctxOf (n : Nat) : Ctx patSig := List.replicate n PatSrt.pat

theorem ctxOf_add (n k : Nat) :
    ctxOf (n + k) = List.replicate k PatSrt.pat ++ ctxOf n :=
  (congrArg (fun m => List.replicate m PatSrt.pat) (Nat.add_comm n k)).trans
    (List.replicate_add k n PatSrt.pat)

/-! ## Levels are positions -/

def varOfFin : {n : Nat} → Fin n → Var (ctxOf n) PatSrt.pat
  | 0, i => absurd i.isLt (Nat.not_lt_zero _)
  | _ + 1, ⟨0, _⟩ => Var.zero
  | _ + 1, ⟨k + 1, h⟩ => Var.succ (varOfFin ⟨k, Nat.lt_of_succ_lt_succ h⟩)

def finOfVar : (n : Nat) → Var (ctxOf n) PatSrt.pat → Fin n
  | 0, v => nomatch v
  | n + 1, v =>
      match v with
      | .zero => ⟨0, Nat.succ_pos n⟩
      | .succ w => (finOfVar n w).succ

theorem finOfVar_varOfFin : ∀ {n : Nat} (i : Fin n), finOfVar n (varOfFin i) = i
  | 0, i => absurd i.isLt (Nat.not_lt_zero _)
  | _ + 1, ⟨0, _⟩ => rfl
  | n + 1, ⟨k + 1, h⟩ => by
      show (finOfVar n (varOfFin ⟨k, _⟩)).succ = _
      rw [finOfVar_varOfFin (n := n) ⟨k, Nat.lt_of_succ_lt_succ h⟩]
      rfl

theorem varOfFin_finOfVar : ∀ (n : Nat) (v : Var (ctxOf n) PatSrt.pat),
    varOfFin (finOfVar n v) = v
  | 0, v => nomatch v
  | n + 1, v => by
      cases v with
      | zero => rfl
      | succ w =>
          show Var.succ (varOfFin (finOfVar n w)) = _
          rw [varOfFin_finOfVar n w]

/-! ## The translation -/

def lenList : {n : Nat} → ScopedList n → Nat
  | _, .nil => 0
  | _, .cons _ tl => lenList tl + 1

mutual
/-- A scoped pattern is a term of the signature. -/
def toTerm : {n : Nat} → Scoped n → Term patSig (ctxOf n) PatSrt.pat
  | _, .bvar i => Term.var (varOfFin i)
  | _, .fvar name => Term.op (S := patSig) (PatOp.fvarOp name) Args.nil
  | _, .apply label args =>
      Term.op (S := patSig) (PatOp.applyOp label (lenList args)) (toArgs args)
  | _, .lambda name body =>
      Term.op (S := patSig) (PatOp.lamOp name) (.cons (toTerm body) .nil)
  | n, .multiLambda ar names body =>
      Term.op (S := patSig) (PatOp.multiLamOp ar names)
        (.cons (castTermCtx (T := patSig) (ctxOf_add n ar) (toTerm body)) .nil)
  | _, .subst body repl =>
      Term.op (S := patSig) PatOp.substOp
        (.cons (toTerm body) (.cons (toTerm repl) .nil))
  | _, .collection kind elems rest =>
      Term.op (S := patSig) (PatOp.collOp kind (lenList elems) rest) (toArgs elems)

def toArgs : {n : Nat} → (l : ScopedList n) →
    Args patSig (List.replicate (lenList l) ([], PatSrt.pat)) (ctxOf n)
  | _, .nil => .nil
  | _, .cons hd tl => .cons (toTerm hd) (toArgs tl)
end

/-! ## Erasure back to the untyped representation

A position is a number, so erasure needs no naming environment: the binder
annotations the presentation kept are handed straight back.  Erasure forgets the
arity index, so it is transport-free except at the one context cast the
multi-binder former carries. -/

def varIndex : {Γ : Ctx patSig} → {s : PatSrt} → Var Γ s → Nat
  | _, _, .zero => 0
  | _, _, .succ w => varIndex w + 1

theorem varIndex_varOfFin : ∀ {n : Nat} (i : Fin n), varIndex (varOfFin i) = i.val
  | 0, i => absurd i.isLt (Nat.not_lt_zero _)
  | _ + 1, ⟨0, _⟩ => rfl
  | n + 1, ⟨k + 1, h⟩ => by
      show varIndex (varOfFin (⟨k, Nat.lt_of_succ_lt_succ h⟩ : Fin n)) + 1 = k + 1
      rw [varIndex_varOfFin (n := n) ⟨k, Nat.lt_of_succ_lt_succ h⟩]

mutual
def erase : {Γ : Ctx patSig} → {s : PatSrt} → Term patSig Γ s → Pattern
  | _, _, .var v => .bvar (varIndex v)
  | _, _, .op (.fvarOp name) _ => .fvar name
  | _, _, .op (.applyOp label _) args => .apply label (eraseArgs args)
  | _, _, .op (.lamOp name) (.cons body .nil) => .lambda name (erase body)
  | _, _, .op (.multiLamOp ar names) (.cons body .nil) =>
      .multiLambda ar names (erase body)
  | _, _, .op .substOp (.cons body (.cons repl .nil)) =>
      .subst (erase body) (erase repl)
  | _, _, .op (.collOp kind _ rest) args => .collection kind (eraseArgs args) rest

def eraseArgs : {as : List (List PatSrt × PatSrt)} → {Γ : Ctx patSig} →
    Args patSig as Γ → List Pattern
  | _, _, .nil => []
  | _, _, .cons hd tl => erase hd :: eraseArgs tl
end

/-- Moving a term along an equality of contexts does not change its erasure,
because a position is a number and the two contexts have the same shape. -/
theorem erase_castTermCtx {Γ Δ : Ctx patSig} (h : Γ = Δ) {s : PatSrt}
    (t : Term patSig Γ s) : erase (castTermCtx (T := patSig) h t) = erase t := by
  subst h; rfl

mutual
/-- **Erasure compatibility.**  Translating a scoped pattern into the signature
and erasing gives back exactly the pattern the existing erasure produces, so the
presentation adds structure without changing the term. -/
theorem erase_toTerm : ∀ {n : Nat} (t : Scoped n), erase (toTerm t) = toPattern t
  | _, .bvar i => by
      show Pattern.bvar (varIndex (varOfFin i)) = Pattern.bvar i.val
      rw [varIndex_varOfFin]
  | _, .fvar _ => rfl
  | _, .apply label args => by
      show Pattern.apply label (eraseArgs (toArgs args)) = _
      rw [eraseArgs_toArgs args]
      rfl
  | _, .lambda name body => by
      show Pattern.lambda name (erase (toTerm body)) = _
      rw [erase_toTerm body]
      rfl
  | n, .multiLambda ar names body => by
      show Pattern.multiLambda ar names
          (erase (castTermCtx (T := patSig) (ctxOf_add n ar) (toTerm body))) = _
      rw [erase_castTermCtx, erase_toTerm body]
      rfl
  | _, .subst body repl => by
      show Pattern.subst (erase (toTerm body)) (erase (toTerm repl)) = _
      rw [erase_toTerm body, erase_toTerm repl]
      rfl
  | _, .collection kind elems rest => by
      show Pattern.collection kind (eraseArgs (toArgs elems)) rest = _
      rw [eraseArgs_toArgs elems]
      rfl

theorem eraseArgs_toArgs : ∀ {n : Nat} (l : ScopedList n),
    eraseArgs (toArgs l) = toPatternList l
  | _, .nil => rfl
  | _, .cons hd tl => by
      show erase (toTerm hd) :: eraseArgs (toArgs tl) = _
      rw [erase_toTerm hd, eraseArgs_toArgs tl]
      rfl
end

/-! ## Well-scopedness preservation

Erasure produces a pattern well-scoped at the length of the context the term was
typed in.  Nothing is checked to obtain this: the scope is what the type said,
and erasure only reads positions off. -/

theorem varIndex_lt : ∀ {Γ : Ctx patSig} {s : PatSrt} (v : Var Γ s),
    varIndex v < Γ.length
  | _, _, .zero => Nat.succ_pos _
  | _, _, .succ w => Nat.succ_lt_succ (varIndex_lt w)

mutual
theorem erase_isWellScopedAt : ∀ {Γ : Ctx patSig} {s : PatSrt} (t : Term patSig Γ s),
    (erase t).isWellScopedAt Γ.length = true
  | _, _, .var v => by
      show decide (varIndex v < _) = true
      exact decide_eq_true (varIndex_lt v)
  | _, _, .op (.fvarOp _) _ => rfl
  | Γ, _, .op (.applyOp lbl arity) args => by
      show Pattern.isWellScopedListAt Γ.length (eraseArgs args) = true
      exact eraseArgs_isWellScopedListAt args (fun e he => by
        rw [List.eq_of_mem_replicate he])
  | Γ, _, .op (.lamOp nm) (.cons body .nil) => by
      show Pattern.isWellScopedAt (Γ.length + 1) (erase body) = true
      exact erase_isWellScopedAt body
  | Γ, _, .op (.multiLamOp ar nms) (.cons body .nil) => by
      have h : Pattern.isWellScopedAt
          (List.replicate ar PatSrt.pat ++ Γ).length (erase body) = true :=
        erase_isWellScopedAt body
      have hlen : (List.replicate ar PatSrt.pat ++ Γ).length = Γ.length + ar := by
        rw [List.length_append, List.length_replicate, Nat.add_comm]
      rw [hlen] at h
      show Pattern.isWellScopedAt (Γ.length + ar) (erase body) = true
      exact h
  | Γ, _, .op .substOp (.cons body (.cons repl .nil)) => by
      have h1 : Pattern.isWellScopedAt (Γ.length + 1) (erase body) = true :=
        erase_isWellScopedAt body
      have h2 : Pattern.isWellScopedAt Γ.length (erase repl) = true :=
        erase_isWellScopedAt repl
      show (Pattern.isWellScopedAt (Γ.length + 1) (erase body)
        && Pattern.isWellScopedAt Γ.length (erase repl)) = true
      rw [h1, h2]
      rfl
  | Γ, _, .op (.collOp knd arity rst) args => by
      show Pattern.isWellScopedListAt Γ.length (eraseArgs args) = true
      exact eraseArgs_isWellScopedListAt args (fun e he => by
        rw [List.eq_of_mem_replicate he])

theorem eraseArgs_isWellScopedListAt :
    ∀ {as : List (List PatSrt × PatSrt)} {Γ : Ctx patSig} (args : Args patSig as Γ),
      (∀ e ∈ as, e.1 = []) → Pattern.isWellScopedListAt Γ.length (eraseArgs args) = true
  | _, _, .nil, _ => rfl
  | (bs, _) :: rest, Γ, .cons hd tl, hnb => by
      have hbs : bs = [] := hnb _ List.mem_cons_self
      have h0 : Pattern.isWellScopedAt ((bs ++ Γ).length) (erase hd) = true :=
        erase_isWellScopedAt hd
      have hlen : (bs ++ Γ).length = Γ.length := by rw [hbs]; rfl
      have h1 : Pattern.isWellScopedAt Γ.length (erase hd) = true := hlen ▸ h0
      have h2 : Pattern.isWellScopedListAt Γ.length (eraseArgs tl) = true :=
        eraseArgs_isWellScopedListAt tl (fun e he => hnb e (List.mem_cons_of_mem _ he))
      show (Pattern.isWellScopedAt Γ.length (erase hd)
        && Pattern.isWellScopedListAt Γ.length (eraseArgs tl)) = true
      rw [h1, h2]
      rfl
end

/-- In particular, a closed term erases to a closed pattern. -/
theorem erase_closed {s : PatSrt} (t : Term patSig [] s) :
    (erase t).isWellScopedAt 0 = true := erase_isWellScopedAt t

/-! ## Erasure turns the signature's operations into the existing ones

Both statements below abstract over the map and characterise it by what it does
to indices.  That is what keeps them free of transports: the recursion under a
binder instantiates the characterisation at a higher cutoff rather than needing
an equation between contexts. -/

/-- A renaming shifts at cutoff `c` **by `k`** when it moves exactly the indices
at or above `c` up by `k`.

The amount is a parameter rather than fixed at one because the rule-firing path
needs an arbitrary shift: a value captured `dc` binders deep and delivered `d`
deep moves by `d - dc`.  The same shape of statement -- abstract over the
renaming and characterise it by what it does to indices -- already carries the
corresponding fact for the Megalodon term language. -/
def ShiftsAtBy {Γ Δ : Ctx patSig} (rho : Ren patSig Γ Δ) (c k : Nat) : Prop :=
  ∀ (s : PatSrt) (v : Var Γ s),
    varIndex (rho s v) = if c ≤ varIndex v then varIndex v + k else varIndex v

/-- Shifting by one: what a single weakening supplies. -/
abbrev ShiftsAt {Γ Δ : Ctx patSig} (rho : Ren patSig Γ Δ) (c : Nat) : Prop :=
  ShiftsAtBy rho c 1

theorem shiftsAtBy_succ {Γ : Ctx patSig} :
    ShiftsAtBy (fun _ v => Var.succ (Γ := Γ) (t := PatSrt.pat) v) 0 1 := by
  intro s v
  simp [varIndex]

theorem shiftsAt_succ {Γ : Ctx patSig} :
    ShiftsAt (fun _ v => Var.succ (Γ := Γ) (t := PatSrt.pat) v) 0 :=
  shiftsAtBy_succ

theorem shiftsAtBy_liftRen {Γ Δ : Ctx patSig} {rho : Ren patSig Γ Δ} {c k : Nat}
    (h : ShiftsAtBy rho c k) :
    ∀ (bs : List PatSrt), ShiftsAtBy (liftRen rho bs) (c + bs.length) k
  | [] => by exact h
  | _ :: bs => by
      intro s v
      cases v with
      | zero => simp [liftRen, varIndex]
      | succ w =>
          have ih := shiftsAtBy_liftRen h bs s w
          show varIndex (liftRen rho bs s w) + 1
            = if c + (bs.length + 1) ≤ varIndex w + 1 then varIndex w + 1 + k
              else varIndex w + 1
          rw [ih]
          by_cases hc : c + bs.length ≤ varIndex w
          · rw [if_pos hc, if_pos (show c + (bs.length + 1) ≤ varIndex w + 1 by omega)]
            omega
          · rw [if_neg hc, if_neg (show ¬ (c + (bs.length + 1) ≤ varIndex w + 1) by omega)]

theorem shiftsAt_liftRen {Γ Δ : Ctx patSig} {rho : Ren patSig Γ Δ} {c : Nat}
    (h : ShiftsAt rho c) (bs : List PatSrt) :
    ShiftsAt (liftRen rho bs) (c + bs.length) :=
  shiftsAtBy_liftRen h bs

/-- Lifting twice at the same cutoff is lifting once by the sum. -/
theorem liftBVars_liftBVars (a b : Nat) :
    ∀ (p : Pattern) (c : Nat), liftBVars c a (liftBVars c b p) = liftBVars c (a + b) p := by
  intro p
  induction p using Pattern.inductionOn with
  | hbvar n =>
      intro c
      simp only [liftBVars]
      split <;> simp only [liftBVars] <;> split <;> first | rfl | (congr 1; omega)
  | hfvar _ => intro _; simp only [liftBVars]
  | happly c' args ih =>
      intro c
      simp only [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map, List.map_map]
      refine congrArg (fun l => Pattern.apply c' l) (List.map_congr_left ?_)
      intro q hq
      exact ih q hq c
  | hlambda nm body ih => intro c; simp only [liftBVars]; rw [ih (c + 1)]
  | hmultiLambda n nms body ih => intro c; simp only [liftBVars]; rw [ih (c + n)]
  | hsubst body repl ihb ihr =>
      intro c; simp only [liftBVars]; rw [ihb (c + 1), ihr c]
  | hcollection ct elems rest ih =>
      intro c
      simp only [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map, List.map_map]
      refine congrArg (fun l => Pattern.collection ct l rest) (List.map_congr_left ?_)
      intro q hq
      exact ih q hq c

mutual
/-- **Erasure turns renaming into index shifting.** -/
theorem erase_rename_shiftBy : ∀ {Γ Δ : Ctx patSig} (rho : Ren patSig Γ Δ) (c k : Nat)
    (_ : ShiftsAtBy rho c k) {s : PatSrt} (t : Term patSig Γ s),
    erase (rename rho t) = liftBVars c k (erase t)
  | _, _, rho, c, k, h, _, .var v => by
      show Pattern.bvar (varIndex (rho _ v)) = liftBVars c k (Pattern.bvar (varIndex v))
      rw [h _ v]
      simp only [liftBVars]
      by_cases hc : c ≤ varIndex v
      · simp [hc]
      · simp [hc]
  | _, _, _, _, _, _, _, .op (.fvarOp _) _ => by simp only [rename, erase, liftBVars]
  | _, _, rho, c, amount, h, _, .op (.applyOp lbl arity) args => by
      show Pattern.apply lbl (eraseArgs (renameArgs rho args)) = _
      rw [eraseArgs_rename_shiftBy rho c amount h args (fun e he => by
        rw [List.eq_of_mem_replicate he])]
      simp only [erase, liftBVars,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  | _, _, rho, c, amount, h, _, .op (.lamOp nm) (.cons body .nil) => by
      show Pattern.lambda nm (erase (rename (liftRen rho [PatSrt.pat]) body)) = _
      rw [erase_rename_shiftBy (liftRen rho [PatSrt.pat]) (c + 1) amount
        (by simpa using shiftsAtBy_liftRen h [PatSrt.pat]) body]
      simp only [erase, liftBVars,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  | _, _, rho, c, amount, h, _, .op (.multiLamOp ar nms) (.cons body .nil) => by
      show Pattern.multiLambda ar nms
        (erase (rename (liftRen rho (List.replicate ar PatSrt.pat)) body)) = _
      rw [erase_rename_shiftBy (liftRen rho (List.replicate ar PatSrt.pat)) (c + ar) amount
        (by simpa using shiftsAtBy_liftRen h (List.replicate ar PatSrt.pat)) body]
      simp only [erase, liftBVars,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  | _, _, rho, c, amount, h, _, .op .substOp (.cons body (.cons repl .nil)) => by
      show Pattern.subst (erase (rename (liftRen rho [PatSrt.pat]) body))
        (erase (rename (liftRen rho []) repl)) = _
      rw [erase_rename_shiftBy (liftRen rho [PatSrt.pat]) (c + 1) amount
          (by simpa using shiftsAtBy_liftRen h [PatSrt.pat]) body,
        erase_rename_shiftBy (liftRen rho []) c amount (by exact h) repl]
      simp only [erase, liftBVars,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  | _, _, rho, c, amount, h, _, .op (.collOp knd arity rst) args => by
      show Pattern.collection knd (eraseArgs (renameArgs rho args)) rst = _
      rw [eraseArgs_rename_shiftBy rho c amount h args (fun e he => by
        rw [List.eq_of_mem_replicate he])]
      simp only [erase, liftBVars,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]

theorem eraseArgs_rename_shiftBy : ∀ {Γ Δ : Ctx patSig} (rho : Ren patSig Γ Δ) (c k : Nat)
    (_ : ShiftsAtBy rho c k) {as : List (List PatSrt × PatSrt)} (args : Args patSig as Γ),
    (∀ e ∈ as, e.1 = []) →
    eraseArgs (renameArgs rho args) = (eraseArgs args).map (liftBVars c k)
  | _, _, _, _, _, _, _, .nil, _ => rfl
  | _, _, rho, c, amount, h, (bs, _) :: rest, .cons hd tl, hnb => by
      have hbs : bs = [] := hnb _ List.mem_cons_self
      have hlift : ShiftsAtBy (liftRen rho bs) c amount := by
        subst hbs
        exact h
      show erase (rename (liftRen rho bs) hd) :: eraseArgs (renameArgs rho tl) = _
      rw [erase_rename_shiftBy (liftRen rho bs) c amount hlift hd,
        eraseArgs_rename_shiftBy rho c amount h tl
          (fun e he => hnb e (List.mem_cons_of_mem _ he))]
      simp only [eraseArgs, List.map_cons]
end

/-- The shift-by-one case, which a single weakening supplies. -/
theorem erase_rename_shift {Γ Δ : Ctx patSig} (rho : Ren patSig Γ Δ) (c : Nat)
    (h : ShiftsAt rho c) {s : PatSrt} (t : Term patSig Γ s) :
    erase (rename rho t) = liftBVars c 1 (erase t) :=
  erase_rename_shiftBy rho c 1 h t

/-- Ordered-list companion. -/
theorem eraseArgs_rename_shift {Γ Δ : Ctx patSig} (rho : Ren patSig Γ Δ) (c : Nat)
    (h : ShiftsAt rho c) {as : List (List PatSrt × PatSrt)} (args : Args patSig as Γ)
    (hnb : ∀ e ∈ as, e.1 = []) :
    eraseArgs (renameArgs rho args) = (eraseArgs args).map (liftBVars c 1) :=
  eraseArgs_rename_shiftBy rho c 1 h args hnb

/-! ## Erasure turns substitution into the existing binder-eliminating one

Same shape as the renaming statement: abstract over the substitution and
characterise it by what it does to indices, so the recursion under a binder
instantiates the characterisation at a higher cutoff. -/

/-- A substitution instantiates at cutoff `c` with replacement `R` when it sends
each variable where the existing binder-eliminating substitution would. -/
def InstAt {Γ Δ : Ctx patSig} (sigma : Sub patSig Γ Δ) (c : Nat) (R : Pattern) : Prop :=
  ∀ (s : PatSrt) (v : Var Γ s),
    erase (sigma s v) = instantiateBVarAt c R (Pattern.bvar (varIndex v))

theorem liftBVars_instantiateBVarAt_bvar (R : Pattern) (d n : Nat) :
    liftBVars 0 1 (instantiateBVarAt d R (Pattern.bvar n))
      = instantiateBVarAt (d + 1) R (Pattern.bvar (n + 1)) := by
  simp only [instantiateBVarAt]
  by_cases h1 : n < d
  · rw [if_pos h1, if_pos (show n + 1 < d + 1 by omega)]
    simp only [liftBVars]
    rw [if_pos (show n ≥ 0 by omega)]
  · rw [if_neg h1, if_neg (show ¬ (n + 1 < d + 1) by omega)]
    by_cases h2 : n = d
    · rw [if_pos h2, if_pos (show n + 1 = d + 1 by omega)]
      rw [liftBVars_liftBVars 1 d R 0]
      congr 1
      omega
    · rw [if_neg h2, if_neg (show ¬ (n + 1 = d + 1) by omega)]
      simp only [liftBVars]
      rw [if_pos (show n - 1 ≥ 0 by omega)]
      congr 1
      omega

theorem instAt_liftSub {Γ Δ : Ctx patSig} {sigma : Sub patSig Γ Δ} {c : Nat} {R : Pattern}
    (h : InstAt sigma c R) :
    ∀ (bs : List PatSrt), InstAt (liftSub sigma bs) (c + bs.length) R
  | [] => by exact h
  | _ :: bs => by
      intro s v
      cases v with
      | zero =>
          show Pattern.bvar 0 = instantiateBVarAt (c + (bs.length + 1)) R (Pattern.bvar 0)
          simp only [instantiateBVarAt]
          rw [if_pos (show (0 : Nat) < c + (bs.length + 1) by omega)]
      | succ w =>
          have ih := instAt_liftSub h bs s w
          show erase (weaken (liftSub sigma bs s w))
            = instantiateBVarAt (c + (bs.length + 1)) R (Pattern.bvar (varIndex w + 1))
          rw [weaken,
            erase_rename_shift (fun _ x => Var.succ x) 0 shiftsAt_succ
              (liftSub sigma bs s w),
            ih]
          rw [show c + (bs.length + 1) = (c + bs.length) + 1 by omega]
          exact liftBVars_instantiateBVarAt_bvar R (c + bs.length) (varIndex w)

mutual
/-- **Erasure turns the signature's substitution into the existing one.** -/
theorem erase_bind_inst : ∀ {Γ Δ : Ctx patSig} (sigma : Sub patSig Γ Δ) (c : Nat)
    (R : Pattern) (_ : InstAt sigma c R) {s : PatSrt} (t : Term patSig Γ s),
    erase (bind sigma t) = instantiateBVarAt c R (erase t)
  | _, _, sigma, c, R, h, _, .var v => by
      show erase (sigma _ v) = _
      rw [h _ v]
      simp only [erase]
  | _, _, _, _, _, _, _, .op (.fvarOp _) _ => by
      simp only [bind, erase, instantiateBVarAt]
  | _, _, sigma, c, R, h, _, .op (.applyOp lbl arity) args => by
      show Pattern.apply lbl (eraseArgs (bindArgs sigma args)) = _
      rw [eraseArgs_bind_inst sigma c R h args (fun e he => by
        rw [List.eq_of_mem_replicate he])]
      simp only [erase, instantiateBVarAt]
  | _, _, sigma, c, R, h, _, .op (.lamOp nm) (.cons body .nil) => by
      show Pattern.lambda nm (erase (bind (liftSub sigma [PatSrt.pat]) body)) = _
      rw [erase_bind_inst (liftSub sigma [PatSrt.pat]) (c + 1) R
        (by simpa using instAt_liftSub h [PatSrt.pat]) body]
      simp only [erase, instantiateBVarAt]
  | _, _, sigma, c, R, h, _, .op (.multiLamOp ar nms) (.cons body .nil) => by
      show Pattern.multiLambda ar nms
        (erase (bind (liftSub sigma (List.replicate ar PatSrt.pat)) body)) = _
      rw [erase_bind_inst (liftSub sigma (List.replicate ar PatSrt.pat)) (c + ar) R
        (by simpa using instAt_liftSub h (List.replicate ar PatSrt.pat)) body]
      simp only [erase, instantiateBVarAt]
  | _, _, sigma, c, R, h, _, .op .substOp (.cons body (.cons repl .nil)) => by
      show Pattern.subst (erase (bind (liftSub sigma [PatSrt.pat]) body))
        (erase (bind (liftSub sigma []) repl)) = _
      rw [erase_bind_inst (liftSub sigma [PatSrt.pat]) (c + 1) R
          (by simpa using instAt_liftSub h [PatSrt.pat]) body,
        erase_bind_inst (liftSub sigma []) c R (by exact h) repl]
      simp only [erase, instantiateBVarAt]
  | _, _, sigma, c, R, h, _, .op (.collOp knd arity rst) args => by
      show Pattern.collection knd (eraseArgs (bindArgs sigma args)) rst = _
      rw [eraseArgs_bind_inst sigma c R h args (fun e he => by
        rw [List.eq_of_mem_replicate he])]
      simp only [erase, instantiateBVarAt]

theorem eraseArgs_bind_inst : ∀ {Γ Δ : Ctx patSig} (sigma : Sub patSig Γ Δ) (c : Nat)
    (R : Pattern) (_ : InstAt sigma c R) {as : List (List PatSrt × PatSrt)}
    (args : Args patSig as Γ), (∀ e ∈ as, e.1 = []) →
    eraseArgs (bindArgs sigma args) = (eraseArgs args).map (instantiateBVarAt c R)
  | _, _, _, _, _, _, _, .nil, _ => rfl
  | _, _, sigma, c, R, h, (bs, _) :: rest, .cons hd tl, hnb => by
      have hbs : bs = [] := hnb _ List.mem_cons_self
      have hlift : InstAt (liftSub sigma bs) c R := by
        subst hbs
        exact h
      show erase (bind (liftSub sigma bs) hd) :: eraseArgs (bindArgs sigma tl) = _
      rw [erase_bind_inst (liftSub sigma bs) c R hlift hd,
        eraseArgs_bind_inst sigma c R h tl (fun e he => hnb e (List.mem_cons_of_mem _ he))]
      simp only [eraseArgs, List.map_cons]
end

/-- **Plugging, after erasure, is the existing binder-eliminating substitution** --
for every term, not only for the instances checked earlier. -/
theorem erase_bind_extend {Γ : Ctx patSig} (r : Term patSig Γ PatSrt.pat)
    {s : PatSrt} (b : Term patSig (PatSrt.pat :: Γ) s) :
    erase (bind (extend r) b) = instantiateBVar (erase r) (erase b) := by
  refine erase_bind_inst (extend r) 0 (erase r) ?_ b
  intro _ v
  cases v with
  | zero =>
      show erase r = instantiateBVarAt 0 (erase r) (Pattern.bvar 0)
      simp [instantiateBVarAt, liftBVars_zero]
  | succ w =>
      show Pattern.bvar (varIndex w)
        = instantiateBVarAt 0 (erase r) (Pattern.bvar (varIndex w + 1))
      simp [instantiateBVarAt]

end PatternPresentation

end Mettapedia.OSLF.Binding
