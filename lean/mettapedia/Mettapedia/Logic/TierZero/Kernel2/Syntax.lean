import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Patterns
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Scope

/-!
# The tier-0 kernel in Lean: terms, patterns and the generic term functions

The kernel's terms are binding trees (`SignatureIndexedABT.Term`), the meaning of the thinned
co-de-Bruijn store of `GuardedMultisetRewriting.Thinnings`. Their heads mirror MeTTa atoms one for one:

* a symbol `f` is `node (sym "f") []`; a number `3` is `node (num 3) []`;
* an expression `(a₁ … aₖ)` is `node expr [a₁, …, aₖ]`, so `(f)` and `f` stay different, as in
  MeTTa; for example `(wi ph ps)` is `node expr [wi, ph, ps]`;
* the binder form `(bind A B)` is `node bind [A, B]` with `B` under one binder, and the bound
  variable `(bv n)` is `idx n`;
* a claim's name `k` (a formal or a dummy, which the MeTTa kernel turns into a fresh name) is
  `node (fv k) [...]`: with no fields it is a plain fresh name; with fields it is a name over the
  names of the scope variables it depends on (MM0's regular variables, `Claims`; MeTTa's
  `(over X (Y …))`). Every claim variable is a name, never a bound variable `idx`: the kernel
  instantiates patterns literally, without shifting, so a claim variable placed under a binder
  must not meet that binder's bound variable.

A rule's **pattern** is a tree with pattern variables (`TreePat Head ℕ` of `Thinnings.Patterns`):
`mvar v` is the rule's `v`-th formal. Instantiation is `TreePat.inst`; matching is `matchT`, which is
sound, complete and minimal.

The generic term functions of the side conditions, on trees, all binder-correct:

* `occursAt x d t`: `x`, seen under `d` binders (`Term.lift 0 d x`), is a subterm of `t`; on a
  variable `x = idx j` it is "`j` is free in `t`" (`occursAt_idx`), which the thinned store reads
  off a reference's thinning; example: `a` occurs in `(f (g a))`, `b` does not;
* `fvsOf t`: the claim names occurring in `t` (MeTTa's `t0:filter-occurring` against the frame);
* `Term.supportedAt d t`: `t` is **locally closed** at depth `d`: every free variable is below `d`
  (`supportedAt_iff`); the store reads it off a reference's thinning;
* `abstractAt x d t`: `t` with `x` (seen under the binders) replaced by the bound variable `d`,
  other free variables at or above `d` moved up;
* `substT s t`: each key of `s` (seen under the binders) replaced by its value, top-down,
  simultaneously;
* opening a body `b` with a value `v` is `Term.instantiate v b`, which shifts `v` under the binders
  it crosses.

The MeTTa kernel-v2 computes `open`, `abstract` and `subst` without shifts, and asks the terms to be
locally closed; under those conditions the two agree, and the rules of `Rules` ask the same
conditions (`Controls`).

`render` prints a term as MeTTa source, so Lean-defined data can be run on the MeTTa kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

/-- Heads of kernel terms. -/
inductive Head where
  /-- A symbol: a judgment head, a constructor, a constant. -/
  | sym (s : String)
  /-- A number (a MeTTa grounded number). -/
  | num (n : ℕ)
  /-- A string (a MeTTa grounded string), e.g. a HOL name `"x"`. -/
  | str (s : String)
  /-- The claim's name `k`: a fresh name while the claim is checked. -/
  | fv (k : ℕ)
  /-- An expression: its fields are its elements, all at depth `0`. -/
  | expr
  /-- The binder `(bind A B)`: field `A` at depth `0`, field `B` at depth `1`. -/
  | bind
  deriving DecidableEq, Repr, Inhabited

/-- Kernel terms. -/
abbrev Tm := Term Head

/-- Rule patterns: pattern variable `v` is the rule's `v`-th formal. -/
abbrev Pat := TreePat Head ℕ

/-! ## Building terms and patterns -/

/-- Fields at depth `0`. -/
def flds : List Tm → Fields Head
  | [] => .nil
  | t :: ts => .cons 0 t (flds ts)

/-- A symbol. -/
def sym (s : String) : Tm := .node (.sym s) .nil
/-- A number. -/
def num (n : ℕ) : Tm := .node (.num n) .nil
/-- A string. -/
def str (s : String) : Tm := .node (.str s) .nil
/-- The claim's name `k` over the names `ds` of the scope variables it depends on. -/
def fvar (k : ℕ) (ds : List ℕ := []) : Tm := .node (.fv k) (flds (ds.map fun d => .node (.fv d) .nil))
/-- An expression. -/
def ex (ts : List Tm) : Tm := .node .expr (flds ts)
/-- The binder `(bind A B)`. -/
def bnd (a b : Tm) : Tm := .node .bind (.cons 0 a (.cons 1 b .nil))
/-- A judgment `(H a₁ … aₙ)`. -/
def jd (h : String) (args : List Tm) : Tm := ex (sym h :: args)

/-- Pattern fields at depth `0`. -/
def pflds : List Pat → TreePatFields Head ℕ
  | [] => .nil
  | p :: ps => .cons 0 p (pflds ps)

/-- A symbol pattern. -/
def psym (s : String) : Pat := .node (.sym s) .nil
/-- A number pattern. -/
def pnum (n : ℕ) : Pat := .node (.num n) .nil
/-- A string pattern. -/
def pstr (s : String) : Pat := .node (.str s) .nil
/-- An expression pattern. -/
def pex (ps : List Pat) : Pat := .node .expr (pflds ps)
/-- A binder pattern. -/
def pbnd (a b : Pat) : Pat := .node .bind (.cons 0 a (.cons 1 b .nil))
/-- A judgment pattern `(H p₁ … pₙ)`. -/
def pjd (h : String) (args : List Pat) : Pat := pex (psym h :: args)
/-- The `v`-th formal. -/
def pv (v : ℕ) : Pat := .mvar v

/-! ## Reading fields -/

/-- The fields of a node as a list of (depth, child). -/
def fieldsToList : Fields Head → List (ℕ × Tm)
  | .nil => []
  | .cons d t rest => (d, t) :: fieldsToList rest

/-- The judgment head of a term `(H a₁ … aₙ)`, if it is a symbol. -/
def headSym : Tm → Option String
  | .node .expr (.cons 0 (.node (.sym h) .nil) _) => some h
  | _ => none

/-- The judgment head of a pattern `(H p₁ … pₙ)`, if it is a symbol. -/
def patHeadSym : Pat → Option String
  | .node .expr (.cons 0 (.node (.sym h) .nil) _) => some h
  | _ => none

/-! ## Occurrence, binder-correct -/

mutual

/-- `x`, seen under `d` binders, is a subterm of the tree. -/
def occursAt (x : Tm) (d : ℕ) : Tm → Bool
  | .idx k => decide (Term.lift 0 d x = .idx k)
  | .node h fs => decide (Term.lift 0 d x = .node h fs) || occursFields x d fs

/-- `x` occurs in some field, under the field's binders. -/
def occursFields (x : Tm) (d : ℕ) : Fields Head → Bool
  | .nil => false
  | .cons e t rest => occursAt x (d + e) t || occursFields x d rest

end

/-- `x` occurs in `t`. -/
def occursIn (x t : Tm) : Bool := occursAt x 0 t

theorem lift_idx (d j : ℕ) : Term.lift 0 d (.idx j : Tm) = .idx (j + d) := by
  simp [Term.lift]

mutual

/-- **A variable occurs exactly where it is free.** -/
theorem occursAt_idx (j : ℕ) : ∀ (d : ℕ) (t : Tm), occursAt (.idx j) d t = freeAt t (j + d)
  | d, .idx k => by
      simp only [occursAt, lift_idx, Term.idx.injEq, freeAt_idx]
      exact decide_eq_decide.mpr ⟨fun h => h.symm, fun h => h.symm⟩
  | d, .node h fs => by
      simp only [occursAt, lift_idx, reduceCtorEq, decide_false, Bool.false_or, freeAt_node]
      exact occursFields_idx j d fs

theorem occursFields_idx (j : ℕ) : ∀ (d : ℕ) (fs : Fields Head),
    occursFields (.idx j) d fs = fieldsFreeAt fs (j + d)
  | _, .nil => by simp [occursFields]
  | d, .cons e t rest => by
      simp only [occursFields, fieldsFreeAt_cons]
      rw [occursAt_idx j (d + e) t, occursFields_idx j d rest, Nat.add_assoc]

end

theorem occursIn_idx (j : ℕ) (t : Tm) : occursIn (.idx j) t = freeAt t j := by
  have := occursAt_idx j 0 t
  rwa [Nat.add_zero] at this

/-! ## Local closedness -/

theorem supportedAt_iff (d : ℕ) (t : Tm) :
    Term.supportedAt d t = true ↔ ∀ i, freeAt t i = true → i < d :=
  Scope.supportedAt_iff d t

theorem fieldsSupportedAt_iff (d : ℕ) (fs : Fields Head) :
    Term.Fields.supportedAt d fs = true ↔ ∀ i, fieldsFreeAt fs i = true → i < d :=
  Scope.fieldsSupportedAt_iff d fs

/-- Locally closed at depth `0` is closed. -/
theorem closed_of_supportedAt_zero {t : Tm} (h : Term.supportedAt 0 t = true) : Closed t := by
  intro i
  cases e : freeAt t i with
  | false => rfl
  | true => exact absurd ((supportedAt_iff 0 t).mp h i e) (Nat.not_lt_zero _)

theorem lift_of_closed {t : Tm} (h : Closed t) (d : ℕ) : Term.lift 0 d t = t := by
  rw [lift_zero_eq_rename]; exact rename_of_closed h _

/-! ## Claim names occurring in a term -/

mutual

/-- The claim names occurring in a tree. -/
def fvsOf : Tm → List ℕ
  | .idx _ => []
  | .node (.fv k) fs => k :: fvsFields fs
  | .node (.sym _) fs => fvsFields fs
  | .node (.num _) fs => fvsFields fs
  | .node (.str _) fs => fvsFields fs
  | .node .expr fs => fvsFields fs
  | .node .bind fs => fvsFields fs

/-- The claim names occurring in some field. -/
def fvsFields : Fields Head → List ℕ
  | .nil => []
  | .cons _ t rest => fvsOf t ++ fvsFields rest

end

/-! ## Abstraction and substitution, binder-correct -/

mutual

/-- Replace the subterm `x` (seen under the binders) by the bound variable `d`, moving the free
variables at or above `d` up by one. -/
def abstractAt (x : Tm) (d : ℕ) : Tm → Tm
  | .idx k =>
      if Term.lift 0 d x = .idx k then .idx d else if k < d then .idx k else .idx (k + 1)
  | .node h fs =>
      if Term.lift 0 d x = .node h fs then .idx d else .node h (abstractFields x d fs)

/-- Abstract under each field's binders. -/
def abstractFields (x : Tm) (d : ℕ) : Fields Head → Fields Head
  | .nil => .nil
  | .cons e t rest => .cons e (abstractAt x (d + e) t) (abstractFields x d rest)

end

/-- Abstract `x` out of `t`: the body of a binder whose bound variable stands for `x`. -/
def abstractT (x t : Tm) : Tm := abstractAt x 0 t

/-- Look a term up among the keys of a substitution, under `d` binders. -/
def lookupAt (s : List (Tm × Tm)) (d : ℕ) (t : Tm) : Option Tm :=
  (s.find? fun p => decide (Term.lift 0 d p.1 = t)).map fun p => Term.lift 0 d p.2

mutual

/-- Simultaneous replacement, top-down, under the binders: a subterm that is a key (seen under the
binders) is replaced by its value (seen under the binders). -/
def substAt (s : List (Tm × Tm)) (d : ℕ) : Tm → Tm
  | .idx k => (lookupAt s d (.idx k)).getD (.idx k)
  | .node h fs =>
      match lookupAt s d (.node h fs) with
      | some v => v
      | none => .node h (substFields s d fs)

/-- Replace in each field. -/
def substFields (s : List (Tm × Tm)) (d : ℕ) : Fields Head → Fields Head
  | .nil => .nil
  | .cons e t rest => .cons e (substAt s (d + e) t) (substFields s d rest)

end

/-- Simultaneous substitution. -/
def substT (s : List (Tm × Tm)) (t : Tm) : Tm := substAt s 0 t

/-- A pair `(X T)`. -/
def pairOf : Tm → Option (Tm × Tm)
  | .node .expr (.cons 0 x (.cons 0 v .nil)) => some (x, v)
  | _ => none

/-- A substitution written as the expression `((X₁ T₁) … (Xₖ Tₖ))`. -/
def decodePairs : Tm → Option (List (Tm × Tm))
  | .node .expr fs => (fieldsToList fs).mapM fun (d, t) => if d = 0 then pairOf t else none
  | _ => none

/-- Open a binder body `b` with the value `v` (shifting `v` under the binders it crosses). -/
def openT (b v : Tm) : Tm := Term.instantiate v b

/-! ## MeTTa source -/

/-- A string as a MeTTa string literal: `"` and `\` are escaped, e.g. `a"b` prints as `"a\"b"`. -/
def quoteStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c = '"' then "\\\"" else if c = '\\' then "\\\\" else c.toString) ++ "\""

mutual

/-- A term as MeTTa source; `var k` names the claim's name `k`. -/
def render (var : ℕ → String) : Tm → String
  | .idx n => s!"(bv {n})"
  | .node (.sym s) .nil => s
  | .node (.num n) .nil => toString n
  | .node (.str s) .nil => quoteStr s
  | .node (.fv k) .nil => var k
  | .node .expr fs => "(" ++ " ".intercalate (renderFields var fs) ++ ")"
  | .node .bind fs => "(bind " ++ " ".intercalate (renderFields var fs) ++ ")"
  | .node (.sym s) fs => "(" ++ s ++ " " ++ " ".intercalate (renderFields var fs) ++ ")"
  | .node (.num n) fs => "(" ++ toString n ++ " " ++ " ".intercalate (renderFields var fs) ++ ")"
  | .node (.str s) fs => "(" ++ quoteStr s ++ " " ++ " ".intercalate (renderFields var fs) ++ ")"
  | .node (.fv k) fs => "(" ++ var k ++ " " ++ " ".intercalate (renderFields var fs) ++ ")"

/-- The fields' sources. -/
def renderFields (var : ℕ → String) : Fields Head → List String
  | .nil => []
  | .cons _ t rest => render var t :: renderFields var rest

end

mutual

/-- A pattern as MeTTa source; formal `v` is the variable `$x{v}`. -/
def renderPat : Pat → String
  | .mvar v => s!"$x{v}"
  | .idx n => s!"(bv {n})"
  | .node (.sym s) .nil => s
  | .node (.num n) .nil => toString n
  | .node (.str s) .nil => quoteStr s
  | .node (.fv k) .nil => s!"fv{k}"
  | .node .expr fs => "(" ++ " ".intercalate (renderPatFields fs) ++ ")"
  | .node .bind fs => "(bind " ++ " ".intercalate (renderPatFields fs) ++ ")"
  | .node (.sym s) fs => "(" ++ s ++ " " ++ " ".intercalate (renderPatFields fs) ++ ")"
  | .node (.num n) fs => "(" ++ toString n ++ " " ++ " ".intercalate (renderPatFields fs) ++ ")"
  | .node (.str s) fs => "(" ++ quoteStr s ++ " " ++ " ".intercalate (renderPatFields fs) ++ ")"
  | .node (.fv k) fs => s!"(fv{k} " ++ " ".intercalate (renderPatFields fs) ++ ")"

/-- The pattern fields' sources. -/
def renderPatFields : TreePatFields Head ℕ → List String
  | .nil => []
  | .cons _ p rest => renderPat p :: renderPatFields rest

end

/-! ## Controls -/

namespace Controls

/-- `a` occurs in `(f (g a))`; `b` does not. -/
theorem occurs_positive : occursIn (sym "a") (ex [sym "f", ex [sym "g", sym "a"]]) = true := by
  decide

theorem occurs_negative : occursIn (sym "b") (ex [sym "f", ex [sym "g", sym "a"]]) = false := by
  decide

/-- Binder-correct: the variable `0` does not occur in `(bind T (bv 0))`, where `(bv 0)` is bound,
and occurs in `(bind T (bv 1))`. MeTTa's syntactic `t0:occurs?` finds `(bv 0)` in both. -/
theorem occurs_bound_negative : occursIn (.idx 0) (bnd (sym "T") (.idx 0)) = false := by decide

theorem occurs_bound_positive : occursIn (.idx 0) (bnd (sym "T") (.idx 1)) = true := by decide

/-- The claim names of `(f v0 (g v2 v0))` are `0, 2, 0`. -/
theorem fvs_example : fvsOf (ex [sym "f", fvar 0, ex [sym "g", fvar 2, fvar 0]]) = [0, 2, 0] := by
  decide

/-- Abstracting `x` from `(f x y)` gives `(f (bv 0) y)`; opening it with `z` gives `(f z y)`. -/
theorem abstract_open :
    openT (abstractT (sym "x") (ex [sym "f", sym "x", sym "y"])) (sym "z") =
      ex [sym "f", sym "z", sym "y"] := by
  decide

/-- Opening a body that sits under a binder: the closed value goes in at index `1` there. -/
theorem open_under_binder :
    openT (bnd (sym "T") (ex [sym "g", .idx 1, .idx 0])) (sym "z") =
      bnd (sym "T") (ex [sym "g", sym "z", .idx 0]) := by
  decide

/-- Binder-correct abstraction: abstracting the variable `0` from `(bind a (g (bv 0)))` leaves the
bound variable alone (MeTTa's unshifted abstraction would capture it; the rules ask `x` locally
closed). -/
theorem abstract_bound_kept :
    abstractT (.idx 0) (bnd (sym "a") (ex [sym "g", .idx 0])) = bnd (sym "a") (ex [sym "g", .idx 0]) := by
  decide

/-- Substitution replaces keys top-down, simultaneously: `x ↦ y, y ↦ x` swaps. -/
theorem subst_swaps :
    substT [(sym "x", sym "y"), (sym "y", sym "x")] (ex [sym "f", sym "x", sym "y"]) =
      ex [sym "f", sym "y", sym "x"] := by
  decide

/-- `(f (bv 0))` is not locally closed at depth `0`, and is at depth `1`. -/
theorem lc_example :
    Term.supportedAt 0 (ex [sym "f", .idx 0]) = false ∧ Term.supportedAt 1 (ex [sym "f", .idx 0]) = true := by
  decide

/-- The MeTTa source of `(bind T (g (bv 0) v1))`, and of a name over the scope variable `2`. -/
theorem render_example :
    render (fun k => s!"$v{k}") (bnd (sym "T") (ex [sym "g", .idx 0, fvar 1])) =
      "(bind T (g (bv 0) $v1))" ∧ render (fun k => s!"n{k}") (fvar 3 [2]) = "(n3 n2)" := by
  decide

end Controls

end Mettapedia.Logic.TierZero.Kernel2
