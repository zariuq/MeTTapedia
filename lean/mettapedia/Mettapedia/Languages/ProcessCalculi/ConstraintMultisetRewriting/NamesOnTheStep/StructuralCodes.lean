import Mathlib.Data.Finset.Basic

/-!
# Structural codes: computed from terms, never issued

A name position holds one of two sorts of atom.

* A **generative name** (`Expr.name`) is meaningful only once a firing has issued it.
* A **structural code** (`Expr.code`) is computed from a term: `quote e` is the code of `e`, and
  `unquote` reads a code back. Its identity is the identity of the term, as with hash-consed terms
  or Gödel numbers, and no firing issues it.

The two sorts are different constructors, so they never collide: no side condition is needed
(`quote_ne_name`). Comparing modulo an equivalence of terms keeps them apart by the definition of
`NameEquiv`, which relates a name only to itself (`not_nameEquiv_name_quote` records that design
choice).

## Laws

* `quote_injective`, `quote_eq_quote_iff`: **equality of codes is equality of terms**.
* `unquote_quote`, `unquote_eq_some_iff`: unquote is the inverse of quote on codes, and the codes are
  exactly the image of quote; `unquote_name`: a generative name is the code of nothing.
* `support_quote`: a code mentions exactly the generative names of its term, so quoting needs no more
  issuing than the term itself, and the code of a closed term needs none (`support_quote_closed`).
* `unquote_support`: **unquoting forges no name**: the term read back mentions only names the code
  mentioned.

## Modulo a structural congruence

A hosted calculus may identify terms up to an equivalence `R`, as rho identifies processes up to
structural congruence and quoted processes up to the induced name equivalence. `NameEquiv R` is that
equivalence on name positions: a generative name is equivalent only to itself, a code to the codes
of `R`-equivalent terms. Then codes are equivalent exactly when their terms are
(`nameEquiv_quote_iff`), and no generative name is equivalent to any code, whatever `R` is
(`not_nameEquiv_name_quote`). Rho's name-eta equation `@*x = x` is an equation of the hosted
calculus between a code and a name variable; it is not part of this equivalence.

## Controls

`Controls.name_zero_is_not_code_zero` (the name `0` is not the code of the constant `0`);
`Controls.code_reads_back`, `Controls.constant_is_not_a_code`; and
`Controls.opaque_code_forges_a_name`: a code whose support is not its term's support lets unquote
produce a generative name the code did not mention. Carrying the support is necessary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep

/-- Terms with two sorts of atom. -/
inductive Expr where
  /-- A constant of the signature: structural, needs no issuing. -/
  | sym (k : ℕ)
  /-- Application. -/
  | app (f a : Expr)
  /-- A generative name: meaningful only once a firing has issued it. -/
  | name (n : ℕ)
  /-- The structural code of a term: computed from the term, never issued. -/
  | code (e : Expr)
  deriving DecidableEq

namespace Expr

/-- The generative names a term mentions: its support. -/
def support : Expr → Finset ℕ
  | sym _ => ∅
  | app f a => f.support ∪ a.support
  | name n => {n}
  | code e => e.support

@[simp] theorem support_sym (k : ℕ) : (sym k).support = ∅ := rfl
@[simp] theorem support_app (f a : Expr) : (app f a).support = f.support ∪ a.support := rfl
@[simp] theorem support_name (n : ℕ) : (name n).support = {n} := rfl
@[simp] theorem support_code (e : Expr) : (code e).support = e.support := rfl

/-- The generative names a term mentions, as a set. -/
def names (e : Expr) : Set ℕ := ↑e.support

@[simp] theorem mem_names {e : Expr} {n : ℕ} : n ∈ e.names ↔ n ∈ e.support := Finset.mem_coe

end Expr

open Expr

/-- **Quote**: the structural code of a term. -/
def quote (e : Expr) : Expr := .code e

/-- **Unquote**: read a code back; anything else is the code of nothing. -/
def unquote : Expr → Option Expr
  | .code e => some e
  | _ => none

theorem quote_injective : Function.Injective quote := fun _ _ same => Expr.code.inj same

/-- **Equality of codes is equality of terms.** -/
theorem quote_eq_quote_iff {e e' : Expr} : quote e = quote e' ↔ e = e' :=
  quote_injective.eq_iff

theorem unquote_quote (e : Expr) : unquote (quote e) = some e := rfl

/-- The codes are exactly the image of quote, and unquote inverts it there. -/
theorem unquote_eq_some_iff {a e : Expr} : unquote a = some e ↔ a = quote e := by
  cases a <;> simp [unquote, quote]

/-- **Codes and generative names never collide**: by construction. -/
theorem quote_ne_name (e : Expr) (n : ℕ) : quote e ≠ .name n := by simp [quote]

/-- A generative name is the code of nothing. -/
theorem unquote_name (n : ℕ) : unquote (.name n) = none := rfl

/-- **A code mentions exactly the generative names of its term.** -/
theorem support_quote (e : Expr) : (quote e).support = e.support := rfl

/-- The code of a closed term needs no issuing. -/
theorem support_quote_closed {e : Expr} (closed : e.support = ∅) : (quote e).support = ∅ := closed

/-- **Unquoting forges no name**: the term read back mentions only what the code mentioned. -/
theorem unquote_support {a e : Expr} (read : unquote a = some e) : e.support ⊆ a.support := by
  rw [unquote_eq_some_iff.mp read]
  exact subset_of_eq rfl

/-! ## Modulo an equivalence of terms -/

/-- Equality at a name position modulo an equivalence `R` of terms: a generative name equals only
itself, and a code equals the codes of `R`-equivalent terms. -/
def NameEquiv (R : Expr → Expr → Prop) : Expr → Expr → Prop
  | .name n, .name m => n = m
  | .code e, .code e' => R e e'
  | _, _ => False

theorem nameEquiv_quote_iff (R : Expr → Expr → Prop) (e e' : Expr) :
    NameEquiv R (quote e) (quote e') ↔ R e e' := Iff.rfl

theorem nameEquiv_name_iff (R : Expr → Expr → Prop) (n m : ℕ) :
    NameEquiv R (.name n) (.name m) ↔ n = m := Iff.rfl

/-- **By the definition of `NameEquiv`, no generative name is equivalent to a code**, whatever
equivalence of terms is used. This records a design choice, that an equivalence of terms acts only
on codes; it is not a property derived from the equivalence. -/
theorem not_nameEquiv_name_quote (R : Expr → Expr → Prop) (n : ℕ) (e : Expr) :
    ¬ NameEquiv R (.name n) (quote e) ∧ ¬ NameEquiv R (quote e) (.name n) :=
  ⟨fun equivalent => equivalent, fun equivalent => equivalent⟩

/-- On name positions, `NameEquiv R` is an equivalence whenever `R` is. -/
theorem nameEquiv_symm {R : Expr → Expr → Prop} (symm : ∀ {e e'}, R e e' → R e' e) :
    ∀ {a b : Expr}, NameEquiv R a b → NameEquiv R b a
  | .name _, .name _, same => Eq.symm same
  | .code _, .code _, related => symm related
  | .name _, .code _, impossible => False.elim impossible
  | .code _, .name _, impossible => False.elim impossible
  | .sym _, _, impossible => False.elim impossible
  | .app _ _, _, impossible => False.elim impossible
  | .name _, .sym _, impossible => False.elim impossible
  | .name _, .app _ _, impossible => False.elim impossible
  | .code _, .sym _, impossible => False.elim impossible
  | .code _, .app _ _, impossible => False.elim impossible

theorem nameEquiv_trans {R : Expr → Expr → Prop} (trans : ∀ {e e' e''}, R e e' → R e' e'' → R e e'') :
    ∀ {a b c : Expr}, NameEquiv R a b → NameEquiv R b c → NameEquiv R a c
  | .name _, .name _, .name _, first, second => Eq.trans first second
  | .code _, .code _, .code _, first, second => trans first second
  | .name _, .name _, .code _, _, impossible => False.elim impossible
  | .code _, .code _, .name _, _, impossible => False.elim impossible
  | .name _, .code _, _, impossible, _ => False.elim impossible
  | .code _, .name _, _, impossible, _ => False.elim impossible
  | .name _, .name _, .sym _, _, impossible => False.elim impossible
  | .name _, .name _, .app _ _, _, impossible => False.elim impossible
  | .code _, .code _, .sym _, _, impossible => False.elim impossible
  | .code _, .code _, .app _ _, _, impossible => False.elim impossible
  | .name _, .sym _, _, impossible, _ => False.elim impossible
  | .name _, .app _ _, _, impossible, _ => False.elim impossible
  | .code _, .sym _, _, impossible, _ => False.elim impossible
  | .code _, .app _ _, _, impossible, _ => False.elim impossible
  | .sym _, _, _, impossible, _ => False.elim impossible
  | .app _ _, _, _, impossible, _ => False.elim impossible

namespace Controls

/-- The name `0` is not the code of the constant `0`, and not the constant `0` itself. -/
theorem name_zero_is_not_code_zero :
    (Expr.name 0 ≠ quote (.sym 0)) ∧ (Expr.name 0 ≠ .sym 0) := by decide

/-- A code reads back its term, names inside included. -/
theorem code_reads_back :
    unquote (quote (.app (.sym 1) (.name 2))) = some (.app (.sym 1) (.name 2)) ∧
      (quote (.app (.sym 1) (.name 2))).support = {2} := by
  refine ⟨rfl, ?_⟩
  simp [quote]

/-- A constant is a structural atom but not the code of a term; a name is neither. -/
theorem constant_is_not_a_code : unquote (.sym 3) = none ∧ unquote (.name 3) = none := ⟨rfl, rfl⟩

/-- A reading of codes that does not carry their terms' support: the constant `7` read back as the
generative name `7`. -/
def opaqueUnquote : Expr → Option Expr
  | .sym k => some (.name k)
  | _ => none

/-- **Control.** Such a reading forges a generative name its code did not mention. -/
theorem opaque_code_forges_a_name :
    opaqueUnquote (.sym 7) = some (.name 7) ∧ (Expr.sym 7).support = ∅ ∧ 7 ∈ (Expr.name 7).support := by
  refine ⟨rfl, rfl, ?_⟩
  simp

/-- Modulo the equivalence that identifies every pair of terms, all codes are equivalent, and still
no name is equivalent to a code. -/
theorem total_equivalence_keeps_names_apart :
    NameEquiv (fun _ _ => True) (quote (.sym 0)) (quote (.name 5)) ∧
      ¬ NameEquiv (fun _ _ => True) (.name 5) (quote (.name 5)) :=
  ⟨trivial, fun equivalent => equivalent⟩

end Controls

#print axioms quote_eq_quote_iff
#print axioms unquote_eq_some_iff
#print axioms quote_ne_name
#print axioms support_quote
#print axioms unquote_support
#print axioms not_nameEquiv_name_quote
#print axioms nameEquiv_trans
#print axioms Controls.opaque_code_forges_a_name

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep
