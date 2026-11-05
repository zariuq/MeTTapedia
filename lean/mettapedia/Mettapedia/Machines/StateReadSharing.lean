import Mathlib.Tactic

/-!
# Reads of one stored term share its variables

PeTTa's named state keeps one stored term (a write keeps a copy with fresh
variables, as `nb_setval/2` copies its term), and every read answers that one
term (as `nb_getval/2` does), so two reads share its variables: binding a
variable through one read binds it in the other.

A compiled reader keeps its own variables (cells) and imports each host term
by a renaming of the host's variables into cells.  If each read is imported
with a renaming of its own, a variable of the stored term becomes two cells,
and a binding made through one read is not seen through the other.  If every
read uses one renaming, the reads are one term and share every binding.

The model: terms over variables, symbols and binary applications; a read's
image `rename ρ t`; a binding of cells `θ`, applied by `subst`.  This file
proves:
* `reads_share_of_agree`: imports whose renamings agree on the stored term's
  variables give equal reads, so every binding acts on them alike;
* `reads_share_iff`: imports preserve, for every binding, the equality of
  the two reads of every stored term exactly when their renamings agree on
  every variable;
* `fresh_reads_lose_binding`: two reads of `(g $z)` imported with different
  cells, the first unified with `(g 1)`: the second still holds an unbound
  cell, where the shared reading answers `(g 1)`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StateReadSharing

/-- Terms: variables, symbols, and binary applications. -/
inductive Tm
  | var (x : Nat)
  | sym (s : Nat)
  | app (a b : Tm)
  deriving DecidableEq

/-- Importing a host term: each host variable becomes the cell `ρ x`. -/
def rename (ρ : Nat → Nat) : Tm → Tm
  | .var x => .var (ρ x)
  | .sym s => .sym s
  | .app a b => .app (rename ρ a) (rename ρ b)

/-- A binding of cells, applied to a term. -/
def subst (θ : Nat → Tm) : Tm → Tm
  | .var x => θ x
  | .sym s => .sym s
  | .app a b => .app (subst θ a) (subst θ b)

/-- The variables of a term. -/
def vars : Tm → List Nat
  | .var x => [x]
  | .sym _ => []
  | .app a b => vars a ++ vars b

theorem rename_congr (ρ₁ ρ₂ : Nat → Nat) (t : Tm)
    (h : ∀ x ∈ vars t, ρ₁ x = ρ₂ x) : rename ρ₁ t = rename ρ₂ t := by
  induction t with
  | var x => simp [rename, h x (by simp [vars])]
  | sym s => rfl
  | app a b iha ihb =>
      simp only [rename]
      rw [iha (fun x hx => h x (by simp [vars, hx])),
          ihb (fun x hx => h x (by simp [vars, hx]))]

/-- Imports agreeing on the stored term's variables give one term, which
every binding acts on alike. -/
theorem reads_share_of_agree (ρ₁ ρ₂ : Nat → Nat) (t : Tm)
    (h : ∀ x ∈ vars t, ρ₁ x = ρ₂ x) (θ : Nat → Tm) :
    subst θ (rename ρ₁ t) = subst θ (rename ρ₂ t) := by
  rw [rename_congr ρ₁ ρ₂ t h]

/-- Every binding acts alike on the two reads of every stored term exactly
when the two imports send every variable to one cell. -/
theorem reads_share_iff (ρ₁ ρ₂ : Nat → Nat) :
    (∀ (t : Tm) (θ : Nat → Tm),
        subst θ (rename ρ₁ t) = subst θ (rename ρ₂ t)) ↔
      ∀ x, ρ₁ x = ρ₂ x := by
  constructor
  · intro h x
    have := h (.var x) Tm.var
    simpa [rename, subst] using this
  · intro h t θ
    exact reads_share_of_agree ρ₁ ρ₂ t (fun x _ => h x) θ

/-- The stored term `(g $z)`, with `g` the symbol 7 and `$z` the variable 0. -/
def stored : Tm := .app (.sym 7) (.var 0)

/-- Two reads imported with cells 1 and 2 for `$z`; unifying the first with
`(g 1)` binds cell 1 to the symbol 1.  The second read still holds its
unbound cell 2, where reads sharing one cell answer `(g 1)`. -/
theorem fresh_reads_lose_binding :
    let θ : Nat → Tm := fun c => if c = 1 then .sym 1 else .var c
    subst θ (rename (fun _ => 1) stored) = .app (.sym 7) (.sym 1) ∧
    subst θ (rename (fun _ => 2) stored) = .app (.sym 7) (.var 2) ∧
    subst θ (rename (fun _ => 1) stored) ≠ subst θ (rename (fun _ => 2) stored) := by
  simp [stored, rename, subst]

end Mettapedia.Machines.StateReadSharing
