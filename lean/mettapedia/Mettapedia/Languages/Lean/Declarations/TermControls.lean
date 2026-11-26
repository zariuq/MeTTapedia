import Mettapedia.Languages.Lean.Declarations.Terms

/-!
# Controls for reading Lean terms

A family's constructor index, which Lean generates with the family, is read as
the case analysis it abbreviates: for an enumeration, for a recursive family
and for a family with parameters.  A definition that only shares the name is
read as itself.
-/

set_option autoImplicit false

open Lean Elab Term

namespace Mettapedia.Languages.Lean.Declarations.TermControls

/-- The atom that `readTerm` gives a closed term. -/
scoped elab "read_term% " t:term : term => do
  let e ← withSynthesize <| elabTerm t none
  match ← (readTerm {} (← instantiateMVars e)).run with
  | .ok f => return toExpr f.atom
  | .error reason => throwError reason

theorem bool_ctor_index_read :
    (read_term% (fun x : Bool => Bool.ctorIdx x)) =
      "(lam v_x (app Bool ()) (app Bool.casesOn ((lam v_x1 (app Bool ()) (app Nat ())) (var v_x) (num 0) (num 1))))" :=
  rfl

theorem nat_ctor_index_read :
    (read_term% (fun n : Nat => Nat.ctorIdx n)) =
      "(lam v_n (app Nat ()) (app Nat.casesOn ((lam v_x (app Nat ()) (app Nat ())) (var v_n) (num 0) (lam v_x1 (app Nat ()) (num 1)))))" :=
  rfl

theorem list_ctor_index_read :
    (read_term% (fun x : List Bool => List.ctorIdx x)) =
      "(lam v_x (app List ((app Bool ()))) (app List.casesOn ((app Bool ()) (lam v_x1 (app List ((app Bool ()))) (app Nat ())) (var v_x) (num 0) (lam v_head (app Bool ()) (lam v_tail (app List ((app Bool ()))) (num 1))))))" :=
  rfl

/-- A definition of the same last name, of no family. -/
def ctorIdx (n : Nat) : Nat := n + 7

/-- Negative: sharing the name does not make a definition a constructor index. -/
theorem same_name_kept :
    (read_term% (fun n : Nat => TermControls.ctorIdx n)) =
      "(lam v_n (app Nat ()) (app Mettapedia.Languages.Lean.Declarations.TermControls.ctorIdx ((var v_n))))" :=
  rfl

/-! ## A set reading and a reading of syntax

The same terms in both readings: a set reading refuses or erases what the Egal
interpretation does not cover, a reading of syntax reads all of it. -/

/-- The atom, with the proofs inside it, that a reading gives a closed term, or its refusal. -/
def readWith (syntaxOnly : Bool) (e : Expr) : TermElabM String :=
  withOptions (syntaxReading.set · syntaxOnly) do
    match ← (readTerm {} (← instantiateMVars e)).run with
    | .ok f => return f.atomWithProofs
    | .error reason => return s!"refused: {reason}"

scoped elab "set_read% " t:term : term => do
  return toExpr (← readWith false (← withSynthesize <| elabTerm t none))

scoped elab "syntax_read% " t:term : term => do
  return toExpr (← readWith true (← withSynthesize <| elabTerm t none))

/-- The kernel's projection `x.i`, which elaboration never writes: the term `t` projected. -/
scoped elab "kernel_proj% " S:ident i:num t:term : term => do
  return .proj S.getId i.getNat (← withSynthesize <| elabTerm t none)

/-- Negative: a set reading refuses the kernel's projection. -/
theorem projection_set_refused :
    (set_read% (fun p : Nat × Bool => kernel_proj% Prod 1 p)) =
      "refused: not a first-order application: p.2" :=
  rfl

/-- Positive: a reading of syntax reads it as the projection function applied. -/
theorem projection_syntax_read :
    (syntax_read% (fun p : Nat × Bool => kernel_proj% Prod 1 p)) =
      "(lam v_p (app Prod ((app Nat ()) (app Bool ()))) (app Prod.snd ((app Nat ()) (app Bool ()) (var v_p))))" :=
  rfl

/-- Negative: a set reading refuses a string literal. -/
theorem string_set_refused :
    (set_read% ("Proc" : String)) = "refused: a string literal, outside the set reading: \"Proc\"" :=
  rfl

/-- Positive: a reading of syntax reads it as the literal. -/
theorem string_syntax_read :
    (syntax_read% ("Proc" : String)) = "(str \"Proc\")" :=
  rfl

/-- Negative: a literal its atom cannot write as it is (a quote inside) is refused. -/
theorem string_with_quote_refused :
    (syntax_read% ("a\"b" : String)) =
      "refused: a string literal with characters its atom does not write: \"a\\\"b\"" :=
  rfl

/-- Negative: a set reading erases a proof by a constructor; it follows theorems. -/
theorem constructor_proof_set_erased :
    (set_read% (⟨3, Eq.refl 3⟩ : { n : Nat // n = 3 })) =
      "(app Subtype.mk ((app Nat ()) (lam v_n (app Nat ()) (app Eq ((app Nat ()) (var v_n) (num 3)))) (num 3) (proof)))" :=
  rfl

/-- Positive: a reading of syntax keeps it. -/
theorem constructor_proof_syntax_kept :
    (syntax_read% (⟨3, Eq.refl 3⟩ : { n : Nat // n = 3 })) =
      "(app Subtype.mk ((app Nat ()) (lam v_n (app Nat ()) (app Eq ((app Nat ()) (var v_n) (num 3)))) (num 3) (by (app Eq.refl ((app Nat ()) (num 3))))))" :=
  rfl

/-- Positive, both readings: a proof by a theorem is followed by both. -/
theorem theorem_proof_both_kept :
    (set_read% (⟨0, Nat.zero_le 0⟩ : { n : Nat // 0 ≤ n })) =
      (syntax_read% (⟨0, Nat.zero_le 0⟩ : { n : Nat // 0 ≤ n })) :=
  rfl

end Mettapedia.Languages.Lean.Declarations.TermControls
