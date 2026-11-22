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

end Mettapedia.Languages.Lean.Declarations.TermControls
