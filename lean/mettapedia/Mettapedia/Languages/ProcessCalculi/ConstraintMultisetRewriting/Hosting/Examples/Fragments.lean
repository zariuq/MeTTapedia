import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Correspondence

/-!
# Which elaborated programs lie in the first fragment

The first fragment (`PlainComp`) has `ret`, `apply`, `choice`, `fail`. The elaboration of surface text
(`Elaboration.elabText`, `elabArgs`) puts an arrow `let_` on every argument passed by value (even a
variable or a symbol), and makes a variable passed by name a `run`. So:

* by value (no declarations), `(= (double $x) (add $x $x))` elaborates to two arrows
  (`double_byValue`), outside the first fragment (`double_byValue_outside`);
* by name, the base case `(= (add Z $y) $y)` elaborates to `run $y` (`addZero_byName`), outside every
  fragment of the hosting theorem;
* with every parameter declared `Atom` (held), results `%Undefined%` and held text staying data, the
  Peano program with `double` lies in the first fragment (`arith_held`, `arith_plain`, `query_plain`);
* in that reading a call inside a constructor is passed as text and never run: `len`'s recursive case
  elaborates to the single call `(S (len $t))` (`len_held`), so the held `len` does not compute a
  length; by value the same equation needs arrows (`len_byValue`, `len_byValue_outside`), which is the
  fragment with `let` (`Examples.UserPrograms`, `Examples.Recursion`).

A call through a function variable, `($f …)`, has an elaboration clause of its own (a tuple whose head
is not a symbol); programs whose text contains one are not among these examples.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.Fragments

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit

/-- By value at every undeclared position; held text stays data; held results returned as written. -/
def byValue : Params := ⟨fun _ _ => .value, false, false⟩

/-- By name at every undeclared position. -/
def byName : Params := ⟨fun _ _ => .name, false, false⟩

/-! ## The program -/

def yZ : MData := foD [] [200] 0
def xS : MData := foD [] [201] 0
def yS : MData := foD [] [201] 1
def xd : MData := foD [] [202] 0

/-- `(= (add Z $y) $y)` -/
def addZS : SEquation := ⟨[200], "add", [sym "Z", yZ], .text yZ⟩
/-- `(= (add (S $x) $y) (add $x (S $y)))` -/
def addSS : SEquation := ⟨[201], "add", [tuple [sym "S", xS], yS], .text (tuple [sym "add", xS, tuple [sym "S", yS]])⟩
/-- `(= (double $x) (add $x $x))` -/
def doubleS : SEquation := ⟨[202], "double", [xd], .text (tuple [sym "add", xd, xd])⟩

/-! ## By value: every argument gets an arrow -/

theorem double_byValue :
    (elabEquation byValue [] doubleS).rhs =
      .let_ [1, 202, 0] (slot [1, 202, 0]) (.ret xd)
        (.let_ [1, 202, 1] (slot [1, 202, 1]) (.ret xd)
          (.apply (tuple [sym "add", slot [1, 202, 0], slot [1, 202, 1]]))) := rfl

theorem double_byValue_outside : ¬ PlainComp (elabEquation byValue [] doubleS).rhs := by
  rw [double_byValue]
  exact id

/-! ## By name: a variable at a value position is run -/

theorem addZero_byName : (elabEquation byName [] addZS).rhs = .run yZ := rfl

theorem addZero_byName_outside : ¬ PlainComp (elabEquation byName [] addZS).rhs := by
  rw [addZero_byName]
  exact id

/-! ## Every parameter held: the first fragment -/

def heldDecls : List Decl :=
  [⟨"add", [.atom, .atom], .undefined⟩, ⟨"double", [.atom], .undefined⟩, ⟨"S", [.atom], .undefined⟩,
   ⟨"len", [.atom], .undefined⟩]

def arith : SProgram := ⟨heldDecls, [addZS, addSS, doubleS]⟩

theorem arith_held :
    (elaborate byValue arith).equations =
      [⟨[200], tuple [sym "add", sym "Z", yZ], .ret yZ⟩,
       ⟨[201], tuple [sym "add", tuple [sym "S", xS], yS], .apply (tuple [sym "add", xS, tuple [sym "S", yS]])⟩,
       ⟨[202], tuple [sym "double", xd], .apply (tuple [sym "add", xd, xd])⟩] := rfl

theorem arith_plain : PlainProgram (elaborate byValue arith) := by
  intro e member
  rw [arith_held] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> trivial

def two : MData := tuple [sym "S", tuple [sym "S", sym "Z"]]

theorem query_held :
    elabQuery byValue arith (.text (tuple [sym "double", two])) = .apply (tuple [sym "double", two]) := rfl

theorem query_plain : PlainComp (elabQuery byValue arith (.text (tuple [sym "double", two]))) := by
  rw [query_held]
  trivial

/-! ## A recursive function that uses its own result -/

def hL : MData := foD [] [204] 0
def tL : MData := foD [] [204] 1

/-- `(= (len (Cons $h $t)) (S (len $t)))` -/
def lenConsS : SEquation :=
  ⟨[204], "len", [tuple [sym "Cons", hL, tL]], .text (tuple [sym "S", tuple [sym "len", tL]])⟩

/-- Held: one call of `S` on the text `(len $t)`; the recursive call is never run. -/
theorem len_held :
    (elabEquation byValue heldDecls lenConsS).rhs = .apply (tuple [sym "S", tuple [sym "len", tL]]) := rfl

theorem len_held_plain : PlainComp (elabEquation byValue heldDecls lenConsS).rhs := by
  rw [len_held]
  trivial

/-- By value the recursive call is computed first, under an arrow. -/
theorem len_byValue :
    (elabEquation byValue [] lenConsS).rhs =
      .let_ [1, 204, 0] (slot [1, 204, 0])
        (.let_ [1, 204, 0, 0] (slot [1, 204, 0, 0]) (.ret tL)
          (.apply (tuple [sym "len", slot [1, 204, 0, 0]])))
        (.apply (tuple [sym "S", slot [1, 204, 0]])) := rfl

theorem len_byValue_outside : ¬ PlainComp (elabEquation byValue [] lenConsS).rhs := by
  rw [len_byValue]
  exact id

#print axioms double_byValue_outside
#print axioms addZero_byName_outside
#print axioms arith_plain
#print axioms query_plain
#print axioms len_held_plain
#print axioms len_byValue_outside

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.Fragments
