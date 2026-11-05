import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBody

/-!
# Extraction after actual callback clause selection

The preparer uses the existing source matcher and clause selector. Exactly
one selected body is required, not exactly one authored equation globally.
Registers are read from that body's captured scalar bindings, including
bindings obtained from tuple patterns. The result theorem concerns an actual
two-variable source call whose arguments are already captured values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarInvocation

open Mettapedia.Machines.TypedScalar
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval ScalarSource ScalarBody

def decode : Atom → Option Data
  | .grounded (.int value) => some (.integer value)
  | .symbol name => some (.symbol name)
  | _ => none

theorem decode_exact (atom : Atom) (value : Data) (decoded : decode atom = some value) :
    atom = encode (kind := .data) value := by
  cases atom with
  | grounded ground =>
      cases ground <;> simp only [decode] at decoded
      all_goals cases decoded
      rfl
  | symbol name => cases decoded; rfl
  | var name => cases decoded
  | expression items => cases decoded

def register (callee : Subst) (name : String) : Option Data := (callee.lookup name).bind decode
def environment (callee : Subst) : Environment String := fun name =>
  if (register callee name).isSome then some name else none
def locals (callee : Subst) : String → Data := fun name => (register callee name).getD (.integer 0)

theorem captured (callee : Subst) : Captured (environment callee) callee (locals callee) := by
  intro name slot found
  cases lookup : callee.lookup name with
  | none => simp [environment, register, lookup] at found
  | some atom =>
      cases decoded : decode atom with
      | none => simp [environment, register, lookup, decoded] at found
      | some value =>
          have same : name = slot := by simpa [environment, register, lookup, decoded] using found
          subst slot
          simp [locals, register, lookup, decoded, ← decode_exact atom value decoded]

structure Prepared (program : SpaceSemantics.Program) (head : String) (left right : Atom) where
  callee : Subst
  body : Atom
  ir : Body String
  selected : clauses program head [left, right] = [.evaluate callee body]
  compiled : Compiles program (environment callee) body ir
  notIO : ioHead head = false
  notNative : StdLib.known head = false
  registered : program.equations.any (·.head == head) = true
  ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"]

def prepare (program : SpaceSemantics.Program) (head : String) (left right : Atom) :
    Option (Prepared program head left right) := do
  if notIO : ioHead head = false then
    if notNative : StdLib.known head = false then
      if registered : program.equations.any (·.head == head) = true then
        if ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"] then
          match selected : clauses program head [left, right] with
          | [.evaluate callee body] =>
              let compiled ← ScalarBody.elaborate program (environment callee) body
              return ⟨callee, body, compiled.val, selected, compiled.property, notIO, notNative, registered, ordinary⟩
          | _ => none
        else none
      else none
    else none
  else none

def Prepared.evaluate {program : SpaceSemantics.Program} {head : String} {left right : Atom}
    (prepared : Prepared program head left right) : Option Atom :=
  prepared.ir.eval program (locals prepared.callee)

theorem prepare_selected (program : SpaceSemantics.Program) (head : String) (left right : Atom)
    (callee : Subst) (body : Atom)
    (notIO : ioHead head = false) (notNative : StdLib.known head = false)
    (registered : program.equations.any (·.head == head) = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"])
    (selected : clauses program head [left, right] = [.evaluate callee body]) :
    prepare program head left right = do
      let compiled ← ScalarBody.elaborate program (environment callee) body
      return ⟨callee, body, compiled.val, selected, compiled.property, notIO, notNative, registered, ordinary⟩ := by
  simp [prepare, notIO, notNative, registered, ordinary]
  split
  next actualCallee actualBody actual =>
    have same := actual.symm.trans selected
    have parts := Control.evaluate.inj (List.cons.inj same).1
    obtain ⟨rfl, rfl⟩ := parts
    rfl
  next notSelected => exact False.elim (notSelected callee body selected)

theorem prepare_no_singleton (program : SpaceSemantics.Program) (head : String) (left right : Atom)
    (noneSelected : ∀ callee body, clauses program head [left, right] ≠ [.evaluate callee body]) :
    prepare program head left right = none := by
  unfold prepare
  split_ifs
  all_goals first
    | rfl
    | (split
       next callee body selected => exact False.elim (noneSelected callee body selected)
       next => rfl)

theorem Prepared.body_returns {program : SpaceSemantics.Program} {head : String} {left right : Atom}
    (prepared : Prepared program head left right) (state : Effects.State) (value : Atom)
    (computed : prepared.evaluate = some value) :
    PureReturns program prepared.callee state prepared.body state value :=
  prepared.compiled.returns prepared.callee state (locals prepared.callee) (captured prepared.callee) value computed

theorem Prepared.call_returns {program : SpaceSemantics.Program} {head : String} {left right : Atom}
    (prepared : Prepared program head left right) (caller : Subst) (state : Effects.State)
    (leftName rightName : String) (leftFound : caller.lookup leftName = some left)
    (rightFound : caller.lookup rightName = some right) (value : Atom)
    (computed : prepared.evaluate = some value) :
    PureReturns program caller state (.expression [.symbol head, .var leftName, .var rightName]) state value := by
  apply authored_variable_call_returns program caller prepared.callee state state head [leftName, rightName]
    prepared.body value prepared.notIO prepared.notNative prepared.registered _
    (prepared.body_returns state value computed) prepared.ordinary
  simpa [applySubst, leftFound, rightFound] using prepared.selected

theorem Prepared.call_completed_iff {program : SpaceSemantics.Program} {head : String} {left right : Atom}
    (prepared : Prepared program head left right) (caller : Subst) (state : Effects.State)
    (leftName rightName : String) (leftFound : caller.lookup leftName = some left)
    (rightFound : caller.lookup rightName = some right) (value : Atom)
    (computed : prepared.evaluate = some value)
    (after : Effects.State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      {state, control := .evaluate caller (.expression [.symbol head, .var leftName, .var rightName])} =
        .complete after answers input output) ↔
      after = state ∧ answers = [value] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program caller state state _ value
    (prepared.call_returns caller state leftName rightName leftFound rightFound value computed)
    after answers input output

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarInvocation
