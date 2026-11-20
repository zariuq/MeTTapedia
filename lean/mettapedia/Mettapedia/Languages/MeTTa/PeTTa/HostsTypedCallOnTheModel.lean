import Mettapedia.Languages.MeTTa.PeTTa.DeclaredTypesAtACall
import Mettapedia.Languages.MeTTa.PeTTa.Streaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.AnswerBags

/-!
# The hosts' typed call, built from the model's own evaluation

`DeclaredTypesAtACall` states what both PeTTa hosts do at a declared call on the typed-call
protocol (`CalleeDemand.hostRoute`), with the evaluator of arguments and the body as
parameters. Here both parameters are the Lean PeTTa model's own: arguments are evaluated by
its streaming machine, and the body is the machine's dispatch of the name on delivered values.
So the two readings of a declared call are stated over one model.

* `modelValues`, `modelCall`: the machine's answers for an expression, and for a name
  dispatched on values that are already values.
* `hostsCall`: **the hosts' reading**: each declared row is an alternative; it delivers the
  written arguments by its own demand, checks its guards, runs the body, guards the result.
  The program holds the equations; the rows are given beside it.
* `hosts_atom_and_number_rows`, `model_atom_and_number_rows`: with the rows `(-> Atom Atom)`
  and `(-> Number Number)` for `(= (q2 $x) $x)`, the hosts' reading answers `(q2 (+ 1 2))` with
  `(+ 1 2)` and `3`, as both hosts print; the model with the two declarations loaded answers
  `(+ 1 2)` once.
* `hosts_number_and_identity_rows`, `model_number_and_identity_rows`: with the rows
  `(-> Number Number)` and `(-> $t $t)` for `(= (g2 $x) (+ $x 1))`, the hosts' reading answers
  `(g2 1)` with `2` twice, as both hosts print; the model answers `2` once.
* `undeclared_is_the_model's_call`: with no row, the hosts' reading is the model's own call.

The model's reading is the one in which a declared row is a check: a row that refuses
nothing adds no answer. The hosts' reading is not: `(-> $t $t)` refuses nothing here and adds
an answer.

The model facts are computed by the kernel at fuel 80, where each run has finished
(`Finished`, `runs_finished`), and they hold from fuel 80 on (`hosts_atom_and_number_rows_from`,
`hosts_number_and_identity_rows_from`, `model_rows_from`). Negative example: `no_fuel_no_answer` (with no fuel the machine has
answered nothing, and it has not finished).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.HostsTypedCallOnTheModel

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
open DeclaredTypesAtACall (ledger onePlusTwo dedupAlpha_single number_row number_is_a_number)

/-! ## The model's evaluation and call -/

/-- The machine's state after `fuel` steps from the entry of an expression. -/
def evaluated (program : SpaceSemantics.Program) (fuel : Nat) (expression : Atom) :
    Streaming.State :=
  Streaming.advance program fuel (Streaming.enter { state := Effects.loaded program } expression)

/-- The machine's state after `fuel` steps from the dispatch of a name on values. -/
def called (program : SpaceSemantics.Program) (fuel : Nat) (name : String)
    (values : List Atom) : Streaming.State :=
  Streaming.advance program fuel
    { world := { state := Effects.loaded program, uses := 1 },
      agenda := [.execute ⟨.dynamic [] (.symbol name) values, []⟩] }

/-- A run has finished: nothing is left on its agenda. -/
def Finished (state : Streaming.State) : Prop := state.agenda = []

instance (state : Streaming.State) : Decidable (Finished state) := by
  unfold Finished
  infer_instance

/-- **The model's answers for an expression**, as a bag. -/
def modelValues (program : SpaceSemantics.Program) (fuel : Nat) (expression : Atom) :
    Multiset Atom :=
  ↑(Streaming.values (evaluated program fuel expression))

/-- **The model's answers for a name dispatched on values.** The values are not evaluated
again. -/
def modelCall (program : SpaceSemantics.Program) (fuel : Nat) (name : String)
    (values : List Atom) : Multiset Atom :=
  ↑(Streaming.values (called program fuel name values))

/-- A finished evaluation answers the same with more fuel. -/
theorem modelValues_stable {program : SpaceSemantics.Program} {expression : Atom} {m : Nat}
    (done : Finished (evaluated program m expression)) (n : Nat) (enough : m ≤ n) :
    modelValues program n expression = modelValues program m expression := by
  unfold modelValues evaluated
  rw [Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.AnswerBags.advance_stable
    done n enough]

/-- A finished call answers the same with more fuel. -/
theorem modelCall_stable {program : SpaceSemantics.Program} {name : String} {values : List Atom}
    {m : Nat} (done : Finished (called program m name values)) (n : Nat) (enough : m ≤ n) :
    modelCall program n name values = modelCall program m name values := by
  unfold modelCall called
  rw [Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.AnswerBags.advance_stable
    done n enough]

/-- **The hosts' typed call over the model.** `program` holds the equations of `name`; its
declared rows are `rows`. -/
noncomputable def hostsCall (Γ : Decls) (kind : Atom → String)
    (program : SpaceSemantics.Program) (fuel : Nat) (name : String) (rows : List (Ty String))
    (arguments : List Atom) : Multiset Atom :=
  hostRoute Γ kind (modelValues program fuel) (modelCall program fuel name) rows arguments

/-! ## The protocol on the two measured shapes, for any evaluator and body -/

section Protocol

variable (eval : Atom → Multiset Atom) (body : List Atom → Multiset Atom)

/-- The row `(-> Atom Atom)` on the written `(+ 1 2)`: delivered as written, and the body's
answer on it is the row's answer. -/
theorem held_row (held : body [onePlusTwo] = {onePlusTwo}) :
    (deliver eval (params Controls.quoteRow) [onePlusTwo]).bind
        (chainCall ledger Controls.probeKind body Controls.quoteRow) = {onePlusTwo} := by
  have delivered : deliver eval (params Controls.quoteRow) [onePlusTwo] = {[onePlusTwo]} := by
    simp [deliver, params, Controls.quoteRow, demand]
  have closed := chainCall_closed ledger Controls.probeKind body [.sym "Atom"]
    (.sym "Atom") [onePlusTwo]
  simp only [List.map_cons, List.map_nil] at closed
  rw [delivered, Multiset.singleton_bind, show Controls.quoteRow =
    arrow [(Ty.sym "Atom" : Ty Empty).lift] (Ty.sym "Atom" : Ty Empty).lift from rfl, closed]
  simp [argCount, demand, Ty.lift, ResultGuarded, held]

/-- The row `(-> Number Number)` on the written `(+ 1 2)`: evaluated, guarded, and the body's
answer on the value is the row's answer. -/
theorem evaluated_row (evaluates : eval onePlusTwo = {.grounded (.int 3)})
    (given : body [.grounded (.int 3)] = {.grounded (.int 3)}) :
    (deliver eval (params Controls.numberRow) [onePlusTwo]).bind
        (chainCall ledger Controls.probeKind body Controls.numberRow) =
      {.grounded (.int 3)} := by
  have delivered : deliver eval (params Controls.numberRow) [onePlusTwo] =
      {[.grounded (.int 3)]} := by
    have evaluated : demand (Ty.sym "Number" : Ty String) ≠ .raw := by decide
    simp [deliver, params, Controls.numberRow, evaluated, evaluates]
  rw [delivered, Multiset.singleton_bind, number_row]
  simp [argCount, demand, Unchecked, Ty.lift, number_is_a_number, ResultGuarded, given]

/-- **Each row delivers by its own demand, for any evaluator and body** that evaluate
`(+ 1 2)` to `3` and give back the value they are given. -/
theorem rows_deliver_by_demand (evaluates : eval onePlusTwo = {.grounded (.int 3)})
    (held : body [onePlusTwo] = {onePlusTwo})
    (given : body [.grounded (.int 3)] = {.grounded (.int 3)}) :
    hostRoute ledger Controls.probeKind eval body
        [Controls.quoteRow, Controls.numberRow] [onePlusTwo] =
      {onePlusTwo, .grounded (.int 3)} := by
  unfold hostRoute
  rw [if_neg (by simp),
    dedupAlpha_cons_fresh Controls.quoteRow [Controls.numberRow]
      (by intro σ member; simp at member; subst member; decide),
    dedupAlpha_single, ← Multiset.cons_coe, Multiset.cons_bind, Multiset.coe_singleton,
    Multiset.singleton_bind, held_row eval body held, evaluated_row eval body evaluates given]
  rfl

/-- The typed call on given values depends on the body only through its answers on those
values. -/
theorem typedCall_congr_body (Γ : Decls) (kind : Atom → String)
    {body body' : List Atom → Multiset Atom} (rows : List (Ty String)) (values : List Atom)
    (same : body values = body' values) :
    typedCall Γ kind body rows values = typedCall Γ kind body' rows values := by
  unfold typedCall chainCall
  simp only [same]

/-- **Two rows that both admit repeat the answer, for any evaluator and body** that leave
`1` as it is and answer `2` on it. -/
theorem rows_repeat (evaluates : eval (Controls.num 1) = {Controls.num 1})
    (answers : body [Controls.num 1] = {Controls.num 2}) :
    hostRoute Controls.decls Controls.probeKind eval body
        [Controls.numberRow, Controls.identityRow] [Controls.num 1] =
      {Controls.num 2, Controls.num 2} := by
  have noRaw : ¬ RawDemand [Controls.numberRow, Controls.identityRow] := by
    rintro ⟨τ, member, A, inParams, raw⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [params, Controls.numberRow, Controls.identityRow] at inParams <;>
      subst inParams <;> rw [DeclaredTypesAtACall.demand_raw_iff] at raw <;> simp at raw
  rw [← nativeRoute_eq_hostRoute Controls.decls Controls.probeKind eval body _ _ noRaw]
  unfold nativeRoute
  rw [if_neg (by simp)]
  have delivered : evalArgs eval [Controls.num 1] = {[Controls.num 1]} := by
    simp [evalArgs, evaluates]
  rw [delivered, Multiset.singleton_bind,
    typedCall_congr_body Controls.decls Controls.probeKind (body' := fun _ => {Controls.num 2}) _ _
      answers, Controls.distinct_rows_two_answers]

end Protocol

/-! ## The two measured programs -/

/-- A program from its forms. -/
def programOf (forms : List Atom) : SpaceSemantics.Program :=
  match SpaceSemantics.collect forms with
  | .ok program => program
  | .error _ => { equations := [], declarations := [] }

/-- An application. -/
def app (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)

/-- An equation. -/
def equation (left right : Atom) : Atom := .expression [.symbol "=", left, right]

/-- A declaration `(: name (-> types))`. -/
def declaration (name : String) (types : List Atom) : Atom :=
  .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]

/-- `(= (q2 $x) $x)`. -/
def given : SpaceSemantics.Program := programOf [equation (app "q2" [.var "x"]) (.var "x")]

/-- The same with `(: q2 (-> Atom Atom))` and `(: q2 (-> Number Number))` loaded. -/
def declaredGiven : SpaceSemantics.Program :=
  programOf [declaration "q2" [.symbol "Atom", .symbol "Atom"],
    declaration "q2" [.symbol "Number", .symbol "Number"],
    equation (app "q2" [.var "x"]) (.var "x")]

/-- `(= (g2 $x) (+ $x 1))`. -/
def successor : SpaceSemantics.Program :=
  programOf [equation (app "g2" [.var "x"]) (app "+" [.var "x", Controls.num 1])]

/-- The same with `(: g2 (-> Number Number))` and `(: g2 (-> $t $t))` loaded. -/
def declaredSuccessor : SpaceSemantics.Program :=
  programOf [declaration "g2" [.symbol "Number", .symbol "Number"],
    declaration "g2" [.var "t", .var "t"],
    equation (app "g2" [.var "x"]) (app "+" [.var "x", Controls.num 1])]

/-- Every run used below has finished at fuel 80. -/
theorem runs_finished :
    Finished (evaluated given 80 onePlusTwo) ∧
      Finished (called given 80 "q2" [onePlusTwo]) ∧
      Finished (called given 80 "q2" [Controls.num 3]) ∧
      Finished (evaluated given 80 (app "q2" [onePlusTwo])) ∧
      Finished (evaluated declaredGiven 80 (app "q2" [onePlusTwo])) ∧
      Finished (evaluated successor 80 (Controls.num 1)) ∧
      Finished (called successor 80 "g2" [Controls.num 1]) ∧
      Finished (evaluated declaredSuccessor 80 (app "g2" [Controls.num 1])) := by
  decide +kernel

theorem model_evaluates_the_sum : modelValues given 80 onePlusTwo = {Controls.num 3} := by
  have computed : Streaming.values (evaluated given 80 onePlusTwo) = [Controls.num 3] := by
    decide +kernel
  simp [modelValues, computed]

/-- A value that is an expression stays as it is: the call does not evaluate it again. -/
theorem model_keeps_a_held_value : modelCall given 80 "q2" [onePlusTwo] = {onePlusTwo} := by
  have computed : Streaming.values (called given 80 "q2" [onePlusTwo]) = [onePlusTwo] := by
    decide +kernel
  simp [modelCall, computed]

theorem model_gives_the_value :
    modelCall given 80 "q2" [Controls.num 3] = {Controls.num 3} := by
  have computed : Streaming.values (called given 80 "q2" [Controls.num 3]) =
      [Controls.num 3] := by decide +kernel
  simp [modelCall, computed]

/-- **The hosts' reading of the rows `(-> Atom Atom)` and `(-> Number Number)`**: `(q2 (+ 1 2))`
answers `(+ 1 2)` by the first row and `3` by the second. Both hosts print `((+ 1 2) 3)`. -/
theorem hosts_atom_and_number_rows :
    hostsCall ledger Controls.probeKind given 80 "q2"
        [Controls.quoteRow, Controls.numberRow] [onePlusTwo] =
      {onePlusTwo, Controls.num 3} :=
  rows_deliver_by_demand _ _ model_evaluates_the_sum model_keeps_a_held_value
    model_gives_the_value

/-- The same from fuel 80 on. -/
theorem hosts_atom_and_number_rows_from (fuel : Nat) (enough : 80 ≤ fuel) :
    hostsCall ledger Controls.probeKind given fuel "q2"
        [Controls.quoteRow, Controls.numberRow] [onePlusTwo] =
      {onePlusTwo, Controls.num 3} :=
  rows_deliver_by_demand _ _
    ((modelValues_stable runs_finished.1 fuel enough).trans model_evaluates_the_sum)
    ((modelCall_stable runs_finished.2.1 fuel enough).trans model_keeps_a_held_value)
    ((modelCall_stable runs_finished.2.2.1 fuel enough).trans model_gives_the_value)

/-- **The model's reading of the same rows**: the argument is held for the whole call and the
call runs once. -/
theorem model_atom_and_number_rows :
    modelValues declaredGiven 80 (app "q2" [onePlusTwo]) = {onePlusTwo} := by
  have computed : Streaming.values (evaluated declaredGiven 80 (app "q2" [onePlusTwo])) =
      [onePlusTwo] := by decide +kernel
  simp [modelValues, computed]

theorem model_leaves_a_number :
    modelValues successor 80 (Controls.num 1) = {Controls.num 1} := by
  have computed : Streaming.values (evaluated successor 80 (Controls.num 1)) =
      [Controls.num 1] := by decide +kernel
  simp [modelValues, computed]

theorem model_adds_one : modelCall successor 80 "g2" [Controls.num 1] = {Controls.num 2} := by
  have computed : Streaming.values (called successor 80 "g2" [Controls.num 1]) =
      [Controls.num 2] := by decide +kernel
  simp [modelCall, computed]

/-- **The hosts' reading of the rows `(-> Number Number)` and `(-> $t $t)`**: `(g2 1)` answers
`2` once for each row. Both hosts print `(2 2)`. -/
theorem hosts_number_and_identity_rows :
    hostsCall Controls.decls Controls.probeKind successor 80 "g2"
        [Controls.numberRow, Controls.identityRow] [Controls.num 1] =
      {Controls.num 2, Controls.num 2} :=
  rows_repeat _ _ model_leaves_a_number model_adds_one

/-- The same from fuel 80 on. -/
theorem hosts_number_and_identity_rows_from (fuel : Nat) (enough : 80 ≤ fuel) :
    hostsCall Controls.decls Controls.probeKind successor fuel "g2"
        [Controls.numberRow, Controls.identityRow] [Controls.num 1] =
      {Controls.num 2, Controls.num 2} :=
  rows_repeat _ _
    ((modelValues_stable runs_finished.2.2.2.2.2.1 fuel enough).trans model_leaves_a_number)
    ((modelCall_stable runs_finished.2.2.2.2.2.2.1 fuel enough).trans model_adds_one)

/-- **The model's reading of the same rows**: the call runs once. -/
theorem model_number_and_identity_rows :
    modelValues declaredSuccessor 80 (app "g2" [Controls.num 1]) = {Controls.num 2} := by
  have computed : Streaming.values (evaluated declaredSuccessor 80 (app "g2" [Controls.num 1])) =
      [Controls.num 2] := by decide +kernel
  simp [modelValues, computed]

/-- The model's answers with the declarations loaded do not change with more fuel either. -/
theorem model_rows_from (fuel : Nat) (enough : 80 ≤ fuel) :
    modelValues declaredGiven fuel (app "q2" [onePlusTwo]) = {onePlusTwo} ∧
      modelValues declaredSuccessor fuel (app "g2" [Controls.num 1]) = {Controls.num 2} :=
  ⟨(modelValues_stable runs_finished.2.2.2.2.1 fuel enough).trans model_atom_and_number_rows,
    (modelValues_stable runs_finished.2.2.2.2.2.2.2 fuel enough).trans
      model_number_and_identity_rows⟩

/-- **With no declared row the hosts' reading is the model's own call**: both answer
`(q2 (+ 1 2))` with `3`. -/
theorem undeclared_is_the_model's_call :
    hostsCall ledger Controls.probeKind given 80 "q2" [] [onePlusTwo] =
      modelValues given 80 (app "q2" [onePlusTwo]) := by
  have direct : modelValues given 80 (app "q2" [onePlusTwo]) = {Controls.num 3} := by
    have computed : Streaming.values (evaluated given 80 (app "q2" [onePlusTwo])) =
        [Controls.num 3] := by decide +kernel
    simp [modelValues, computed]
  rw [direct]
  simp [hostsCall, hostRoute, evalArgs, model_evaluates_the_sum, model_gives_the_value]

/-- Negative: with no fuel the machine has answered nothing and has not finished. -/
theorem no_fuel_no_answer :
    modelCall successor 0 "g2" [Controls.num 1] = 0 ∧
      ¬ Finished (called successor 0 "g2" [Controls.num 1]) := by
  refine ⟨?_, by decide +kernel⟩
  have computed : Streaming.values (called successor 0 "g2" [Controls.num 1]) = [] := by
    decide +kernel
  simp [modelCall, computed]

#print axioms hosts_atom_and_number_rows
#print axioms model_atom_and_number_rows
#print axioms hosts_number_and_identity_rows
#print axioms model_number_and_identity_rows
#print axioms undeclared_is_the_model's_call
#print axioms hosts_atom_and_number_rows_from
#print axioms hosts_number_and_identity_rows_from
#print axioms model_rows_from

end Mettapedia.Languages.MeTTa.PeTTa.HostsTypedCallOnTheModel
