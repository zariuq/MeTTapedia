import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.DeclaredBuiltins
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.CalleeDemand
import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeRows
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-!
# Declared types at a call: what they can and cannot change

Both PeTTa hosts run a call of a declared function once for each declared row: the row
delivers each argument (as written to a parameter typed `Atom`, evaluated otherwise), checks
each guarded argument against its parameter type, runs the body, and checks each answer
against the result type. A value that fails a check gives no answer and no error.
`TypedCalls.Protocol` states one row on delivered values (`chainCall`) and the rows together
(`typedCall`); `TypedCalls.CalleeDemand` adds the delivery (`hostRoute`). Both take the
evaluator and the untyped call's answers as parameters. This module states what the
declarations do to the untyped call, whatever machine supplies those two.

* **No new answer value on the same delivered values**
  (`typed_call_adds_no_answer_value`): every answer of the typed call is an answer of the
  untyped call on the values the row was delivered.
* **At the written call, with no parameter typed `Atom`, no new answer value**
  (`written_call_adds_no_answer_value`).
* Neither says "declarations only remove answers", and that is false twice over, each
  measured on both hosts:
  * distinct rows are alternatives, so an answer can come once for each
    (`rows_can_repeat_an_answer`: `(-> Number Number)` and `(-> $t $t)` answer `(g2 1)` twice);
  * a parameter typed `Atom` receives its argument as written, so the typed call can answer a
    value the untyped call never does (`a_held_parameter_gives_another_answer`: declared
    `(-> Atom Atom)`, `(q (+ 1 2))` answers `(+ 1 2)`; undeclared it answers `3`).
* **A row whose argument guards refuse the values answers nothing, whatever the body**
  (`chainCall_of_refused_arguments`, `typedCall_of_refused_arguments`).
* **Each row delivers by its own demand** (`each_row_delivers_by_its_own_demand`): with the
  rows `(-> Atom Atom)` and `(-> Number Number)`, `(h (+ 1 2))` answers `(+ 1 2)` and `3`, as
  both hosts do. The PeTTa model's rule holds an argument when any row of the name has `Atom`
  there (`the_model_holds_the_argument_for_every_row`), so on this call it delivers the
  expression as written only: its rule and the hosts' differ where a name's rows disagree
  on which parameters are `Atom`, and where they agree the model's one delivery is each
  row's (`the_model_delivers_as_each_row_where_rows_agree`). On one parameter type the two
  tests agree (`the_model_holds_what_the_protocol_holds`).

Controls are three typed programs of the measured HE and PeTTa ledger, with the function
declared `(-> Number Number)`:

* `(= (f $x) yes)`, `(f 4)`: no answer, the result `yes` is no number
  (`a_result_of_another_type_is_no_answer`);
* `(: b Bool)`, `(f b)`: no answer for any body, the argument is no number
  (`an_argument_of_another_type_is_no_answer`);
* `(= (f $x) (+ $x 1))`, `(f 4)`: the answer `5` once (`a_well_typed_call_answers`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.DeclaredTypesAtACall

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

variable (Γ : Decls) (kind : Atom → String)

/-- The result guard answers the value it was given, or nothing. -/
theorem mem_resultGuard {k : ℕ} {R : Ty String} {S : List (Eqn CallVar)} {r answer : Atom}
    (member : answer ∈ resultGuard Γ kind k R S r) : answer = r := by
  unfold resultGuard at member
  split_ifs at member
  · obtain ⟨_, _, same⟩ := Multiset.mem_map.mp member
    exact same.symm
  · exact Multiset.mem_singleton.mp member

/-- One row's protocol answers only what the untyped call answers. -/
theorem mem_chainCall {body : List Atom → Multiset Atom} {τ : Ty String} {values : List Atom}
    {answer : Atom} (member : answer ∈ chainCall Γ kind body τ values) :
    answer ∈ body values := by
  unfold chainCall at member
  split at member
  · obtain ⟨_, _, inner⟩ := Multiset.mem_bind.mp member
    obtain ⟨r, fromBody, guarded⟩ := Multiset.mem_bind.mp inner
    rw [mem_resultGuard Γ kind guarded]
    exact fromBody
  · simp at member

/-- **No new answer value on the same delivered values**: every answer of the typed call is
an answer of the untyped call on the values the row was delivered. It bounds which values
are answered, not how often: `rows_can_repeat_an_answer`. -/
theorem typed_call_adds_no_answer_value {body : List Atom → Multiset Atom}
    {rows : List (Ty String)} {values : List Atom} {answer : Atom}
    (member : answer ∈ typedCall Γ kind body rows values) : answer ∈ body values := by
  unfold typedCall at member
  obtain ⟨_, _, inRow⟩ := Multiset.mem_bind.mp member
  exact mem_chainCall Γ kind inRow

/-- **At the written call, with no parameter typed `Atom`, no new answer value**: every
answer of the declared call is an answer of the undeclared call, which evaluates every
argument and runs the body. -/
theorem written_call_adds_no_answer_value {eval : Atom → Multiset Atom}
    {body : List Atom → Multiset Atom} {rows : List (Ty String)} {arguments : List Atom}
    {answer : Atom} (noneHeld : ¬ RawDemand rows)
    (member : answer ∈ hostRoute Γ kind eval body rows arguments) :
    answer ∈ (evalArgs eval arguments).bind body := by
  rw [← nativeRoute_eq_hostRoute Γ kind eval body rows arguments noneHeld] at member
  unfold nativeRoute at member
  split_ifs at member
  · exact member
  · obtain ⟨values, delivered, inCall⟩ := Multiset.mem_bind.mp member
    exact Multiset.mem_bind.mpr
      ⟨values, delivered, typed_call_adds_no_answer_value Γ kind inCall⟩

/-- **Distinct rows can repeat an answer**: with the rows `(-> Number Number)` and
`(-> $t $t)`, the call `(g2 1)` whose body answers `2` once answers `2` twice. Both hosts
print `(2 2)`. -/
theorem rows_can_repeat_an_answer :
    Multiset.count (Controls.num 2) ((fun _ => {Controls.num 2} : List Atom → Multiset Atom)
        [Controls.num 1]) <
      Multiset.count (Controls.num 2)
        (typedCall Controls.decls Controls.probeKind (fun _ => {Controls.num 2})
          [Controls.numberRow, Controls.identityRow] [Controls.num 1]) := by
  rw [Controls.distinct_rows_two_answers]
  simp

/-- A row whose argument guards refuse the values answers nothing, whatever the body. -/
theorem chainCall_of_refused_arguments (body : List Atom → Multiset Atom) {τ : Ty String}
    {As : List (Ty String)} {R : Ty String} {values : List Atom}
    (split : arrowSplit τ = some (As, R)) (refused : guards Γ kind 0 As values [] = 0) :
    chainCall Γ kind body τ values = 0 := by
  unfold chainCall
  rw [split]
  simp [refused]

/-- When every row's argument guards refuse the values the typed call answers nothing,
whatever the body: no equation's body is consulted. -/
theorem typedCall_of_refused_arguments (body : List Atom → Multiset Atom)
    {rows : List (Ty String)} {values : List Atom}
    (refused : ∀ τ ∈ dedupAlpha rows, ∃ As R, arrowSplit τ = some (As, R) ∧
      guards Γ kind 0 As values [] = 0) :
    typedCall Γ kind body rows values = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro answer member
  unfold typedCall at member
  obtain ⟨τ, inRows, inRow⟩ := Multiset.mem_bind.mp member
  obtain ⟨As, R, split, none⟩ := refused τ (Multiset.mem_coe.mp inRows)
  rw [chainCall_of_refused_arguments Γ kind body split none] at inRow
  simp at inRow

/-! ## Which arguments are held -/

/-- The protocol's demand holds an argument exactly at the type `Atom`. -/
theorem demand_raw_iff (type : Ty String) : demand type = .raw ↔ type = .sym "Atom" := by
  unfold demand
  split_ifs with isAtom unchecked
  · exact ⟨fun _ => isAtom, fun _ => rfl⟩
  · exact ⟨fun wrong => (by cases wrong), fun same => absurd same isAtom⟩
  · exact ⟨fun wrong => (by cases wrong), fun same => absurd same isAtom⟩

/-- **The model and the protocol hold the same arguments**: for a declared parameter type the
parser reads, the model's test for an argument taken as written holds exactly when the
protocol's demand is to take it as written. -/
theorem the_model_holds_what_the_protocol_holds {formal : Atom} {type : Ty String}
    (parsed : PettaSourceTypeRows.parseType formal = some type) :
    Mettapedia.Languages.MeTTa.PeTTa.formalArgumentIsRaw formal = true ↔ demand type = .raw := by
  rw [demand_raw_iff]
  cases formal with
  | var name =>
      simp only [PettaSourceTypeRows.parseType, Option.some.injEq] at parsed
      subst parsed
      simp
  | symbol name =>
      simp only [PettaSourceTypeRows.parseType, Option.some.injEq] at parsed
      subst parsed
      simp
  | grounded held => simp [PettaSourceTypeRows.parseType] at parsed
  | expression children =>
      simp only [PettaSourceTypeRows.parseType, Option.map_eq_some_iff] at parsed
      obtain ⟨types, _, same⟩ := parsed
      subst same
      simp

/-- Positive: a parameter typed `Atom` is held by both. -/
theorem atom_is_held_by_both :
    Mettapedia.Languages.MeTTa.PeTTa.formalArgumentIsRaw (.symbol "Atom") = true ∧
      demand (.sym "Atom") = .raw := by
  exact ⟨by decide, by decide⟩

/-- Negative: a parameter typed `Number` is held by neither. -/
theorem number_is_held_by_neither :
    Mettapedia.Languages.MeTTa.PeTTa.formalArgumentIsRaw (.symbol "Number") = false ∧
      demand (.sym "Number") ≠ .raw := by
  exact ⟨by decide, by decide⟩

/-! ## Controls: three typed programs of the measured ledger -/

/-- The declarations of the ledger's typed programs: `(: b Bool)`. -/
def ledger : Decls := fun name => if name = "b" then [.sym "Bool"] else []

/-- The row `(-> Number Number)` on one value: the argument's guard, then each answer of
the body counted by its result guard. -/
theorem number_row (body : List Atom → Multiset Atom) (value : Atom) :
    chainCall ledger Controls.probeKind body Controls.numberRow [value] =
      argCount ledger Controls.probeKind [.sym "Number"] [value] •
        (body [value]).bind fun r =>
          if ResultGuarded (Ty.sym "Number" : Ty Empty).lift then
            guardCount (info ledger r) (.sym "Number") (Controls.probeKind r) • {r}
          else {r} := by
  have closed := chainCall_closed ledger Controls.probeKind body [.sym "Number"]
    (.sym "Number") [value]
  simp only [List.map_cons, List.map_nil] at closed
  rw [show Controls.numberRow =
    arrow [(Ty.sym "Number" : Ty Empty).lift] (Ty.sym "Number" : Ty Empty).lift from rfl, closed]

theorem number_is_a_number (n : ℤ) :
    guardCount (info ledger (.grounded (.int n))) (.sym "Number")
      (Controls.probeKind (.grounded (.int n))) = 1 := by
  rw [guardCount_of_ne _ _ _ (by simp [Controls.probeKind, metatype]),
    count_class ledger (c := "Number") rfl]
  simp

/-- Negative: `(= (f $x) yes)`, `(f 4)` has no answer. The result is no number. -/
theorem a_result_of_another_type_is_no_answer :
    chainCall ledger Controls.probeKind (fun _ => {.symbol "yes"}) Controls.numberRow
      [.grounded (.int 4)] = 0 := by
  have result : guardCount (info ledger (.symbol "yes")) (.sym "Number")
      (Controls.probeKind (.symbol "yes")) = 0 := by
    rw [guardCount_of_ne _ _ _ (by simp [Controls.probeKind, metatype]),
      Controls.count_symbol_undeclared ledger "yes" (by simp [ledger]) _ (by decide)]
  rw [number_row]
  simp [argCount, demand, Unchecked, Ty.lift, number_is_a_number, ResultGuarded, result]

/-- Negative: with `(: b Bool)`, `(f b)` has no answer, whatever the body. The argument is
no number. -/
theorem an_argument_of_another_type_is_no_answer (body : List Atom → Multiset Atom) :
    chainCall ledger Controls.probeKind body Controls.numberRow [.symbol "b"] = 0 := by
  have argument : guardCount (info ledger (.symbol "b")) (.sym "Number")
      (Controls.probeKind (.symbol "b")) = 0 := by
    rw [guardCount_of_ne _ _ _ (by simp [Controls.probeKind, metatype]),
      count_symbol_closed ledger "b" (.sym "Bool") (by simp [ledger, Ty.lift])]
    simp
  rw [number_row]
  simp [argCount, demand, Unchecked, Ty.lift, argument]

/-- Positive: `(= (f $x) (+ $x 1))`, `(f 4)` answers `5` once. -/
theorem a_well_typed_call_answers :
    chainCall ledger Controls.probeKind (fun _ => {.grounded (.int 5)}) Controls.numberRow
      [.grounded (.int 4)] = {.grounded (.int 5)} := by
  rw [number_row]
  simp [argCount, demand, Unchecked, Ty.lift, number_is_a_number, ResultGuarded]

/-! ## Controls: delivery by each row -/

/-- `(+ 1 2)`. -/
def onePlusTwo : Atom :=
  .expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)]

/-- The evaluator of the controls: `(+ 1 2)` has the value `3`, any other atom is its own
value. -/
def sums (written : Atom) : Multiset Atom :=
  if written = onePlusTwo then {.grounded (.int 3)} else {written}

/-- The body of `(= (f $x) $x)`: the value it was given. -/
def givenValue : List Atom → Multiset Atom
  | [value] => {value}
  | _ => 0

theorem dedupAlpha_single (τ : Ty String) : dedupAlpha [τ] = [τ] := by
  rw [dedupAlpha_cons_fresh τ [] (by simp)]
  rfl

/-- The row `(-> Atom Atom)` on the written argument: delivered as written, no guard. -/
theorem atom_row_on_the_written_argument :
    (deliver sums (params Controls.quoteRow) [onePlusTwo]).bind
        (chainCall ledger Controls.probeKind givenValue Controls.quoteRow) = {onePlusTwo} := by
  have delivered : deliver sums (params Controls.quoteRow) [onePlusTwo] = {[onePlusTwo]} := by
    simp [deliver, params, Controls.quoteRow, demand]
  have closed := chainCall_closed ledger Controls.probeKind givenValue [.sym "Atom"]
    (.sym "Atom") [onePlusTwo]
  simp only [List.map_cons, List.map_nil] at closed
  rw [delivered, Multiset.singleton_bind, show Controls.quoteRow =
    arrow [(Ty.sym "Atom" : Ty Empty).lift] (Ty.sym "Atom" : Ty Empty).lift from rfl, closed]
  simp [argCount, demand, Ty.lift, ResultGuarded, givenValue]

/-- The row `(-> Number Number)` on the written argument: evaluated, then guarded. -/
theorem number_row_on_the_written_argument :
    (deliver sums (params Controls.numberRow) [onePlusTwo]).bind
        (chainCall ledger Controls.probeKind givenValue Controls.numberRow) =
      {.grounded (.int 3)} := by
  have delivered : deliver sums (params Controls.numberRow) [onePlusTwo] =
      {[.grounded (.int 3)]} := by
    have evaluated : demand (Ty.sym "Number" : Ty String) ≠ .raw := by decide
    simp [deliver, params, Controls.numberRow, evaluated, sums]
  rw [delivered, Multiset.singleton_bind, number_row]
  simp [argCount, demand, Unchecked, Ty.lift, number_is_a_number, ResultGuarded, givenValue]

/-- **A parameter typed `Atom` gives the typed call an answer the untyped call does not
have**: declared `(-> Atom Atom)`, `(q (+ 1 2))` answers `(+ 1 2)`; undeclared, it answers
`3`. Both hosts print these. -/
theorem a_held_parameter_gives_another_answer :
    hostRoute ledger Controls.probeKind sums givenValue [Controls.quoteRow] [onePlusTwo] =
        {onePlusTwo} ∧
      hostRoute ledger Controls.probeKind sums givenValue [] [onePlusTwo] =
        {.grounded (.int 3)} := by
  constructor
  · unfold hostRoute
    rw [if_neg (by simp), dedupAlpha_single, Multiset.coe_singleton, Multiset.singleton_bind]
    exact atom_row_on_the_written_argument
  · simp [hostRoute, evalArgs, sums, givenValue]

/-- **Each row delivers by its own demand**: with the rows `(-> Atom Atom)` and
`(-> Number Number)`, `(h (+ 1 2))` answers `(+ 1 2)` by the first row and `3` by the
second. Both hosts print `((+ 1 2) 3)`. -/
theorem each_row_delivers_by_its_own_demand :
    hostRoute ledger Controls.probeKind sums givenValue
        [Controls.quoteRow, Controls.numberRow] [onePlusTwo] =
      {onePlusTwo, .grounded (.int 3)} := by
  unfold hostRoute
  rw [if_neg (by simp),
    dedupAlpha_cons_fresh Controls.quoteRow [Controls.numberRow]
      (by intro σ member; simp at member; subst member; decide),
    dedupAlpha_single, ← Multiset.cons_coe, Multiset.cons_bind, Multiset.coe_singleton,
    Multiset.singleton_bind, atom_row_on_the_written_argument,
    number_row_on_the_written_argument]
  rfl

/-- The two declarations of `h`, as the PeTTa model stores them. -/
def twoRows : SpaceSemantics.Program where
  equations := []
  declarations :=
    [.expression [.symbol ":", .symbol "h",
        .expression [.symbol "->", .symbol "Atom", .symbol "Atom"]],
      .expression [.symbol ":", .symbol "h",
        .expression [.symbol "->", .symbol "Number", .symbol "Number"]]]

/-- **The model holds the argument for every row**: its rule takes the argument of `h` as
written because one of the name's rows has `Atom` there. On `(h (+ 1 2))` it delivers the
expression only, where the hosts also deliver `3` to the second row
(`each_row_delivers_by_its_own_demand`). -/
theorem the_model_holds_the_argument_for_every_row :
    Eval.argumentIsRaw twoRows "h" 0 = true := by
  decide

/-- Positive: with the second row alone the model evaluates the argument, as that row does. -/
theorem the_model_evaluates_for_a_number_row :
    Eval.argumentIsRaw { twoRows with declarations := twoRows.declarations.drop 1 } "h" 0 =
      false := by
  decide

/-! ## Where the model's delivery is the hosts'

The model's rule read on rows: an argument is held when some row of the name has `Atom` at
its position (`Eval.argumentIsRaw_iff_declaredAtom` states the rule on the stored
declarations). One delivery then serves the whole call. -/

/-- Some row has `Atom` at the position. -/
def HeldBySome (rows : List (Ty String)) (position : ℕ) : Prop :=
  ∃ τ ∈ rows, (params τ)[position]? = some (Ty.sym "Atom")

instance (rows : List (Ty String)) (position : ℕ) : Decidable (HeldBySome rows position) := by
  unfold HeldBySome
  infer_instance

/-- Delivery by the model's rule, from a position on: each argument as written when some row
holds it, evaluated otherwise. -/
def deliverForAll (eval : Atom → Multiset Atom) (rows : List (Ty String)) :
    ℕ → List Atom → Multiset (List Atom)
  | _, [] => {[]}
  | position, written :: others =>
      (if HeldBySome rows position then {written} else eval written).bind fun value =>
        (deliverForAll eval rows (position + 1) others).map (value :: ·)

/-- The rows agree on which parameters are `Atom`. -/
def AgreeOnHeld (rows : List (Ty String)) : Prop :=
  ∀ τ ∈ rows, ∀ σ ∈ rows, ∀ position : ℕ,
    (params τ)[position]? = some (Ty.sym "Atom") → (params σ)[position]? = some (Ty.sym "Atom")

theorem deliver_from {eval : Atom → Multiset Atom} {rows : List (Ty String)}
    (agree : AgreeOnHeld rows) {τ : Ty String} (member : τ ∈ rows) :
    ∀ (parameters : List (Ty String)) (position : ℕ) (arguments : List Atom),
      (∀ offset, parameters[offset]? = (params τ)[position + offset]?) →
      parameters.length = arguments.length →
      deliver eval parameters arguments = deliverForAll eval rows position arguments
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, sameLength => by simp at sameLength
  | _ :: _, _, [], _, sameLength => by simp at sameLength
  | parameter :: parameters, position, written :: others, suffix, sameLength => by
      have here : (params τ)[position]? = some parameter := by
        simpa using (suffix 0).symm
      have held : demand parameter = .raw ↔ HeldBySome rows position := by
        rw [demand_raw_iff]
        constructor
        · intro isAtom
          exact ⟨τ, member, by rw [here, isAtom]⟩
        · rintro ⟨σ, inRows, atSigma⟩
          have atTau := agree σ inRows τ member position atSigma
          rw [here] at atTau
          exact Option.some.inj atTau
      have rest : deliver eval parameters others =
          deliverForAll eval rows (position + 1) others :=
        deliver_from agree member parameters (position + 1) others
        (fun offset => by
          have step := suffix (offset + 1)
          rw [List.getElem?_cons_succ] at step
          rw [step]
          congr 1
          omega)
        (by simpa using sameLength)
      simp only [deliver, deliverForAll, rest]
      by_cases isHeld : HeldBySome rows position
      · rw [if_pos (held.mpr isHeld), if_pos isHeld]
      · rw [if_neg (fun raw => isHeld (held.mp raw)), if_neg isHeld]

/-- **Where a name's rows agree on which parameters are `Atom`, the model's delivery is each
row's**: one delivery by the model's rule is what every row of the name delivers. -/
theorem the_model_delivers_as_each_row_where_rows_agree {eval : Atom → Multiset Atom}
    {rows : List (Ty String)} (agree : AgreeOnHeld rows) {τ : Ty String} (member : τ ∈ rows)
    (arguments : List Atom) (sameLength : (params τ).length = arguments.length) :
    deliver eval (params τ) arguments = deliverForAll eval rows 0 arguments :=
  deliver_from agree member (params τ) 0 arguments (fun offset => by simp) sameLength

/-- Negative: the rows `(-> Atom Atom)` and `(-> Number Number)` do not agree, and the
model's one delivery of `(h (+ 1 2))` is the expression as written, which is not what the
second row delivers. -/
theorem rows_that_disagree_are_delivered_otherwise :
    ¬ AgreeOnHeld [Controls.quoteRow, Controls.numberRow] ∧
      deliverForAll sums [Controls.quoteRow, Controls.numberRow] 0 [onePlusTwo] = {[onePlusTwo]} ∧
      deliver sums (params Controls.numberRow) [onePlusTwo] = {[.grounded (.int 3)]} := by
  refine ⟨?_, ?_, ?_⟩
  · intro agree
    have wrong := agree Controls.quoteRow (by simp) Controls.numberRow (by simp) 0
      (by simp [params, Controls.quoteRow])
    simp [params, Controls.numberRow] at wrong
  · have held : HeldBySome [Controls.quoteRow, Controls.numberRow] 0 :=
      ⟨Controls.quoteRow, by simp, by simp [params, Controls.quoteRow]⟩
    simp [deliverForAll, held]
  · have evaluated : demand (Ty.sym "Number" : Ty String) ≠ .raw := by decide
    simp [deliver, params, Controls.numberRow, evaluated, sums]

end Mettapedia.Languages.MeTTa.PeTTa.DeclaredTypesAtACall
