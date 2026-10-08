import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2

/-!
# Source controls for one-shot and standing MM2 programmes

The standing programme is ordinary authored MM2: rule records, a turn token,
and a self-reinstalling dispatcher. An activation remains one-shot. Fair
repetition belongs to the authored dispatcher, not to a new native grammar.

The observation selects the `p` and `q` support facts. It deliberately forgets
administrative rule records and turns, but the source store and execution
trace retain them. Stable observed facts do not mean a quiescent agenda.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open ProgrammableSpaceMM2

def form (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

def p (name : String) : Atom := form "p" [.symbol name]
def q (name : String) : Atom := form "q" [.symbol name]

def instruction (priority name : String) (inputs outputs : List Atom) : Atom :=
  form "exec" [form priority [.symbol name], form "," inputs, form "O" outputs]

def consumer (priority : String) : Atom :=
  instruction priority "consumer" [form "p" [.var "x"]]
    [form "+" [form "q" [.var "x"]]]

def producer (priority : String) : Atom :=
  instruction priority "producer" [] [form "+" [p "b"]]

def oneShot (consumerFirst : Bool) : List Atom :=
  if consumerFirst then [p "a", consumer "0", producer "1"]
  else [p "a", consumer "1", producer "0"]

def run (fuel : Nat) (space : List Atom) : List Atom × Nat :=
  cRuleScopedSourceWorkQueueRunN .leaveInert fuel space

theorem oneShot_consumer_first :
    run 3 (oneShot true) = ([p "a", q "a", p "b"], 2) := by decide +kernel

theorem oneShot_producer_first :
    run 3 (oneShot false) = ([p "a", p "b", q "a", q "b"], 2) := by decide +kernel

theorem oneShot_order_observable :
    q "b" ∉ (run 3 (oneShot true)).1 ∧ q "b" ∈ (run 3 (oneShot false)).1 := by
  rw [oneShot_consumer_first, oneShot_producer_first]
  decide

def unresolved : Atom := form "unresolved" [.var "outside"]

theorem strict_and_rule_scoped_templates_differ :
    instantiateTemplateAtom? [] unresolved = none ∧
      instantiateRuleTemplateAtom? (.compat ⟨[]⟩) [] unresolved = some unresolved := by
  decide +kernel

theorem input_variable_still_requires_its_match :
    instantiateRuleTemplateAtom? (.compat ⟨[form "p" [.var "x"]]⟩) []
      (form "q" [.var "x"]) = none := by decide +kernel

theorem output_local_directive_runs :
    run 2 [form "exec" [.symbol "first", form "," [],
      form "O" [form "+" [unresolved]]]] = ([unresolved], 1) := by decide +kernel

def generated : Atom :=
  form "exec" [.symbol "first", form "," [], form "O" [form "+" [
    form "exec" [.symbol "second", form "," [form "p" [.var "outside"]],
      form "O" [form "+" [form "q" [.var "outside"]]]]]]]

theorem generated_local_becomes_next_input :
    run 3 [p "a", generated] = ([p "a", q "a"], 2) := by decide +kernel

def captured : Atom := form "payload" [
  form "exec" [.symbol "second", form "," [form "p" [.var "inner"]],
    form "O" [form "+" [form "q" [.var "inner"]]]]]

def captureActivation : Atom :=
  form "exec" [.symbol "first", form "," [form "payload" [.var "captured"]],
    form "O" [form "+" [.var "captured"]]]

theorem captured_payload_keeps_inner_scope :
    run 3 [p "a", captured, captureActivation] = ([p "a", captured, q "a"], 2) := by
  decide +kernel

def dispatcher : Atom :=
  instruction "1" "dispatch"
    [form "turn" [.var "name"], form "next" [.var "name", .var "next"],
      form "standing" [.var "name", .var "input", .var "output"],
      form "exec" [form "1" [.symbol "dispatch"], .var "selfinput", .var "selfoutput"]]
    [form "-" [form "turn" [.var "name"]],
      form "+" [form "turn" [.var "next"]],
      form "+" [form "exec" [form "0" [.symbol "instance"], .var "input", .var "output"]],
      form "+" [form "exec" [form "1" [.symbol "dispatch"], .var "selfinput", .var "selfoutput"]]]

def standingRules : List Atom :=
  [p "a", form "standing" [.symbol "consumer", form "," [form "p" [.var "x"]],
      form "O" [form "+" [form "q" [.var "x"]]]],
    form "standing" [.symbol "producer", form "," [], form "O" [form "+" [p "b"]]],
    form "next" [.symbol "consumer", .symbol "producer"],
    form "next" [.symbol "producer", .symbol "consumer"], dispatcher]

def standing (consumerFirst : Bool) : List Atom :=
  standingRules ++ [form "turn" [.symbol (if consumerFirst then "consumer" else "producer")]]

def isFact : Atom → Bool
  | .expression [.symbol head, .symbol _] => head == "p" || head == "q"
  | _ => false

def facts (space : List Atom) : Finset Atom := (space.filter isFact).toFinset

def expectedFacts : Finset Atom := [p "a", p "b", q "a", q "b"].toFinset

theorem standing_both_orders_reach_all_facts (consumerFirst : Bool) :
    facts (run 8 (standing consumerFirst)).1 = expectedFacts := by
  cases consumerFirst <;> decide +kernel

theorem standing_still_has_work (consumerFirst : Bool) :
    cRuleScopedSourceWorkQueueStep .leaveInert (run 8 (standing consumerFirst)).1 ≠ none := by
  cases consumerFirst <;> decide +kernel

/-- The four residual stores are actual source execution states. Closure of
this cycle is checked against the independent source step, including its
selected rule, full matcher, generated directive and support finalization. -/
def cycle (consumerFirst : Bool) (phase : Fin 4) : List Atom :=
  (run phase.val (run 8 (standing consumerFirst)).1).1

theorem run_zero_store (space : List Atom) : (run 0 space).1 = space := rfl

theorem cycle_zero (consumerFirst : Bool) :
    cycle consumerFirst 0 = (run 8 (standing consumerFirst)).1 := by
  unfold cycle
  exact run_zero_store _

theorem run_add_store (first later : Nat) (space : List Atom) :
    (run (first + later) space).1 = (run later (run first space).1).1 := by
  have split := congrArg (fun result : List Atom × Nat => result.1)
    (MM2ResumableExecution.pause_resume_exact .leaveInert first later space)
  exact split

theorem cycle_step (consumerFirst : Bool) (phase : Fin 4) :
    cRuleScopedSourceWorkQueueStep .leaveInert (cycle consumerFirst phase) =
      some (cycle consumerFirst (phase + 1)) := by
  cases consumerFirst <;> fin_cases phase <;> decide +kernel

theorem cycle_facts (consumerFirst : Bool) (phase : Fin 4) :
    facts (cycle consumerFirst phase) = expectedFacts := by
  cases consumerFirst <;> fin_cases phase <;> decide +kernel

def advancePhase : Nat → Fin 4 → Fin 4
  | 0, phase => phase
  | fuel + 1, phase => advancePhase fuel (phase + 1)

theorem run_cycle (consumerFirst : Bool) (fuel : Nat) (phase : Fin 4) :
    run fuel (cycle consumerFirst phase) =
      (cycle consumerFirst (advancePhase fuel phase), fuel) := by
  induction fuel generalizing phase with
  | zero => rfl
  | succ fuel ih =>
      change (match cRuleScopedSourceWorkQueueStep .leaveInert (cycle consumerFirst phase) with
        | none => (cycle consumerFirst phase, 0)
        | some next => let later := run fuel next; (later.1, later.2 + 1)) = _
      rw [cycle_step]
      simp only [ih, advancePhase]

/-- Both fair standing schedules agree from this point onward at every
finite observation depth, not only at the tested completion prefix. -/
theorem standing_eventual_agreement (consumerFirst : Bool) (later : Nat) :
    facts (run (8 + later) (standing consumerFirst)).1 = expectedFacts := by
  rw [run_add_store, ← cycle_zero, run_cycle]
  exact cycle_facts consumerFirst _

theorem standing_eventually_never_quiescent (consumerFirst : Bool) (later : Nat) :
    cRuleScopedSourceWorkQueueStep .leaveInert
      (run (8 + later) (standing consumerFirst)).1 ≠ none := by
  rw [run_add_store, ← cycle_zero, run_cycle, cycle_step]
  exact Option.some_ne_none _

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Controls
