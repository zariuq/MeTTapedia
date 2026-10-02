import Mettapedia.Machines.SourceProducerAdmission

/-!
# Bounded production: source admission, instruction cost, and residual state

This module instruments `RecursiveFiniteProducer.step`, rather than counting
only successful pull requests. One counted instruction is an existing cursor
`advance`, `yield`, or `finish`; callback implementation cost is not included.
The concrete repeated-tail source has no callbacks, and its first occurrence
requires exactly `4 * input.length + 3` instructions although its eager result
has `2 ^ input.length` occurrences. The residual frames retain the other
occurrences. Thus collection materialization can disappear without pretending
that all continuation state can disappear.

The correctness statements concern successful bounded requests. Fuel exhaustion
returns no result and discards the private partial batch. No theorem here
asserts externally interrupted partial-execution resumption, or equivalence
of eager and bounded execution under semantic fuel or timing observation.

The source bridge is the checked, scope-resolved equation fragment of
`SourceProducerAdmission`. A parser-to-IR and native-runtime correspondence
remain separate obligations. This is not a theorem for arbitrary PeTTa or HE.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProducerDemandCost


universe u v
variable {Item : Type u} {Value : Type v}

structure Result (Item : Type u) (Value : Type v) where
  output : List Value
  residual : RecursiveFiniteProducer.State Item Value
  instructions : Nat

/-- Fuel exhaustion and declined instructions publish no successful result.
Satisfied demand retains the actual cursor state, without pulling ahead. -/
def run (construct : Item → Value → Value)
    (callback : Nat → Value → Value → Value) (program : RecursiveFiniteProducer.Code Value) :
    Nat → Nat → RecursiveFiniteProducer.State Item Value → Option (Result Item Value)
  | _, 0, state => some ⟨[], state, 0⟩
  | 0, _ + 1, _ => none
  | fuel + 1, demand + 1, state =>
      match RecursiveFiniteProducer.step construct callback program state with
      | .decline => none
      | .finish => some ⟨[], [], 1⟩
      | .advance next =>
          (run construct callback program fuel (demand + 1) next).map
            (fun result => { result with instructions := result.instructions + 1 })
      | .yield value next =>
          (run construct callback program fuel demand next).map
            (fun result => ⟨value :: result.output, result.residual, result.instructions + 1⟩)

@[simp] theorem zero_demand (construct : Item → Value → Value)
    (callback : Nat → Value → Value → Value) (program : RecursiveFiniteProducer.Code Value)
    (fuel : Nat) (state : RecursiveFiniteProducer.State Item Value) :
    run construct callback program fuel 0 state = some ⟨[], state, 0⟩ := by
  cases fuel <;> rfl

/-- Every successful bounded run has exactly the requested prefix (or the
complete exhausted result), and its residual denotes precisely the rest.
The invariant retains occurrences, including equal payloads. -/
theorem run_sound (construct : Item → Value → Value)
    (callback : Nat → Value → Value → Value) (program : RecursiveFiniteProducer.Code Value)
    (fuel demand : Nat) (state : RecursiveFiniteProducer.State Item Value) (items : List Value)
    (meaning : RecursiveFiniteProducer.denote construct callback program state = some items)
    (result : Result Item Value)
    (done : run construct callback program fuel demand state = some result) :
    result.output = items.take demand ∧
      RecursiveFiniteProducer.denote construct callback program result.residual =
        some (items.drop result.output.length) ∧ result.instructions ≤ fuel := by
  induction fuel generalizing demand state items result with
  | zero =>
      cases demand with
      | zero => simp only [run, Option.some.injEq] at done; subst result; simp [meaning]
      | succ demand => simp [run] at done
  | succ fuel ih =>
      cases demand with
      | zero => simp only [run, Option.some.injEq] at done; subst result; simp [meaning]
      | succ demand =>
          have stepMeaning := RecursiveFiniteProducer.step_meaning construct callback program state
          cases observed : RecursiveFiniteProducer.step construct callback program state with
          | decline => simp [run, observed] at done
          | finish =>
              simp only [observed] at stepMeaning
              rw [meaning] at stepMeaning
              cases stepMeaning
              simp only [run, observed, Option.some.injEq] at done
              subst result
              simp [RecursiveFiniteProducer.denote]
          | advance next =>
              simp only [observed] at stepMeaning
              cases tailDone : run construct callback program fuel (demand + 1) next with
              | none => simp [run, observed, tailDone] at done
              | some tail =>
                  simp only [run, observed, tailDone, Option.map_some, Option.some.injEq] at done
                  subst result
                  obtain ⟨out, rest, cost⟩ := ih (demand + 1) next items
                    (stepMeaning.symm.trans meaning) tail tailDone
                  exact ⟨out, rest, Nat.add_le_add_right cost 1⟩
          | yield value next =>
              simp only [observed] at stepMeaning
              cases tailMeaning : RecursiveFiniteProducer.denote construct callback program next with
              | none => simp [meaning, tailMeaning] at stepMeaning
              | some suffix =>
                  simp only [tailMeaning, Option.map_some, meaning, Option.some.injEq] at stepMeaning
                  subst items
                  cases tailDone : run construct callback program fuel demand next with
                  | none => simp [run, observed, tailDone] at done
                  | some tail =>
                      simp only [run, observed, tailDone, Option.map_some, Option.some.injEq] at done
                      subst result
                      obtain ⟨out, rest, cost⟩ := ih demand next suffix tailMeaning tail tailDone
                      refine ⟨?_, ?_, Nat.add_le_add_right cost 1⟩
                      · simpa using congrArg (value :: ·) out
                      · simpa using rest

/-- Each output occurrence requires its own `yield` instruction in this
explicit-emission cursor model. This lower bound does not apply to compressed
counts or folds, which have a different observation. -/
theorem output_length_le_instructions (construct : Item → Value → Value)
    (callback : Nat → Value → Value → Value) (program : RecursiveFiniteProducer.Code Value)
    (fuel demand : Nat) (state : RecursiveFiniteProducer.State Item Value)
    (result : Result Item Value)
    (done : run construct callback program fuel demand state = some result) :
    result.output.length ≤ result.instructions := by
  induction fuel generalizing demand state result with
  | zero =>
      cases demand with
      | zero => simp only [run, Option.some.injEq] at done; subst result; simp
      | succ demand => simp [run] at done
  | succ fuel ih =>
      cases demand with
      | zero => simp only [run, Option.some.injEq] at done; subst result; simp
      | succ demand =>
          cases observed : RecursiveFiniteProducer.step construct callback program state with
          | decline => simp [run, observed] at done
          | finish => simp only [run, observed, Option.some.injEq] at done; subst result; simp
          | advance next =>
              cases nextDone : run construct callback program fuel (demand + 1) next with
              | none => simp [run, observed, nextDone] at done
              | some tail =>
                  simp only [run, observed, nextDone, Option.map_some, Option.some.injEq] at done
                  subst result
                  exact Nat.le_trans (ih _ _ tail nextDone) (Nat.le_succ _)
          | yield value next =>
              cases nextDone : run construct callback program fuel demand next with
              | none => simp [run, observed, nextDone] at done
              | some tail =>
                  simp only [run, observed, nextDone, Option.map_some, Option.some.injEq] at done
                  subst result
                  exact Nat.add_le_add_right (ih _ _ tail nextDone) 1

/-- The compiler, not an assumed total result, establishes applicability to
an equation program. Successful measured runs agree with its unique eager
collection and keep an exact residual. -/
theorem admitted_source_run (construct : Item → Value → Value)
    (callback : Nat → Value → Value → Value)
    (source : List (SourceProducerAdmission.Equation Value)) (program : RecursiveFiniteProducer.Code Value)
    (accepted : SourceProducerAdmission.compile source = some program) (input : List Item) (parameter : Nat) :
    ∃ items, SourceProducerAdmission.source construct callback source input parameter = [items] ∧
      ∀ fuel demand result,
        run construct callback program fuel demand (RecursiveFiniteProducer.initial program input parameter) = some result →
        result.output = items.take demand ∧
          RecursiveFiniteProducer.denote construct callback program result.residual =
            some (items.drop result.output.length) ∧ result.instructions ≤ fuel := by
  obtain ⟨_, items, eager, sourceMeaning⟩ :=
    SourceProducerAdmission.compile_source construct callback source program accepted input parameter
  refine ⟨items, sourceMeaning, ?_⟩
  intro fuel demand result done
  exact run_sound construct callback program fuel demand _ items
    ((RecursiveFiniteProducer.denote_initial construct callback program input parameter).trans eager) result done

/-- Remaining answers require a semantically nonempty continuation. This
says nothing about whether that continuation uses a list, stack, or graph. -/
theorem residual_required (construct : Item → Value → Value)
    (callback : Nat → Value → Value → Value) (program : RecursiveFiniteProducer.Code Value)
    (fuel demand : Nat) (state : RecursiveFiniteProducer.State Item Value) (items : List Value)
    (meaning : RecursiveFiniteProducer.denote construct callback program state = some items)
    (result : Result Item Value)
    (done : run construct callback program fuel demand state = some result)
    (remaining : demand < items.length) : result.residual ≠ [] := by
  obtain ⟨out, rest, _⟩ := run_sound construct callback program fuel demand state items meaning result done
  intro empty
  rw [empty, RecursiveFiniteProducer.denote] at rest
  have lengths := congrArg (fun value : Option (List Value) => value.map List.length) rest
  simp only [Option.map_some, Option.some.injEq, List.length_nil, List.length_drop] at lengths
  rw [out, List.length_take] at lengths
  omega

namespace Repeated

/-- Two source equations: the empty input yields one value; the cons input
appends two calls on its tail. This is source structure, not a function-name
recognizer. Source admission supplies the four-way decision tree. -/
abbrev source (value : Value) := SourceProducerAdmission.Examples.repeated value
abbrev program (value : Value) := (SourceProducerAdmission.Examples.repeatedTree value).code

/-- Pending right-hand tail calls, deepest first, after the first leaf. -/
def residual (items : List Item) (parameter : Nat) : RecursiveFiniteProducer.State Item Value :=
  match items with
  | [] => []
  | head :: tail => residual tail parameter ++ [⟨.callTail, head :: tail, parameter, []⟩]

@[simp] theorem residual_length (items : List Item) (parameter : Nat) :
    (residual (Value := Value) items parameter).length = items.length := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp [residual, ih]

/-- Exact cost against the existing small-step cursor: two shape tests per
invocation, append and recursive-call instructions per cons, and one yield.
No continuation beyond the first yielded value is executed. -/
theorem first_instruction_count (construct : Item → Value → Value)
    (callback : Nat → Value → Value → Value) (value : Value)
    (items : List Item) (parameter : Nat) (rest : RecursiveFiniteProducer.State Item Value) :
    run construct callback (program value) (4 * items.length + 3) 1
        (⟨program value, items, parameter, []⟩ :: rest) =
      some ⟨[value], residual items parameter ++ rest, 4 * items.length + 3⟩ := by
  induction items generalizing rest with
  | nil =>
      cases parameter <;> rfl
  | cons head tail ih =>
      have cost : 4 * (head :: tail).length + 3 = (4 * tail.length + 3) + 4 := by simp; omega
      rw [cost]
      have first := ih (⟨.callTail, head :: tail, parameter, []⟩ :: rest)
      let bump : Result Item Value → Result Item Value :=
        fun result => {result with instructions := result.instructions + 1}
      have unfoldFour :
          run construct callback (program value) (4 * tail.length + 3 + 4) 1
            (⟨program value, head :: tail, parameter, []⟩ :: rest) =
          ((((run construct callback (program value) (4 * tail.length + 3) 1
            (⟨program value, tail, parameter, []⟩ ::
             ⟨.callTail, head :: tail, parameter, []⟩ :: rest)).map bump).map bump).map bump).map bump := by
        cases parameter <;> rfl
      rw [unfoldFour, first]
      simp [bump, residual, List.append_assoc, Nat.add_assoc]

/-- The source and the measured cursor are connected through the actual
admission compiler, not an assumed equality to a prefix-producing oracle. -/
theorem source_first_cost (construct : Item → Value → Value)
    (callback : Nat → Value → Value → Value) (value : Value)
    (items : List Item) (parameter : Nat) :
    SourceProducerAdmission.compile (source value) = some (program value) ∧
    SourceProducerAdmission.source construct callback (source value) items parameter =
      [List.replicate (2 ^ items.length) value] ∧
    run construct callback (program value) (4 * items.length + 3) 1
        (RecursiveFiniteProducer.initial (program value) items parameter) =
      some ⟨[value], residual items parameter, 4 * items.length + 3⟩ ∧
    (residual (Value := Value) items parameter).length = items.length := by
  refine ⟨SourceProducerAdmission.Examples.repeated_accepted value,
    SourceProducerAdmission.Examples.repeated_source_cardinality construct callback value items parameter,
    ?_, residual_length items parameter⟩
  simpa [RecursiveFiniteProducer.initial] using
    first_instruction_count construct callback value items parameter []

/-- Complete explicit enumeration cannot take the first-answer shortcut: all
occurrences must be emitted, even when every payload is identical. -/
theorem complete_enumeration_lower_bound (construct : Item → Value → Value)
    (callback : Nat → Value → Value → Value) (value : Value)
    (items : List Item) (parameter fuel : Nat) (result : Result Item Value)
    (done : run construct callback (program value) fuel (2 ^ items.length)
      (RecursiveFiniteProducer.initial (program value) items parameter) = some result) :
    2 ^ items.length ≤ result.instructions := by
  obtain ⟨values, sourceValues, correct⟩ := admitted_source_run construct callback
    (source value) (program value) (SourceProducerAdmission.Examples.repeated_accepted value)
    items parameter
  rw [SourceProducerAdmission.Examples.repeated_source_cardinality] at sourceValues
  have equal : values = List.replicate (2 ^ items.length) value := by simpa using sourceValues.symm
  subst values
  have prefixEq := (correct fuel (2 ^ items.length) result done).1
  have count := output_length_le_instructions construct callback (program value) fuel
    (2 ^ items.length) _ result done
  rw [prefixEq] at count
  simpa using count

theorem first_cost_below_full_emissions (n : Nat) (large : 5 ≤ n) :
    4 * n + 3 < 2 ^ n := by
  induction n, large using Nat.le_induction with
  | base => decide
  | succ n lower ih =>
      rw [Nat.pow_succ]
      omega

/-- Discarding a nonempty-input residual destroys legitimate future
occurrences. Equal payloads cannot justify discarding these alternatives. -/
theorem first_residual_denotation (construct : Item → Value → Value)
    (callback : Nat → Value → Value → Value) (value : Value)
    (items : List Item) (parameter : Nat) :
    RecursiveFiniteProducer.denote construct callback (program value) (residual items parameter) =
      some (List.replicate (2 ^ items.length - 1) value) := by
  obtain ⟨values, sourceValues, correct⟩ := admitted_source_run construct callback
    (source value) (program value) (SourceProducerAdmission.Examples.repeated_accepted value)
    items parameter
  rw [SourceProducerAdmission.Examples.repeated_source_cardinality] at sourceValues
  have equal : values = List.replicate (2 ^ items.length) value := by simpa using sourceValues.symm
  subst values
  have done := (source_first_cost construct callback value items parameter).2.2.1
  have remaining := (correct (4 * items.length + 3) 1 _ done).2.1
  simpa using remaining

/-- Independent source admission rejects overlapping alternative collections.
A list-valued deterministic producer and a relational mapper are distinct. -/
theorem uncommitted_alternatives_not_admitted :
    SourceProducerAdmission.compile
      (SourceProducerAdmission.Examples.uncommittedCombinations (Item := Nat)) = none :=
  SourceProducerAdmission.Examples.uncommitted_rejected

/-- A concrete source workload: 20 tail duplications describe 1,048,576
occurrences, but selecting one executes 83 cursor instructions and retains
20 frames. No complete million-element collection is evaluated in this proof. -/
theorem twenty_levels_first :
    (run (fun (_ : Nat) value => value) (fun _ left _ => left) (program 7)
      83 1 (RecursiveFiniteProducer.initial (program 7) (List.replicate 20 0) 0)).map
      (fun result => (result.output, result.instructions, result.residual.length)) =
      some ([7], 83, 20) := by
  have first := (source_first_cost (fun (_ : Nat) value => value)
    (fun _ left _ => left) 7 (List.replicate 20 0) 0).2.2.1
  simp only [List.length_replicate, Nat.reduceMul, Nat.reduceAdd] at first
  rw [first]
  simp

/-- The same source family has multiplicity, despite equal payloads. -/
theorem twenty_levels_eager_cardinality :
    (List.replicate (2 ^ (List.replicate 20 (0 : Nat)).length) (7 : Nat)).length =
      1048576 := by
  simp only [List.length_replicate]

/-- The actual bounded cursor's visible payload list, discarding its state.
All inputs to this admitted family succeed; the default is never used. -/
def firstObservation (items : List Nat) : List Nat :=
  ((run (fun (_ : Nat) value => value) (fun _ left _ => left) (program 7)
    (4 * items.length + 3) 1
    (RecursiveFiniteProducer.initial (program 7) items 0)).map Result.output).getD []

theorem firstObservation_eq (items : List Nat) : firstObservation items = [7] := by
  unfold firstObservation
  rw [(source_first_cost (fun (_ : Nat) value => value)
    (fun _ left _ => left) 7 items 0).2.2.1]
  rfl

/-- No representation-independent recovery function can reconstruct complete
source results from the first observed payload alone. Empty and singleton
inputs have the same first observation but different occurrence multiplicity.
A resumable implementation must retain additional information; this theorem
requires no particular representation for that information. -/
theorem no_recovery_from_first_observation :
    ¬ ∃ recover : List Nat → List (List Nat), ∀ items : List Nat,
      recover (firstObservation items) =
        SourceProducerAdmission.source (fun (_ : Nat) value => value)
          (fun _ left _ => left) (source 7) items 0 := by
  rintro ⟨recover, faithful⟩
  have empty := faithful []
  have singleton := faithful [0]
  rw [firstObservation_eq] at empty singleton
  have same := empty.symm.trans singleton
  change SourceProducerAdmission.source _ _ (SourceProducerAdmission.Examples.repeated _) _ _ =
    SourceProducerAdmission.source _ _ (SourceProducerAdmission.Examples.repeated _) _ _ at same
  rw [SourceProducerAdmission.Examples.repeated_source_cardinality,
    SourceProducerAdmission.Examples.repeated_source_cardinality] at same
  simp at same

end Repeated

namespace Controls

open FiniteProducerLowering

/-- These existing eager-source programs are not silently coerced into the
pure producer fragment. Each rejection accompanies an observable mismatch. -/
theorem effectful_tail_requires_eager_effect :
    eagerPrefix FiniteProducerLowering.Controls.combine id 1 FiniteProducerLowering.Controls.lateEffect = .done [1] [9] ∧
    lower FiniteProducerLowering.Controls.lateEffect = none :=
  ⟨FiniteProducerLowering.Controls.early_return_would_omit_late_effect.1,
    FiniteProducerLowering.Controls.early_return_would_omit_late_effect.2.2⟩

theorem failing_tail_cannot_publish_first :
    eagerPrefix FiniteProducerLowering.Controls.combine id 1 FiniteProducerLowering.Controls.lateFailure = .done [] [] ∧
    lower FiniteProducerLowering.Controls.lateFailure = none :=
  ⟨FiniteProducerLowering.Controls.late_failure_cancels_collection.1,
    FiniteProducerLowering.Controls.late_failure_cancels_collection.2.2⟩

theorem divergent_tail_cannot_publish_first :
    eagerPrefix FiniteProducerLowering.Controls.combine id 1 FiniteProducerLowering.Controls.lateLoop = .diverges ∧
    lower FiniteProducerLowering.Controls.lateLoop = none :=
  ⟨FiniteProducerLowering.Controls.early_return_would_hide_late_divergence.1,
    FiniteProducerLowering.Controls.early_return_would_hide_late_divergence.2.2⟩

theorem relational_mapper_has_cartesian_occurrences :
    eagerPrefix FiniteProducerLowering.Controls.combine id 20 FiniteProducerLowering.Controls.lateChoice =
      .done [1, 2, 1, 12, 11, 2, 11, 12] [] ∧
    lower FiniteProducerLowering.Controls.lateChoice = none :=
  ⟨FiniteProducerLowering.Controls.nondeterministic_map_is_not_stream_flatMap.1,
    FiniteProducerLowering.Controls.nondeterministic_map_is_not_stream_flatMap.2.2⟩

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- A PeTTa value occurrence remains a value even if its payload spells a
call. An evaluating adapter needs a different theorem. -/
theorem producer_payload_is_value
    (p : Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences.Program) (value : Atom) :
    Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences.evalPlanned p .value value = [value] := by
  cases value <;> rfl

theorem changing_adapter_changes_call_payload :
    SuperposeFusion.answers [FiniteProducerLowering.Controls.callValue] = [FiniteProducerLowering.Controls.callValue] ∧
    evaluateElements
      (Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences.evalCode
        Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences.Examples.callsSymbols)
      [FiniteProducerLowering.Controls.callValue] = [.grounded (.int 42)] :=
  FiniteProducerLowering.Controls.value_and_evaluating_adapters_differ

/-- Zero demand is a control boundary, including for a rejected body. -/
theorem zero_demand_skips_unsupported :
    run (fun (_ : Nat) value => value) (fun _ left _ => left)
      (.unsupported : RecursiveFiniteProducer.Code Nat) 0 0
      (RecursiveFiniteProducer.initial .unsupported [] 0) =
      some ⟨[], RecursiveFiniteProducer.initial .unsupported [] 0, 0⟩ := rfl

end Controls


end Mettapedia.Machines.ProducerDemandCost
