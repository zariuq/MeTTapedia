import Mettapedia.Machines.RuntimePlumbing.DependencyStamps

/-!
# Dependency regions for declaration observers

The direct lookup separates exact-subject declarations, general-subject rows
and subtype rows. It deliberately does not assert that these are all the
dependencies of recursive inference, evaluated types, modules or mutable
identity values. Such services issue their own additional reads.

The observer is a pure parameter and answers from all three regions. The
theorems justify reuse of this service in any pure adaptive client. They do not
identify it with an implementation of HE type inference or license erasing
fresh-variable allocation from a polymorphic type answer.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RuntimePlumbing.DeclarationDependencies

open ReadOnlyQuery DependencyStamps

inductive Region where
  | subject (symbol : Nat)
  | generalSubjects
  | subtypes
  | imports
  | equations (symbol : Nat)
  | identity (cell : Nat)
  deriving DecidableEq, Repr

variable {Row Answer : Type}

def lookup (subject : Nat) (observe : List Row → List Row → List Row → Answer) :
    Program Region (List Row) Answer :=
  .read (.subject subject) fun exactRows =>
    .read .generalSubjects fun generalRows =>
      .read .subtypes fun subtypeRows => .pure (observe exactRows generalRows subtypeRows)

theorem lookup_reads (memory : Memory Region (List Row)) (subject : Nat)
    (observe : List Row → List Row → List Row → Answer) :
    (run memory.value (lookup subject observe)).reads =
      [(.subject subject, memory.value (.subject subject)),
        (.generalSubjects, memory.value .generalSubjects),
        (.subtypes, memory.value .subtypes)] := rfl

theorem unrelated_subject_reuses (memory : Memory Region (List Row)) (subject other : Nat)
    (different : other ≠ subject) (rows : List Row)
    (observe : List Row → List Row → List Row → Answer) :
    run (write memory (.subject other) rows).value (lookup subject observe) =
      run memory.value (lookup subject observe) := by
  apply unrelated_write_reuses
  intro observed member
  simp only [lookup_reads, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [Ne.symm different]

namespace Controls

def initial : Memory Region (List Nat) :=
  ⟨fun region => match region with | .subject 1 => [10] | _ => [], fun _ => 0⟩

def answers : Program Region (List Nat) (List Nat) :=
  lookup 1 (fun exactRows generalRows subtypeRows => exactRows ++ generalRows ++ subtypeRows)

theorem unrelated_type_declaration_does_not_flush_the_entry :
    check initial (write initial (.subject 2) [99]) (run initial.value answers).reads = true ∧
      (run (write initial (.subject 2) [99]).value answers).answer = [10] := by decide

theorem a_general_declaration_changes_the_answer_and_expires_the_entry :
    check initial (write initial .generalSubjects [20]) (run initial.value answers).reads = false ∧
      (run (write initial .generalSubjects [20]).value answers).answer = [10, 20] := by decide

theorem a_subtype_change_is_also_a_dependency :
    check initial (write initial .subtypes [30]) (run initial.value answers).reads = false ∧
      (run (write initial .subtypes [30]).value answers).answer = [10, 30] := by decide

theorem checking_only_the_named_stamp_misses_a_changed_general_region :
    initial.stamp (.subject 1) = (write initial .generalSubjects [20]).stamp (.subject 1) ∧
      (run initial.value answers).answer ≠
        (run (write initial .generalSubjects [20]).value answers).answer := by decide

end Controls

end Mettapedia.Machines.RuntimePlumbing.DeclarationDependencies
