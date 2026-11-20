import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Refutation

/-!
# The checker: from the rows of a definition to a verdict

**For each row** (`checkRow`, `rowVerdict`): elaborate it (frame, what its patterns teach, made row),
synthesize the body's typing in its frame, and decide admission with the package's settler
(`vecAdmits?`). When that decision says nothing, try to refute the row at the settler's answer
(`refuteRow?`). Three outcomes: **admitted**, **refused**, **not decided**.

**For the definition** (`checkDefinition`): admitted when every row is; refused, with the first
refused row; otherwise not decided.

* **Soundness of yes** (`checkDefinition_admitted`): every row elaborates, its firing is admitted by
  the computable converting step, and its made row is typed after its match, at every solution of
  what its patterns teach.
* **Soundness of no** (`checkDefinition_refused`): the refused row elaborates, and its firing is
  refused by the converting step **for every settler**.
* A failure of elaboration, of synthesis or of the budget never gives a verdict by itself: a "yes"
  needs the settler's answer and a found conversion, and a "no" needs refuted information or a proved
  refutation at the settler's answer; otherwise the verdict is **not decided**.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors.Checker

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg)

/-! ## One row -/

/-- The families the checker settles with, at a budget. -/
abbrev families (fuel : Nat) : List (Family vecS.levels) := [vecFamily fuel fuel]

/-- **Refuting a row at the settler's answer**: the answer solves what the patterns teach, and along
it the body is not typed at the declared type. -/
def refuteRow? (fuel : Nat) {n : Nat} (e : Elaborated n) :
    Option (PLift (¬ TypedAfterMatch vecS.levels e.tells e.made)) :=
  match firstDecisionAt vecS.levels e.firing.information (families fuel) with
  | .settled M σ initial =>
      (refute? fuel M.raw (subst σ.substitution e.made.code) (e.made.type.reindex σ).code).bind fun r =>
        some ⟨fun after => r.down M.formed (e.made.type.reindex σ).isType
          ((typedAfterMatch_iff vecS.levels e.tells e.made).mp after M σ initial.solves)⟩
  | _ => none

/-- **A row not typed after its match is refused, for every settler.** -/
theorem refused_of_not_typedAfterMatch {n : Nat} {e : Elaborated n}
    (notTyped : ¬ TypedAfterMatch vecS.levels e.tells e.made) (settler : Settler vecS.levels) :
    ¬ (convertingStep vecS.levels Nat settler).Admits e.firing := fun admitted =>
  notTyped (converting_typedAfterMatch vecS.levels settler admitted (0, e.made) (List.mem_singleton_self _))

/-- The three outcomes for a row. -/
inductive RowVerdict where
  | admitted
  | refused
  | undecided
  deriving DecidableEq, Repr

/-- **The verdict on an elaborated row.** -/
def checkRow (fuel : Nat) {n : Nat} (e : Elaborated n) : RowVerdict :=
  match synthesize fuel e.frame e.made.code with
  | some s =>
      match vecAdmits? (families fuel) fuel e.firing (frameTypeOf e s) with
      | some true => .admitted
      | some false => .refused
      | none => if (refuteRow? fuel e).isSome then .refused else .undecided
  | none => if (refuteRow? fuel e).isSome then .refused else .undecided

/-- **Soundness of yes for a row**: the computable converting step admits its firing. -/
theorem checkRow_admitted {fuel n : Nat} {e : Elaborated n} (verdict : checkRow fuel e = .admitted) :
    (convertingStep vecS.levels Nat (vecSettler fuel fuel)).Admits e.firing := by
  unfold checkRow at verdict
  split at verdict
  · rename_i s _
    split at verdict
    · rename_i decided
      exact vecAdmits?_sound decided
    · cases verdict
    · split at verdict <;> cases verdict
  · split at verdict <;> cases verdict

/-- **Soundness of no for a row**: no settler's converting step admits its firing. -/
theorem checkRow_refused {fuel n : Nat} {e : Elaborated n} (verdict : checkRow fuel e = .refused)
    (settler : Settler vecS.levels) : ¬ (convertingStep vecS.levels Nat settler).Admits e.firing := by
  have fromRefutation : (refuteRow? fuel e).isSome = true →
      ¬ (convertingStep vecS.levels Nat settler).Admits e.firing := by
    intro found
    obtain ⟨r, _⟩ := Option.isSome_iff_exists.mp found
    exact refused_of_not_typedAfterMatch r.down settler
  unfold checkRow at verdict
  split at verdict
  · split at verdict
    · cases verdict
    · rename_i decided
      exact vecAdmits?_refuted decided settler
    · split at verdict
      · rename_i found
        exact fromRefutation found
      · cases verdict
  · split at verdict
    · rename_i found
      exact fromRefutation found
    · cases verdict

/-- **An admitted row is typed after its match**, at every solution of what its patterns teach. -/
theorem checkRow_typedAfterMatch {fuel n : Nat} {e : Elaborated n} (verdict : checkRow fuel e = .admitted) :
    TypedAfterMatch vecS.levels e.tells e.made :=
  converting_typedAfterMatch vecS.levels (vecSettler fuel fuel) (checkRow_admitted verdict) (0, e.made)
    (List.mem_singleton_self _)

/-- **The verdict on a source row**: not decided when it does not elaborate within the budget. -/
def rowVerdict (fuel : Nat) (d : Definition) (r : Row) : RowVerdict :=
  match elaborate fuel d r with
  | none => .undecided
  | some e => checkRow fuel e

/-! ## The definition -/

/-- The three outcomes for a definition; a refusal names the row. -/
inductive Verdict where
  | admitted
  | refused (row : Nat)
  | undecided
  deriving DecidableEq, Repr

/-- The verdicts of the rows, from position `i`: the first refused row, or admitted if all are. -/
def combine : Nat → List RowVerdict → Verdict
  | _, [] => .admitted
  | i, .refused :: _ => .refused i
  | i, .admitted :: rest => combine (i + 1) rest
  | i, .undecided :: rest =>
      match combine (i + 1) rest with
      | .refused j => .refused j
      | _ => .undecided

/-- **The checker.** -/
def checkDefinition (fuel : Nat) (d : Definition) : Verdict :=
  combine 0 (d.rows.map (rowVerdict fuel d))

theorem combine_admitted : ∀ {i : Nat} {vs : List RowVerdict}, combine i vs = .admitted →
    ∀ v ∈ vs, v = .admitted
  | _, [], _ => fun _ member => absurd member List.not_mem_nil
  | _, .refused :: _, h => by cases h
  | i, .admitted :: rest, h => by
      intro v member
      rcases List.mem_cons.mp member with same | later
      · exact same
      · exact combine_admitted (i := i + 1) h v later
  | i, .undecided :: rest, h => by
      simp only [combine] at h
      split at h <;> cases h

theorem combine_refused : ∀ {i j : Nat} {vs : List RowVerdict}, combine i vs = .refused j →
    i ≤ j ∧ vs[j - i]? = some .refused
  | _, _, [], h => by cases h
  | i, j, .refused :: _, h => by
      cases h
      exact ⟨le_rfl, by simp⟩
  | i, j, .admitted :: rest, h => by
      obtain ⟨le, at'⟩ := combine_refused (i := i + 1) h
      refine ⟨by omega, ?_⟩
      have shift : j - i = (j - (i + 1)) + 1 := by omega
      rw [shift]
      simpa using at'
  | i, j, .undecided :: rest, h => by
      simp only [combine] at h
      split at h
      · rename_i k later
        cases h
        obtain ⟨le, at'⟩ := combine_refused (i := i + 1) later
        refine ⟨by omega, ?_⟩
        have shift : j - i = (j - (i + 1)) + 1 := by omega
        rw [shift]
        simpa using at'
      · cases h

/-- **Soundness of yes**: if the definition is admitted, every row elaborates, its firing is admitted
by the computable converting step, and its made row is typed after its match. -/
theorem checkDefinition_admitted {fuel : Nat} {d : Definition} (verdict : checkDefinition fuel d = .admitted) :
    ∀ r ∈ d.rows, ∃ e, elaborate fuel d r = some e ∧
      (convertingStep vecS.levels Nat (vecSettler fuel fuel)).Admits e.firing ∧
        TypedAfterMatch vecS.levels e.tells e.made := by
  intro r member
  have rowAdmitted := combine_admitted verdict (rowVerdict fuel d r) (List.mem_map_of_mem member)
  unfold rowVerdict at rowAdmitted
  split at rowAdmitted
  · cases rowAdmitted
  · rename_i e elaborated
    exact ⟨e, elaborated, checkRow_admitted rowAdmitted, checkRow_typedAfterMatch rowAdmitted⟩

/-- **Soundness of no**: the refused row elaborates, and its firing is refused by the converting step
for every settler. -/
theorem checkDefinition_refused {fuel : Nat} {d : Definition} {i : Nat}
    (verdict : checkDefinition fuel d = .refused i) :
    ∃ r, d.rows[i]? = some r ∧ ∃ e, elaborate fuel d r = some e ∧
      ∀ settler : Settler vecS.levels, ¬ (convertingStep vecS.levels Nat settler).Admits e.firing := by
  obtain ⟨-, at'⟩ := combine_refused verdict
  simp only [Nat.sub_zero, List.getElem?_map] at at'
  cases row : d.rows[i]? with
  | none => rw [row] at at'; cases at'
  | some r =>
      rw [row] at at'
      simp only [Option.map_some, Option.some.injEq] at at'
      refine ⟨r, rfl, ?_⟩
      unfold rowVerdict at at'
      split at at'
      · cases at'
      · rename_i e elaborated
        exact ⟨e, elaborated, fun settler => checkRow_refused at' settler⟩

end NativeTypesOnTheStep.Computing.Vectors.Checker

#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.refuteRow?
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.refused_of_not_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.checkRow
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.checkRow_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.checkRow_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.checkRow_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.checkDefinition
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.combine_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.combine_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.checkDefinition_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.checkDefinition_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
