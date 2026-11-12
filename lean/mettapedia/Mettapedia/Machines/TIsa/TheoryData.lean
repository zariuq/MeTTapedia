import Mettapedia.Machines.TIsa.RuleCompiler

/-!
# Data and acceptance for reflected native rule tables

JSON is an external adapter. This module and the matching proofs operate only
on ordinary data. Privileged publishers are accounted for without asserting
that arbitrary published typing or conversion facts are true.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.TheoryData

open RuleTable

inductive Role where
  | publisher
  | premise
  deriving DecidableEq, Repr

structure Entry where
  id : Nat
  name : String
  role : Role
  variableCount : Nat
  source : Rule
  plan : Option Plan
  deriving DecidableEq, Repr

def Atom.within (variableCount : Nat) : Atom → Bool
  | .literal _ => true
  | .variable name => decide (name < variableCount)

def Entry.checked? (entry : Entry) : Bool :=
  entry.source.atoms.all (Atom.within entry.variableCount) &&
    match entry.role, entry.plan with
    | .publisher, none => entry.source.premises.isEmpty
    | .premise, some plan => entry.source.checkPlan plan
    | _, _ => false

def checkedKernelTable? (entries : List Entry) : Bool :=
  entries.map Entry.id == List.range 23 &&
  entries.all (fun entry => entry.role == (if entry.id < 12 then .publisher else .premise)) &&
  entries.all Entry.checked?

theorem checkedKernelTable_member (entries : List Entry)
    (checked : checkedKernelTable? entries = true) (entry : Entry) (member : entry ∈ entries) :
    entry.checked? = true := by
  simp only [checkedKernelTable?, Bool.and_eq_true, and_assoc] at checked
  exact List.all_eq_true.mp checked.2.2 entry member

theorem Entry.checked_plan (entry : Entry) (plan : Plan)
    (role : entry.role = .premise) (selected : entry.plan = some plan)
    (checked : entry.checked? = true) : entry.source.checkPlan plan = true := by
  have payload := (Bool.and_eq_true _ _).mp checked |>.2
  simpa only [role, selected] using payload

theorem Entry.premise_correspondence (entry : Entry) (plan : Plan)
    (role : entry.role = .premise) (selected : entry.plan = some plan)
    (checked : entry.checked? = true) (premises : List Tuple) (output : Tuple) :
    plan.run premises = some output ↔ Derives entry.source premises output :=
  entry.source.checkPlan_correct plan (entry.checked_plan plan role selected checked) premises output

def publisherFields (arguments : List Word) : List Atom → Option (List Word)
  | [] => some []
  | atom :: rest => do
      let value ← match atom with
        | .literal value => some value
        | .variable name => arguments[name]?
      let later ← publisherFields arguments rest
      pure (value :: later)

def Entry.publish (entry : Entry) (arguments : List Word) : Option Tuple := do
  if entry.role = .publisher ∧ arguments.length = entry.variableCount then
    let fields ← publisherFields arguments entry.source.conclusion.fields
    pure ⟨entry.source.conclusion.tag, fields⟩
  else none

theorem publisherFields_reads (arguments : List Word) (atoms : List Atom)
    (values : List Word) (published : publisherFields arguments atoms = some values) :
    values = atoms.map (Atom.evaluate (fun name => arguments[name]?.getD 0)) := by
  induction atoms generalizing values with
  | nil => simpa [publisherFields] using published.symm
  | cons atom rest ih =>
      cases atom with
      | literal value =>
          cases tailEq : publisherFields arguments rest with
          | none => simp [publisherFields, tailEq] at published
          | some tail =>
              have same : value :: tail = values := by simpa [publisherFields, tailEq] using published
              rw [← same, List.map_cons, ih tail tailEq]
              rfl
      | «variable» name =>
          cases argEq : arguments[name]? with
          | none => simp [publisherFields, argEq] at published
          | some value =>
              cases tailEq : publisherFields arguments rest with
              | none => simp [publisherFields, argEq, tailEq] at published
              | some tail =>
                  have same : value :: tail = values := by
                    simpa [publisherFields, argEq, tailEq] using published
                  rw [← same, List.map_cons, ih tail tailEq]
                  simp [Atom.evaluate, argEq]

/-- Publisher agreement concerns the supplied ID words, not their logical truth. -/
theorem Entry.publish_reflects_source (entry : Entry) (arguments : List Word) (output : Tuple)
    (checked : entry.checked? = true) (published : entry.publish arguments = some output) :
    Derives entry.source [] output := by
  unfold publish at published
  split at published
  · rename_i admitted
    have role : entry.role = .publisher := admitted.1
    have empty : entry.source.premises = [] := by
      have payload := (Bool.and_eq_true _ _).mp checked |>.2
      cases selected : entry.plan with
      | none => simpa [role, selected, List.isEmpty_iff] using payload
      | some plan => simp [role, selected] at payload
    cases fieldsEq : publisherFields arguments entry.source.conclusion.fields with
    | none => simp [fieldsEq] at published
    | some fields =>
        have same : Tuple.mk entry.source.conclusion.tag fields = output := by
          simpa [fieldsEq] using published
        refine ⟨fun name => arguments[name]?.getD 0, by simp [empty], ?_⟩
        rw [← same]
        exact congrArg (Tuple.mk entry.source.conclusion.tag) (publisherFields_reads arguments _ _ fieldsEq)
  · cases published

end Mettapedia.Machines.TIsa.TheoryData
