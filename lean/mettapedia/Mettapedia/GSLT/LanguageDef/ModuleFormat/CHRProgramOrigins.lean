import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuleCompilation
import Mathlib.Data.List.Forall2

/-! Successful preparation retains the source rule/head occurrence at each
query position. Selected execution-plan declarations read through that same
table; their execution ordinal is separate from the authored source index. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.ProgramOrigins

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission

def EntryOrigin (vocabulary : Vocabulary) (program : Program)
    (input : RuleOccurrence × Nat) (entry : Entry) : Prop :=
  ∃ source, program.rules[input.1.rule]? = some source ∧
    compileRule? vocabulary input.2 input.1.head source = some entry.rule ∧
    entry.occurrence = input.1 ∧ entry.boundVariables = source.variables.eraseDups

structure PreparedSource (program : Program) (seeds : List Constraint) (prepared : Prepared) : Prop where
  source : prepared.program = program
  vocabulary : prepared.vocabulary = CHRCompilation.vocabulary program seeds
  rows : List.Forall₂ (EntryOrigin prepared.vocabulary program)
    (occurrences program).zipIdx prepared.entries
  rewrites : prepared.compiled.rewrites = prepared.entries.map Entry.rule
  terms : prepared.compiled.terms = baseLanguage.terms ++
    (List.range prepared.entries.length).map queryDeclaration
  equations : prepared.compiled.equations = baseLanguage.equations

private theorem traverse_relation {α β ε : Type} (compile : α → Except ε β)
    (inputs : List α) (outputs : List β) (success : inputs.mapM compile = .ok outputs) :
    List.Forall₂ (fun input output => compile input = .ok output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil =>
    have empty : outputs = [] := Except.ok.inj
      (show (Except.ok outputs : Except ε (List β)) = .ok [] from success.symm)
    subst outputs
    exact .nil
  | cons input rest ih =>
    rw [List.mapM_cons] at success
    change Except.bind (compile input) (fun output => Except.bind (rest.mapM compile)
      (fun results => Except.ok (output :: results))) = .ok outputs at success
    cases first : compile input with
    | error error => simp [first, Except.bind] at success
    | ok output =>
      cases tail : rest.mapM compile with
      | error error => simp [first, tail, Except.bind] at success
      | ok results =>
        have same : output :: results = outputs := by simpa [first, tail, Except.bind] using success
        subst outputs
        exact .cons first (ih results tail)

private theorem entry_origin (vocabulary : Vocabulary) (program : Program)
    (input : RuleOccurrence × Nat) (entry : Entry)
    (success : (do
      let some source := program.rules[input.1.rule]? | throw "invalid authored rule occurrence"
      let some compiled := compileRule? vocabulary input.2 input.1.head source | throw "CHR head compilation refused"
      pure (Entry.mk input.1 source.variables.eraseDups compiled) : Except String Entry) = .ok entry) :
    EntryOrigin vocabulary program input entry := by
  cases sourceRead : program.rules[input.1.rule]? with
  | none => simp [sourceRead] at success
  | some source =>
    cases compiled : compileRule? vocabulary input.2 input.1.head source with
    | none => simp [sourceRead, compiled] at success
    | some rule =>
      simp only [sourceRead, compiled] at success
      change Except.ok (Entry.mk input.1 source.variables.eraseDups rule) = Except.ok entry at success
      have same := Except.ok.inj success
      subst entry
      exact ⟨source, sourceRead, compiled, rfl, rfl⟩

theorem prepare_source (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (success : prepare program seeds = .ok prepared) : PreparedSource program seeds prepared := by
  cases diagnosed : Admission.diagnose program with
  | some diagnostic =>
    rw [prepare, diagnosed] at success
    change (Except.error s!"CHR admission refused: {reprStr diagnostic}" : Except String Prepared) = .ok prepared at success
    cases success
  | none =>
    cases untyped : seeds.find? (fun constraint =>
        !program.declarations.any (fun declaration => declaration.name == constraint.name &&
          declaration.arity == constraint.arguments.length)) with
    | some constraint =>
      rw [prepare, diagnosed] at success
      simp only [untyped] at success
      change (Except.error s!"input constraint is undeclared: {reprStr constraint}" : Except String Prepared) = .ok prepared at success
      cases success
    | none =>
      let compileEntry (input : RuleOccurrence × Nat) : Except String Entry := do
        let some source := program.rules[input.1.rule]? | throw "invalid authored rule occurrence"
        let some compiled := compileRule? (CHRCompilation.vocabulary program seeds) input.2 input.1.head source
          | throw "CHR head compilation refused"
        pure (Entry.mk input.1 source.variables.eraseDups compiled)
      simp only [prepare, diagnosed, untyped] at success
      change (((occurrences program).zipIdx.mapM compileEntry).bind fun entries =>
          let language : LanguageDef := { baseLanguage with
            name := "CHRCompiledMatch"
            terms := baseLanguage.terms ++ (List.range entries.length).map queryDeclaration
            rewrites := entries.map Entry.rule }
          if !language.validate.isEmpty then throw s!"compiled CHR declarations are invalid: {reprStr language.validate}"
          else pure ⟨program, CHRCompilation.vocabulary program seeds, entries, language⟩) = .ok prepared at success
      cases rowsRead : (occurrences program).zipIdx.mapM compileEntry with
      | error error => simp [rowsRead, Except.bind] at success
      | ok entries =>
        rw [rowsRead] at success
        simp only [Except.bind] at success
        split at success
        next => cases success
        next =>
          cases Except.ok.inj success
          refine ⟨rfl, rfl, ?_, rfl, rfl, rfl⟩
          have compiled := traverse_relation compileEntry _ entries rowsRead
          exact compiled.imp (fun input entry read => entry_origin _ _ input entry read)

theorem entry_origin_at (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (success : prepare program seeds = .ok prepared) (index : Nat) (entry : Entry)
    (atEntry : prepared.entries[index]? = some entry) :
    ∃ source,
      (occurrences program)[index]? = some entry.occurrence ∧
      program.rules[entry.occurrence.rule]? = some source ∧
      compileRule? prepared.vocabulary index entry.occurrence.head source = some entry.rule ∧
      entry.boundVariables = source.variables.eraseDups := by
  have rows := (prepare_source program seeds prepared success).rows
  have inside : index < prepared.entries.length := (List.getElem?_eq_some_iff.mp atEntry).1
  have sourceInside : index < (occurrences program).zipIdx.length := by rw [rows.length_eq]; exact inside
  have read := rows.get sourceInside inside
  change EntryOrigin prepared.vocabulary program ((occurrences program).zipIdx[index]) prepared.entries[index] at read
  have same : prepared.entries[index] = entry := (List.getElem?_eq_some_iff.mp atEntry).2
  rw [same] at read
  simp only [List.getElem_zipIdx] at read
  obtain ⟨source, sourceRead, compiled, occurrence, bound⟩ := read
  refine ⟨source, ?_, ?_, ?_, bound⟩
  · rw [occurrence]
    exact List.getElem?_eq_getElem (by simpa using sourceInside)
  · simpa [occurrence] using sourceRead
  · simpa [occurrence] using compiled

theorem plan_rule_origin (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (success : prepare program seeds = .ok prepared) (selectedPlan : RulePlan)
    (member : selectedPlan ∈ (plan prepared).rules) :
    ∃ entry source,
      prepared.entries[selectedPlan.declarationIndex]? = some entry ∧
      (occurrences program)[selectedPlan.declarationIndex]? = some entry.occurrence ∧
      program.rules[entry.occurrence.rule]? = some source ∧
      compileRule? prepared.vocabulary selectedPlan.declarationIndex entry.occurrence.head source =
        some selectedPlan.authored ∧
      entry.rule = selectedPlan.authored ∧ entry.boundVariables = source.variables.eraseDups := by
  obtain ⟨raw, index, declared, _, planned⟩ := compiled_rule_origin member
  have fields := rulePlan_readout planned
  have atRaw := List.mk_mem_zipIdx_iff_getElem?.mp declared
  change prepared.compiled.rewrites[index]? = some raw at atRaw
  rw [(prepare_source program seeds prepared success).rewrites, List.getElem?_map] at atRaw
  obtain ⟨entry, atEntry, same⟩ := Option.map_eq_some_iff.mp atRaw
  obtain ⟨source, occurrence, sourceRead, compiled, bound⟩ := entry_origin_at program seeds prepared success index entry atEntry
  refine ⟨entry, source, ?_, ?_, sourceRead, ?_, ?_, bound⟩
  · simpa [fields.1] using atEntry
  · simpa [fields.1] using occurrence
  · simpa [fields.1, fields.2.1, same] using compiled
  · exact same.trans fields.2.1.symm

#print axioms prepare_source
#print axioms entry_origin_at
#print axioms plan_rule_origin

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.ProgramOrigins
