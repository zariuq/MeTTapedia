import Mettapedia.GSLT.Parsing.PlainBnfDeclarationRealization

/-!
# Reverse meaning of authored declaration rules

The meaning below is an independent, typed-input specification over arbitrary
ground output packets. Rule and provider soundness use the existing Horn
operational semantics; they are not defined by replay acceptance.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfDeclarationReflection

open HornCertificate HornIntegerProvider HornProviderGSLT
open PlainBnfDeclarationEncoding
open PlainBnfDeclarationSemantics PlainBnfDeclarationSource PlainBnfDeclarationRealization

mutual
  def totalTerm (assignment : Nat → GroundTerm) : Term → GroundTerm
    | .var index => assignment index
    | .atom name => .atom name
    | .integer value => .integer value
    | .app name arguments => .app name (totalTerms assignment arguments)
  def totalTerms (assignment : Nat → GroundTerm) : Terms → GroundTerms
    | .nil => .nil
    | .cons head tail => .cons (totalTerm assignment head) (totalTerms assignment tail)
end

def totalAtom (assignment : Nat → GroundTerm) (atom : Atom) : GroundAtom :=
  ⟨atom.relation, totalTerms assignment atom.arguments⟩

def assignmentOf (substitution : Substitution) (index : Nat) : GroundTerm :=
  (instantiateTerm substitution (.var index)).getD (.atom "unbound")

mutual
  theorem instantiateTerm_total {substitution : Substitution} {term : Term} {value : GroundTerm}
      (success : instantiateTerm substitution term = some value) :
      totalTerm (assignmentOf substitution) term = value := by
    cases term with
    | var index => simp [totalTerm, assignmentOf, success]
    | atom name => simpa [instantiateTerm, totalTerm] using success
    | integer value => simpa [instantiateTerm, totalTerm] using success
    | app name arguments =>
        cases evaluated : instantiateTerms substitution arguments with
        | none => simp [instantiateTerm, evaluated] at success
        | some values =>
            have equal : GroundTerm.app name values = value := by
              simpa [instantiateTerm, evaluated] using success
            rw [totalTerm, instantiateTerms_total evaluated, equal]
  theorem instantiateTerms_total {substitution : Substitution} {terms : Terms} {values : GroundTerms}
      (success : instantiateTerms substitution terms = some values) :
      totalTerms (assignmentOf substitution) terms = values := by
    cases terms with
    | nil => simpa [instantiateTerms, totalTerms] using success
    | cons head tail =>
        cases first : instantiateTerm substitution head with
        | none => simp [instantiateTerms, first] at success
        | some headValue =>
            cases rest : instantiateTerms substitution tail with
            | none => simp [instantiateTerms, first, rest] at success
            | some tailValues =>
                have equal : GroundTerms.cons headValue tailValues = values := by
                  simpa [instantiateTerms, first, rest] using success
                rw [totalTerms, instantiateTerm_total first, instantiateTerms_total rest, equal]
end

theorem instantiateAtom_total {substitution : Substitution} {atom : Atom} {goal : GroundAtom}
    (success : instantiateAtom substitution atom = some goal) :
    totalAtom (assignmentOf substitution) atom = goal := by
  cases arguments : instantiateTerms substitution atom.arguments with
  | none => simp [instantiateAtom, arguments] at success
  | some values =>
      have equal : ({relation := atom.relation, arguments := values} : GroundAtom) = goal := by
        simpa [instantiateAtom, arguments] using success
      rw [totalAtom, instantiateTerms_total arguments, equal]

theorem instantiateAtoms_total {substitution : Substitution} {atoms : List Atom}
    {goals : List GroundAtom} (success : instantiateAtoms substitution atoms = some goals) :
    atoms.map (totalAtom (assignmentOf substitution)) = goals := by
  induction atoms generalizing goals with
  | nil => simpa [instantiateAtoms] using success
  | cons atom atoms ih =>
      cases first : instantiateAtom substitution atom with
      | none => simp [instantiateAtoms, List.mapM_cons, first] at success
      | some goal =>
          cases rest : instantiateAtoms substitution atoms with
          | none =>
              change List.mapM (instantiateAtom substitution) atoms = none at rest
              simp [instantiateAtoms, List.mapM_cons, first, rest] at success
          | some tail =>
              change List.mapM (instantiateAtom substitution) atoms = some tail at rest
              have equal : goal :: tail = goals := by
                simpa [instantiateAtoms, List.mapM_cons, first, rest] using success
              rw [List.map_cons, instantiateAtom_total first, ih rest, equal]

def LookupMeaning (arguments : GroundTerms) : Prop :=
  ∀ name definitions output,
    arguments = GroundTerms.ofList [name, encodeDefinitions definitions, output] →
    AliasFree name → CanonicalDefinitions definitions →
    output = encodeLookupResult (lookup name definitions)

def AppendDefinitionMeaning (arguments : GroundTerms) : Prop :=
  ∀ before definition output,
    arguments = GroundTerms.ofList [encodeDefinitions before, encodeDefinition definition, output] →
    output = encodeDefinitions (before ++ [definition])

def AppendDiagnosticsMeaning (arguments : GroundTerms) : Prop :=
  ∀ left right output,
    arguments = GroundTerms.ofList [encodeDiagnostics left, encodeDiagnostics right, output] →
    output = encodeDiagnostics (left ++ right)

def DefinitionStepMeaning (arguments : GroundTerms) : Prop :=
  ∀ name span expression result before after diagnostics,
    arguments = GroundTerms.ofList [name, span, expression, encodeLookupResult result,
      encodeDefinitions before, after, diagnostics] →
    after = encodeDefinitions (definitionStep name span expression result before).1 ∧
    diagnostics = encodeDiagnostics (definitionStep name span expression result before).2

def CollectMeaning (arguments : GroundTerms) : Prop :=
  ∀ entries before after diagnostics,
    arguments = GroundTerms.ofList [encodeEntries entries, encodeDefinitions before,
      after, diagnostics] →
    CanonicalEntries entries → CanonicalDefinitions before →
    after = encodeDefinitions (collect entries before).1 ∧
    diagnostics = encodeDiagnostics (collect entries before).2

def DifferentMeaning (arguments : GroundTerms) : Prop :=
  ∀ left right, arguments = GroundTerms.ofList [left, right] →
    AliasFree left → AliasFree right → left ≠ right

def DeclarationMeaning (goal : GroundAtom) : Prop :=
  match goal.relation with
  | "BNFDefinitionLookupV1" => LookupMeaning goal.arguments
  | "BNFAppendDefinitionV1" => AppendDefinitionMeaning goal.arguments
  | "BNFAppendDiagnosticsV1" => AppendDiagnosticsMeaning goal.arguments
  | "BNFDefinitionStepV1" => DefinitionStepMeaning goal.arguments
  | "BNFCollectDefinitionsV1" => CollectMeaning goal.arguments
  | "different" => DifferentMeaning goal.arguments
  | _ => True

def InstantiatedRuleSound (index : Fin 13) : Prop :=
  ∀ assignment : Nat → GroundTerm,
    (∀ premise ∈ (declarationRules[index.val]).body.map (totalAtom assignment),
      DeclarationMeaning premise) →
    DeclarationMeaning (totalAtom assignment (declarationRules[index.val]).head)

theorem lookup_missing_rule_sound : InstantiatedRuleSound 0 := by
  intro assignment _
  change LookupMeaning (.cons (assignment 0) (.cons (.atom "BNFDefinitionsNilV1")
    (.cons (.atom "BNFDefinitionMissingV1") .nil)))
  intro name definitions output equal _ _
  cases definitions with
  | nil =>
      simp only [GroundTerms.ofList, encodeDefinitions, GroundTerms.cons.injEq,
        and_true] at equal
      simp_all [lookup, encodeLookupResult]
  | cons head tail => simp [GroundTerms.ofList, encodeDefinitions] at equal

theorem lookup_found_rule_sound : InstantiatedRuleSound 1 := by
  intro assignment _
  change LookupMeaning (.cons (assignment 0)
    (.cons (.app "BNFDefinitionsConsV1" (.cons (.app "BNFDefinitionV1"
      (.cons (assignment 0) (.cons (assignment 1) (.cons (assignment 2) .nil))))
        (.cons (assignment 3) .nil)))
      (.cons (.app "BNFDefinitionFoundV1" (.cons (assignment 1)
        (.cons (assignment 2) .nil))) .nil)))
  intro name definitions output equal _ _
  cases definitions with
  | nil => simp [GroundTerms.ofList, encodeDefinitions] at equal
  | cons head tail =>
      cases head with
      | mk headName expression span =>
          simp only [GroundTerms.ofList, encodeDefinitions, encodeDefinition,
            GroundTerms.cons.injEq, GroundTerm.app.injEq, true_and, and_true] at equal
          rcases equal with ⟨rfl, ⟨⟨headEqual, rfl, rfl⟩, tailEqual⟩, rfl⟩
          simp [encodeLookupResult, lookup, headEqual, GroundTerms.ofList]

theorem lookup_tail_rule_sound : InstantiatedRuleSound 2 := by
  intro a premises
  have difference : DifferentMeaning (GroundTerms.ofList [a 0, a 1]) :=
    premises ⟨"different", GroundTerms.ofList [a 0, a 1]⟩ (by
      exact List.Mem.head _)
  have recurse : LookupMeaning (GroundTerms.ofList [a 0, a 4, a 5]) :=
    premises ⟨"BNFDefinitionLookupV1", GroundTerms.ofList [a 0, a 4, a 5]⟩ (by
      exact List.Mem.tail _ (List.Mem.head _))
  change LookupMeaning (GroundTerms.ofList [a 0,
    .app "BNFDefinitionsConsV1" (GroundTerms.ofList
      [.app "BNFDefinitionV1" (GroundTerms.ofList [a 1, a 2, a 3]), a 4]), a 5])
  intro name definitions output equal nameCanonical canonical
  cases definitions with
  | nil => simp [GroundTerms.ofList, encodeDefinitions] at equal
  | cons head tail =>
      cases head with
      | mk headName expression span =>
          simp only [GroundTerms.ofList, encodeDefinitions, encodeDefinition,
            GroundTerms.cons.injEq, GroundTerm.app.injEq, true_and, and_true] at equal
          rcases equal with ⟨rfl, ⟨⟨rfl, rfl, rfl⟩, tailEqual⟩, rfl⟩
          have unequal : a 0 ≠ a 1 := difference _ _ rfl nameCanonical
            (canonical ⟨a 1, a 2, a 3⟩ (by simp))
          have tailCanonical : CanonicalDefinitions tail :=
            fun definition member => canonical _ (by simp [member])
          have result := recurse (a 0) tail (a 5) (by rw [tailEqual]) nameCanonical tailCanonical
          simpa [lookup, unequal] using result

theorem append_definition_nil_rule_sound : InstantiatedRuleSound 3 := by
  intro a _
  change AppendDefinitionMeaning (GroundTerms.ofList [.atom "BNFDefinitionsNilV1", a 0,
    .app "BNFDefinitionsConsV1" (GroundTerms.ofList [a 0, .atom "BNFDefinitionsNilV1"])])
  intro before definition output equal
  cases before with
  | nil =>
      simp only [GroundTerms.ofList, encodeDefinitions, GroundTerms.cons.injEq,
        true_and, and_true] at equal
      rcases equal with ⟨encoded, rfl⟩
      simp [encodeDefinitions, encoded, GroundTerms.ofList]
  | cons => simp [GroundTerms.ofList, encodeDefinitions] at equal

theorem append_definition_cons_rule_sound : InstantiatedRuleSound 4 := by
  intro a premises
  have recurse : AppendDefinitionMeaning (GroundTerms.ofList [a 1, a 2, a 3]) :=
    premises ⟨"BNFAppendDefinitionV1", GroundTerms.ofList [a 1, a 2, a 3]⟩ (by
      exact List.Mem.head _)
  change AppendDefinitionMeaning (GroundTerms.ofList
    [.app "BNFDefinitionsConsV1" (GroundTerms.ofList [a 0, a 1]), a 2,
      .app "BNFDefinitionsConsV1" (GroundTerms.ofList [a 0, a 3])])
  intro before definition output equal
  cases before with
  | nil => simp [GroundTerms.ofList, encodeDefinitions] at equal
  | cons head tail =>
      simp only [GroundTerms.ofList, encodeDefinitions, GroundTerms.cons.injEq,
        GroundTerm.app.injEq, true_and, and_true] at equal
      rcases equal with ⟨⟨headEqual, tailEqual⟩, definitionEqual, rfl⟩
      have result := recurse tail definition (a 3) (by rw [tailEqual, definitionEqual])
      simp [encodeDefinitions, headEqual, result, GroundTerms.ofList]

theorem append_diagnostics_nil_rule_sound : InstantiatedRuleSound 5 := by
  intro a _
  change AppendDiagnosticsMeaning (GroundTerms.ofList [.atom "BNFDiagnosticsNilV1", a 0, a 0])
  intro left right output equal
  cases left with
  | nil =>
      simp only [GroundTerms.ofList, encodeDiagnostics, GroundTerms.cons.injEq,
        true_and, and_true] at equal
      rcases equal with ⟨encoded, rfl⟩
      simpa using encoded
  | cons => simp [GroundTerms.ofList, encodeDiagnostics] at equal

theorem append_diagnostics_cons_rule_sound : InstantiatedRuleSound 6 := by
  intro a premises
  have recurse : AppendDiagnosticsMeaning (GroundTerms.ofList [a 1, a 2, a 3]) :=
    premises ⟨"BNFAppendDiagnosticsV1", GroundTerms.ofList [a 1, a 2, a 3]⟩ (by
      exact List.Mem.head _)
  change AppendDiagnosticsMeaning (GroundTerms.ofList
    [.app "BNFDiagnosticsConsV1" (GroundTerms.ofList [a 0, a 1]), a 2,
      .app "BNFDiagnosticsConsV1" (GroundTerms.ofList [a 0, a 3])])
  intro left right output equal
  cases left with
  | nil => simp [GroundTerms.ofList, encodeDiagnostics] at equal
  | cons head tail =>
      simp only [GroundTerms.ofList, encodeDiagnostics, GroundTerms.cons.injEq,
        GroundTerm.app.injEq, true_and, and_true] at equal
      rcases equal with ⟨⟨headEqual, tailEqual⟩, rightEqual, rfl⟩
      have result := recurse tail right (a 3) (by rw [tailEqual, rightEqual])
      simp [encodeDiagnostics, headEqual, result, GroundTerms.ofList]

theorem definition_step_fresh_rule_sound : InstantiatedRuleSound 7 := by
  intro a premises
  have append : AppendDefinitionMeaning (GroundTerms.ofList [a 3,
    .app "BNFDefinitionV1" (GroundTerms.ofList [a 0, a 2, a 1]), a 4]) :=
    premises ⟨"BNFAppendDefinitionV1", GroundTerms.ofList [a 3,
      .app "BNFDefinitionV1" (GroundTerms.ofList [a 0, a 2, a 1]), a 4]⟩ (by
      exact List.Mem.head _)
  change DefinitionStepMeaning (GroundTerms.ofList
    [a 0, a 1, a 2, .atom "BNFDefinitionMissingV1", a 3, a 4, .atom "BNFDiagnosticsNilV1"])
  intro name span expression result before after diagnostics equal
  cases result with
  | found => simp [GroundTerms.ofList, encodeLookupResult] at equal
  | missing =>
      simp only [GroundTerms.ofList, encodeLookupResult, GroundTerms.cons.injEq,
        true_and, and_true] at equal
      rcases equal with ⟨rfl, rfl, rfl, beforeEqual, rfl, rfl⟩
      have result := append before ⟨a 0, a 2, a 1⟩ (a 4) (by rw [beforeEqual]; rfl)
      exact ⟨result, rfl⟩

theorem definition_step_duplicate_rule_sound : InstantiatedRuleSound 8 := by
  intro a _
  change DefinitionStepMeaning (GroundTerms.ofList
    [a 0, a 1, a 2, .app "BNFDefinitionFoundV1" (GroundTerms.ofList [a 3, a 4]),
      a 5, a 5, .app "BNFDiagnosticsConsV1" (GroundTerms.ofList
        [.app "BNFDuplicateDefinitionV1" (GroundTerms.ofList [a 0, a 4, a 1]),
          .atom "BNFDiagnosticsNilV1"])])
  intro name span expression result before after diagnostics equal
  cases result with
  | missing => simp [GroundTerms.ofList, encodeLookupResult] at equal
  | found firstExpression firstSpan =>
      simp only [GroundTerms.ofList, encodeLookupResult, GroundTerms.cons.injEq,
        GroundTerm.app.injEq, true_and, and_true] at equal
      rcases equal with ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩, beforeEqual, rfl, rfl⟩
      exact ⟨beforeEqual, rfl⟩

theorem collect_nil_rule_sound : InstantiatedRuleSound 9 := by
  intro a _
  change CollectMeaning (GroundTerms.ofList
    [.app "metta-nullary" (.cons (.atom "bnf-v1:entries-nil") .nil),
      a 0, a 0, .atom "BNFDiagnosticsNilV1"])
  intro entries before after diagnostics equal _ _
  cases entries with
  | nil =>
      simp only [GroundTerms.ofList, encodeEntries, GroundTerms.cons.injEq,
        true_and, and_true] at equal
      rcases equal with ⟨beforeEqual, rfl, rfl⟩
      exact ⟨beforeEqual, rfl⟩
  | cons => simp [GroundTerms.ofList, encodeEntries] at equal

theorem collect_comment_rule_sound : InstantiatedRuleSound 10 := by
  intro a premises
  have recurse : CollectMeaning (GroundTerms.ofList [a 2, a 3, a 4, a 5]) :=
    premises ⟨"BNFCollectDefinitionsV1", GroundTerms.ofList [a 2, a 3, a 4, a 5]⟩
      (by exact List.Mem.head _)
  change CollectMeaning (GroundTerms.ofList
    [.app "bnf-v1:entries-cons" (GroundTerms.ofList
      [.app "bnf-v1:comment" (GroundTerms.ofList [a 0, a 1]), a 2]), a 3, a 4, a 5])
  intro entries before after diagnostics equal canonical canonicalBefore
  cases entries with
  | nil => simp [GroundTerms.ofList, encodeEntries] at equal
  | cons entry tail =>
      cases entry with
      | rule => simp [GroundTerms.ofList, encodeEntries, encodeEntry] at equal
      | blank => simp [GroundTerms.ofList, encodeEntries, encodeEntry] at equal
      | comment text span =>
          simp only [GroundTerms.ofList, encodeEntries, encodeEntry, GroundTerms.cons.injEq,
            GroundTerm.app.injEq, true_and, and_true] at equal
          rcases equal with ⟨⟨⟨rfl, rfl⟩, tailEqual⟩, beforeEqual, rfl, rfl⟩
          exact recurse tail before (a 4) (a 5) (by rw [tailEqual, beforeEqual])
            (fun entry member => canonical entry (by simp [member])) canonicalBefore

theorem collect_blank_rule_sound : InstantiatedRuleSound 11 := by
  intro a premises
  have recurse : CollectMeaning (GroundTerms.ofList [a 1, a 2, a 3, a 4]) :=
    premises ⟨"BNFCollectDefinitionsV1", GroundTerms.ofList [a 1, a 2, a 3, a 4]⟩
      (by exact List.Mem.head _)
  change CollectMeaning (GroundTerms.ofList
    [.app "bnf-v1:entries-cons" (GroundTerms.ofList
      [.app "bnf-v1:blank" (GroundTerms.ofList [a 0]), a 1]), a 2, a 3, a 4])
  intro entries before after diagnostics equal canonical canonicalBefore
  cases entries with
  | nil => simp [GroundTerms.ofList, encodeEntries] at equal
  | cons entry tail =>
      cases entry with
      | rule => simp [GroundTerms.ofList, encodeEntries, encodeEntry] at equal
      | comment => simp [GroundTerms.ofList, encodeEntries, encodeEntry] at equal
      | blank span =>
          simp only [GroundTerms.ofList, encodeEntries, encodeEntry, GroundTerms.cons.injEq,
            GroundTerm.app.injEq, true_and, and_true] at equal
          rcases equal with ⟨⟨rfl, tailEqual⟩, beforeEqual, rfl, rfl⟩
          exact recurse tail before (a 3) (a 4) (by rw [tailEqual, beforeEqual])
            (fun entry member => canonical entry (by simp [member])) canonicalBefore

theorem collect_rule_rule_sound : InstantiatedRuleSound 12 := by
  intro a premises
  have find : LookupMeaning (GroundTerms.ofList [a 0, a 4, a 7]) :=
    premises ⟨"BNFDefinitionLookupV1", GroundTerms.ofList [a 0, a 4, a 7]⟩
      (by exact List.Mem.head _)
  have step : DefinitionStepMeaning (GroundTerms.ofList
      [a 0, a 2, a 1, a 7, a 4, a 8, a 9]) :=
    premises ⟨"BNFDefinitionStepV1", GroundTerms.ofList
      [a 0, a 2, a 1, a 7, a 4, a 8, a 9]⟩
      (by exact List.Mem.tail _ (List.Mem.head _))
  have recurse : CollectMeaning (GroundTerms.ofList [a 3, a 8, a 5, a 10]) :=
    premises ⟨"BNFCollectDefinitionsV1", GroundTerms.ofList [a 3, a 8, a 5, a 10]⟩
      (by exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have append : AppendDiagnosticsMeaning (GroundTerms.ofList [a 9, a 10, a 6]) :=
    premises ⟨"BNFAppendDiagnosticsV1", GroundTerms.ofList [a 9, a 10, a 6]⟩
      (by exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  change CollectMeaning (GroundTerms.ofList
    [.app "bnf-v1:entries-cons" (GroundTerms.ofList
      [.app "bnf-v1:rule" (GroundTerms.ofList [a 0, a 1, a 2]), a 3]), a 4, a 5, a 6])
  intro entries before after diagnostics equal canonical canonicalBefore
  cases entries with
  | nil => simp [GroundTerms.ofList, encodeEntries] at equal
  | cons entry tail =>
      cases entry with
      | blank => simp [GroundTerms.ofList, encodeEntries, encodeEntry] at equal
      | comment => simp [GroundTerms.ofList, encodeEntries, encodeEntry] at equal
      | rule name expression span =>
          simp only [GroundTerms.ofList, encodeEntries, encodeEntry, GroundTerms.cons.injEq,
            GroundTerm.app.injEq, true_and, and_true] at equal
          rcases equal with ⟨⟨⟨rfl, rfl, rfl⟩, tailEqual⟩, beforeEqual, rfl, rfl⟩
          have nameCanonical : AliasFree (a 0) := by
            cases canonical (.rule (a 0) (a 1) (a 2)) (by simp) with
            | rule _ _ nameCanonical => exact nameCanonical
          have found := find (a 0) before (a 7) (by rw [beforeEqual]) nameCanonical canonicalBefore
          let next := definitionStep (a 0) (a 2) (a 1) (lookup (a 0) before) before
          have stepped := step (a 0) (a 2) (a 1) (lookup (a 0) before) before (a 8) (a 9)
            (by rw [found, beforeEqual])
          have nextCanonical : CanonicalDefinitions next.1 :=
            definitionStep_preserves_canonical
              (definitionStepDerivation (a 0) (a 2) (a 1) (lookup (a 0) before) before)
              nameCanonical canonicalBefore
          have recursed := recurse tail next.1 (a 5) (a 10)
            (by rw [tailEqual, stepped.1])
            (fun entry member => canonical entry (by simp [member])) nextCanonical
          have appended := append next.2 (collect tail next.1).2 (a 6)
            (by rw [stepped.2, recursed.2])
          exact ⟨recursed.1, appended⟩

theorem all_declaration_rules_sound (index : Fin 13) : InstantiatedRuleSound index := by
  rcases index with ⟨index, bound⟩
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨
      index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 := by
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lookup_missing_rule_sound
  · exact lookup_found_rule_sound
  · exact lookup_tail_rule_sound
  · exact append_definition_nil_rule_sound
  · exact append_definition_cons_rule_sound
  · exact append_diagnostics_nil_rule_sound
  · exact append_diagnostics_cons_rule_sound
  · exact definition_step_fresh_rule_sound
  · exact definition_step_duplicate_rule_sound
  · exact collect_nil_rule_sound
  · exact collect_comment_rule_sound
  · exact collect_blank_rule_sound
  · exact collect_rule_rule_sound

def NoDifferentRules (program : Program) : Prop :=
  ∀ (occurrence : Nat) (rule : Rule), program[occurrence]? = some rule → rule.head.relation ≠ "different"

def NoDeclarationProviders (program : Program) : Prop :=
  ∀ (occurrence : Nat) (declaration : Rule) (goal : GroundAtom), program[occurrence]? = some declaration →
    CapabilityDeclaration declaration goal → declarationRelation goal.relation = false

def DifferentProviderSound (program : Program) : Prop :=
  ∀ (capabilityOccurrence equationOccurrence : Nat) (declaration : Rule)
    (goal : GroundAtom) (residual : GroundTerm),
    program[capabilityOccurrence]? = some declaration →
    CapabilityDeclaration declaration goal →
    HornEquationContextual.StepAt program equationOccurrence [] (providerCall goal) residual →
    AnswersEval residual [queryTerm goal] → goal.relation = "different" →
    DifferentMeaning goal.arguments

theorem declaration_rules_sound {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noDifferent : NoDifferentRules program) : RuleSound program DeclarationMeaning := by
  intro occurrence rule substitution goal premises selected _ head body children
  have totalHead := instantiateAtom_total head
  have totalBody := instantiateAtoms_total body
  have relation : goal.relation = rule.head.relation :=
    (congrArg GroundAtom.relation totalHead).symm
  by_cases admitted : declarationRelation goal.relation = true
  · have bounds := only occurrence rule selected (by simpa [relation] using admitted)
    let index : Fin 13 := ⟨occurrence - offset, by omega⟩
    have occurrenceEq : offset + index.val = occurrence := by dsimp [index]; omega
    have expected := source index
    rw [occurrenceEq, selected] at expected
    have ruleEq : rule = declarationRules[index.val] := by
      exact Option.some.inj (expected.trans (List.getElem?_eq_getElem (by
        simp [declarationRules, index.isLt])))
    rw [ruleEq] at totalHead totalBody
    rw [← totalHead]
    apply all_declaration_rules_sound index (assignmentOf substitution)
    intro premise member
    exact children premise (by simpa [totalBody] using member)
  · have notDifferent : goal.relation ≠ "different" := by
      simpa [relation] using noDifferent occurrence rule selected
    have excluded : goal.relation ≠ "BNFDefinitionLookupV1" ∧
        goal.relation ≠ "BNFAppendDefinitionV1" ∧ goal.relation ≠ "BNFAppendDiagnosticsV1" ∧
        goal.relation ≠ "BNFDefinitionStepV1" ∧ goal.relation ≠ "BNFCollectDefinitionsV1" := by
      simpa [declarationRelation, List.contains_iff_mem, or_assoc, not_or] using admitted
    simp [DeclarationMeaning, excluded.1, excluded.2.1, excluded.2.2.1,
      excluded.2.2.2.1, excluded.2.2.2.2]

theorem declaration_providers_sound {program : Program}
    (noDeclarations : NoDeclarationProviders program)
    (different : DifferentProviderSound program) : ProviderSound program DeclarationMeaning := by
  intro capabilityOccurrence equationOccurrence declaration goal residual selected capability equation answer
  have excluded := noDeclarations capabilityOccurrence declaration goal selected capability
  have nonfamily : goal.relation ≠ "BNFDefinitionLookupV1" ∧
      goal.relation ≠ "BNFAppendDefinitionV1" ∧ goal.relation ≠ "BNFAppendDiagnosticsV1" ∧
      goal.relation ≠ "BNFDefinitionStepV1" ∧ goal.relation ≠ "BNFCollectDefinitionsV1" := by
    simpa [declarationRelation, List.contains_iff_mem, or_assoc, not_or] using excluded
  by_cases isDifferent : goal.relation = "different"
  · simpa [DeclarationMeaning, isDifferent] using
      different capabilityOccurrence equationOccurrence declaration goal residual
        selected capability equation answer isDifferent
  · simp [DeclarationMeaning, nonfamily.1, nonfamily.2.1, nonfamily.2.2.1,
      nonfamily.2.2.2.1, nonfamily.2.2.2.2]

/-- Every successful ground path from a canonical typed declaration input has
exactly the specified output packets; arbitrary malformed outputs are excluded. -/
theorem collect_path_reflects_outputs {program : Program} {offset fuel : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noDifferent : NoDifferentRules program) (noDeclarations : NoDeclarationProviders program)
    (different : DifferentProviderSound program)
    (entries : List (Entry GroundTerm GroundTerm GroundTerm GroundTerm)) (before : List (Definition GroundTerm
        GroundTerm GroundTerm)) (after diagnostics : GroundTerm)
    (canonicalEntries : CanonicalEntries entries) (canonicalBefore : CanonicalDefinitions before)
    {actions : List Action}
    (path : Path program actions [(fuel, ⟨"BNFCollectDefinitionsV1", GroundTerms.ofList
      [encodeEntries entries, encodeDefinitions before, after, diagnostics]⟩)] []) :
    after = encodeDefinitions (collect entries before).1 ∧
    diagnostics = encodeDiagnostics (collect entries before).2 := by
  have meaning := path.terminal_soundness (declaration_rules_sound source only noDifferent)
    (declaration_providers_sound noDeclarations different)
  have result : CollectMeaning (GroundTerms.ofList
      [encodeEntries entries, encodeDefinitions before, after, diagnostics]) :=
    meaning (fuel, ⟨"BNFCollectDefinitionsV1", GroundTerms.ofList
      [encodeEntries entries, encodeDefinitions before, after, diagnostics]⟩)
      (by exact List.Mem.head _)
  exact result entries before after diagnostics rfl canonicalEntries canonicalBefore

theorem lookup_path_reflects_output {program : Program} {offset fuel : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noDifferent : NoDifferentRules program) (noDeclarations : NoDeclarationProviders program)
    (different : DifferentProviderSound program)
    (name : GroundTerm) (definitions : List (Definition GroundTerm GroundTerm GroundTerm)) (output : GroundTerm)
    (canonicalName : AliasFree name) (canonicalDefinitions : CanonicalDefinitions definitions)
    {actions : List Action}
    (path : Path program actions [(fuel, ⟨"BNFDefinitionLookupV1", GroundTerms.ofList
      [name, encodeDefinitions definitions, output]⟩)] []) :
    output = encodeLookupResult (lookup name definitions) := by
  have meaning := path.goal_soundness (declaration_rules_sound source only noDifferent)
    (declaration_providers_sound noDeclarations different)
  exact meaning name definitions output rfl canonicalName canonicalDefinitions

theorem append_definition_path_reflects_output {program : Program} {offset fuel : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noDifferent : NoDifferentRules program) (noDeclarations : NoDeclarationProviders program)
    (different : DifferentProviderSound program)
    (before : List (Definition GroundTerm GroundTerm GroundTerm)) (definition : Definition GroundTerm
        GroundTerm GroundTerm) (output : GroundTerm)
    {actions : List Action}
    (path : Path program actions [(fuel, ⟨"BNFAppendDefinitionV1", GroundTerms.ofList
      [encodeDefinitions before, encodeDefinition definition, output]⟩)] []) :
    output = encodeDefinitions (before ++ [definition]) := by
  have meaning := path.goal_soundness (declaration_rules_sound source only noDifferent)
    (declaration_providers_sound noDeclarations different)
  exact meaning before definition output rfl

theorem append_diagnostics_path_reflects_output {program : Program} {offset fuel : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noDifferent : NoDifferentRules program) (noDeclarations : NoDeclarationProviders program)
    (different : DifferentProviderSound program)
    (left right : List (Diagnostic GroundTerm GroundTerm)) (output : GroundTerm)
    {actions : List Action}
    (path : Path program actions [(fuel, ⟨"BNFAppendDiagnosticsV1", GroundTerms.ofList
      [encodeDiagnostics left, encodeDiagnostics right, output]⟩)] []) :
    output = encodeDiagnostics (left ++ right) := by
  have meaning := path.goal_soundness (declaration_rules_sound source only noDifferent)
    (declaration_providers_sound noDeclarations different)
  exact meaning left right output rfl

/-- Exact all-input value correspondence. This deliberately does not identify
raw certificate/action fibres, which may differ in unused substitution entries. -/
theorem collect_realizable_iff_outputs {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noDifferent : NoDifferentRules program) (noDeclarations : NoDeclarationProviders program)
    (differentSound : DifferentProviderSound program) (differentRuns : DifferentRealizes program)
    (entries : List (Entry GroundTerm GroundTerm GroundTerm GroundTerm)) (before : List (Definition GroundTerm
        GroundTerm GroundTerm)) (after diagnostics : GroundTerm)
    (canonicalEntries : CanonicalEntries entries) (canonicalBefore : CanonicalDefinitions before) :
    Realizable program ⟨"BNFCollectDefinitionsV1", GroundTerms.ofList
      [encodeEntries entries, encodeDefinitions before, after, diagnostics]⟩ ↔
      after = encodeDefinitions (collect entries before).1 ∧
      diagnostics = encodeDiagnostics (collect entries before).2 := by
  constructor
  · rintro ⟨fuel, actions, path⟩
    exact collect_path_reflects_outputs source only noDifferent noDeclarations differentSound
      entries before after diagnostics canonicalEntries canonicalBefore path
  · rintro ⟨rfl, rfl⟩
    exact collect_result_realizable source differentRuns entries before canonicalEntries canonicalBefore

/-- A forged output cannot be accepted merely because some valid output exists. -/
theorem collect_wrong_output_has_no_path {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noDifferent : NoDifferentRules program) (noDeclarations : NoDeclarationProviders program)
    (different : DifferentProviderSound program)
    (entries : List (Entry GroundTerm GroundTerm GroundTerm GroundTerm)) (before : List (Definition GroundTerm
        GroundTerm GroundTerm)) (after diagnostics : GroundTerm)
    (canonicalEntries : CanonicalEntries entries) (canonicalBefore : CanonicalDefinitions before)
    (wrong : after ≠ encodeDefinitions (collect entries before).1 ∨
      diagnostics ≠ encodeDiagnostics (collect entries before).2) :
    ¬ Realizable program ⟨"BNFCollectDefinitionsV1", GroundTerms.ofList
      [encodeEntries entries, encodeDefinitions before, after, diagnostics]⟩ := by
  rintro ⟨fuel, actions, path⟩
  have exactOutputs := collect_path_reflects_outputs source only noDifferent noDeclarations different
    entries before after diagnostics canonicalEntries canonicalBefore path
  rcases wrong with wrong | wrong
  · exact wrong exactOutputs.1
  · exact wrong exactOutputs.2

end Mettapedia.GSLT.Parsing.PlainBnfDeclarationReflection
