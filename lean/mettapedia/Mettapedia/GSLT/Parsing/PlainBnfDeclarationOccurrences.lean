import Mettapedia.GSLT.Parsing.PlainBnfDeclarationReflection

/-!
# Source occurrence observations for declaration-list operations

These results concern the existing occurrence-labelled Horn source paths. The
observation forgets substitution certificates but retains rule occurrences
and both provider coordinates. Rule inversion separately constrains the
ground premises and results. This is not an answer-enumeration semantics for
native PeTTa or C.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfDeclarationOccurrences

open HornCertificate HornProviderGSLT
open HornCertificateGSLT (State goalsAt)
open PlainBnfDeclarationEncoding
open PlainBnfDeclarationSemantics PlainBnfDeclarationSource
open PlainBnfDeclarationRealization PlainBnfDeclarationReflection

/-- An observation of existing actions, not a new executable instruction set. -/
def occurrenceOf : Action → Sum Nat (Nat × Nat)
  | .rule occurrence _ => .inl occurrence
  | .provider capability equation => .inr (capability, equation)

def occurrenceTrace (actions : List Action) : List (Sum Nat (Nat × Nat)) :=
  actions.map occurrenceOf

private theorem selected_family {program : Program} {offset occurrence : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    {rule : Rule} {substitution : Substitution} {goal : GroundAtom}
    (selected : program[occurrence]? = some rule)
    (head : instantiateAtom substitution rule.head = some goal)
    (family : declarationRelation goal.relation = true) :
    ∃ index : Fin 13, occurrence = offset + index.val ∧ rule = declarationRules[index.val] := by
  have totalHead := instantiateAtom_total head
  have relation : goal.relation = rule.head.relation :=
    (congrArg GroundAtom.relation totalHead).symm
  have bounds := only occurrence rule selected (by simpa [relation] using family)
  let index : Fin 13 := ⟨occurrence - offset, by omega⟩
  have occurrenceEq : offset + index.val = occurrence := by dsimp [index]; omega
  have expected := source index
  rw [occurrenceEq, selected] at expected
  refine ⟨index, occurrenceEq.symm, ?_⟩
  exact Option.some.inj (expected.trans (List.getElem?_eq_getElem (by
    simp [declarationRules, index.isLt])))

def appendDefinitionInput (before : List (Definition GroundTerm GroundTerm GroundTerm)) (definition :
    Definition GroundTerm GroundTerm GroundTerm)
    (output : GroundTerm) : GroundAtom :=
  ⟨"BNFAppendDefinitionV1", GroundTerms.ofList
    [encodeDefinitions before, encodeDefinition definition, output]⟩

private theorem append_definition_rule {program : Program} {offset occurrence : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    {rule : Rule} {substitution : Substitution} {premises : List GroundAtom}
    (before : List (Definition GroundTerm GroundTerm GroundTerm)) (definition : Definition GroundTerm
        GroundTerm GroundTerm) (output : GroundTerm)
    (selected : program[occurrence]? = some rule)
    (head : instantiateAtom substitution rule.head =
      some (appendDefinitionInput before definition output))
    (body : instantiateAtoms substitution rule.body = some premises) :
    match before with
    | [] => occurrence = offset + 3 ∧ premises = [] ∧
        output = encodeDefinitions [definition]
    | first :: tail => occurrence = offset + 4 ∧ ∃ rest,
        premises = [appendDefinitionInput tail definition rest] ∧
        output = .app "BNFDefinitionsConsV1"
          (GroundTerms.ofList [encodeDefinition first, rest]) := by
  obtain ⟨index, occurrenceEq, ruleEq⟩ := selected_family source only selected head (by rfl)
  have totalHead := instantiateAtom_total head
  have totalBody := instantiateAtoms_total body
  rw [ruleEq] at totalHead totalBody
  have relation := congrArg GroundAtom.relation totalHead
  have indices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨
      index = 11 ∨ index = 12 := by omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    try { exact False.elim ((of_decide_eq_false rfl) relation) }
  · cases before with
    | nil =>
      change (⟨"BNFAppendDefinitionV1", GroundTerms.ofList
        [.atom "BNFDefinitionsNilV1", assignmentOf substitution 0,
         .app "BNFDefinitionsConsV1" (GroundTerms.ofList
           [assignmentOf substitution 0, .atom "BNFDefinitionsNilV1"])]⟩ : GroundAtom) =
        appendDefinitionInput [] definition output at totalHead
      simp only [appendDefinitionInput, encodeDefinitions, GroundAtom.mk.injEq,
        GroundTerms.ofList, GroundTerms.cons.injEq, true_and, and_true] at totalHead
      rcases totalHead with ⟨definitionEq, outputEq⟩
      refine ⟨occurrenceEq, totalBody.symm, ?_⟩
      simpa [encodeDefinitions, GroundTerms.ofList, definitionEq] using outputEq.symm
    | cons first tail =>
      have firstEq := congrArg (fun atom => atom.arguments) totalHead
      exact False.elim ((of_decide_eq_false rfl) (congrArg (fun args =>
        match args with | .cons (.atom _) _ => true | _ => false) firstEq))
  · cases before with
    | nil =>
      have firstEq := congrArg (fun atom => atom.arguments) totalHead
      exact False.elim ((of_decide_eq_false rfl) (congrArg (fun args =>
        match args with | .cons (.atom _) _ => true | _ => false) firstEq))
    | cons first tail =>
      change (⟨"BNFAppendDefinitionV1", GroundTerms.ofList
        [.app "BNFDefinitionsConsV1" (GroundTerms.ofList
           [assignmentOf substitution 0, assignmentOf substitution 1]),
         assignmentOf substitution 2,
         .app "BNFDefinitionsConsV1" (GroundTerms.ofList
           [assignmentOf substitution 0, assignmentOf substitution 3])]⟩ : GroundAtom) =
        appendDefinitionInput (first :: tail) definition output at totalHead
      simp only [appendDefinitionInput, encodeDefinitions, GroundAtom.mk.injEq,
        GroundTerms.ofList, GroundTerms.cons.injEq, GroundTerm.app.injEq,
        true_and, and_true] at totalHead
      rcases totalHead with ⟨⟨firstEq, tailEq⟩, definitionEq, outputEq⟩
      refine ⟨occurrenceEq, assignmentOf substitution 3, ?_, ?_⟩
      · change [⟨"BNFAppendDefinitionV1", GroundTerms.ofList
          [assignmentOf substitution 1, assignmentOf substitution 2,
           assignmentOf substitution 3]⟩] = premises at totalBody
        simpa [appendDefinitionInput, tailEq, definitionEq] using totalBody.symm
      · simpa [firstEq, GroundTerms.ofList] using outputEq.symm

private theorem path_from_empty {program : Program} {actions : List Action} {target : State}
    (path : Path program actions [] target) : actions = [] ∧ target = [] := by
  cases path with
  | nil => exact ⟨rfl, rfl⟩
  | cons first _ => cases first

/-- Arbitrary successful paths, not only paths constructed by the forward
realization, have this exact source-occurrence list and output. Fuel and unused
substitution entries need not agree between paths. -/
theorem append_definition_path_exact {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noProviders : NoDeclarationProviders program)
    (before : List (Definition GroundTerm GroundTerm GroundTerm)) (definition : Definition GroundTerm
        GroundTerm GroundTerm) (output : GroundTerm)
    {fuel : Nat} {actions : List Action}
    (path : Path program actions [(fuel, appendDefinitionInput before definition output)] []) :
    output = encodeDefinitions (before ++ [definition]) ∧
    occurrenceTrace actions = List.replicate before.length (.inl (offset + 4)) ++
      [.inl (offset + 3)] := by
  induction before generalizing fuel actions output with
  | nil =>
    cases path with
    | cons first rest =>
      cases first with
      | rule selected _ head body =>
        obtain ⟨occurrenceEq, premisesEq, outputEq⟩ :=
          append_definition_rule source only [] definition output selected head body
        subst_vars
        have actionsEq := (path_from_empty (by simpa [goalsAt] using rest)).1
        simp [occurrenceTrace, occurrenceOf, actionsEq]
      | provider selected capability _ _ =>
        have excluded := noProviders _ _ _ selected capability
        contradiction
  | cons first tail ih =>
    cases path with
    | cons step rest =>
      cases step with
      | rule selected _ head body =>
        obtain ⟨occurrenceEq, restOutput, premisesEq, outputEq⟩ :=
          append_definition_rule source only (first :: tail) definition output selected head body
        subst_vars
        have recurse := ih restOutput (by simpa [goalsAt] using rest)
        constructor
        · simpa [encodeDefinitions, GroundTerms.ofList] using
            congrArg (fun term => GroundTerm.app "BNFDefinitionsConsV1"
              (GroundTerms.ofList [encodeDefinition first, term])) recurse.1
        · simpa [occurrenceTrace, occurrenceOf, List.replicate_succ] using recurse.2
      | provider selected capability _ _ =>
        have excluded := noProviders _ _ _ selected capability
        contradiction

def appendDiagnosticsInput (left right : List (Diagnostic GroundTerm GroundTerm))
    (output : GroundTerm) : GroundAtom :=
  ⟨"BNFAppendDiagnosticsV1", GroundTerms.ofList
    [encodeDiagnostics left, encodeDiagnostics right, output]⟩

private theorem append_diagnostics_rule {program : Program} {offset occurrence : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    {rule : Rule} {substitution : Substitution} {premises : List GroundAtom}
    (left right : List (Diagnostic GroundTerm GroundTerm)) (output : GroundTerm)
    (selected : program[occurrence]? = some rule)
    (head : instantiateAtom substitution rule.head =
      some (appendDiagnosticsInput left right output))
    (body : instantiateAtoms substitution rule.body = some premises) :
    match left with
    | [] => occurrence = offset + 5 ∧ premises = [] ∧ output = encodeDiagnostics right
    | first :: tail => occurrence = offset + 6 ∧ ∃ rest,
        premises = [appendDiagnosticsInput tail right rest] ∧
        output = .app "BNFDiagnosticsConsV1"
          (GroundTerms.ofList [encodeDiagnostic first, rest]) := by
  obtain ⟨index, occurrenceEq, ruleEq⟩ := selected_family source only selected head (by rfl)
  have totalHead := instantiateAtom_total head
  have totalBody := instantiateAtoms_total body
  rw [ruleEq] at totalHead totalBody
  have relation := congrArg GroundAtom.relation totalHead
  have indices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨
      index = 11 ∨ index = 12 := by omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    try { exact False.elim ((of_decide_eq_false rfl) relation) }
  · cases left with
    | nil =>
      change (⟨"BNFAppendDiagnosticsV1", GroundTerms.ofList
        [.atom "BNFDiagnosticsNilV1", assignmentOf substitution 0,
         assignmentOf substitution 0]⟩ : GroundAtom) =
        appendDiagnosticsInput [] right output at totalHead
      simp only [appendDiagnosticsInput, encodeDiagnostics, GroundAtom.mk.injEq,
        GroundTerms.ofList, GroundTerms.cons.injEq, true_and, and_true] at totalHead
      exact ⟨occurrenceEq, totalBody.symm, totalHead.2.symm.trans totalHead.1⟩
    | cons first tail =>
      have firstEq := congrArg (fun atom => atom.arguments) totalHead
      exact False.elim ((of_decide_eq_false rfl) (congrArg (fun args =>
        match args with | .cons (.atom _) _ => true | _ => false) firstEq))
  · cases left with
    | nil =>
      have firstEq := congrArg (fun atom => atom.arguments) totalHead
      exact False.elim ((of_decide_eq_false rfl) (congrArg (fun args =>
        match args with | .cons (.atom _) _ => true | _ => false) firstEq))
    | cons first tail =>
      change (⟨"BNFAppendDiagnosticsV1", GroundTerms.ofList
        [.app "BNFDiagnosticsConsV1" (GroundTerms.ofList
           [assignmentOf substitution 0, assignmentOf substitution 1]),
         assignmentOf substitution 2,
         .app "BNFDiagnosticsConsV1" (GroundTerms.ofList
           [assignmentOf substitution 0, assignmentOf substitution 3])]⟩ : GroundAtom) =
        appendDiagnosticsInput (first :: tail) right output at totalHead
      simp only [appendDiagnosticsInput, encodeDiagnostics, GroundAtom.mk.injEq,
        GroundTerms.ofList, GroundTerms.cons.injEq, GroundTerm.app.injEq,
        true_and, and_true] at totalHead
      rcases totalHead with ⟨⟨firstEq, tailEq⟩, rightEq, outputEq⟩
      refine ⟨occurrenceEq, assignmentOf substitution 3, ?_, ?_⟩
      · change [⟨"BNFAppendDiagnosticsV1", GroundTerms.ofList
          [assignmentOf substitution 1, assignmentOf substitution 2,
           assignmentOf substitution 3]⟩] = premises at totalBody
        simpa [appendDiagnosticsInput, tailEq, rightEq] using totalBody.symm
      · simpa [firstEq, GroundTerms.ofList] using outputEq.symm

/-- Repeated equal diagnostics remain repeated positions in the output, and
every successful source path uses the same ordered rule occurrences. -/
theorem append_diagnostics_path_exact {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noProviders : NoDeclarationProviders program)
    (left right : List (Diagnostic GroundTerm GroundTerm)) (output : GroundTerm)
    {fuel : Nat} {actions : List Action}
    (path : Path program actions [(fuel, appendDiagnosticsInput left right output)] []) :
    output = encodeDiagnostics (left ++ right) ∧
    occurrenceTrace actions = List.replicate left.length (.inl (offset + 6)) ++
      [.inl (offset + 5)] := by
  induction left generalizing fuel actions output with
  | nil =>
    cases path with
    | cons first rest =>
      cases first with
      | rule selected _ head body =>
        obtain ⟨occurrenceEq, premisesEq, outputEq⟩ :=
          append_diagnostics_rule source only [] right output selected head body
        subst_vars
        have actionsEq := (path_from_empty (by simpa [goalsAt] using rest)).1
        simp [occurrenceTrace, occurrenceOf, actionsEq]
      | provider selected capability _ _ =>
        have excluded := noProviders _ _ _ selected capability
        contradiction
  | cons first tail ih =>
    cases path with
    | cons step rest =>
      cases step with
      | rule selected _ head body =>
        obtain ⟨occurrenceEq, restOutput, premisesEq, outputEq⟩ :=
          append_diagnostics_rule source only (first :: tail) right output selected head body
        subst_vars
        have recurse := ih restOutput (by simpa [goalsAt] using rest)
        constructor
        · simpa [encodeDiagnostics, GroundTerms.ofList] using
            congrArg (fun term => GroundTerm.app "BNFDiagnosticsConsV1"
              (GroundTerms.ofList [encodeDiagnostic first, term])) recurse.1
        · simpa [occurrenceTrace, occurrenceOf, List.replicate_succ] using recurse.2
      | provider selected capability _ _ =>
        have excluded := noProviders _ _ _ selected capability
        contradiction

/-- Successful source paths may differ in fuel or irrelevant certificate
bindings, but not in either their result or their source-occurrence observation. -/
theorem append_definition_two_paths_agree {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noProviders : NoDeclarationProviders program)
    (before : List (Definition GroundTerm GroundTerm GroundTerm)) (definition : Definition GroundTerm
        GroundTerm GroundTerm) (firstOutput secondOutput : GroundTerm)
    {firstFuel secondFuel : Nat} {firstActions secondActions : List Action}
    (first : Path program firstActions
      [(firstFuel, appendDefinitionInput before definition firstOutput)] [])
    (second : Path program secondActions
      [(secondFuel, appendDefinitionInput before definition secondOutput)] []) :
    firstOutput = secondOutput ∧ occurrenceTrace firstActions = occurrenceTrace secondActions := by
  have left := append_definition_path_exact source only noProviders before definition firstOutput first
  have right := append_definition_path_exact source only noProviders before definition secondOutput second
  exact ⟨left.1.trans right.1.symm, left.2.trans right.2.symm⟩

/-- A second equal source rule creates a genuinely different source path;
answer-value equality does not license erasing the extra answer occurrence. -/
theorem duplicate_append_source_paths (definition : Definition GroundTerm GroundTerm GroundTerm) :
    ∃ first second : List Action,
      Path (declarationRules ++ declarationRules) first
        [(1, appendDefinitionGoal [] definition [definition])] [] ∧
      Path (declarationRules ++ declarationRules) second
        [(1, appendDefinitionGoal [] definition [definition])] [] ∧
      occurrenceTrace first ≠ occurrenceTrace second := by
  refine ⟨[.rule 3 [(0, encodeDefinition definition)]],
    [.rule 16 [(0, encodeDefinition definition)]], ?_, ?_, ?_⟩
  · exact .cons (.rule (fuel := 0) (rest := []) (rule := declarationRules[3])
      (goals := []) (by decide +kernel)
      (by rfl) (by rfl) (by rfl)) (.nil [])
  · exact .cons (.rule (fuel := 0) (rest := []) (rule := declarationRules[3])
      (goals := []) (by decide +kernel)
      (by rfl) (by rfl) (by rfl)) (.nil [])
  · simp [occurrenceTrace, occurrenceOf]

/-- Erasing unused certificate bindings is necessary even for one fact. This
does not erase a source rule or provider coordinate. -/
theorem unused_bindings_change_actions_not_occurrences (definition : Definition GroundTerm GroundTerm
    GroundTerm) :
    ∃ first second : List Action,
      Path declarationRules first [(1, appendDefinitionGoal [] definition [definition])] [] ∧
      Path declarationRules second [(1, appendDefinitionGoal [] definition [definition])] [] ∧
      first ≠ second ∧ occurrenceTrace first = occurrenceTrace second := by
  refine ⟨[.rule 3 [(0, encodeDefinition definition)]],
    [.rule 3 [(0, encodeDefinition definition), (1, .integer 7)]], ?_, ?_, ?_, rfl⟩
  · exact .cons (.rule (fuel := 0) (rest := []) (rule := declarationRules[3])
      (goals := []) (by decide +kernel)
      (by rfl) (by rfl) (by rfl)) (.nil [])
  · exact .cons (.rule (fuel := 0) (rest := []) (rule := declarationRules[3])
      (goals := []) (by decide +kernel)
      (by rfl) (by rfl) (by rfl)) (.nil [])
  · simp

/-- The source's observed answer includes its ordered occurrence trace. Both
directions use actual source paths; the output is not defined by this relation. -/
theorem append_definition_observation_iff {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noProviders : NoDeclarationProviders program)
    (before : List (Definition GroundTerm GroundTerm GroundTerm)) (definition : Definition GroundTerm
        GroundTerm GroundTerm) (output : GroundTerm)
    (trace : List (Sum Nat (Nat × Nat))) :
    (∃ fuel actions, Path program actions
      [(fuel, appendDefinitionInput before definition output)] [] ∧
      occurrenceTrace actions = trace) ↔
    output = encodeDefinitions (before ++ [definition]) ∧
      trace = List.replicate before.length (.inl (offset + 4)) ++ [.inl (offset + 3)] := by
  constructor
  · rintro ⟨fuel, actions, path, rfl⟩
    exact append_definition_path_exact source only noProviders before definition output path
  · rintro ⟨rfl, rfl⟩
    obtain ⟨fuel, actions, path⟩ := appendDefinition_realizable source
      (appendDefinitionDerivation definition before)
    exact ⟨fuel, actions, path,
      (append_definition_path_exact source only noProviders before definition _ path).2⟩

theorem append_diagnostics_observation_iff {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noProviders : NoDeclarationProviders program)
    (left right : List (Diagnostic GroundTerm GroundTerm)) (output : GroundTerm)
    (trace : List (Sum Nat (Nat × Nat))) :
    (∃ fuel actions, Path program actions
      [(fuel, appendDiagnosticsInput left right output)] [] ∧
      occurrenceTrace actions = trace) ↔
    output = encodeDiagnostics (left ++ right) ∧
      trace = List.replicate left.length (.inl (offset + 6)) ++ [.inl (offset + 5)] := by
  constructor
  · rintro ⟨fuel, actions, path, rfl⟩
    exact append_diagnostics_path_exact source only noProviders left right output path
  · rintro ⟨rfl, rfl⟩
    obtain ⟨fuel, actions, path⟩ := appendDiagnostics_realizable source
      (appendDiagnosticsDerivation right left)
    exact ⟨fuel, actions, path,
      (append_diagnostics_path_exact source only noProviders left right _ path).2⟩

/-- This counts the actual source actions, including any provider actions if
they had existed. The inventory proof excludes them rather than discarding
them from the measured trace. No native allocation or timing claim follows. -/
theorem append_definition_source_action_count {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noProviders : NoDeclarationProviders program)
    (before : List (Definition GroundTerm GroundTerm GroundTerm)) (definition : Definition GroundTerm
        GroundTerm GroundTerm) (output : GroundTerm)
    {fuel : Nat} {actions : List Action}
    (path : Path program actions [(fuel, appendDefinitionInput before definition output)] []) :
    actions.length = before.length + 1 := by
  have count := congrArg List.length
    (append_definition_path_exact source only noProviders before definition output path).2
  simpa [occurrenceTrace] using count

theorem append_diagnostics_source_action_count {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noProviders : NoDeclarationProviders program)
    (left right : List (Diagnostic GroundTerm GroundTerm)) (output : GroundTerm)
    {fuel : Nat} {actions : List Action}
    (path : Path program actions [(fuel, appendDiagnosticsInput left right output)] []) :
    actions.length = left.length + 1 := by
  have count := congrArg List.length
    (append_diagnostics_path_exact source only noProviders left right output path).2
  simpa [occurrenceTrace] using count

#print axioms append_definition_path_exact
#print axioms append_diagnostics_path_exact
#print axioms duplicate_append_source_paths
#print axioms unused_bindings_change_actions_not_occurrences
#print axioms append_definition_observation_iff
#print axioms append_diagnostics_observation_iff

end Mettapedia.GSLT.Parsing.PlainBnfDeclarationOccurrences
