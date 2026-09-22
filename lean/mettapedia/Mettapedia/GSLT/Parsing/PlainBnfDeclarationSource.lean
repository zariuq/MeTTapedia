import Mettapedia.GSLT.Parsing.HornProviderGSLT

/-!
# Source boundary of plain-BNF declaration collection

The thirteen rule shapes here are obligations for a source-quotation client,
not a replacement program. A client must locate them in its actual elaborated
source. Realizability below uses the existing occurrence-indexed provider GSLT;
increasing proof depth neither chooses a different rule nor changes bindings.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfDeclarationSource

open HornCertificate
open HornCertificateGSLT (State goalsAt)
open HornProviderGSLT

private def app (name : String) (arguments : List Term) : Term :=
  .app name (Terms.ofList arguments)

private def atom (name : String) (arguments : List Term) : Atom :=
  ⟨name, Terms.ofList arguments⟩

/-- Complete source shapes, including ordered premises and repeated variables. -/
def declarationRules : Program :=
  [ ⟨"bnf-definition-lookup-missing-v1",
      atom "BNFDefinitionLookupV1" [.var 0, .atom "BNFDefinitionsNilV1",
        .atom "BNFDefinitionMissingV1"], []⟩
  , ⟨"bnf-definition-lookup-found-v1",
      atom "BNFDefinitionLookupV1" [.var 0,
        app "BNFDefinitionsConsV1"
          [app "BNFDefinitionV1" [.var 0, .var 1, .var 2], .var 3],
        app "BNFDefinitionFoundV1" [.var 1, .var 2]], []⟩
  , ⟨"bnf-definition-lookup-tail-v1",
      atom "BNFDefinitionLookupV1" [.var 0,
        app "BNFDefinitionsConsV1"
          [app "BNFDefinitionV1" [.var 1, .var 2, .var 3], .var 4], .var 5],
      [atom "different" [.var 0, .var 1],
       atom "BNFDefinitionLookupV1" [.var 0, .var 4, .var 5]]⟩
  , ⟨"bnf-append-definition-nil-v1",
      atom "BNFAppendDefinitionV1" [.atom "BNFDefinitionsNilV1", .var 0,
        app "BNFDefinitionsConsV1" [.var 0, .atom "BNFDefinitionsNilV1"]], []⟩
  , ⟨"bnf-append-definition-cons-v1",
      atom "BNFAppendDefinitionV1"
        [app "BNFDefinitionsConsV1" [.var 0, .var 1], .var 2,
         app "BNFDefinitionsConsV1" [.var 0, .var 3]],
      [atom "BNFAppendDefinitionV1" [.var 1, .var 2, .var 3]]⟩
  , ⟨"bnf-append-diagnostics-nil-v1",
      atom "BNFAppendDiagnosticsV1" [.atom "BNFDiagnosticsNilV1", .var 0, .var 0], []⟩
  , ⟨"bnf-append-diagnostics-cons-v1",
      atom "BNFAppendDiagnosticsV1"
        [app "BNFDiagnosticsConsV1" [.var 0, .var 1], .var 2,
         app "BNFDiagnosticsConsV1" [.var 0, .var 3]],
      [atom "BNFAppendDiagnosticsV1" [.var 1, .var 2, .var 3]]⟩
  , ⟨"bnf-definition-step-fresh-v1",
      atom "BNFDefinitionStepV1"
        [.var 0, .var 1, .var 2, .atom "BNFDefinitionMissingV1",
         .var 3, .var 4, .atom "BNFDiagnosticsNilV1"],
      [atom "BNFAppendDefinitionV1"
        [.var 3, app "BNFDefinitionV1" [.var 0, .var 2, .var 1], .var 4]]⟩
  , ⟨"bnf-definition-step-duplicate-v1",
      atom "BNFDefinitionStepV1"
        [.var 0, .var 1, .var 2, app "BNFDefinitionFoundV1" [.var 3, .var 4],
         .var 5, .var 5, app "BNFDiagnosticsConsV1"
          [app "BNFDuplicateDefinitionV1" [.var 0, .var 4, .var 1],
           .atom "BNFDiagnosticsNilV1"]], []⟩
  , ⟨"bnf-collect-definitions-nil-v1",
      atom "BNFCollectDefinitionsV1"
        [app "metta-nullary" [.atom "bnf-v1:entries-nil"],
         .var 0, .var 0, .atom "BNFDiagnosticsNilV1"], []⟩
  , ⟨"bnf-collect-definitions-comment-v1",
      atom "BNFCollectDefinitionsV1"
        [app "bnf-v1:entries-cons" [app "bnf-v1:comment" [.var 0, .var 1], .var 2],
         .var 3, .var 4, .var 5],
      [atom "BNFCollectDefinitionsV1" [.var 2, .var 3, .var 4, .var 5]]⟩
  , ⟨"bnf-collect-definitions-blank-v1",
      atom "BNFCollectDefinitionsV1"
        [app "bnf-v1:entries-cons" [app "bnf-v1:blank" [.var 0], .var 1],
         .var 2, .var 3, .var 4],
      [atom "BNFCollectDefinitionsV1" [.var 1, .var 2, .var 3, .var 4]]⟩
  , ⟨"bnf-collect-definitions-rule-v1",
      atom "BNFCollectDefinitionsV1"
        [app "bnf-v1:entries-cons"
          [app "bnf-v1:rule" [.var 0, .var 1, .var 2], .var 3], .var 4, .var 5, .var 6],
      [atom "BNFDefinitionLookupV1" [.var 0, .var 4, .var 7],
       atom "BNFDefinitionStepV1" [.var 0, .var 2, .var 1, .var 7, .var 4, .var 8, .var 9],
       atom "BNFCollectDefinitionsV1" [.var 3, .var 8, .var 5, .var 10],
       atom "BNFAppendDiagnosticsV1" [.var 9, .var 10, .var 6]]⟩ ]

/-- Occurrences are supplied by the source client, not selected by rule name. -/
def HasDeclarationRules (program : Program) (offset : Nat) : Prop :=
  ∀ index : Fin 13, program[offset + index.val]? = declarationRules[index.val]?

def declarationRelation (relation : String) : Bool :=
  ["BNFDefinitionLookupV1", "BNFAppendDefinitionV1", "BNFAppendDiagnosticsV1",
   "BNFDefinitionStepV1", "BNFCollectDefinitionsV1"].contains relation

/-- Reverse source coverage must exclude additional matching occurrences. -/
def OnlyDeclarationRules (program : Program) (offset : Nat) : Prop :=
  ∀ index rule, program[index]? = some rule → declarationRelation rule.head.relation = true →
    offset ≤ index ∧ index < offset + 13

/-- Presence of the expected rules alone does not rule out duplicate answers. -/
theorem duplicated_family_contains_selected_rules :
    HasDeclarationRules (declarationRules ++ declarationRules) 0 := by
  intro index
  rw [Nat.zero_add, List.getElem?_append_left]
  simp [declarationRules, index.isLt]

/-- The reverse inventory, unlike a selected-image check, detects the duplicate. -/
theorem duplicated_family_fails_reverse_inventory :
    ¬ OnlyDeclarationRules (declarationRules ++ declarationRules) 0 := by
  intro covered
  have bad := covered 13 declarationRules[0] (by decide +kernel) (by decide +kernel)
  omega

private def raiseDepth (extra : Nat) (state : State) : State :=
  state.map fun obligation => (obligation.1 + extra, obligation.2)

private theorem raiseDepth_goalsAt (extra fuel : Nat) (goals : List GroundAtom) :
    raiseDepth extra (goalsAt fuel goals) = goalsAt (fuel + extra) goals := by
  simp [raiseDepth, goalsAt, List.map_map, Function.comp_def]

private theorem step_raiseDepth {program : Program} {action : Action}
    {source target : State} (step : Step program action source target) (extra : Nat) :
    Step program action (raiseDepth extra source) (raiseDepth extra target) := by
  cases step with
  | rule selected valid head body =>
    simpa [raiseDepth, goalsAt, List.map_map, Function.comp_def,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Step.rule (fuel := _ + extra) (rest := raiseDepth extra _) selected valid head body)
  | provider selected capability equation answer =>
    simpa [raiseDepth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Step.provider (fuel := _ + extra) (rest := raiseDepth extra _)
        selected capability equation answer)

private theorem path_raiseDepth {program : Program} {actions : List Action}
    {source target : State} (path : Path program actions source target) (extra : Nat) :
    Path program actions (raiseDepth extra source) (raiseDepth extra target) := by
  induction path with
  | nil => exact .nil _
  | cons step _ ih => exact .cons (step_raiseDepth step extra) ih

/-- Existence of an actual finite source path; no assertion about search order,
answer enumeration, or native runtime execution is made by this predicate. -/
def Realizable (program : Program) (goal : GroundAtom) : Prop :=
  ∃ fuel actions, Path program actions [(fuel, goal)] []

theorem Realizable.at_least {program : Program} {goal : GroundAtom}
    (runs : Realizable program goal) (minimum : Nat) :
    ∃ fuel actions, minimum ≤ fuel ∧ Path program actions [(fuel, goal)] [] := by
  obtain ⟨fuel, actions, path⟩ := runs
  refine ⟨fuel + minimum, actions, Nat.le_add_left _ _, ?_⟩
  simpa [raiseDepth] using path_raiseDepth path minimum

private theorem all_realizable {program : Program} (goals : List GroundAtom)
    (runs : ∀ goal ∈ goals, Realizable program goal) :
    ∃ fuel actions, Path program actions (goalsAt fuel goals) [] := by
  induction goals with
  | nil => exact ⟨0, [], .nil _⟩
  | cons goal goals ih =>
    obtain ⟨leftFuel, leftActions, leftPath⟩ := runs goal (by simp)
    obtain ⟨rightFuel, rightActions, rightPath⟩ :=
      ih (fun child member => runs child (by simp [member]))
    have first := path_raiseDepth leftPath rightFuel
    have rest := path_raiseDepth rightPath leftFuel
    have first' : Path program leftActions [(leftFuel + rightFuel, goal)] [] := by
      simpa [raiseDepth] using first
    have rest' : Path program rightActions (goalsAt (leftFuel + rightFuel) goals) [] := by
      simpa [raiseDepth, goalsAt, List.map_map, Function.comp_def, Nat.add_comm] using rest
    refine ⟨leftFuel + rightFuel, leftActions ++ rightActions, ?_⟩
    simpa [goalsAt] using
      (first'.append_suffix (goalsAt (leftFuel + rightFuel) goals)).append rest'

/-- A genuine authored clause instance followed by its ordered source paths. -/
theorem Realizable.rule {program : Program} {occurrence : Nat} {sourceRule : Rule}
    {substitution : Substitution} {goal : GroundAtom} {premises : List GroundAtom}
    (selected : program[occurrence]? = some sourceRule)
    (valid : substitutionValid substitution = true)
    (head : instantiateAtom substitution sourceRule.head = some goal)
    (body : instantiateAtoms substitution sourceRule.body = some premises)
    (children : ∀ child ∈ premises, Realizable program child) : Realizable program goal := by
  obtain ⟨fuel, actions, path⟩ := all_realizable premises children
  refine ⟨fuel + 1, .rule occurrence substitution :: actions, ?_⟩
  exact .cons (by simpa using Step.rule (rest := []) selected valid head body) path

end Mettapedia.GSLT.Parsing.PlainBnfDeclarationSource
