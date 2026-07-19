import Mettapedia.Languages.MeTTa.HE.HumanTypeSpec
import Mettapedia.Languages.MeTTa.HE.HumanMatchSolutionTheory

/-!
# Executable-independent evaluator steps

This module formalizes the non-recursive control steps used by the future
`HumanEvalSpec`: primitive `unify`, ordered `switch-minimal`, and equation-rule
selection including its negative cases.  Every judgment is fuel-free and uses
the independent human match and merge relations.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanEvalSteps

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open HumanMatchMergeSpec

/-! ## Primitive unify -/

/-- One surviving match-and-merge candidate for primitive `unify`. -/
def HumanUnifyCandidateRel
    (target pattern : Atom) (incoming output : Bindings) : Prop :=
  ∃ matched,
    MatchRel equalityGroundedSemantic target pattern matched ∧
      MergeRel equalityGroundedSemantic matched incoming output ∧
      SemanticLoopFree output ∧
      ∃ valuation : String → Metta.Atom,
        LeaTTaBridge.HEBindingSatisfied valuation output

/-- A successful primitive `unify` selection.  The emitted atom is observed
only through every model of the merged bindings. -/
def HumanUnifySuccessRel
    (target pattern thenBranch : Atom) (incoming : Bindings)
    (emitted : Atom) (output : Bindings) : Prop :=
    HumanUnifyCandidateRel target pattern incoming output ∧
    ∀ valuation : String → Metta.Atom,
      LeaTTaBridge.HEBindingSatisfied valuation output →
        LeaTTaBridge.HEAtomEquationSatisfied valuation emitted thenBranch

/-- No structurally matched binding survives the merge and semantic filters. -/
def HumanUnifyNoMatchRel
    (target pattern : Atom) (incoming : Bindings) : Prop :=
  ∀ output, ¬HumanUnifyCandidateRel target pattern incoming output

/-- One complete primitive `unify` step. -/
inductive HumanUnifyStep
    (target pattern thenBranch elseBranch : Atom) (incoming : Bindings) :
    Atom → Bindings → Prop where
  | success {emitted : Atom} {output : Bindings} :
      HumanUnifySuccessRel target pattern thenBranch incoming emitted output →
      HumanUnifyStep target pattern thenBranch elseBranch incoming
        emitted output
  | noMatch :
      HumanUnifyNoMatchRel target pattern incoming →
      HumanUnifyStep target pattern thenBranch elseBranch incoming
        elseBranch incoming

/-! ## Ordered switch -/

/-- Raw outcome of scanning a `switch-minimal` branch list. -/
inductive HumanSwitchRawOutcome where
  | selected (atom : Atom) (bindings : Bindings)
  | noMatch
  deriving Repr

/-- Left-to-right branch scan.  Malformed branches and well-formed branches
without a surviving unify candidate fall through; the first viable branch
wins. -/
inductive HumanSwitchRawRel (scrutinee : Atom) (incoming : Bindings) :
    List Atom → HumanSwitchRawOutcome → Prop where
  | nil : HumanSwitchRawRel scrutinee incoming [] .noMatch
  | malformed {branch : Atom} {branches : List Atom}
      {outcome : HumanSwitchRawOutcome} :
      (∀ pattern template,
        branch ≠ .expression [pattern, template]) →
      HumanSwitchRawRel scrutinee incoming branches outcome →
      HumanSwitchRawRel scrutinee incoming (branch :: branches) outcome
  | hit {pattern template emitted : Atom} {branches : List Atom}
      {output : Bindings} :
      HumanUnifySuccessRel scrutinee pattern template incoming emitted output →
      HumanSwitchRawRel scrutinee incoming
        (.expression [pattern, template] :: branches)
        (.selected emitted output)
  | miss {pattern template : Atom} {branches : List Atom}
      {outcome : HumanSwitchRawOutcome} :
      HumanUnifyNoMatchRel scrutinee pattern incoming →
      HumanSwitchRawRel scrutinee incoming branches outcome →
      HumanSwitchRawRel scrutinee incoming
        (.expression [pattern, template] :: branches) outcome

/-- Final `switch-minimal` step.  No match and a selected `NotReducible`
sentinel both become `Empty`; every other first-hit result is preserved. -/
inductive HumanSwitchStep (scrutinee : Atom) (branches : List Atom)
    (incoming : Bindings) : Atom → Bindings → Prop where
  | noMatch :
      HumanSwitchRawRel scrutinee incoming branches .noMatch →
      HumanSwitchStep scrutinee branches incoming Atom.empty incoming
  | notReducible {output : Bindings} :
      HumanSwitchRawRel scrutinee incoming branches
        (.selected Atom.notReducible output) →
      HumanSwitchStep scrutinee branches incoming Atom.empty output
  | selected {atom : Atom} {output : Bindings} :
      HumanSwitchRawRel scrutinee incoming branches (.selected atom output) →
      atom ≠ Atom.notReducible →
      HumanSwitchStep scrutinee branches incoming atom output

/-! ## Capture-avoiding equation selection -/

/- Structural variable renaming on atoms. -/
mutual
  inductive AlphaRenameAtomRel (rename : String → String) : Atom → Atom → Prop where
    | symbol (name : String) :
        AlphaRenameAtomRel rename (.symbol name) (.symbol name)
    | variable (name : String) :
        AlphaRenameAtomRel rename (.var name) (.var (rename name))
    | grounded (value : GroundedValue) :
        AlphaRenameAtomRel rename (.grounded value) (.grounded value)
    | expression {source target : List Atom} :
        AlphaRenameAtomsRel rename source target →
        AlphaRenameAtomRel rename (.expression source) (.expression target)

  inductive AlphaRenameAtomsRel (rename : String → String) :
      List Atom → List Atom → Prop where
    | nil : AlphaRenameAtomsRel rename [] []
    | cons {sourceHead targetHead : Atom} {sourceTail targetTail : List Atom} :
        AlphaRenameAtomRel rename sourceHead targetHead →
        AlphaRenameAtomsRel rename sourceTail targetTail →
        AlphaRenameAtomsRel rename
          (sourceHead :: sourceTail) (targetHead :: targetTail)
end

/-- A variable name visible to the current query configuration. -/
def QueryVisibleName
    (live : List Atom) (query : Atom) (incoming : Bindings)
    (name : String) : Prop :=
  AtomOccurs query name ∨
    (∃ atom ∈ live, AtomOccurs atom name) ∨
    (∃ value, (name, value) ∈ incoming.assignments) ∨
    (∃ key value,
      (key, value) ∈ incoming.assignments ∧ AtomOccurs value name) ∨
    ∃ left right,
      (left, right) ∈ incoming.equalities ∧
        (name = left ∨ name = right)

/-- A simultaneous injective alpha-variant of both sides of an equation.  All
renamed rule variables avoid names visible in the query and incoming binding
state. -/
def AlphaVariantRel
    (live : List Atom) (query : Atom) (incoming : Bindings)
    (rawLhs rawRhs freshLhs freshRhs : Atom) : Prop :=
  ∃ rename : String → String,
    Function.Injective rename ∧
      AlphaRenameAtomRel rename rawLhs freshLhs ∧
      AlphaRenameAtomRel rename rawRhs freshRhs ∧
      ∀ name,
        (AtomOccurs rawLhs name ∨ AtomOccurs rawRhs name) →
          ¬QueryVisibleName live query incoming (rename name)

/-- One hygienically selected equation rule whose fresh left-hand side
matches the query. -/
def HumanEquationRuleMatchRel
    (space : Space) (live : List Atom) (query : Atom) (incoming : Bindings)
    (freshPattern freshRhs : Atom) (matched : Bindings) : Prop :=
  ∃ rawLhs rawRhs,
    .expression [.symbol "=", rawLhs, rawRhs] ∈ space.atoms ∧
      AlphaVariantRel live query incoming
        rawLhs rawRhs freshPattern freshRhs ∧
      MatchRel equalityGroundedSemantic query freshPattern matched

/-- One selected equation rule survives the ambient merge and emits an atom
observationally equal to the fresh RHS. -/
def HumanEquationQueryCandidateRel
    (space : Space) (live : List Atom) (query : Atom) (incoming : Bindings)
    (emitted : Atom) (output : Bindings) : Prop :=
  ∃ freshPattern freshRhs matched,
    HumanEquationRuleMatchRel space live query incoming
      freshPattern freshRhs matched ∧
      MergeRel equalityGroundedSemantic incoming matched output ∧
      SemanticLoopFree output ∧
      (∃ valuation : String → Metta.Atom,
        LeaTTaBridge.HEBindingSatisfied valuation output) ∧
      ∀ valuation : String → Metta.Atom,
        LeaTTaBridge.HEBindingSatisfied valuation output →
          LeaTTaBridge.HEAtomEquationSatisfied valuation emitted freshRhs

/-- No selected equation rule matches the query.  This is the human
counterpart of the unchanged-query result, without an executable empty-list
test. -/
def HumanEquationQueryNoMatchRel
    (space : Space) (live : List Atom) (query : Atom)
    (incoming : Bindings) : Prop :=
  ∀ freshPattern freshRhs matched,
    ¬HumanEquationRuleMatchRel space live query incoming
      freshPattern freshRhs matched

/-- At least one equation rule matches, but every match is eliminated by the
ambient merge or semantic filters.  This is the human counterpart of the
`Empty` result after a nonempty equation query. -/
def HumanEquationQueryAllFilteredRel
    (space : Space) (live : List Atom) (query : Atom)
    (incoming : Bindings) : Prop :=
  (∃ freshPattern freshRhs matched,
    HumanEquationRuleMatchRel space live query incoming
      freshPattern freshRhs matched) ∧
    ∀ emitted output,
      ¬HumanEquationQueryCandidateRel
        space live query incoming emitted output

/-! ## Boundary examples -/

private theorem mergeEmptyEmpty :
    MergeRel equalityGroundedSemantic
      Bindings.empty Bindings.empty Bindings.empty :=
  .mk (by simp [constraints, Bindings.empty]) MergeConstraintsRel.nil

private theorem emptyBindingsSatisfied :
    LeaTTaBridge.HEBindingSatisfied
      (fun name => .var name) Bindings.empty := by
  constructor
  · intro name value hmem
    simp [Bindings.empty] at hmem
  · intro left right hmem
    simp [Bindings.empty] at hmem

private theorem equalSymbolUnifySuccess (branch : Atom) :
    HumanUnifySuccessRel
      (.symbol "a") (.symbol "a") branch
      Bindings.empty branch Bindings.empty := by
  refine ⟨⟨Bindings.empty,
    MatchRel.symSym "a" semanticLoopFree_empty,
    mergeEmptyEmpty, semanticLoopFree_empty,
    ⟨fun name => .var name, emptyBindingsSatisfied⟩⟩, ?_⟩
  intro valuation _
  rfl

/-- Positive unify: equal symbols select the then branch. -/
example : HumanUnifyStep
    (.symbol "a") (.symbol "a") (.symbol "then") (.symbol "else")
    Bindings.empty (.symbol "then") Bindings.empty :=
  .success (equalSymbolUnifySuccess (.symbol "then"))

private theorem distinctSymbolUnifyNoMatch :
    HumanUnifyNoMatchRel
      (.symbol "a") (.symbol "b") Bindings.empty := by
  intro output hcandidate
  obtain ⟨matched, hmatch, _⟩ := hcandidate
  exact symbol_mismatch_not_match (by decide) matched hmatch

/-- Negative unify: distinct symbols select the else branch. -/
example : HumanUnifyStep
    (.symbol "a") (.symbol "b") (.symbol "then") (.symbol "else")
    Bindings.empty (.symbol "else") Bindings.empty :=
  .noMatch distinctSymbolUnifyNoMatch

/-- Positive ordered switch: a failed first branch falls through to the first
successful branch. -/
example : HumanSwitchStep (.symbol "a")
    [.expression [.symbol "b", .symbol "wrong"],
      .expression [.symbol "a", .symbol "right"]]
    Bindings.empty (.symbol "right") Bindings.empty := by
  apply HumanSwitchStep.selected
  · exact HumanSwitchRawRel.miss distinctSymbolUnifyNoMatch
      (HumanSwitchRawRel.hit (by
        simpa only using equalSymbolUnifySuccess (.symbol "right")))
  · decide

/-- Negative ordered switch: an empty branch list yields `Empty`. -/
example : HumanSwitchStep (.symbol "a") [] Bindings.empty
    Atom.empty Bindings.empty :=
  .noMatch HumanSwitchRawRel.nil

private def oneRuleSpace : Space :=
  Space.ofList [
    .expression [.symbol "=", .symbol "a", .symbol "result"]]

private theorem closedSymbolsAlphaVariant :
    AlphaVariantRel [] (.symbol "a") Bindings.empty
      (.symbol "a") (.symbol "result")
      (.symbol "a") (.symbol "result") := by
  refine ⟨id, Function.injective_id,
    AlphaRenameAtomRel.symbol "a", AlphaRenameAtomRel.symbol "result", ?_⟩
  intro name hocc
  rcases hocc with hocc | hocc <;> cases hocc

/-- Positive equation selection: a closed rule in the space supplies a human
query candidate without any executable query operation. -/
example : HumanEquationQueryCandidateRel oneRuleSpace []
    (.symbol "a") Bindings.empty (.symbol "result") Bindings.empty := by
  refine ⟨.symbol "a", .symbol "result", Bindings.empty, ?_,
    mergeEmptyEmpty, semanticLoopFree_empty,
    ⟨fun name => .var name, emptyBindingsSatisfied⟩, ?_⟩
  · refine ⟨.symbol "a", .symbol "result", ?_, closedSymbolsAlphaVariant,
      MatchRel.symSym "a" semanticLoopFree_empty⟩
    simp [oneRuleSpace, Space.ofList]
  · intro valuation _
    rfl

/-- Negative equation selection: an empty space has no matching rule. -/
example : HumanEquationQueryNoMatchRel Space.empty []
    (.symbol "a") Bindings.empty := by
  intro freshPattern freshRhs matched hmatch
  obtain ⟨rawLhs, rawRhs, hmem, _⟩ := hmatch
  simp [Space.empty] at hmem

end Mettapedia.Languages.MeTTa.HE.HumanEvalSteps
