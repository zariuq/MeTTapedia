import Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
import Mettapedia.GSLT.Parsing.ClassAwarePackedForest
import Mettapedia.GSLT.Parsing.GrammarConstructorActions
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Constructor values selected from exact ParserPack certificates

The existing certificate authority checks physical row positions, scalar
spans and ordered terminal/nonterminal seams. This module adds the existing
fixed-head constructor actions and an explicit ambiguity policy: accept one
distinct semantic value, retaining every certificate that produced it.

All physical parser slots, including terminals and EOF, participate in action
evaluation. Raw `cons` applications remain constructor data. An unavailable
action refuses the entire catalogue; it never silently drops an alternative.

The source reflection theorem uses the existing exact source-plan agreement.
It does not claim that an arbitrary native forest is complete or that an
unmatched span/guard extension implements this certificate authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ParserPackSelectedValue

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open GrammarConstructorActions (Action)
open ClassAwareParserPackCorrespondence
open ClassAwareParserPackCertificate
open ClassAwareParserPackEnumeration
open LanguageDefSyntaxCompiler (CompiledRule)
open ParserProfileSemantics (ParserProfileLayer)
open PresentationExprSemantics (CST)

abbrev ConstructorAction := Action Atom Empty

/-- The native fixed-head fragment constructs data without evaluating it. -/
def execute (slots : List Atom) (action : ConstructorAction) : Option Atom :=
  action.executeWith some (fun head values =>
    some (.expression (.symbol head :: values))) (fun impossible => nomatch impossible) slots

def executeArguments (slots : List Atom) (actions : List ConstructorAction) :
    Option (List Atom) :=
  GrammarConstructorActions.executeArgumentsWith some
    (fun head values => some (.expression (.symbol head :: values)))
    (fun impossible => nomatch impossible) slots actions

mutual
  /-- Independent construction judgment for the existing fixed-head actions. -/
  inductive ActionEvaluates (slots : List Atom) : ConstructorAction → Atom → Prop where
    | slot {index : Nat} {value : Atom} (selected : slots[index]? = some value) :
        ActionEvaluates slots (.slot index) value
    | constant (value : Atom) : ActionEvaluates slots (.constant value) value
    | apply {head : String} {actions : List ConstructorAction} {values : List Atom}
        (arguments : ArgumentsEvaluate slots actions values) :
        ActionEvaluates slots (.apply head actions) (.expression (.symbol head :: values))

  inductive ArgumentsEvaluate (slots : List Atom) :
      List ConstructorAction → List Atom → Prop where
    | nil : ArgumentsEvaluate slots [] []
    | cons {head : ConstructorAction} {tail : List ConstructorAction}
        {first : Atom} {rest : List Atom}
        (firstValue : ActionEvaluates slots head first)
        (restValues : ArgumentsEvaluate slots tail rest) :
        ArgumentsEvaluate slots (head :: tail) (first :: rest)
end

mutual
  theorem execute_iff (slots : List Atom) (action : ConstructorAction) (value : Atom) :
      execute slots action = some value ↔ ActionEvaluates slots action value := by
    cases action with
    | slot index =>
        constructor
        · exact ActionEvaluates.slot
        · intro evaluated; cases evaluated; assumption
    | constant literal =>
        constructor
        · intro same
          have equal : literal = value := by simpa [execute, Action.executeWith] using same
          subst value
          exact .constant literal
        · intro evaluated; cases evaluated; rfl
    | apply head actions =>
        change (do let values ← executeArguments slots actions
                   pure (Atom.expression (.symbol head :: values))) = some value ↔ _
        constructor
        · intro accepted
          cases computed : executeArguments slots actions with
          | none => simp [computed] at accepted
          | some values =>
              have same : Atom.expression (.symbol head :: values) = value := by
                simpa [computed] using accepted
              subst value
              exact .apply ((executeArguments_iff slots actions values).mp computed)
        · intro evaluated
          cases evaluated with
          | apply arguments =>
              rw [(executeArguments_iff slots actions _).mpr arguments]
              rfl
    | primitive impossible _ => nomatch impossible

  theorem executeArguments_iff (slots : List Atom) (actions : List ConstructorAction)
      (values : List Atom) :
      executeArguments slots actions = some values ↔ ArgumentsEvaluate slots actions values := by
    cases actions with
    | nil =>
        constructor
        · intro same; cases same; exact .nil
        · intro evaluated; cases evaluated; rfl
    | cons head tail =>
        change (do let first ← execute slots head
                   let rest ← executeArguments slots tail
                   pure (first :: rest)) = some values ↔ _
        constructor
        · intro accepted
          cases firstEq : execute slots head with
          | none => simp [firstEq] at accepted
          | some first =>
              cases restEq : executeArguments slots tail with
              | none => simp [firstEq, restEq] at accepted
              | some rest =>
                  have same : first :: rest = values := by simpa [firstEq, restEq] using accepted
                  subst values
                  exact .cons ((execute_iff slots head first).mp firstEq)
                    ((executeArguments_iff slots tail rest).mp restEq)
        · intro evaluated
          cases evaluated with
          | cons firstValue restValues =>
              rw [(execute_iff slots head _).mpr firstValue,
                (executeArguments_iff slots tail _).mpr restValues]
              rfl
end

/-- Actions are indexed by physical table position, never by rule spelling. -/
structure ActionTable where
  lexical : List ConstructorAction
  structural : List ConstructorAction

/-- An action exists for every physical row and no extra row is admitted. -/
def ActionTable.Covers (actions : ActionTable) (plan : CompiledParserPackPlan) : Prop :=
  actions.lexical.length = plan.lexical.productions.length ∧
    actions.structural.length = plan.structural.length

/-- The scalar/EOF values occupying physical terminal slots. Class and exact
character admission is supplied by the existing exact parser replay. -/
def terminalValue? (input : List Nat) (matcher : TerminalMatcher) (start stop : Nat) :
    Option Atom :=
  match matcher with
  | .eof => if start = stop ∧ start = input.length then some (.symbol "eof") else none
  | _ => if stop = start + 1 then
      input[start]?.map fun scalar => .expression [.symbol "cp", .grounded (.int scalar)]
    else none

mutual
  def certificateValue? (actions : ActionTable) (input : List Nat) :
      Certificate → Option Atom
    | .lexical position matcher start stop => do
        let action ← actions.lexical[position]?
        let scalar ← terminalValue? input matcher start stop
        execute [scalar] action
    | .structural position _ _ body => do
        let action ← actions.structural[position]?
        let values ← itemsValues? actions input body
        execute values action

  def itemsValues? (actions : ActionTable) (input : List Nat) :
      ItemsCertificate → Option (List Atom)
    | .nil _ => some []
    | .terminal matcher start stop rest => do
        let first ← terminalValue? input matcher start stop
        let values ← itemsValues? actions input rest
        pure (first :: values)
    | .nonterminal _ _ _ head rest => do
        let first ← certificateValue? actions input head
        let values ← itemsValues? actions input rest
        pure (first :: values)
end

mutual
  inductive ValueReplays (actions : ActionTable) (input : List Nat) :
      Certificate → Atom → Prop where
    | lexical {position start stop : Nat} {matcher : TerminalMatcher}
        {action : ConstructorAction} {scalar value : Atom}
        (selected : actions.lexical[position]? = some action)
        (terminal : terminalValue? input matcher start stop = some scalar)
        (evaluated : ActionEvaluates [scalar] action value) :
        ValueReplays actions input (.lexical position matcher start stop) value
    | structural {position start stop : Nat} {body : ItemsCertificate}
        {action : ConstructorAction} {values : List Atom} {value : Atom}
        (selected : actions.structural[position]? = some action)
        (children : ItemsValuesReplay actions input body values)
        (evaluated : ActionEvaluates values action value) :
        ValueReplays actions input (.structural position start stop body) value

  inductive ItemsValuesReplay (actions : ActionTable) (input : List Nat) :
      ItemsCertificate → List Atom → Prop where
    | nil (cursor : Nat) : ItemsValuesReplay actions input (.nil cursor) []
    | terminal {matcher : TerminalMatcher} {start stop : Nat}
        {rest : ItemsCertificate} {first : Atom} {values : List Atom}
        (terminal : terminalValue? input matcher start stop = some first)
        (children : ItemsValuesReplay actions input rest values) :
        ItemsValuesReplay actions input (.terminal matcher start stop rest) (first :: values)
    | nonterminal {sort : String} {start stop : Nat} {head : Certificate}
        {rest : ItemsCertificate} {first : Atom} {values : List Atom}
        (value : ValueReplays actions input head first)
        (children : ItemsValuesReplay actions input rest values) :
        ItemsValuesReplay actions input
          (.nonterminal sort start stop head rest) (first :: values)
end

mutual
  theorem certificateValue?_iff (actions : ActionTable) (input : List Nat)
      (certificate : Certificate) (value : Atom) :
      certificateValue? actions input certificate = some value ↔
        ValueReplays actions input certificate value := by
    cases certificate with
    | lexical position matcher start stop =>
        constructor
        · intro computed
          cases actionEq : actions.lexical[position]? with
          | none => simp [certificateValue?, actionEq] at computed
          | some action =>
              cases scalarEq : terminalValue? input matcher start stop with
              | none => simp [certificateValue?, actionEq, scalarEq] at computed
              | some scalar =>
                  exact .lexical actionEq scalarEq ((execute_iff [scalar] action value).mp
                    (by simpa [certificateValue?, actionEq, scalarEq] using computed))
        · intro replay
          cases replay with
          | lexical selected terminal evaluated =>
              simp [certificateValue?, selected, terminal, (execute_iff _ _ _).mpr evaluated]
    | structural position start stop body =>
        constructor
        · intro computed
          cases actionEq : actions.structural[position]? with
          | none => simp [certificateValue?, actionEq] at computed
          | some action =>
              cases valuesEq : itemsValues? actions input body with
              | none => simp [certificateValue?, actionEq, valuesEq] at computed
              | some values =>
                  exact .structural actionEq ((itemsValues?_iff actions input body values).mp valuesEq)
                    ((execute_iff values action value).mp
                      (by simpa [certificateValue?, actionEq, valuesEq] using computed))
        · intro replay
          cases replay with
          | structural selected children evaluated =>
              simp [certificateValue?, selected, (itemsValues?_iff _ _ _ _).mpr children,
                (execute_iff _ _ _).mpr evaluated]

  theorem itemsValues?_iff (actions : ActionTable) (input : List Nat)
      (certificate : ItemsCertificate) (values : List Atom) :
      itemsValues? actions input certificate = some values ↔
        ItemsValuesReplay actions input certificate values := by
    cases certificate with
    | nil cursor =>
        constructor
        · intro same; cases same; exact .nil cursor
        · intro replay; cases replay; rfl
    | terminal matcher start stop rest =>
        constructor
        · intro computed
          cases firstEq : terminalValue? input matcher start stop with
          | none => simp [itemsValues?, firstEq] at computed
          | some first =>
              cases restEq : itemsValues? actions input rest with
              | none => simp [itemsValues?, firstEq, restEq] at computed
              | some remaining =>
                  have same : first :: remaining = values := by
                    simpa [itemsValues?, firstEq, restEq] using computed
                  subst values
                  exact .terminal firstEq ((itemsValues?_iff _ _ _ _).mp restEq)
        · intro replay
          cases replay with
          | terminal first restReplay =>
              simp [itemsValues?, first, (itemsValues?_iff _ _ _ _).mpr restReplay]
    | nonterminal sort start stop head rest =>
        constructor
        · intro computed
          cases firstEq : certificateValue? actions input head with
          | none => simp [itemsValues?, firstEq] at computed
          | some first =>
              cases restEq : itemsValues? actions input rest with
              | none => simp [itemsValues?, firstEq, restEq] at computed
              | some remaining =>
                  have same : first :: remaining = values := by
                    simpa [itemsValues?, firstEq, restEq] using computed
                  subst values
                  exact .nonterminal ((certificateValue?_iff _ _ _ _).mp firstEq)
                    ((itemsValues?_iff _ _ _ _).mp restEq)
        · intro replay
          cases replay with
          | nonterminal first restReplay =>
              simp [itemsValues?, (certificateValue?_iff _ _ _ _).mpr first,
                (itemsValues?_iff _ _ _ _).mpr restReplay]
end

abbrev Catalogue := List (Certificate × CST)

def evaluateCatalogue? (actions : ActionTable) (input : List Nat) :
    Catalogue → Option (List Atom)
  | [] => some []
  | row :: rows => do
      let value ← certificateValue? actions input row.1
      let rest ← evaluateCatalogue? actions input rows
      pure (value :: rest)

theorem evaluateCatalogue?_iff (actions : ActionTable) (input : List Nat)
    (rows : Catalogue) (values : List Atom) :
    evaluateCatalogue? actions input rows = some values ↔
      List.Forall₂ (fun row value => certificateValue? actions input row.1 = some value)
        rows values := by
  induction rows generalizing values with
  | nil =>
      cases values <;> simp [evaluateCatalogue?]
  | cons row rows ih =>
      cases computed : certificateValue? actions input row.1 with
      | none => simp [evaluateCatalogue?, computed, List.forall₂_cons_left_iff]
      | some value =>
          cases restEq : evaluateCatalogue? actions input rows with
          | none =>
              constructor
              · intro impossible; simp [evaluateCatalogue?, computed, restEq] at impossible
              · intro related
                cases related with
                | cons first rest =>
                    have accepted := (ih _).mpr rest
                    simp [restEq] at accepted
          | some rest =>
              constructor
              · intro accepted
                have same : value :: rest = values := by
                  simpa [evaluateCatalogue?, computed, restEq] using accepted
                subst values
                exact .cons computed ((ih _).mp restEq)
              · intro related
                cases related with
                | cons first tail =>
                    have firstEq : value = _ := Option.some.inj (computed.symm.trans first)
                    have tailEq := (ih _).mpr tail
                    have remainingEq := Option.some.inj (restEq.symm.trans tailEq)
                    subst_vars
                    simp [evaluateCatalogue?, computed, restEq]

/-- Exactly one distinct value; derivation multiplicity remains in the catalogue. -/
def selectUnique : List Atom → Option Atom
  | [] => none
  | first :: rest => if rest.all (fun value => value == first) then some first else none

theorem selectUnique_iff (values : List Atom) (value : Atom) :
    selectUnique values = some value ↔ values ≠ [] ∧ ∀ candidate ∈ values, candidate = value := by
  cases values with
  | nil => simp [selectUnique]
  | cons first rest =>
      simp only [selectUnique, List.all_eq_true, beq_iff_eq]
      split
      · rename_i equal
        constructor
        · intro same
          have sameValue : first = value := Option.some.inj same
          subst value
          refine ⟨by simp, ?_⟩
          intro candidate member
          rcases List.mem_cons.mp member with rfl | occurs
          · rfl
          · exact equal candidate occurs
        · rintro ⟨_, all⟩
          rw [all first (by simp)]
      · rename_i different
        constructor
        · intro impossible; contradiction
        · rintro ⟨_, all⟩
          have same := all first (by simp)
          exfalso
          apply different
          intro candidate occurs
          exact (all candidate (by simp [occurs])).trans same.symm

def selectCatalogue? (actions : ActionTable) (input : List Nat) (rows : Catalogue) : Option Atom :=
  (evaluateCatalogue? actions input rows).bind selectUnique

/-- Catalogue qualification retains every exact root replay and requires every
root derivation occurrence, including equal-valued duplicate productions. -/
structure CompleteCatalogue (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (rows : Catalogue) : Prop where
  replay : ∀ row ∈ rows, Nonempty (Replays profile plan input row.1
    plan.lexical.startSort 0 input.length row.2)
  complete : ∀ tree (derivation : ParserPackRootDerives profile plan input tree),
    (Certificate.ofDerivation derivation, tree) ∈ rows

theorem enumeratedCatalogue_complete {fuel : Nat} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (bounded : RootHeightBound profile plan input fuel) :
    CompleteCatalogue profile plan input (rootCatalogueRows fuel profile plan input) :=
  ⟨fun _ => rootCatalogueRows_replay, rootCatalogueRows_complete bounded⟩

private theorem forall₂_row {rows : Catalogue} {values : List Atom}
    {relation : Certificate × CST → Atom → Prop}
    (related : List.Forall₂ relation rows values) {row : Certificate × CST}
    (occurs : row ∈ rows) : ∃ value ∈ values, relation row value := by
  induction related with
  | nil => simp at occurs
  | @cons firstRow firstValue restRows restValues first rest ih =>
      rcases List.mem_cons.mp occurs with rfl | occurs
      · exact ⟨firstValue, by simp, first⟩
      · obtain ⟨value, member, exactValue⟩ := ih occurs
        exact ⟨value, by simp [member], exactValue⟩

private theorem evaluateCatalogue?_constant (actions : ActionTable) (input : List Nat)
    (rows : Catalogue) (value : Atom)
    (same : ∀ row ∈ rows, certificateValue? actions input row.1 = some value) :
    evaluateCatalogue? actions input rows = some (rows.map fun _ => value) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      have first := same row (by simp)
      have tail := ih (fun candidate occurs => same candidate (by simp [occurs]))
      simp [evaluateCatalogue?, first, tail]

/-- Two-sided selection, including refusal of a failed action on any retained
alternative. This does not require a first-match or backend-order assumption. -/
theorem selectCatalogue?_iff (actions : ActionTable) (input : List Nat)
    (rows : Catalogue) (value : Atom) :
    selectCatalogue? actions input rows = some value ↔
      rows ≠ [] ∧ ∀ row ∈ rows, ValueReplays actions input row.1 value := by
  constructor
  · intro selected
    cases computed : evaluateCatalogue? actions input rows with
    | none => simp [selectCatalogue?, computed] at selected
    | some values =>
        have unique := (selectUnique_iff values value).mp
          (by simpa [selectCatalogue?, computed] using selected)
        have related := (evaluateCatalogue?_iff actions input rows values).mp computed
        refine ⟨?_, ?_⟩
        · intro empty; subst rows; cases related; exact unique.1 rfl
        · intro row occurs
          obtain ⟨answer, member, exactValue⟩ := forall₂_row related occurs
          rw [unique.2 answer member] at exactValue
          exact (certificateValue?_iff _ _ _ _).mp exactValue
  · rintro ⟨nonempty, same⟩
    have computed := evaluateCatalogue?_constant actions input rows value
      (fun row occurs => (certificateValue?_iff _ _ _ _).mpr (same row occurs))
    simp only [selectCatalogue?, computed, Option.bind_some]
    apply (selectUnique_iff _ _).mpr
    refine ⟨by simpa using nonempty, ?_⟩
    intro candidate member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    rfl

/-- Packing the retained catalogue keeps all physical families and source
spans; only literally equal families are shared by the existing packer. -/
def retainedForest (plan : CompiledParserPackPlan) (rows : Catalogue) :
    ClassAwarePackedForest.Forest :=
  ClassAwarePackedForest.pack (rows.map fun row => (plan.lexical.startSort, row.1))

theorem retainedForest_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {rows : Catalogue}
    (qualified : CompleteCatalogue profile plan input rows) :
    ∀ tree, ClassAwarePackedForest.Complete (retainedForest plan rows) profile plan input
      plan.lexical.startSort 0 input.length tree := by
  intro tree derivation
  apply ClassAwarePackedForest.member_pack_rootUnfolds
  apply List.mem_map.mpr
  exact ⟨(Certificate.ofDerivation derivation, tree), qualified.complete tree derivation, rfl⟩

/-- Unique semantic value for all independently admitted root occurrences.
The universal condition includes action availability, rather than forgetting
uninterpreted roots before testing ambiguity. -/
def UniqueRootValue (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (actions : ActionTable) (input : List Nat) (value : Atom) : Prop :=
  (∃ tree, Nonempty (ParserPackRootDerives profile plan input tree)) ∧
    ∀ tree (derivation : ParserPackRootDerives profile plan input tree),
      ValueReplays actions input (Certificate.ofDerivation derivation) value

theorem selectCatalogue?_iff_uniqueRootValue {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {actions : ActionTable} {input : List Nat}
    {rows : Catalogue} {value : Atom}
    (qualified : CompleteCatalogue profile plan input rows) :
    selectCatalogue? actions input rows = some value ↔
      UniqueRootValue profile plan actions input value := by
  rw [selectCatalogue?_iff]
  constructor
  · rintro ⟨nonempty, same⟩
    constructor
    · cases rows with
      | nil => contradiction
      | cons row rest =>
          obtain ⟨replay⟩ := qualified.replay row (by simp)
          exact ⟨row.2, ⟨replay.derivation⟩⟩
    · intro tree derivation
      exact same _ (qualified.complete tree derivation)
  · rintro ⟨⟨tree, ⟨derivation⟩⟩, unique⟩
    refine ⟨?_, ?_⟩
    · intro empty
      have member := qualified.complete tree derivation
      simp [empty] at member
    · intro row member
      obtain ⟨replay⟩ := qualified.replay row member
      have evaluated := unique row.2 replay.derivation
      simpa only [Replays.certificate_derivation] using evaluated

theorem selectedCatalogue_reflects {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule} {plan : CompiledParserPackPlan}
    {actions : ActionTable} {input : List Nat} {rows : Catalogue} {value : Atom}
    (agreement : ParserPackPlanAgreement literalScalars? profile rules plan)
    (qualified : CompleteCatalogue profile plan input rows)
    (selected : selectCatalogue? actions input rows = some value) :
    (∃ row ∈ rows, Nonempty (SourcePlanRootDerives literalScalars? profile rules input row.2) ∧
      ValueReplays actions input row.1 value) ∧
    (∀ tree (derivation : ParserPackRootDerives profile plan input tree),
      ValueReplays actions input (Certificate.ofDerivation derivation) value) := by
  cases computed : evaluateCatalogue? actions input rows with
  | none => simp [selectCatalogue?, computed] at selected
  | some values =>
      have unique := (selectUnique_iff values value).mp
        (by simpa [selectCatalogue?, computed] using selected)
      have related := (evaluateCatalogue?_iff actions input rows values).mp computed
      have nonempty : rows ≠ [] := by
        intro empty; subst rows; cases related; exact unique.1 rfl
      constructor
      · cases rows with
        | nil => contradiction
        | cons row rest =>
            have occurs : row ∈ row :: rest := by simp
            obtain ⟨answer, occursValue, exactValue⟩ := forall₂_row related occurs
            have replay := (qualified.replay row occurs).some
            refine ⟨row, occurs, ⟨(sourcePlanRootDerivationEquiv agreement row.2).symm replay.derivation⟩, ?_⟩
            rw [unique.2 answer occursValue] at exactValue
            exact (certificateValue?_iff _ _ _ _).mp exactValue
      · intro tree derivation
        obtain ⟨answer, occursValue, exactValue⟩ :=
          forall₂_row related (qualified.complete tree derivation)
        rw [unique.2 answer occursValue] at exactValue
        exact (certificateValue?_iff _ _ _ _).mp exactValue

theorem selectUnique_permutation (left right : List Atom) (same : left.Perm right) (value : Atom) :
    selectUnique left = some value ↔ selectUnique right = some value := by
  rw [selectUnique_iff, selectUnique_iff]
  constructor <;> rintro ⟨nonempty, unique⟩
  · exact ⟨fun empty => nonempty (by
        apply List.length_eq_zero_iff.mp
        rw [same.length_eq, empty]
        rfl),
      fun candidate occurs => unique candidate (same.mem_iff.mpr occurs)⟩
  · exact ⟨fun empty => nonempty (by
        apply List.length_eq_zero_iff.mp
        rw [← same.length_eq, empty]
        rfl),
      fun candidate occurs => unique candidate (same.mem_iff.mp occurs)⟩

theorem distinct_values_refused (values : List Atom) (left right : Atom)
    (leftMember : left ∈ values) (rightMember : right ∈ values) (different : left ≠ right) :
    selectUnique values = none := by
  cases selected : selectUnique values with
  | none => rfl
  | some value =>
      have unique := (selectUnique_iff values value).mp selected
      exact False.elim (different ((unique.2 left leftMember).trans (unique.2 right rightMember).symm))

theorem raw_cons_action_preserved (first rest : Atom) :
    execute [first, rest] (.apply "cons" [.slot 0, .slot 1]) =
      some (.expression [.symbol "cons", first, rest]) := rfl

theorem equal_values_with_distinct_derivations_accepted (value : Atom) :
    selectUnique [value, value] = some value := by simp [selectUnique]

theorem zero_results_refused : selectUnique [] = none := rfl

theorem extra_value_refused : selectUnique [.symbol "mm0-file", .symbol "wrong"] = none := rfl

theorem missing_action_refuses_catalogue (input : List Nat) (tree : CST) :
    selectCatalogue? ⟨[], []⟩ input [(.structural 0 0 input.length (.nil 0), tree)] = none := rfl

/-! The controls below are a certificate boundary canary, not a second MM0
grammar. Two physical source derivations can intentionally construct one AST. -/

private def controlProfile : ParserProfileLayer := {
  name := "SelectedValueCanary"
  startSort := "Value"
  classes := []
  states := []
}

private def controlPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "SelectedValueCanary"
    startSort := "Value"
    classes := []
    productions := [
      { label := "left", resultSort := "Value", matcher := .char 65, childSlots := [0] },
      { label := "right", resultSort := "Value", matcher := .char 65, childSlots := [0] }]
  }
  structural := []
}

private def controlRows : Catalogue := rootCatalogueRows 1 controlProfile controlPlan [65]

private def controlActions : ActionTable := ⟨[.slot 0, .slot 0], []⟩

private def controlValue : Atom := .expression [.symbol "cp", .grounded (.int 65)]

private theorem controlHeightBound : RootHeightBound controlProfile controlPlan [65] 1 := by
  intro tree derivation
  cases derivation with
  | lexical => simp [ParserPackDerivesAt.height]
  | structural position valid => simp [controlPlan] at valid

theorem control_exact_rows : controlRows = [
    (.lexical 0 (.char 65) 0 1, .node "left" 0 1 [.terminal [65] 0 1]),
    (.lexical 1 (.char 65) 0 1, .node "right" 0 1 [.terminal [65] 0 1])] := by decide

/-- Positive lowering: two independently labelled source trees and two
physical production families produce one transparent scalar AST. -/
theorem control_two_derivations_one_value :
    selectCatalogue? controlActions [65] controlRows = some controlValue := by decide

theorem control_retains_both_physical_families :
    (retainedForest controlPlan controlRows).families.length = 2 := by decide

theorem control_full_semantic_qualification :
    UniqueRootValue controlProfile controlPlan controlActions [65] controlValue :=
  (selectCatalogue?_iff_uniqueRootValue (enumeratedCatalogue_complete controlHeightBound)).mp
    control_two_derivations_one_value

/-- Removing one equal-valued alternative leaves the value policy satisfied,
but violates exact catalogue completeness. Both gates are necessary. -/
theorem control_missing_alternative_not_complete :
    ¬ CompleteCatalogue controlProfile controlPlan [65] (controlRows.take 1) := by
  intro claimed
  let row : Certificate × CST :=
    (.lexical 1 (.char 65) 0 1, .node "right" 0 1 [.terminal [65] 0 1])
  have member : row ∈ controlRows := by rw [control_exact_rows]; simp [row]
  obtain ⟨replay⟩ := rootCatalogueRows_replay member
  have required := claimed.complete row.2 replay.derivation
  rw [Replays.certificate_derivation] at required
  rw [control_exact_rows] at required
  simp [row] at required

theorem control_two_distinct_values_refused :
    selectCatalogue? ⟨[.constant (.symbol "left"), .constant (.symbol "right")], []⟩
      [65] controlRows = none := by decide

theorem control_changed_span_not_admitted :
    ¬ Nonempty (Replays controlProfile controlPlan [65]
      (.lexical 0 (.char 65) 0 2) "Value" 0 1
      (.node "left" 0 1 [.terminal [65] 0 1])) := by
  rintro ⟨replay⟩
  cases replay

theorem control_spurious_production_not_admitted :
    ¬ Nonempty (Replays controlProfile controlPlan [65]
      (.lexical 2 (.char 65) 0 1) "Value" 0 1
      (.node "extra" 0 1 [.terminal [65] 0 1])) := by
  rintro ⟨replay⟩
  cases replay with
  | lexical position valid => simp [controlPlan] at valid

#print axioms selectedCatalogue_reflects
#print axioms selectUnique_permutation
#print axioms certificateValue?_iff
#print axioms control_full_semantic_qualification
#print axioms control_missing_alternative_not_complete

end Mettapedia.GSLT.Parsing.ParserPackSelectedValue
