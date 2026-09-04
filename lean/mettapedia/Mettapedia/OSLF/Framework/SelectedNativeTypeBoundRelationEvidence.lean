import Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
import Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Exact evidence for source-bound relation premises

The selected-native premise decoder recognizes relation queries whose
arguments are typed variables supplied by the authored rewrite source.  This
module gives that fragment an independent operational meaning and relates it
exactly to the ordinary MeTTaIL premise semantics.

The covered runtime boundary is deliberately narrow.  Every query argument
must already be bound, builtin rows must be disjoint, and the external
relation must be an exact deterministic echo: it returns the concrete
argument row once when enabled and no row when disabled.  Under this contract
a query preserves the binding environment exactly.  Ordered rows of such
queries are then equivalent to `PremisesAt`, without deduplication or a second
premise evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Proof-relevant alignment between an authored relation-query argument row
and the values already present in one binding environment.  Names, values,
order, and duplicates all remain explicit. -/
structure BoundArguments {rewrite : RewriteRule}
    (view : View rewrite) (bindings : Bindings) where
  names : List String
  values : List Pattern
  arguments_eq : view.arguments = names.map Pattern.fvar
  aligned : List.Forall₂
    (fun name value => bindings.lookup name = some value) names values

namespace BoundArguments

/-- Substitution of a fully bound authored query yields its retained concrete
value row exactly. -/
theorem applied_eq {rewrite : RewriteRule} {view : View rewrite}
    {bindings : Bindings} (bound : BoundArguments view bindings) :
    view.arguments.map (applyBindings bindings) = bound.values := by
  rw [bound.arguments_eq]
  exact map_applyBindings_boundVariables_eq bound.aligned

/-- A fully bound query matches its own concrete value row with no binding
extension. -/
theorem match_eq {rewrite : RewriteRule} {view : View rewrite}
    {bindings : Bindings} (bound : BoundArguments view bindings) :
    matchRelationArgs bindings view.arguments bound.values = [[]] := by
  rw [bound.arguments_eq]
  exact matchRelationArgs_boundVariables_eq bound.aligned

end BoundArguments

/-- Independent truth of one decoded external relation claim at an exact
binding environment.  This is a fact about the declared `RelationEnv`, not
about generated derivability or checker acceptance. -/
def Meaning {rewrite : RewriteRule} (relations : RelationEnv)
    (bindings : Bindings) (view : View rewrite) : Prop :=
  let values := view.arguments.map (applyBindings bindings)
  values ∈ relations.tuples view.relation values

/-- Exact deterministic contract for a fully bound external query.  The
boolean is fixed by equality with the actual relation table; it is not an
additional authority. -/
structure EchoContract (relations : RelationEnv) (language : LanguageDef)
    {rewrite : RewriteRule} (view : View rewrite) (bindings : Bindings) where
  typed : view.WellTyped
  bound : BoundArguments view bindings
  outcome : Bool
  noBuiltin :
    builtinRelationTuples language view.relation bound.values = []
  echo :
    relations.tuples view.relation bound.values =
      if outcome then [bound.values] else []

/-- Construct the unique boolean view of a table already proved to be either
the exact concrete echo row or empty.  The table equality fixes the outcome;
this constructor does not decide a second relation. -/
def EchoContract.ofEchoOrEmpty
    {relations : RelationEnv} {language : LanguageDef}
    {rewrite : RewriteRule} {view : View rewrite} {bindings : Bindings}
    (typed : view.WellTyped) (bound : BoundArguments view bindings)
    (noBuiltin :
      builtinRelationTuples language view.relation bound.values = [])
    (classified :
      relations.tuples view.relation bound.values = [bound.values] ∨
        relations.tuples view.relation bound.values = []) :
    EchoContract relations language view bindings where
  typed := typed
  bound := bound
  outcome := decide
    (relations.tuples view.relation bound.values = [bound.values])
  noBuiltin := noBuiltin
  echo := by
    by_cases enabled :
        relations.tuples view.relation bound.values = [bound.values]
    · simp [enabled]
    · rcases classified with exactEcho | empty
      · exact (enabled exactEcho).elim
      · simp [empty]

namespace EchoContract

/-- Proof-facing truth projection of an exact echo contract. -/
def Holds {relations : RelationEnv} {language : LanguageDef}
    {rewrite : RewriteRule} {view : View rewrite} {bindings : Bindings}
    (contract : EchoContract relations language view bindings) : Prop :=
  contract.outcome = true

/-- The boolean projection agrees with the independently declared relation
row at the concrete substituted arguments. -/
theorem holds_iff_meaning {relations : RelationEnv} {language : LanguageDef}
    {rewrite : RewriteRule} {view : View rewrite} {bindings : Bindings}
    (contract : EchoContract relations language view bindings) :
    contract.Holds ↔ Meaning relations bindings view := by
  rw [Meaning, contract.bound.applied_eq, contract.echo]
  cases outcomeEq : contract.outcome <;> simp [Holds, outcomeEq]

/-- Exact executable boundary: an enabled fully bound echo query preserves
the binding environment once; a disabled query produces no continuation. -/
theorem relationQueryStep_eq
    {relations : RelationEnv} {language : LanguageDef}
    {rewrite : RewriteRule} {view : View rewrite} {bindings : Bindings}
    (contract : EchoContract relations language view bindings) :
    relationQueryStep relations language bindings view.relation
        view.arguments =
      if contract.outcome then [bindings] else [] := by
  rw [contract.bound.arguments_eq]
  exact relationQueryStep_boundVariables_echo_eq contract.bound.aligned
    contract.noBuiltin contract.echo

/-- The same exactness theorem through the public premise evaluator. -/
theorem premiseStepWithEnv_eq
    {relations : RelationEnv} {language : LanguageDef}
    {rewrite : RewriteRule} {view : View rewrite} {bindings : Bindings}
    (contract : EchoContract relations language view bindings) :
    premiseStepWithEnv relations language bindings view.encode =
      if contract.outcome then [bindings] else [] := by
  simpa [View.encode, premiseStepWithEnv] using contract.relationQueryStep_eq

private theorem premiseAt_relationQuery_iff
    {base : BasePremiseEvaluator} {language : LanguageDef} {fuel : Nat}
    {bindings final : Bindings} {relation : String}
    {arguments : List Pattern} :
    PremiseAt base language fuel bindings
        (.relationQuery relation arguments) final ↔
      final ∈ base language bindings (.relationQuery relation arguments) := by
  constructor
  · intro evidence
    cases evidence with
    | relationQuery member => exact member
  · exact PremiseAt.relationQuery

/-- Exact relational boundary for one guarded query.  Besides its independent
truth, the theorem records that a covered query cannot change bindings. -/
theorem premiseAt_iff
    {relations : RelationEnv} {language : LanguageDef} {fuel : Nat}
    {rewrite : RewriteRule} {view : View rewrite}
    {bindings final : Bindings}
    (contract : EchoContract relations language view bindings) :
    PremiseAt (engineBasePremises relations) language fuel bindings
        view.encode final ↔
      contract.Holds ∧ final = bindings := by
  change PremiseAt (engineBasePremises relations) language fuel bindings
      (.relationQuery view.relation view.arguments) final ↔ _
  rw [premiseAt_relationQuery_iff]
  change final ∈
      premiseStepWithEnv relations language bindings view.encode ↔ _
  rw [contract.premiseStepWithEnv_eq]
  cases outcomeEq : contract.outcome <;> simp [Holds, outcomeEq]

/-- The generated-independent relation meaning is exactly one ordinary
MeTTaIL premise witness at any contextual fuel. -/
theorem meaning_iff_premiseAt
    {relations : RelationEnv} {language : LanguageDef} {fuel : Nat}
    {rewrite : RewriteRule} {view : View rewrite} {bindings : Bindings}
    (contract : EchoContract relations language view bindings) :
    Meaning relations bindings view ↔
      PremiseAt (engineBasePremises relations) language fuel bindings
        view.encode bindings := by
  rw [← contract.holds_iff_meaning]
  simpa using (contract.premiseAt_iff (fuel := fuel) (final := bindings)).symm

end EchoContract

/-- Ordered exact echo contracts for an authored view row.  This dependent
list retains repeated premise occurrences and their authored order. -/
inductive ContractRow (relations : RelationEnv) (language : LanguageDef)
    {rewrite : RewriteRule} (bindings : Bindings) :
    List (View rewrite) → Type where
  | nil : ContractRow relations language bindings []
  | cons {head : View rewrite} {tail : List (View rewrite)}
      (headContract : EchoContract relations language head bindings)
      (tailContracts : ContractRow relations language bindings tail) :
      ContractRow relations language bindings (head :: tail)

namespace ContractRow

/-- Independent ordered meaning of a source-premise view row.  The inductive
shape retains duplicate premise occurrences instead of collapsing the row to
a set. -/
inductive Meanings (relations : RelationEnv) {rewrite : RewriteRule}
    (bindings : Bindings) : List (View rewrite) → Prop where
  | nil : Meanings relations bindings []
  | cons {head : View rewrite} {tail : List (View rewrite)} :
      Meaning relations bindings head → Meanings relations bindings tail →
        Meanings relations bindings (head :: tail)

/-- The inductive ordered-row interpretation is equivalent to checking every
retained occurrence by its exact finite position.  The `Fin` index prevents
duplicate premises from collapsing into set membership. -/
theorem meanings_iff_forall_get
    {relations : RelationEnv} {rewrite : RewriteRule}
    {bindings : Bindings} {views : List (View rewrite)} :
    Meanings relations bindings views ↔
      ∀ index : Fin views.length,
        Meaning relations bindings (views.get index) := by
  induction views with
  | nil =>
      constructor
      · intro _ index
        exact Fin.elim0 index
      · intro _
        exact .nil
  | cons head tail inductionHypothesis =>
      constructor
      · intro meanings
        cases meanings with
        | cons headMeaning tailMeanings =>
            intro index
            refine Fin.cases headMeaning ?_ index
            intro tailIndex
            exact inductionHypothesis.mp tailMeanings tailIndex
      · intro pointwise
        apply Meanings.cons
        · exact pointwise ⟨0, by simp⟩
        · apply inductionHypothesis.mpr
          intro index
          exact pointwise index.succ

/-- Every exact contract in the ordered row is enabled. -/
inductive AllHold
    {relations : RelationEnv} {language : LanguageDef}
    {rewrite : RewriteRule} {bindings : Bindings} :
    {views : List (View rewrite)} →
      ContractRow relations language bindings views → Prop where
  | nil : AllHold (.nil : ContractRow relations language bindings [])
  | cons {head : View rewrite} {tail : List (View rewrite)}
      {headContract : EchoContract relations language head bindings}
      {tailContracts : ContractRow relations language bindings tail} :
      headContract.Holds → AllHold tailContracts →
        AllHold (.cons headContract tailContracts)

/-- Contract booleans are only an executable view: a complete ordered row
holds exactly when the independently interpreted relation claims hold. -/
theorem allHold_iff_meanings
    {relations : RelationEnv} {language : LanguageDef}
    {rewrite : RewriteRule} {bindings : Bindings}
    {views : List (View rewrite)}
    (contracts : ContractRow relations language bindings views) :
    contracts.AllHold ↔ Meanings relations bindings views := by
  induction contracts with
  | nil =>
      constructor
      · intro _
        exact .nil
      · intro _
        exact .nil
  | @cons head tail headContract tailContracts inductionHypothesis =>
      constructor
      · intro holds
        cases holds with
        | cons headHolds tailHolds =>
            exact .cons
              (headContract.holds_iff_meaning.mp headHolds)
              (inductionHypothesis.mp tailHolds)
      · intro meanings
        cases meanings with
        | cons headMeaning tailMeanings =>
            exact .cons
              (headContract.holds_iff_meaning.mpr headMeaning)
              (inductionHypothesis.mpr tailMeanings)

/-- Exact ordered relation between independent echo contracts and the
ordinary proof-relevant `PremisesAt` semantics.  Successful covered premises
preserve the environment, and no disabled premise or alternative final
environment can be invented. -/
theorem premisesAt_iff
    {relations : RelationEnv} {language : LanguageDef} {fuel : Nat}
    {rewrite : RewriteRule} {bindings final : Bindings}
    {views : List (View rewrite)}
    (contracts : ContractRow relations language bindings views) :
    PremisesAt (engineBasePremises relations) language fuel bindings
        (views.map View.encode) final ↔
      contracts.AllHold ∧ final = bindings := by
  induction contracts generalizing final with
  | nil =>
      constructor
      · intro evidence
        cases evidence
        exact ⟨AllHold.nil, rfl⟩
      · rintro ⟨allHold, finalEq⟩
        cases allHold
        cases finalEq
        exact PremisesAt.nil bindings
  | @cons head tail headContract tailContracts inductionHypothesis =>
      constructor
      · intro evidence
        cases evidence with
        | cons headEvidence tailEvidence =>
            obtain ⟨headHolds, middleEq⟩ :=
              headContract.premiseAt_iff.mp headEvidence
            cases middleEq
            obtain ⟨tailHolds, finalEq⟩ :=
              inductionHypothesis.mp tailEvidence
            exact ⟨AllHold.cons headHolds tailHolds, finalEq⟩
      · rintro ⟨allHold, finalEq⟩
        cases allHold with
        | cons headHolds tailHolds =>
            cases finalEq
            exact PremisesAt.cons
              (headContract.premiseAt_iff.mpr ⟨headHolds, rfl⟩)
              (inductionHypothesis.mpr ⟨tailHolds, rfl⟩)

/-- Crown theorem for the covered fragment: the independently meaningful
ordered claim row is equivalent to the ordinary authored-premise semantics,
including exact final bindings. -/
theorem premisesAt_iff_meanings
    {relations : RelationEnv} {language : LanguageDef} {fuel : Nat}
    {rewrite : RewriteRule} {bindings final : Bindings}
    {views : List (View rewrite)}
    (contracts : ContractRow relations language bindings views) :
    PremisesAt (engineBasePremises relations) language fuel bindings
        (views.map View.encode) final ↔
      Meanings relations bindings views ∧ final = bindings := by
  rw [contracts.premisesAt_iff, contracts.allHold_iff_meanings]

end ContractRow

/-! ## Discriminating canaries -/

namespace Canary

private def duplicateRelation : String :=
  "bound-evidence:duplicate"

private def secondRelation : String :=
  "bound-evidence:second"

private def rewrite : RewriteRule where
  name := "bound-evidence-rewrite"
  typeContext := [("x", .base "X"), ("y", .base "Y")]
  premises :=
    [ .relationQuery duplicateRelation [.fvar "x", .fvar "x"]
    , .relationQuery secondRelation [.fvar "y"] ]
  left := .apply "bound-evidence-pair" [.fvar "x", .fvar "y"]
  right := .fvar "x"

private def duplicateView : View rewrite where
  relation := duplicateRelation
  arguments := [.fvar "x", .fvar "x"]
  argumentTypes := [.base "X", .base "X"]

private def secondView : View rewrite where
  relation := secondRelation
  arguments := [.fvar "y"]
  argumentTypes := [.base "Y"]

private def xValue : Pattern :=
  .apply "bound-evidence:x" []

private def yValue : Pattern :=
  .apply "bound-evidence:y" []

private def bindings : Bindings :=
  [("x", xValue), ("y", yValue)]

private def language : LanguageDef :=
  LanguageDef.empty "bound-evidence-language"

private def allowRelations : RelationEnv where
  tuples relation arguments :=
    if relation = duplicateRelation ∨ relation = secondRelation then
      [arguments]
    else
      []

private def duplicateBound : BoundArguments duplicateView bindings where
  names := ["x", "x"]
  values := [xValue, xValue]
  arguments_eq := rfl
  aligned := by
    simp [bindings, Bindings.lookup, xValue, yValue]

private def secondBound : BoundArguments secondView bindings where
  names := ["y"]
  values := [yValue]
  arguments_eq := rfl
  aligned := by
    simp [bindings, Bindings.lookup, xValue, yValue]

private theorem duplicateTyped : duplicateView.WellTyped := by
  simp [duplicateView, View.WellTyped, argumentType?, rewrite,
    Pattern.freeFvarNames, FreeTypeContext.ofList]

private theorem secondTyped : secondView.WellTyped := by
  simp [secondView, View.WellTyped, argumentType?, rewrite,
    Pattern.freeFvarNames, FreeTypeContext.ofList]

private def duplicateAllowed :
    EchoContract allowRelations language duplicateView bindings where
  typed := duplicateTyped
  bound := duplicateBound
  outcome := true
  noBuiltin := by
    simp [builtinRelationTuples, duplicateView, duplicateBound,
      duplicateRelation]
  echo := by
    simp [allowRelations, duplicateView, duplicateBound,
      duplicateRelation, secondRelation]

private def secondAllowed :
    EchoContract allowRelations language secondView bindings where
  typed := secondTyped
  bound := secondBound
  outcome := true
  noBuiltin := by
    simp [builtinRelationTuples, secondView, secondBound, secondRelation]
  echo := by
    simp [allowRelations, secondView, secondBound, duplicateRelation,
      secondRelation]

private def allowedRow :
    ContractRow allowRelations language bindings
      [duplicateView, secondView] :=
  .cons duplicateAllowed (.cons secondAllowed .nil)

private theorem allowedRow_allHold : allowedRow.AllHold := by
  exact .cons rfl (.cons rfl .nil)

/-- Positive control: two enabled queries, including a repeated argument,
produce exact ordered `PremisesAt` evidence and preserve the environment. -/
theorem enabled_ordered_queries_have_exact_premisesAt (fuel : Nat) :
    PremisesAt (engineBasePremises allowRelations) language fuel bindings
      [duplicateView.encode, secondView.encode] bindings := by
  exact (allowedRow.premisesAt_iff).mpr ⟨allowedRow_allHold, rfl⟩

/-- The independent meaning reads the actual external relation row; duplicate
arguments remain duplicated in that query. -/
theorem duplicate_query_has_independent_meaning :
    Meaning allowRelations bindings duplicateView := by
  exact duplicateAllowed.holds_iff_meaning.mp rfl

private def duplicateDenied :
    EchoContract RelationEnv.empty language duplicateView bindings where
  typed := duplicateTyped
  bound := duplicateBound
  outcome := false
  noBuiltin := by
    simp [builtinRelationTuples, duplicateView, duplicateBound,
      duplicateRelation]
  echo := by
    simp [RelationEnv.empty]

private def deniedRow :
    ContractRow RelationEnv.empty language bindings [duplicateView] :=
  .cons duplicateDenied .nil

/-- Negative control: a well-typed, fully bound claim with no external row
cannot manufacture premise evidence. -/
theorem disabled_query_has_no_premisesAt (fuel : Nat) (final : Bindings) :
    ¬ PremisesAt (engineBasePremises RelationEnv.empty) language fuel bindings
      [duplicateView.encode] final := by
  intro evidence
  obtain ⟨allHold, _finalEq⟩ := deniedRow.premisesAt_iff.mp evidence
  cases allHold with
  | cons headHolds _ =>
      simp [EchoContract.Holds, duplicateDenied] at headHolds

/-- The exact encoded premise row retains authored order and duplicate
argument occurrences. -/
theorem encoded_row_preserves_order_and_duplicates :
    [duplicateView, secondView].map View.encode = rewrite.premises := by
  rfl

end Canary

#print axioms BoundArguments.applied_eq
#print axioms BoundArguments.match_eq
#print axioms EchoContract.holds_iff_meaning
#print axioms EchoContract.relationQueryStep_eq
#print axioms EchoContract.premiseStepWithEnv_eq
#print axioms EchoContract.premiseAt_iff
#print axioms EchoContract.meaning_iff_premiseAt
#print axioms ContractRow.allHold_iff_meanings
#print axioms ContractRow.premisesAt_iff
#print axioms ContractRow.premisesAt_iff_meanings
#print axioms Canary.enabled_ordered_queries_have_exact_premisesAt
#print axioms Canary.duplicate_query_has_independent_meaning
#print axioms Canary.disabled_query_has_no_premisesAt
#print axioms Canary.encoded_row_preserves_order_and_duplicates

end Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationEvidence
