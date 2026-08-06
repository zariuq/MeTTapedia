import Mettapedia.Languages.Metamath.InferenceSideConditions

/-!
# Metamath prefix inference projection

This file projects a live, pre-insertion `mm-lean4` database prefix into the
generic proof-relevant inference checker.  Active hypotheses become leaf
rules, and every stored prior assertion becomes an ordered rule schema.  The
assertion schemas expose substitution, essential-hypothesis checking, and
disjoint-variable checking as ordinary side-judgment premises.

Projection is fail-closed.  It rejects malformed runtime objects, unsupported
formula shapes, duplicate floating-variable bindings, and source strings that
would collide with the generated inference vocabulary.  The resulting raw
presentation is still passed through `validateV2?`; this module makes no claim
yet that a projected rule application is equivalent to `DB.stepNormal`.

`RuntimeDB` itself carries no history proving that it was captured before a
particular target assertion was inserted.  `projectForFreshTarget?` adds the
executable absence gate needed by target-facing callers, but parser-prefix
provenance remains a separate theorem obligation.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceEncoding.Builder
open Mettapedia.Languages.Metamath.InferenceSideConditions

/-! ## Projected prefix views -/

def provesHead : String := "$mm.j.proves"

def proves (formula : Pattern) : Pattern :=
  .apply provesHead [formula]

def provesDecl : JudgmentDecl :=
  { head := provesHead, arity := 1 }

/-- A mandatory hypothesis after checking its exact runtime shape. -/
inductive HypothesisView where
  | floating (label typecode variableName : String)
  | essential (label : String) (formula : ConstantHeadedFormula)

namespace HypothesisView

def label : HypothesisView → String
  | .floating label _ _ | .essential label _ => label

def formula : HypothesisView → ConstantHeadedFormula
  | .floating _ typecode variableName =>
      ⟨typecode, [.var variableName]⟩
  | .essential _ formula => formula

def typecode (hypothesis : HypothesisView) : String :=
  hypothesis.formula.typecode

def floatingVariable? : HypothesisView → Option String
  | .floating _ _ variableName => some variableName
  | .essential _ _ => none

end HypothesisView

/-- One prior assertion together with its resolved mandatory hypotheses. -/
structure AssertionView where
  label : String
  formula : ConstantHeadedFormula
  frame : RuntimeFrame
  hypotheses : List HypothesisView

/-- Inspectable finite snapshot used to generate one presentation. -/
structure PrefixProjection where
  declaredConstants : List String
  declaredVariables : List String
  callerFrame : RuntimeFrame
  activeHypotheses : List HypothesisView
  assertions : List AssertionView

/-- Canonical label ordering with a library permutation theorem.  The
projection therefore retains efficient sorting without an unproved
entry-preservation boundary. -/
def sortObjectEntries
    (entries : List (String × Metamath.Verify.Object)) :
    List (String × Metamath.Verify.Object) :=
  entries.mergeSort fun left right => left.1 ≤ right.1

theorem mem_sortObjectEntries_iff
    (target : String × Metamath.Verify.Object)
    (entries : List (String × Metamath.Verify.Object)) :
    target ∈ sortObjectEntries entries ↔ target ∈ entries := by
  exact (List.mergeSort_perm entries _).mem_iff

/-- Runtime objects in a deterministic label order.  No chronological claim is
made: every entry in an input pre-insertion DB is already a prior entry. -/
def objectEntries (db : RuntimeDB) :
    List (String × Metamath.Verify.Object) :=
  sortObjectEntries db.objects.toList

theorem mem_objectEntries_iff
    (db : RuntimeDB) (entry : String × Metamath.Verify.Object) :
    entry ∈ objectEntries db ↔ entry ∈ db.objects.toList := by
  exact mem_sortObjectEntries_iff entry db.objects.toList

/-- Metamath's constant/variable partition is global: the runtime object map
has one object kind per math-symbol label.  These deterministic lists retain
that partition in the inspectable projection artifact. -/
def declaredConstantNames
    (entries : List (String × Metamath.Verify.Object)) : List String :=
  entries.filterMap fun
    | (_, .const name) => some name
    | _ => none

def declaredVariableNames
    (entries : List (String × Metamath.Verify.Object)) : List String :=
  entries.filterMap fun
    | (_, .var name) => some name
    | _ => none

def objectEmbeddedNameMatches : String → Metamath.Verify.Object → Bool
  | label, .const name => name == label
  | label, .var name => name == label
  | label, .hyp _ _ name => name == label
  | label, .assert _ _ name => name == label

def projectHypothesis? (db : RuntimeDB) (label : String) :
    Option HypothesisView := do
  let object ← db.find? label
  match object with
  | .hyp essential runtimeFormula embeddedLabel =>
      guard (embeddedLabel == label)
      let formula ← ConstantHeadedFormula.ofRuntime? runtimeFormula
      if essential then
        some (.essential label formula)
      else
        match formula.body with
        | [.var variableName] =>
            some (.floating label formula.typecode variableName)
        | _ => none
  | _ => none

def projectHypotheses? (db : RuntimeDB) (labels : List String) :
    Option (List HypothesisView) :=
  labels.mapM (projectHypothesis? db)

def floatingVariableNames (hypotheses : List HypothesisView) : List String :=
  hypotheses.filterMap HypothesisView.floatingVariable?

def hasUniqueLabels (hypotheses : List HypothesisView) : Bool :=
  let labels := hypotheses.map HypothesisView.label
  labels.eraseDups.length == labels.length

/-- The syntactically generated finite substitution has one binding for each
floating mandatory hypothesis, so its relational lookup is unambiguous only
under this gate. -/
def hasUniqueFloatingVariables (hypotheses : List HypothesisView) : Bool :=
  let names := floatingVariableNames hypotheses
  names.eraseDups.length == names.length

def formulaVariablesKnown (floatingVariables : List String)
    (formula : ConstantHeadedFormula) : Bool :=
  formula.body.all fun symbol =>
    match symbol with
    | .const _ => true
    | .var variableName => floatingVariables.contains variableName

/-- Exact body-symbol discipline used by the runtime frame check: variables
must have frame floats, while a constant name must not be reclassified by a
same-named floating variable. -/
def symbolRespectsFrame (floatingVariables : List String) :
    RuntimeSym → Bool
  | .const constantName => !(floatingVariables.contains constantName)
  | .var variableName => floatingVariables.contains variableName

def formulaSymbolsRespectFrame (floatingVariables : List String)
    (formula : ConstantHeadedFormula) : Bool :=
  formula.body.all (symbolRespectsFrame floatingVariables)

def taggedVariableNames : List RuntimeSym → List String
  | [] => []
  | .const _ :: symbols => taggedVariableNames symbols
  | .var variableName :: symbols =>
      variableName :: taggedVariableNames symbols

private theorem filterByFrame_eq_taggedVariableNames
    (floatingVariables : List String) (body : List RuntimeSym)
    (hrespect :
      body.all (symbolRespectsFrame floatingVariables) = true) :
    body.filterMap (fun symbol =>
        if symbol.value ∈ floatingVariables then some symbol.value else none) =
      taggedVariableNames body := by
  induction body with
  | nil => rfl
  | cons symbol body ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hrespect
      cases symbol with
      | const constantName =>
          simp only [symbolRespectsFrame] at hrespect
          have hcfalse :
              floatingVariables.contains constantName = false := by
            exact (Bool.not_eq_true' _).mp hrespect.1
          have hcnot : constantName ∉ floatingVariables := by
            intro hmem
            have hctrue : floatingVariables.contains constantName = true :=
              List.contains_iff_mem.mpr hmem
            rw [hcfalse] at hctrue
            contradiction
          rw [List.filterMap_cons]
          simp only [Metamath.Verify.Sym.value, if_neg hcnot,
            taggedVariableNames]
          exact ih hrespect.2
      | var variableName =>
          simp only [symbolRespectsFrame] at hrespect
          have hmem : variableName ∈ floatingVariables :=
            List.contains_iff_mem.mp hrespect.1
          rw [List.filterMap_cons]
          simp only [Metamath.Verify.Sym.value, if_pos hmem,
            taggedVariableNames]
          exact congrArg (List.cons variableName) (ih hrespect.2)

/-- The executable frame gate is exactly what makes runtime name-filtering
agree with the generated calculus's explicit symbol-tag traversal. -/
theorem varsIn_toRuntime_eq_taggedVariableNames
    (floatingVariables : List String) (formula : ConstantHeadedFormula)
    (hrespect :
      formulaSymbolsRespectFrame floatingVariables formula = true) :
    formula.toRuntime.varsIn floatingVariables =
      taggedVariableNames formula.body := by
  simp [ConstantHeadedFormula.toRuntime,
    Metamath.Verify.Formula.varsIn,
    filterByFrame_eq_taggedVariableNames floatingVariables formula.body
      hrespect]

/-- Global source-tag discipline.  The runtime DV implementation classifies a
symbol by membership in the caller variable list, whereas the generated
`Vars` judgment observes the explicit `.const`/`.var` tag.  Requiring every
encoded symbol to agree with the database declarations prevents those two
classifications from diverging on fabricated database snapshots. -/
def formulaSymbolsRespectDeclarations (declaredConstants declaredVariables :
    List String) (formula : ConstantHeadedFormula) : Bool :=
  declaredConstants.contains formula.typecode &&
    formula.body.all fun symbol =>
      match symbol with
      | .const constantName => declaredConstants.contains constantName
      | .var variableName => declaredVariables.contains variableName

/-- Runtime `checkHyp` constructs its substitution from left to right.  An
essential hypothesis may therefore mention only floating variables introduced
by earlier hypotheses, even though the final assertion substitution also
contains later bindings. -/
def hypothesesPrefixScopedFrom : List String → List HypothesisView → Bool
  | _, [] => true
  | available, .floating _ _ variableName :: hypotheses =>
      hypothesesPrefixScopedFrom (variableName :: available) hypotheses
  | available, .essential _ formula :: hypotheses =>
      formulaVariablesKnown available formula &&
        hypothesesPrefixScopedFrom available hypotheses

def hypothesesPrefixScoped (hypotheses : List HypothesisView) : Bool :=
  hypothesesPrefixScopedFrom [] hypotheses

/-- Runtime disjointness normalizes queried pairs before stored membership,
whereas the side rules accept either stored orientation.  Requiring strict
canonical order therefore enforces both orientation agreement and no-self. -/
def frameDVValid (frame : RuntimeFrame)
    (floatingVariables : List String) : Bool :=
  let pairs := frame.dj.toList
  pairs.all fun pair =>
    decide (pair.1 < pair.2) &&
      floatingVariables.contains pair.1 &&
      floatingVariables.contains pair.2

def frameProjectionValid (frame : RuntimeFrame)
    (hypotheses : List HypothesisView) : Bool :=
  let floatingVariables := floatingVariableNames hypotheses
  hasUniqueLabels hypotheses &&
    hasUniqueFloatingVariables hypotheses &&
    hypothesesPrefixScoped hypotheses &&
    (hypotheses.map HypothesisView.label == frame.hyps.toList) &&
    hypotheses.all
      (formulaSymbolsRespectFrame floatingVariables ∘ HypothesisView.formula) &&
    frameDVValid frame floatingVariables

def projectAssertion? (db : RuntimeDB) (label : String)
    (runtimeFormula : RuntimeFormula) (frame : RuntimeFrame)
    (embeddedLabel : String) : Option AssertionView := do
  guard (embeddedLabel == label)
  let formula ← ConstantHeadedFormula.ofRuntime? runtimeFormula
  let hypotheses ← projectHypotheses? db frame.hyps.toList
  guard (frameProjectionValid frame hypotheses)
  guard (formulaSymbolsRespectFrame (floatingVariableNames hypotheses) formula)
  some { label, formula, frame, hypotheses }

def projectAssertionsFromEntries? (db : RuntimeDB) :
    List (String × Metamath.Verify.Object) → Option (List AssertionView)
  | [] => some []
  | (label, .assert runtimeFormula frame embeddedLabel) :: entries => do
      let assertion ←
        projectAssertion? db label runtimeFormula frame embeddedLabel
      let assertions ← projectAssertionsFromEntries? db entries
      some (assertion :: assertions)
  | _ :: entries => projectAssertionsFromEntries? db entries

def sourceRuleLabels (projection : PrefixProjection) : List String :=
  projection.activeHypotheses.map HypothesisView.label ++
    projection.assertions.map AssertionView.label

def sourceRuleLabelsValid (labels : List String) : Bool :=
  labels.all (fun label =>
      label != "" && !(label.startsWith reservedRulePrefix)) &&
    labels.eraseDups.length == labels.length

/-- Recheck the semantic invariants of an inspectable assertion snapshot. -/
def assertionViewValid (declaredConstants declaredVariables : List String)
    (assertion : AssertionView) : Bool :=
  frameProjectionValid assertion.frame assertion.hypotheses &&
    formulaSymbolsRespectFrame
      (floatingVariableNames assertion.hypotheses) assertion.formula &&
    assertion.hypotheses.all
      (formulaSymbolsRespectDeclarations declaredConstants declaredVariables ∘
        HypothesisView.formula) &&
    formulaSymbolsRespectDeclarations declaredConstants declaredVariables
      assertion.formula

/-- Public snapshots are inspectable data rather than proof-carrying subtypes,
so presentation generation repeats their structural gates. -/
def prefixProjectionValid (projection : PrefixProjection) : Bool :=
  projection.declaredConstants.eraseDups.length ==
      projection.declaredConstants.length &&
    projection.declaredVariables.eraseDups.length ==
      projection.declaredVariables.length &&
    projection.declaredConstants.all (fun constantName =>
      !(projection.declaredVariables.contains constantName)) &&
    frameProjectionValid projection.callerFrame projection.activeHypotheses &&
    projection.activeHypotheses.all
      (formulaSymbolsRespectDeclarations projection.declaredConstants
        projection.declaredVariables ∘ HypothesisView.formula) &&
    projection.assertions.all
      (assertionViewValid projection.declaredConstants
        projection.declaredVariables) &&
    sourceRuleLabelsValid (sourceRuleLabels projection)

/-- Proof-facing caller frame for a live parser prefix.  The raw frame keeps
all active `$d` pairs for scope restoration, including legal pairs declared
before their `$f` hypotheses.  Only pairs whose endpoints currently have
floating hypotheses can participate in proof substitution and therefore
belong in the checker projection. -/
def proofFacingCallerFrame (db : RuntimeDB) : RuntimeFrame :=
  let floatingVariables := db.frameFloatVars db.frame
  { dj := db.frame.dj.filter fun pair =>
      floatingVariables.contains pair.1 &&
        floatingVariables.contains pair.2
    hyps := db.frame.hyps }

/-- Proof-facing DV pairs are selected from, never added to, the live runtime
frame. -/
theorem proofFacingCallerFrame_dj_subset (db : RuntimeDB) :
    ∀ pair ∈ (proofFacingCallerFrame db).dj.toList,
      pair ∈ db.frame.dj.toList := by
  intro pair hpair
  simp only [proofFacingCallerFrame, Array.toList_filter,
    List.mem_filter] at hpair
  exact hpair.1

/-- Canonical orientation is required for every raw caller `$d` pair, including
pairs that are not yet proof-facing because one of their `$f` declarations is
not active.  Keeping this as a separate projection gate preserves the runtime
checker bridge without incorrectly exposing those pairs to source proofs. -/
def rawCallerDVStrict (db : RuntimeDB) : Bool :=
  db.frame.dj.toList.all fun pair => decide (pair.1 < pair.2)

/-- Resolve a finite pre-insertion database into the exact objects consumed by
the generated presentation. -/
def projectPrefix? (db : RuntimeDB) : Option PrefixProjection := do
  guard db.error?.isNone
  guard db.wellFormed?
  guard db.assertDvVarsInFrame?
  guard (rawCallerDVStrict db)
  let entries := objectEntries db
  guard (entries.all fun entry =>
    objectEmbeddedNameMatches entry.1 entry.2)
  let declaredConstants := declaredConstantNames entries
  let declaredVariables := declaredVariableNames entries
  guard (declaredConstants.all fun constantName =>
    !(declaredVariables.contains constantName))
  let activeHypotheses ← projectHypotheses? db db.frame.hyps.toList
  let callerFrame := proofFacingCallerFrame db
  guard (frameProjectionValid callerFrame activeHypotheses)
  let assertions ← projectAssertionsFromEntries? db entries
  let projection :=
    { declaredConstants, declaredVariables, callerFrame,
      activeHypotheses, assertions }
  guard (prefixProjectionValid projection)
  some projection

/-! ## Exact source vocabulary -/

def stringsOfFormula (formula : ConstantHeadedFormula) : List String :=
  formula.typecode :: formula.body.map Metamath.Verify.Sym.value

def stringsOfFrame (frame : RuntimeFrame) : List String :=
  frame.dj.toList.flatMap (fun pair => [pair.1, pair.2]) ++
    frame.hyps.toList

def stringsOfHypothesis (hypothesis : HypothesisView) : List String :=
  hypothesis.label :: stringsOfFormula hypothesis.formula

def stringsOfAssertion (assertion : AssertionView) : List String :=
  assertion.label ::
    (stringsOfFormula assertion.formula ++
      stringsOfFrame assertion.frame ++
      assertion.hypotheses.flatMap stringsOfHypothesis)

def sortStrings (values : List String) : List String :=
  values.mergeSort fun left right => left < right

theorem mem_sortStrings_iff (target : String) (values : List String) :
    target ∈ sortStrings values ↔ target ∈ values := by
  exact (List.mergeSort_perm values _).mem_iff

/-- Deduplicated source strings occurring in projected rule identifiers or in
an encoded formula, frame, or substitution binding. -/
def sourceVocabulary (projection : PrefixProjection) : List String :=
  (stringsOfFrame projection.callerFrame ++
      projection.activeHypotheses.flatMap stringsOfHypothesis ++
      projection.assertions.flatMap stringsOfAssertion)
    |>.eraseDups
    |> sortStrings

def reservedProjectionHeads : List String :=
  dataTypeName :: provesHead ::
    (reservedInternalHeads ++
      [Pattern.zipHead, Pattern.mapHead, Pattern.evalHead])

def sourceVocabularyValid (sourceHeads : List String) : Bool :=
  sourceHeads.all (fun head =>
      head != "" &&
        !(head.startsWith reservedRulePrefix) &&
        !(reservedProjectionHeads.contains head)) &&
    sourceHeads.eraseDups.length == sourceHeads.length

/-- Extend only the term-constructor vocabulary; the side-condition language
and its carrier type remain unchanged. -/
def languageWithSourceVocabulary (sourceHeads : List String) : LanguageDef :=
  { dataLanguage with
    name := "metamath-inference-prefix"
    terms := dataLanguage.terms ++ sourceHeads.map nullaryDataConstructor }

/-! ## Generated source rules -/

private def ruleId (value : String) : RuleId := { value }
private def mv (name : String) : Pattern := .fvar name
private def formal (name : String) : String × Nat := (name, 0)

def hypothesisBodyFormalName (index : Nat) : String :=
  s!"H{index}Body"

def conclusionBodyFormalName : String := "ConclusionBody"

def activeHypothesisRule (hypothesis : HypothesisView) : RuleSchema :=
  { id := ruleId hypothesis.label
    metavariables := []
    premises := []
    conclusion := proves (encodeFormula hypothesis.formula) }

def assertionHypothesisFormalsFrom : Nat → List HypothesisView →
    List (String × Nat)
  | _, [] => []
  | index, _ :: hypotheses =>
      formal (hypothesisBodyFormalName index) ::
        assertionHypothesisFormalsFrom (index + 1) hypotheses

def assertionHypothesisProvesFrom : Nat → List HypothesisView → List Pattern
  | _, [] => []
  | index, hypothesis :: hypotheses =>
      proves
          (Builder.formula (encodeString hypothesis.typecode)
            (mv (hypothesisBodyFormalName index))) ::
        assertionHypothesisProvesFrom (index + 1) hypotheses

def assertionBindingsFrom : Nat → List HypothesisView → List Pattern
  | _, [] => []
  | index, .floating _ typecode variableName :: hypotheses =>
      Builder.binding (encodeString variableName)
          (Builder.formula (encodeString typecode)
            (mv (hypothesisBodyFormalName index))) ::
        assertionBindingsFrom (index + 1) hypotheses
  | index, .essential _ _ :: hypotheses =>
      assertionBindingsFrom (index + 1) hypotheses

def assertionSubstitution (assertion : AssertionView) : Pattern :=
  Builder.substitution
    (encodeListWith id (assertionBindingsFrom 0 assertion.hypotheses))

def assertionEssentialChecksFrom (substitution : Pattern) :
    Nat → List HypothesisView → List Pattern
  | _, [] => []
  | index, .floating _ _ _ :: hypotheses =>
      assertionEssentialChecksFrom substitution (index + 1) hypotheses
  | index, .essential _ formula :: hypotheses =>
      applySubst substitution (encodeFormula formula)
          (Builder.formula (encodeString formula.typecode)
            (mv (hypothesisBodyFormalName index))) ::
        assertionEssentialChecksFrom substitution (index + 1) hypotheses

def assertionRule (callerFrame : RuntimeFrame)
    (assertion : AssertionView) : RuleSchema :=
  let substitution := assertionSubstitution assertion
  let resultFormula :=
    Builder.formula (encodeString assertion.formula.typecode)
      (mv conclusionBodyFormalName)
  { id := ruleId assertion.label
    metavariables :=
      assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
        [formal conclusionBodyFormalName]
    premises :=
      assertionHypothesisProvesFrom 0 assertion.hypotheses ++
        assertionEssentialChecksFrom substitution 0 assertion.hypotheses ++
        [ dvOK substitution (encodeFrame callerFrame)
            (encodeFrame assertion.frame)
        , applySubst substitution (encodeFormula assertion.formula)
            resultFormula ]
    conclusion := proves resultFormula }

def generatedSourceRules (projection : PrefixProjection) : List RuleSchema :=
  projection.activeHypotheses.map activeHypothesisRule ++
    projection.assertions.map (assertionRule projection.callerFrame)

/-- Any validated presentation with the projected rule-table shape retains
the complete side-condition proof calculus.  The generic transport theorem
then reuses side derivations with their exact raw proof trees. -/
theorem validatedSidePresentation_refines_of_generated_rules
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hrules :
      target.1.rules = sideRules ++ generatedSourceRules projection) :
    RuleLookupRefines validatedSidePresentation target := by
  apply RuleLookupRefines.of_rules_eq_append
      (generatedSourceRules projection)
  simpa [validatedSidePresentation, sidePresentation] using hrules

def presentationOfProjection? (projection : PrefixProjection) :
    Option Presentation := do
  guard (prefixProjectionValid projection)
  let vocabulary := sourceVocabulary projection
  guard (sourceVocabularyValid vocabulary)
  let sourceRules := generatedSourceRules projection
  guard (sourceRuleIdsDisjoint (sourceRules.map RuleSchema.id))
  some
    { language :=
        { languageWithSourceVocabulary vocabulary with
          judgments := judgmentDecls ++ [provesDecl]
          inferenceRules := sideRules ++ sourceRules } }

/-- A successful presentation projection exposes exactly the side calculus
followed by the generated source rules. -/
theorem rules_eq_of_presentationOfProjection?_eq_some
    (projection : PrefixProjection) (presentation : Presentation)
    (hprojection :
      presentationOfProjection? projection = some presentation) :
    presentation.rules = sideRules ++ generatedSourceRules projection := by
  unfold presentationOfProjection? at hprojection
  simp only [Option.bind_eq_bind] at hprojection
  rw [Option.bind_eq_some_iff] at hprojection
  rcases hprojection with ⟨_, _, hprojection⟩
  rw [Option.bind_eq_some_iff] at hprojection
  rcases hprojection with ⟨_, _, hprojection⟩
  rw [Option.bind_eq_some_iff] at hprojection
  rcases hprojection with ⟨_, _, hprojection⟩
  simp at hprojection
  cases hprojection
  rfl

/-- Every successfully validated projected presentation admits exact transport
of side-condition proofs from the standalone side presentation. -/
theorem validatedSidePresentation_refines_of_projection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1) :
    RuleLookupRefines validatedSidePresentation target :=
  validatedSidePresentation_refines_of_generated_rules projection target
    (rules_eq_of_presentationOfProjection?_eq_some
      projection target.1 hprojection)

/-- Raw general projection.  This is useful for inspecting the generated
schema before admission. -/
def rawPresentation? (db : RuntimeDB) : Option Presentation := do
  let projection ← projectPrefix? db
  presentationOfProjection? projection

/-- Proof-carrying V2-admitted projection. -/
def projectValidated? (db : RuntimeDB) : Option ValidatedPresentation := do
  let presentation ← rawPresentation? db
  presentation.validateV2?

/-- Target-facing projection rejects an already present (and hence potentially
self-usable) target label before admitting the prefix presentation.  Freshness
is an absence check, not a proof of chronological parser provenance. -/
def projectForFreshTarget? (db : RuntimeDB) (targetLabel : String) :
    Option ValidatedPresentation := do
  guard (sourceRuleLabelsValid [targetLabel])
  guard (db.find? targetLabel).isNone
  projectValidated? db

/-! ## Small executable boundaries -/

private def exampleFloatFormula : RuntimeFormula :=
  #[.const "wff", .var "ph"]

private def exampleAssertionFormula : RuntimeFormula :=
  #[.const "|-", .var "ph"]

private def exampleObjects :=
  (default : RuntimeDB).objects
    |>.insert "wff" (.const "wff")
    |>.insert "|-" (.const "|-")
    |>.insert "ph" (.var "ph")
    |>.insert "wph" (.hyp false exampleFloatFormula "wph")
    |>.insert "ax-ph" (.assert exampleAssertionFormula ⟨#[], #["wph"]⟩ "ax-ph")

def exampleDB : RuntimeDB :=
  { (default : RuntimeDB) with
    frame := ⟨#[], #["wph"]⟩
    objects := exampleObjects }

def reservedStringDB : RuntimeDB :=
  let objects :=
    (default : RuntimeDB).objects
      |>.insert "wff" (.const "wff")
      |>.insert "$mm.nil" (.var "$mm.nil")
      |>.insert "wph" (.hyp false #[.const "wff", .var "$mm.nil"] "wph")
  { (default : RuntimeDB) with
    frame := ⟨#[], #["wph"]⟩
    objects }

def variableHeadedHypothesisDB : RuntimeDB :=
  let objects :=
    (default : RuntimeDB).objects
      |>.insert "ph" (.var "ph")
      |>.insert "bad" (.hyp true #[.var "ph"] "bad")
  { (default : RuntimeDB) with
    frame := ⟨#[], #["bad"]⟩
    objects }

def essentialBeforeFloatDB : RuntimeDB :=
  let objects :=
    (default : RuntimeDB).objects
      |>.insert "wff" (.const "wff")
      |>.insert "|-" (.const "|-")
      |>.insert "ph" (.var "ph")
      |>.insert "ess" (.hyp true exampleAssertionFormula "ess")
      |>.insert "wph" (.hyp false exampleFloatFormula "wph")
  { (default : RuntimeDB) with
    frame := ⟨#[], #["ess", "wph"]⟩
    objects }

def constantFloatNameCollisionDB : RuntimeDB :=
  let floatX : RuntimeFormula := #[.const "wff", .var "x"]
  let constantXConclusion : RuntimeFormula := #[.const "|-", .const "x"]
  let assertionFrame : RuntimeFrame := ⟨#[], #["wx"]⟩
  let objects :=
    (default : RuntimeDB).objects
      |>.insert "wff" (.const "wff")
      |>.insert "|-" (.const "|-")
      |>.insert "x" (.var "x")
      |>.insert "wx" (.hyp false floatX "wx")
      |>.insert "ax-const-x"
        (.assert constantXConclusion assertionFrame "ax-const-x")
  { (default : RuntimeDB) with
    frame := assertionFrame
    objects }

/-- A database can satisfy the runtime's local shape checks while assigning
the same globally declared variable name a constant tag in an unrelated
assertion frame.  Projection must reject it before `Vars` can disagree with
runtime `Formula.varsIn`. -/
def globalTagIncoherentDB : RuntimeDB :=
  let floatX : RuntimeFormula := #[.const "wff", .var "x"]
  let constantXConclusion : RuntimeFormula := #[.const "|-", .const "x"]
  let callerFrame : RuntimeFrame := ⟨#[], #["wx"]⟩
  let assertionFrame : RuntimeFrame := ⟨#[], #[]⟩
  let objects :=
    (default : RuntimeDB).objects
      |>.insert "wff" (.const "wff")
      |>.insert "|-" (.const "|-")
      |>.insert "x" (.var "x")
      |>.insert "wx" (.hyp false floatX "wx")
      |>.insert "ax-const-x"
        (.assert constantXConclusion assertionFrame "ax-const-x")
  { (default : RuntimeDB) with
    frame := callerFrame
    objects }

def examplePrefixResult : Option PrefixProjection :=
  projectPrefix? exampleDB

def exampleValidatedResult : Option ValidatedPresentation :=
  projectValidated? exampleDB

def freshTargetResult : Option ValidatedPresentation :=
  projectForFreshTarget? exampleDB "th-ph"

def occupiedTargetResult : Option ValidatedPresentation :=
  projectForFreshTarget? exampleDB "ax-ph"

def reservedStringResult : Option Presentation :=
  rawPresentation? reservedStringDB

def variableHeadedResult : Option PrefixProjection :=
  projectPrefix? variableHeadedHypothesisDB

def essentialBeforeFloatResult : Option PrefixProjection :=
  projectPrefix? essentialBeforeFloatDB

def constantFloatNameCollisionResult : Option PrefixProjection :=
  projectPrefix? constantFloatNameCollisionDB

def globalTagIncoherentResult : Option PrefixProjection :=
  projectPrefix? globalTagIncoherentDB

#guard examplePrefixResult.isSome
#guard exampleValidatedResult.isSome
#guard freshTargetResult.isSome
#guard occupiedTargetResult.isNone
#guard reservedStringResult.isNone
#guard variableHeadedResult.isNone
#guard essentialBeforeFloatResult.isNone
#guard constantFloatNameCollisionResult.isNone
#guard globalTagIncoherentDB.wellFormed?
#guard globalTagIncoherentDB.assertDvVarsInFrame?
#guard globalTagIncoherentResult.isNone
#guard (projectValidated? globalTagIncoherentDB).isNone

theorem prefix_scope_accepts_float_before_essential :
    hypothesesPrefixScoped
      [ .floating "wph" "wff" "ph"
      , .essential "ess" ⟨"|-", [.var "ph"]⟩ ] = true := by
  decide

theorem proves_premises_preserve_hypothesis_appearance_order :
    assertionHypothesisProvesFrom 0
      [ .floating "wph" "wff" "ph"
      , .essential "ess" ⟨"|-", [.var "ph"]⟩ ] =
      [ proves
          (Builder.formula (encodeString "wff")
            (.fvar (hypothesisBodyFormalName 0)))
      , proves
          (Builder.formula (encodeString "|-")
            (.fvar (hypothesisBodyFormalName 1))) ] := by
  rfl

theorem prefix_scope_rejects_essential_before_float :
    hypothesesPrefixScoped
      [ .essential "ess" ⟨"|-", [.var "ph"]⟩
      , .floating "wph" "wff" "ph" ] = false := by
  decide

theorem frame_symbols_reject_constant_float_name_collision :
    formulaSymbolsRespectFrame ["x"] ⟨"|-", [.const "x"]⟩ = false := by
  decide

theorem declarations_reject_variable_tagged_as_constant :
    formulaSymbolsRespectDeclarations ["|-"] ["x"]
      ⟨"|-", [.const "x"]⟩ = false := by
  decide

/-- Repeating an already active `$d` pair is redundant but not malformed. -/
theorem frame_dv_gate_accepts_repeated_canonical_pairs :
    frameDVValid ⟨#[ ("x", "y"), ("x", "y") ], #[]⟩ ["x", "y"] = true := by
  decide

theorem frame_dv_gate_rejects_reversed_pair :
    frameDVValid ⟨#[("y", "x")], #[]⟩ ["x", "y"] = false := by
  decide

theorem frame_dv_gate_rejects_self_pair :
    frameDVValid ⟨#[("x", "x")], #[]⟩ ["x"] = false := by
  decide

theorem reserved_source_head_is_invalid :
    sourceVocabularyValid [nilHead] = false := by
  simp [sourceVocabularyValid, reservedProjectionHeads, reservedInternalHeads,
    reservedDataHeads, nilHead]

end Mettapedia.Languages.Metamath.InferenceProjection
