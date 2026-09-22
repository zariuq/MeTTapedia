import Mettapedia.OSLF.Framework.WMCalculusCombinedNamedFirstOrder
import Mettapedia.GSLT.LanguageDef.NamedFreeContext
import Mettapedia.GSLT.LanguageDef.BindingSignatureOpenReification

/-!
# Open first-order WM patterns and intrinsic certificates

The authored combined language has only one closed first-order generator,
`EvidenceZero`. Its State and Query handles instead live in a typed free
context. This module gives the converse to named erasure for that open
first-order fragment, without adding another constructor declaration list.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedOpenReification

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.Reification
open Mettapedia.GSLT.LanguageDef.BindingSyntax.OpenReification
open Mettapedia.GSLT.LanguageDef.NamedFreeContext
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
open Mettapedia.OSLF.Framework.PredFiniteSufficient
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
open Mettapedia.OSLF.Framework.WMCalculusCombinedNamedFirstOrder

set_option autoImplicit false

private abbrev CombinedLang : LanguageDef :=
  wmExtVertexLanguageDefGuarded combinedVertex

/-- Check that every free name actually used by one open pattern has a base
sort declared by the same authored language. Unused ambient assignments do
not affect admission. -/
def checkUsedFreeSortsDeclared (language : LanguageDef)
    (free : FreeTypeContext) (pattern : Pattern) : Bool :=
  pattern.freeFvarNames.all fun variableName =>
    match free variableName with
    | some (.base tag) => (language.types.map (·.name)).contains tag
    | _ => false

/-- The finite executable declaration check says exactly that every used
external handle is assigned an authored base sort. -/
theorem checkUsedFreeSortsDeclared_iff (language : LanguageDef)
    (free : FreeTypeContext) (pattern : Pattern) :
    checkUsedFreeSortsDeclared language free pattern = true ↔
      ∀ variableName, variableName ∈ pattern.freeFvarNames →
        ∃ tag, free variableName = some (.base tag) ∧
          tag ∈ language.types := by
  constructor
  · intro checked variableName membership
    have accepted :=
      (List.all_eq_true.mp checked) variableName membership
    cases assigned : free variableName with
    | none => simp [assigned] at accepted
    | some type =>
        cases type with
        | base tag =>
            refine ⟨tag, rfl, ?_⟩
            change tag ∈ language.types.map (·.name)
            simpa [assigned] using accepted
        | arrow domain codomain => simp [assigned] at accepted
        | multiBinder body => simp [assigned] at accepted
        | collection kind element => simp [assigned] at accepted
  · intro declared
    apply List.all_eq_true.mpr
    intro variableName membership
    obtain ⟨tag, assigned, member⟩ := declared variableName membership
    change tag ∈ language.types.map (·.name) at member
    simpa [assigned] using member

/-- Two ordinary authored parameters have exactly two typed arguments. -/
private theorem simplePair
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {patterns : List Pattern} {firstName secondName : String}
    {firstType secondType : TypeExpr}
    (typed : ArgumentsHaveTypes language free bound patterns
      [.simple firstName firstType, .simple secondName secondType]) :
    ∃ first second, patterns = [first, second] ∧
      HasType language free bound first firstType ∧
      HasType language free bound second secondType := by
  cases patterns with
  | nil => cases typed
  | cons first rest =>
      obtain ⟨firstTyped, restTyped⟩ :=
        ArgumentsHaveTypes.simple_cons_inv typed
      cases rest with
      | nil => cases restTyped
      | cons second more =>
          obtain ⟨secondTyped, remaining⟩ :=
            ArgumentsHaveTypes.simple_cons_inv restTyped
          cases more with
          | nil => exact ⟨first, second, rfl, firstTyped, secondTyped⟩
          | cons third tail => cases remaining

/-- Three ordinary authored parameters have exactly three typed arguments. -/
private theorem simpleTriple
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {patterns : List Pattern} {firstName secondName thirdName : String}
    {firstType secondType thirdType : TypeExpr}
    (typed : ArgumentsHaveTypes language free bound patterns
      [.simple firstName firstType, .simple secondName secondType,
        .simple thirdName thirdType]) :
    ∃ first second third, patterns = [first, second, third] ∧
      HasType language free bound first firstType ∧
      HasType language free bound second secondType ∧
      HasType language free bound third thirdType := by
  cases patterns with
  | nil => cases typed
  | cons first rest =>
      obtain ⟨firstTyped, restTyped⟩ :=
        ArgumentsHaveTypes.simple_cons_inv typed
      obtain ⟨second, third, shape, secondTyped, thirdTyped⟩ :=
        simplePair restTyped
      cases shape
      exact ⟨first, second, third, rfl, firstTyped, secondTyped, thirdTyped⟩

/-- A typed open first-order WM pattern in the existing eight-constructor
language has a supported intrinsic receipt, provided its free names are
resolved to sorted context positions. The result is deliberately existential:
the executable open elaborator is a separate computational obligation. -/
theorem typedOpen_reifies
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (free : FreeTypeContext)
    (resolves : ∀ {sort : TypeExpr} {variableName : String},
      free variableName = some sort →
        ∃ position : Var Γ sort, names sort position = variableName)
    (pattern : Pattern) {sort : TypeExpr}
    (typed : HasType CombinedLang free [] pattern sort)
    (compiled : compilePattern? pattern ≠ none) :
    ∃ (term : Term CombinedSignature Γ sort) (fragment : FirstOrder term),
      namedErase names fragment = pattern := by
  induction pattern using Pattern.inductionOn generalizing sort with
  | hbvar index =>
      cases typed with
      | bvar lookup => simp at lookup
  | hfvar variableName =>
      cases typed with
      | fvar lookup =>
          obtain ⟨position, named⟩ := resolves lookup
          refine ⟨Term.var position, FirstOrder.variable position, ?_⟩
          simp [namedErase, named]
  | happly label arguments ih =>
      cases typed with
      | constructor member ordinary argumentsTyped =>
          have childrenCompiled := compilePatterns?_ne_none_of_apply compiled
          rcases combined_declaration_cases member with h | h | h | h | h | h | h | h
          · cases h
            obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
              simplePair argumentsTyped
            have firstCompiled := compilePattern?_ne_none_of_cons childrenCompiled
            have secondCompiled := compilePattern?_ne_none_of_cons
              (compilePatterns?_ne_none_of_cons childrenCompiled)
            obtain ⟨firstTerm, firstCert, firstErase⟩ :=
              ih _ (List.Mem.head _) firstTyped firstCompiled
            obtain ⟨secondTerm, secondCert, secondErase⟩ :=
              ih _ (List.Mem.tail _ (List.Mem.head _)) secondTyped secondCompiled
            refine ⟨revise firstTerm secondTerm,
              .revise firstCert secondCert, ?_⟩
            simp [namedErase, pRevise, firstErase, secondErase, reviseDecl]
          · cases h
            obtain ⟨world, query, rfl, worldTyped, queryTyped⟩ :=
              simplePair argumentsTyped
            have worldCompiled := compilePattern?_ne_none_of_cons childrenCompiled
            have queryCompiled := compilePattern?_ne_none_of_cons
              (compilePatterns?_ne_none_of_cons childrenCompiled)
            obtain ⟨worldTerm, worldCert, worldErase⟩ :=
              ih _ (List.Mem.head _) worldTyped worldCompiled
            obtain ⟨queryTerm, queryCert, queryErase⟩ :=
              ih _ (List.Mem.tail _ (List.Mem.head _)) queryTyped queryCompiled
            refine ⟨extract worldTerm queryTerm,
              .extract worldCert queryCert, ?_⟩
            simp [namedErase, pExtract, worldErase, queryErase, extractDecl]
          · cases h
            obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
              simplePair argumentsTyped
            have firstCompiled := compilePattern?_ne_none_of_cons childrenCompiled
            have secondCompiled := compilePattern?_ne_none_of_cons
              (compilePatterns?_ne_none_of_cons childrenCompiled)
            obtain ⟨firstTerm, firstCert, firstErase⟩ :=
              ih _ (List.Mem.head _) firstTyped firstCompiled
            obtain ⟨secondTerm, secondCert, secondErase⟩ :=
              ih _ (List.Mem.tail _ (List.Mem.head _)) secondTyped secondCompiled
            refine ⟨combine firstTerm secondTerm,
              .combine firstCert secondCert, ?_⟩
            simp [namedErase, pCombine, firstErase, secondErase, combineDecl]
          · cases h
            cases argumentsTyped
            refine ⟨zero, .zero, ?_⟩
            rfl
          · cases h
            obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
              simplePair argumentsTyped
            have firstCompiled := compilePattern?_ne_none_of_cons childrenCompiled
            have secondCompiled := compilePattern?_ne_none_of_cons
              (compilePatterns?_ne_none_of_cons childrenCompiled)
            obtain ⟨firstTerm, firstCert, firstErase⟩ :=
              ih _ (List.Mem.head _) firstTyped firstCompiled
            obtain ⟨secondTerm, secondCert, secondErase⟩ :=
              ih _ (List.Mem.tail _ (List.Mem.head _)) secondTyped secondCompiled
            refine ⟨overlapMerge firstTerm secondTerm,
              .overlapMerge firstCert secondCert, ?_⟩
            simp [namedErase, pOverlapMerge, firstErase, secondErase, overlapMergeDecl]
          · cases h
            obtain ⟨first, second, query, rfl, firstTyped, secondTyped, queryTyped⟩ :=
              simpleTriple argumentsTyped
            have firstCompiled := compilePattern?_ne_none_of_cons childrenCompiled
            have restCompiled := compilePatterns?_ne_none_of_cons childrenCompiled
            have secondCompiled := compilePattern?_ne_none_of_cons restCompiled
            have thirdCompiled := compilePattern?_ne_none_of_cons
              (compilePatterns?_ne_none_of_cons restCompiled)
            obtain ⟨firstTerm, firstCert, firstErase⟩ :=
              ih _ (List.Mem.head _) firstTyped firstCompiled
            obtain ⟨secondTerm, secondCert, secondErase⟩ :=
              ih _ (List.Mem.tail _ (List.Mem.head _)) secondTyped secondCompiled
            obtain ⟨queryTerm, queryCert, queryErase⟩ :=
              ih _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                queryTyped thirdCompiled
            refine ⟨overlapFactor firstTerm secondTerm queryTerm,
              .overlapFactor firstCert secondCert queryCert, ?_⟩
            simp [namedErase, pOverlapFactor, firstErase, secondErase, queryErase,
              overlapFactorDecl]
          · cases h
            obtain ⟨first, second, factor, rfl, firstTyped, secondTyped, factorTyped⟩ :=
              simpleTriple argumentsTyped
            have firstCompiled := compilePattern?_ne_none_of_cons childrenCompiled
            have restCompiled := compilePatterns?_ne_none_of_cons childrenCompiled
            have secondCompiled := compilePattern?_ne_none_of_cons restCompiled
            have thirdCompiled := compilePattern?_ne_none_of_cons
              (compilePatterns?_ne_none_of_cons restCompiled)
            obtain ⟨firstTerm, firstCert, firstErase⟩ :=
              ih _ (List.Mem.head _) firstTyped firstCompiled
            obtain ⟨secondTerm, secondCert, secondErase⟩ :=
              ih _ (List.Mem.tail _ (List.Mem.head _)) secondTyped secondCompiled
            obtain ⟨factorTerm, factorCert, factorErase⟩ :=
              ih _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                factorTyped thirdCompiled
            refine ⟨overlapCorrect firstTerm secondTerm factorTerm,
              .overlapCorrect firstCert secondCert factorCert, ?_⟩
            simp [namedErase, pOverlapCorrect, firstErase, secondErase, factorErase,
              overlapCorrectDecl]
          · cases h
            obtain ⟨scope, world, rfl, scopeTyped, worldTyped⟩ :=
              simplePair argumentsTyped
            have scopeCompiled := compilePattern?_ne_none_of_cons childrenCompiled
            have worldCompiled := compilePattern?_ne_none_of_cons
              (compilePatterns?_ne_none_of_cons childrenCompiled)
            obtain ⟨scopeTerm, scopeCert, scopeErase⟩ :=
              ih _ (List.Mem.head _) scopeTyped scopeCompiled
            obtain ⟨worldTerm, worldCert, worldErase⟩ :=
              ih _ (List.Mem.tail _ (List.Mem.head _)) worldTyped worldCompiled
            refine ⟨forget scopeTerm worldTerm,
              .forget scopeCert worldCert, ?_⟩
            simp [namedErase, pForget, scopeErase, worldErase, forgetDecl]
  | hlambda binder body ih => simp [compilePattern?] at compiled
  | hmultiLambda count binders body ih => simp [compilePattern?] at compiled
  | hsubst body replacement bodyIH replacementIH => simp [compilePattern?] at compiled
  | hcollection kind elements rest ih => simp [compilePattern?] at compiled

/-- The executable authored checker may supply the typing premise of the
open receipt theorem. The first-order compiler still determines its exact
supported representation fragment. -/
theorem checkedOpen_reifies
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (free : FreeTypeContext)
    (resolves : ∀ {sort : TypeExpr} {variableName : String},
      free variableName = some sort →
        ∃ position : Var Γ sort, names sort position = variableName)
    (pattern : Pattern) {sort : TypeExpr}
    (checked : checkHasType CombinedLang free [] pattern sort = true)
    (compiled : compilePattern? pattern ≠ none) :
    ∃ (term : Term CombinedSignature Γ sort) (fragment : FirstOrder term),
      namedErase names fragment = pattern :=
  typedOpen_reifies names free resolves pattern (checkHasType_sound checked) compiled

/-- Only names occurring in the checked pattern need intrinsic context
positions. Extra entries in the ambient typing assignment impose no hidden
finite-support requirement on an otherwise open program. -/
theorem checkedOpen_reifies_on_used_names
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (free : FreeTypeContext) (pattern : Pattern) {sort : TypeExpr}
    (resolvesUsed : ∀ {variableName : String} {variableSort : TypeExpr},
      variableName ∈ pattern.freeFvarNames →
      free variableName = some variableSort →
        ∃ position : Var Γ variableSort,
          names variableSort position = variableName)
    (checked : checkHasType CombinedLang free [] pattern sort = true)
    (compiled : compilePattern? pattern ≠ none) :
    ∃ (term : Term CombinedSignature Γ sort) (fragment : FirstOrder term),
      namedErase names fragment = pattern := by
  let relevant := free.restrictTo pattern.freeFvarNames
  have typed : HasType CombinedLang relevant [] pattern sort :=
    (checkHasType_sound checked).recontextualizeFree
      (fun membership lookup => by
        simpa [relevant, FreeTypeContext.restrictTo, membership] using lookup)
  have resolvesRelevant : ∀ {variableSort : TypeExpr} {variableName : String},
      relevant variableName = some variableSort →
        ∃ position : Var Γ variableSort,
          names variableSort position = variableName := by
    intro variableSort variableName lookup
    have membership : variableName ∈ pattern.freeFvarNames :=
      FreeTypeContext.mem_of_restrictTo_eq_some lookup
    exact resolvesUsed membership
      (by simpa [relevant, FreeTypeContext.restrictTo, membership] using lookup)
  exact typedOpen_reifies names relevant resolvesRelevant pattern typed compiled

/-- An authored-checked first-order WM schema determines its own finite
sorted source context: list its used free names, look up their assigned
sorts, and name each resulting intrinsic position by that same entry. No
caller-supplied source resolver or ambient unused position is needed. The
term witness remains propositional rather than a computed elaboration. -/
theorem checkedOpen_reifies_canonical
    (free : FreeTypeContext) (pattern : Pattern) {sort : TypeExpr}
    (checked : checkHasType CombinedLang free [] pattern sort = true)
    (compiled : compilePattern? pattern ≠ none) :
    ∃ (term : Term CombinedSignature
        (contextSorts (fromUsed free pattern.freeFvarNames)) sort)
      (fragment : FirstOrder term),
      namedErase (names (fromUsed free pattern.freeFvarNames)) fragment =
        pattern := by
  apply checkedOpen_reifies_on_used_names
    (names (fromUsed free pattern.freeFvarNames)) free pattern
  · intro variableName variableSort membership assigned
    exact fromUsed_resolves free pattern.freeFvarNames membership assigned
  · exact checked
  · exact compiled

/-- A computed intrinsic term together with evidence that it belongs to the
existing combined first-order fragment. The sort and context are the same
indices used by the generated binding signature. -/
abbrev FirstOrderReceipt (entries : List (String × TypeExpr))
    (sort : TypeExpr) : Type :=
  Σ term : Term CombinedSignature (contextSorts entries) sort, FirstOrder term

/-- Reify an open variable leaf by executing the generic sorted name lookup.
Unlike the existential open reification theorem, this returns data in
`Option`; constructors will require the corresponding recursive codec. -/
def reifyOpenVariable? (entries : List (String × TypeExpr))
    (variableName : String) (sort : TypeExpr) :
    Option (FirstOrderReceipt entries sort) :=
  (lookupPosition? entries variableName sort).map fun position =>
    ⟨Term.var position, .variable position⟩

/-- Successful computed variable reification has exactly the authored name
under the same generated naming map used by the matcher bridge. -/
theorem reifyOpenVariable?_named
    (entries : List (String × TypeExpr)) (variableName : String) (sort : TypeExpr)
    {receipt : FirstOrderReceipt entries sort}
    (accepted : reifyOpenVariable? entries variableName sort = some receipt) :
    namedErase (names entries) receipt.2 = .fvar variableName := by
  cases found : lookupPosition? entries variableName sort with
  | none => simp [reifyOpenVariable?, found] at accepted
  | some position =>
      simp [reifyOpenVariable?, found] at accepted
      cases accepted
      simpa [namedErase, names] using
        congrArg Pattern.fvar (lookupPosition?_sound entries variableName sort found)

/-- Every assigned used free name can be reified as an actual computed
variable receipt in its pattern-derived context. -/
theorem reifyOpenVariable?_fromUsed_complete (free : FreeTypeContext)
    (used : List String) {variableName : String} {sort : TypeExpr}
    (membership : variableName ∈ used)
    (assigned : free variableName = some sort) :
    (reifyOpenVariable? (fromUsed free used) variableName sort).isSome = true := by
  have found := lookupPosition?_fromUsed_complete free used membership assigned
  cases result : lookupPosition? (fromUsed free used) variableName sort with
  | none => simp [result] at found
  | some position => simp [reifyOpenVariable?, result]

/-- A computed simultaneous substitution whose every image has an existing
first-order certificate. This is data, unlike the existential target
substitution produced by the general checked-image theorem. -/
abbrev SupportedSubstitution (sourceEntries targetEntries :
    List (String × TypeExpr)) : Type :=
  Σ sigma : Sub CombinedSignature (contextSorts sourceEntries)
      (contextSorts targetEntries),
    ∀ sort (position : Var (contextSorts sourceEntries) sort),
      FirstOrder (sigma sort position)

/-- Compute the intrinsic substitution for captures whose images are all
renamed free variables. Constructor-tree images remain the separate recursive
open-reifier obligation; they are not silently dropped or coerced here. -/
def reifyVariableImages? (targetEntries : List (String × TypeExpr))
    (bindings : Bindings) : (sourceEntries : List (String × TypeExpr)) →
      Option (SupportedSubstitution sourceEntries targetEntries)
  | [] => some ⟨(fun _ position => nomatch position),
      (fun _ position => nomatch position)⟩
  | (sourceName, sourceSort) :: rest =>
      match applyBindings bindings (.fvar sourceName) with
      | .fvar targetName => do
          let targetPosition ← lookupPosition? targetEntries targetName sourceSort
          let tail ← reifyVariableImages? targetEntries bindings rest
          pure ⟨
            (fun sort position => match position with
              | .zero => Term.var targetPosition
              | .succ earlier => tail.1 sort earlier),
            (fun sort position => match position with
              | .zero => FirstOrder.variable targetPosition
              | .succ earlier => tail.2 sort earlier)⟩
      | _ => none

/-- Every computed variable-only substitution image renders to the exact
captured raw image at its source name. This is a computational receipt for
the actual simultaneous substitution, not a postulated map. -/
theorem reifyVariableImages?_named
    (targetEntries : List (String × TypeExpr)) (bindings : Bindings) :
    ∀ (sourceEntries : List (String × TypeExpr))
      {receipt : SupportedSubstitution sourceEntries targetEntries},
      reifyVariableImages? targetEntries bindings sourceEntries = some receipt →
        ∀ sort (position : Var (contextSorts sourceEntries) sort),
          applyBindings bindings (.fvar (names sourceEntries sort position)) =
            namedErase (names targetEntries) (receipt.2 sort position) := by
  intro sourceEntries
  induction sourceEntries with
  | nil =>
      intro receipt _ sort position
      nomatch position
  | cons head rest ih =>
      rcases head with ⟨sourceName, sourceSort⟩
      intro receipt accepted sort position
      cases image : applyBindings bindings (.fvar sourceName) with
      | fvar targetName =>
          cases targetLookup : lookupPosition? targetEntries targetName sourceSort with
          | none =>
              simp [reifyVariableImages?, image, targetLookup] at accepted
          | some targetPosition =>
              cases tailResult : reifyVariableImages? targetEntries bindings rest with
              | none =>
                  simp [reifyVariableImages?, image, targetLookup,
                    tailResult] at accepted
              | some tailReceipt =>
                  simp [reifyVariableImages?, image, targetLookup,
                    tailResult] at accepted
                  cases accepted
                  cases position with
                  | zero =>
                      have named := lookupPosition?_sound targetEntries
                        targetName sourceSort targetLookup
                      simpa [names, nameAt, namedErase, image] using
                        congrArg Pattern.fvar named |>.symm
                  | succ earlier =>
                      exact ih tailResult sort earlier
      | bvar index => simp [reifyVariableImages?, image] at accepted
      | apply label arguments => simp [reifyVariableImages?, image] at accepted
      | lambda binder body => simp [reifyVariableImages?, image] at accepted
      | multiLambda count binders body =>
          simp [reifyVariableImages?, image] at accepted
      | subst body replacement => simp [reifyVariableImages?, image] at accepted
      | collection kind elements restName =>
          simp [reifyVariableImages?, image] at accepted

/-- The variable-only substitution algorithm succeeds whenever each source
position's captured image is a free variable found at the same sort in the
target context. The hypotheses describe the exact supported fragment. -/
theorem reifyVariableImages?_complete_of_resolved
    (targetEntries : List (String × TypeExpr)) (bindings : Bindings) :
    ∀ (sourceEntries : List (String × TypeExpr)),
      (∀ sort (position : Var (contextSorts sourceEntries) sort),
        ∃ targetName,
          applyBindings bindings (.fvar (names sourceEntries sort position)) =
            .fvar targetName ∧
          (lookupPosition? targetEntries targetName sort).isSome = true) →
      (reifyVariableImages? targetEntries bindings sourceEntries).isSome = true := by
  intro sourceEntries
  induction sourceEntries with
  | nil =>
      intro _
      rfl
  | cons head rest ih =>
      rcases head with ⟨sourceName, sourceSort⟩
      intro allImages
      obtain ⟨targetName, image, found⟩ := allImages sourceSort .zero
      have tailImages : ∀ sort (position : Var (contextSorts rest) sort),
          ∃ targetName,
            applyBindings bindings (.fvar (names rest sort position)) =
              .fvar targetName ∧
            (lookupPosition? targetEntries targetName sort).isSome = true := by
        intro sort position
        exact allImages sort (.succ position)
      have tailSome := ih tailImages
      cases targetLookup : lookupPosition? targetEntries targetName sourceSort with
      | none => simp [targetLookup] at found
      | some targetPosition =>
          cases tailResult : reifyVariableImages? targetEntries bindings rest with
          | none => simp [tailResult] at tailSome
          | some receipt =>
              have headImage : applyBindings bindings (.fvar sourceName) =
                  .fvar targetName := by
                simpa [names, nameAt] using image
              simp [reifyVariableImages?, headImage, targetLookup, tailResult,
                Option.isSome]

private abbrev OpenHandleContext : Ctx CombinedSignature :=
  [.base "State", .base "Query"]

private def openHandleNames :
    (sort : TypeExpr) → Var OpenHandleContext sort → String :=
  fun _ position => match position with
    | .zero => "w"
    | .succ .zero => "q"
    | .succ (.succ earlier) => nomatch earlier

private def openTargetNames :
    (sort : TypeExpr) → Var OpenHandleContext sort → String :=
  fun _ position => match position with
    | .zero => "w2"
    | .succ .zero => "q2"
    | .succ (.succ earlier) => nomatch earlier

private def openSourceFree : FreeTypeContext :=
  fun variableName =>
    if variableName == "w" then some (.base "State")
    else if variableName == "q" then some (.base "Query") else none

private def openTargetFree : FreeTypeContext :=
  fun variableName =>
    if variableName == "w2" then some (.base "State")
    else if variableName == "q2" then some (.base "Query") else none

private theorem openSourceResolves
    {variableSort : TypeExpr} {variableName : String}
    (assigned : openSourceFree variableName = some variableSort) :
    ∃ position : Var OpenHandleContext variableSort,
      openHandleNames variableSort position = variableName := by
  by_cases world : variableName = "w"
  · subst variableName
    have sorted : variableSort = .base "State" := by
      simpa [openSourceFree] using assigned.symm
    subst variableSort
    exact ⟨.zero, rfl⟩
  by_cases query : variableName = "q"
  · subst variableName
    have sorted : variableSort = .base "Query" := by
      simpa [openSourceFree, world] using assigned.symm
    subst variableSort
    exact ⟨.succ .zero, rfl⟩
  simp [openSourceFree, world, query] at assigned

private theorem openTargetResolves
    {variableSort : TypeExpr} {variableName : String}
    (assigned : openTargetFree variableName = some variableSort) :
    ∃ position : Var OpenHandleContext variableSort,
      openTargetNames variableSort position = variableName := by
  by_cases world : variableName = "w2"
  · subst variableName
    have sorted : variableSort = .base "State" := by
      simpa [openTargetFree] using assigned.symm
    subst variableSort
    exact ⟨.zero, rfl⟩
  by_cases query : variableName = "q2"
  · subst variableName
    have sorted : variableSort = .base "Query" := by
      simpa [openTargetFree, world] using assigned.symm
    subst variableSort
    exact ⟨.succ .zero, rfl⟩
  simp [openTargetFree, world, query] at assigned

/-- A concrete open State/Query query has all three receipts: the actual
authored checker accepts it, the actual matcher compiler accepts it, and an
intrinsic supported term names back to the same raw pattern. The closed
non-Evidence impossibility theorem shows why the handles must stay open. -/
theorem open_extract_checked_compiled_reifies :
    checkHasType CombinedLang
      (FreeTypeContext.ofList
        [("w", .base "State"), ("q", .base "Query")]) []
      (pExtract (.fvar "w") (.fvar "q")) (.base "BinaryEvidence") = true ∧
    (compilePattern? (pExtract (.fvar "w") (.fvar "q"))).isSome = true ∧
    ∃ (term : Term CombinedSignature OpenHandleContext (.base "BinaryEvidence"))
      (fragment : FirstOrder term),
        namedErase openHandleNames fragment =
          pExtract (.fvar "w") (.fvar "q") := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  exact ⟨extract (.var .zero) (.var (.succ .zero)),
    .extract (.variable .zero) (.variable (.succ .zero)), rfl⟩

/-- Free-variable assignments are trusted inputs to the authored checker:
it checks their equality with the requested sort but does not itself certify
that an externally supplied sort belongs to the WM declaration list. The
declared-sort condition is therefore a separate requirement for an inhabited
semantic environment or a Prime capability boundary. -/
theorem externally_assigned_sort_checks :
    checkHasType CombinedLang
      (FreeTypeContext.ofList [("ghost", .base "NotDeclared")]) []
      (.fvar "ghost") (.base "NotDeclared") = true ∧
    "NotDeclared" ∉ CombinedLang.types := by
  constructor <;> decide +kernel

/-- The actual State/Query handle example passes the additional declaration
check that the base typing checker intentionally leaves to its caller. -/
theorem open_extract_used_sorts_declared :
    checkUsedFreeSortsDeclared CombinedLang
      (FreeTypeContext.ofList
        [("w", .base "State"), ("q", .base "Query")])
      (pExtract (.fvar "w") (.fvar "q")) = true := by
  simp [checkUsedFreeSortsDeclared, FreeTypeContext.ofList, CombinedLang,
    combined_types, pExtract, Pattern.freeFvarNames, TypeDecl.plain]

/-- The same executable declaration check rejects the externally assigned
but undeclared sort accepted by the base context lookup. -/
theorem undeclared_free_sort_rejected :
    checkUsedFreeSortsDeclared CombinedLang
      (FreeTypeContext.ofList [("ghost", .base "NotDeclared")])
      (.fvar "ghost") = false := by
  simp [checkUsedFreeSortsDeclared, FreeTypeContext.ofList, CombinedLang,
    combined_types, Pattern.freeFvarNames, TypeDecl.plain]

/-- An actually checked, compiled open WM schema no longer needs a
hand-supplied source `FirstOrder` certificate before its successful matcher
result receives the combined-model denotation. Target substitution images
still require supported certificates and exact raw-name binding receipts. -/
theorem checkedOpen_match_denotes
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (free : FreeTypeContext) (pattern : Pattern) {sort : TypeExpr}
    (resolvesUsed : ∀ {variableName : String} {variableSort : TypeExpr},
      variableName ∈ pattern.freeFvarNames →
      free variableName = some variableSort →
        ∃ position : Var Γ variableSort,
          sourceNames variableSort position = variableName)
    (checked : checkHasType CombinedLang free [] pattern sort = true)
    (compiled : compilePattern? pattern ≠ none)
    (bindings : Bindings)
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ variableSort (position : Var Γ variableSort),
      FirstOrder (sigma variableSort position))
    (variableReceipt : ∀ variableSort (position : Var Γ variableSort),
      applyBindings bindings (.fvar (sourceNames variableSort position)) =
        namedErase targetNames (supported variableSort position))
    (concrete : Pattern)
    (matched : bindings ∈ matchPattern pattern concrete) :
    ∃ (term : Term CombinedSignature Γ sort) (fragment : FirstOrder term),
      namedErase sourceNames fragment = pattern ∧
      ∃ targetCertificate : FirstOrder (bind sigma term),
        namedErase targetNames targetCertificate = concrete ∧
          FirstOrder.denote reading environment targetCertificate =
            FirstOrder.denote reading
              (fun variableSort position => FirstOrder.denote reading environment
                (supported variableSort position)) fragment := by
  obtain ⟨term, fragment, sourceNamed⟩ :=
    checkedOpen_reifies_on_used_names sourceNames free pattern resolvesUsed checked compiled
  have matchedNamed : bindings ∈
      matchPattern (namedErase sourceNames fragment) concrete := by
    simpa only [sourceNamed] using matched
  obtain ⟨targetCertificate, targetNamed, value⟩ :=
    matchPattern_namedErase_open_denote reading environment sourceNames targetNames
      bindings sigma supported variableReceipt fragment concrete matchedNamed
  exact ⟨term, fragment, sourceNamed, targetCertificate, targetNamed, value⟩

/-- When every raw image of a source handle passes the authored target checker
and the existing first-order compiler, the intrinsic substitution and all of
its support receipts exist. This derives the target-side hypotheses used by
the matcher semantics instead of asking a caller to fabricate them. The
choice of receipts is propositional; a runnable elaborator is separate. -/
theorem checkedBindingImages_reify
    {Γ Δ : Ctx CombinedSignature}
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (targetFree : FreeTypeContext)
    (targetResolves : ∀ {variableSort : TypeExpr} {variableName : String},
      targetFree variableName = some variableSort →
        ∃ position : Var Δ variableSort,
          targetNames variableSort position = variableName)
    (bindings : Bindings)
    (imagesChecked : ∀ variableSort (position : Var Γ variableSort),
      checkHasType CombinedLang targetFree []
        (applyBindings bindings (.fvar (sourceNames variableSort position)))
        variableSort = true)
    (imagesCompiled : ∀ variableSort (position : Var Γ variableSort),
      compilePattern?
        (applyBindings bindings (.fvar (sourceNames variableSort position))) ≠ none) :
    ∃ (sigma : Sub CombinedSignature Γ Δ)
      (supported : ∀ variableSort (position : Var Γ variableSort),
        FirstOrder (sigma variableSort position)),
      ∀ variableSort (position : Var Γ variableSort),
        applyBindings bindings (.fvar (sourceNames variableSort position)) =
          namedErase targetNames (supported variableSort position) := by
  classical
  have imagesReify : ∀ variableSort (position : Var Γ variableSort),
      ∃ (term : Term CombinedSignature Δ variableSort)
        (fragment : FirstOrder term),
        namedErase targetNames fragment =
          applyBindings bindings (.fvar (sourceNames variableSort position)) := by
    intro variableSort position
    obtain ⟨term, fragment, exactName⟩ :=
      checkedOpen_reifies targetNames targetFree targetResolves
        (applyBindings bindings (.fvar (sourceNames variableSort position)))
        (imagesChecked variableSort position)
        (imagesCompiled variableSort position)
    exact ⟨term, fragment, exactName⟩
  choose sigma supported receipts using imagesReify
  exact ⟨sigma, supported, fun variableSort position =>
    (receipts variableSort position).symm⟩

/-- Admission of one concrete raw target image at its source handle's sort.
The declaration test uses the same authored language as the typing checker;
in particular, an externally supplied undeclared free sort is rejected. -/
def checkBindingImage
    {Γ : Ctx CombinedSignature}
    (targetFree : FreeTypeContext) (bindings : Bindings)
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (sort : TypeExpr) (position : Var Γ sort) : Bool :=
  let image := applyBindings bindings (.fvar (sourceNames sort position))
  checkHasType CombinedLang targetFree [] image sort &&
    (compilePattern? image).isSome &&
    checkUsedFreeSortsDeclared CombinedLang targetFree image

/-- A finite, executable scan of every sorted source-context position. It
does not enumerate constructors or introduce another WM type inventory. -/
def checkBindingImages (targetFree : FreeTypeContext) (bindings : Bindings) :
    (Γ : Ctx CombinedSignature) →
    ((sort : TypeExpr) → Var Γ sort → String) → Bool
  | [], _ => true
  | _ :: rest, names =>
      checkBindingImage targetFree bindings names _ .zero &&
        checkBindingImages targetFree bindings rest
          (fun sort position => names sort (.succ position))

/-- The single-image Boolean is precisely authored typing, compiler support,
and declaration admission for the used free names. -/
theorem checkBindingImage_iff
    {Γ : Ctx CombinedSignature}
    (targetFree : FreeTypeContext) (bindings : Bindings)
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (sort : TypeExpr) (position : Var Γ sort) :
    checkBindingImage targetFree bindings sourceNames sort position = true ↔
      checkHasType CombinedLang targetFree []
        (applyBindings bindings (.fvar (sourceNames sort position))) sort = true ∧
      (compilePattern?
        (applyBindings bindings (.fvar (sourceNames sort position)))).isSome = true ∧
      checkUsedFreeSortsDeclared CombinedLang targetFree
        (applyBindings bindings (.fvar (sourceNames sort position))) = true := by
  simp [checkBindingImage, Bool.and_eq_true, and_assoc]

/-- Scanning the actual finite context is equivalent to admitting every one
of its sorted positions, including positions with repeated source names. -/
theorem checkBindingImages_iff_all
    (targetFree : FreeTypeContext) (bindings : Bindings)
    (Γ : Ctx CombinedSignature)
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String) :
    checkBindingImages targetFree bindings Γ sourceNames = true ↔
      ∀ sort (position : Var Γ sort),
        checkBindingImage targetFree bindings sourceNames sort position = true := by
  induction Γ with
  | nil =>
      constructor
      · intro _ sort position
        nomatch position
      · intro _
        rfl
  | cons head tail ih =>
      let tailNames : (sort : TypeExpr) → Var tail sort → String :=
        fun sort position => sourceNames sort (.succ position)
      change (checkBindingImage targetFree bindings sourceNames head .zero &&
        checkBindingImages targetFree bindings tail tailNames) = true ↔ _
      constructor
      · intro checked sort position
        obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp checked
        cases position with
        | zero => exact first
        | succ earlier => exact (ih tailNames).mp rest sort earlier
      · intro checked
        apply Bool.and_eq_true_iff.mpr
        refine ⟨checked head .zero, (ih tailNames).mpr ?_⟩
        intro sort position
        exact checked sort (.succ position)

/-- The finite target-name inventory consists of names occurring in the
actual raw images of source-context entries, rather than every name in an
ambient target typing assignment. -/
def capturedTargetNames (sourceEntries : List (String × TypeExpr))
    (bindings : Bindings) : List String :=
  sourceEntries.flatMap fun entry =>
    (applyBindings bindings (.fvar entry.1)).freeFvarNames

/-- Every name used by an actual captured image occurs in that finite target
inventory. This is a property of the generated source positions, independent
of the matcher implementation. -/
theorem capturedTargetNames_contains_image
    (sourceEntries : List (String × TypeExpr)) (bindings : Bindings)
    (sort : TypeExpr) (position : Var (contextSorts sourceEntries) sort)
    {variableName : String}
    (membership : variableName ∈
      (applyBindings bindings (.fvar (names sourceEntries sort position))).freeFvarNames) :
    variableName ∈ capturedTargetNames sourceEntries bindings := by
  apply List.mem_flatMap.mpr
  exact ⟨(names sourceEntries sort position, sort),
    position_pair_mem sourceEntries sort position, membership⟩

/-- The runnable context scan discharges the image checks needed for the
target-side substitution theorem. The subsequent intrinsic certificate is
still an existence result, not an executable elaboration algorithm. -/
theorem checkedBindingImages_reify_of_gate
    {Γ Δ : Ctx CombinedSignature}
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (targetFree : FreeTypeContext)
    (targetResolves : ∀ {variableSort : TypeExpr} {variableName : String},
      targetFree variableName = some variableSort →
        ∃ position : Var Δ variableSort,
          targetNames variableSort position = variableName)
    (bindings : Bindings)
    (admitted : checkBindingImages targetFree bindings Γ sourceNames = true) :
    ∃ (sigma : Sub CombinedSignature Γ Δ)
      (supported : ∀ variableSort (position : Var Γ variableSort),
        FirstOrder (sigma variableSort position)),
      ∀ variableSort (position : Var Γ variableSort),
        applyBindings bindings (.fvar (sourceNames variableSort position)) =
          namedErase targetNames (supported variableSort position) := by
  have images :=
    (checkBindingImages_iff_all targetFree bindings Γ sourceNames).mp admitted
  apply checkedBindingImages_reify sourceNames targetNames targetFree targetResolves
    bindings
  · intro sort position
    exact (checkBindingImage_iff targetFree bindings sourceNames sort position).mp
      (images sort position) |>.1
  · intro sort position rejected
    have compiled := ((checkBindingImage_iff targetFree bindings sourceNames
      sort position).mp (images sort position)).2.1
    simp [rejected] at compiled

/-- The finite image gate also yields a supported intrinsic substitution
when the target context is generated from the free names in those very
images. No target-name-resolution premise is supplied by the caller. The
substitution remains an existential witness, not an executable reifier. -/
theorem checkedBindingImages_reify_canonical_target
    (sourceEntries : List (String × TypeExpr))
    (targetFree : FreeTypeContext) (bindings : Bindings)
    (admitted : checkBindingImages targetFree bindings
      (contextSorts sourceEntries) (names sourceEntries) = true) :
    let targetEntries := fromUsed targetFree
      (capturedTargetNames sourceEntries bindings)
    ∃ (sigma : Sub CombinedSignature (contextSorts sourceEntries)
        (contextSorts targetEntries))
      (supported : ∀ variableSort
        (position : Var (contextSorts sourceEntries) variableSort),
        FirstOrder (sigma variableSort position)),
      ∀ variableSort (position : Var (contextSorts sourceEntries) variableSort),
        applyBindings bindings (.fvar (names sourceEntries variableSort position)) =
          namedErase (names targetEntries) (supported variableSort position) := by
  classical
  let targetEntries := fromUsed targetFree
    (capturedTargetNames sourceEntries bindings)
  have images := (checkBindingImages_iff_all targetFree bindings
    (contextSorts sourceEntries) (names sourceEntries)).mp admitted
  have imagesReify : ∀ variableSort
      (position : Var (contextSorts sourceEntries) variableSort),
      ∃ (term : Term CombinedSignature (contextSorts targetEntries) variableSort)
        (fragment : FirstOrder term),
        namedErase (names targetEntries) fragment =
          applyBindings bindings (.fvar (names sourceEntries variableSort position)) := by
    intro variableSort position
    have accepted := (checkBindingImage_iff targetFree bindings
      (names sourceEntries) variableSort position).mp (images variableSort position)
    apply checkedOpen_reifies_on_used_names (names targetEntries) targetFree
      (applyBindings bindings (.fvar (names sourceEntries variableSort position)))
    · intro variableName targetSort membership assigned
      exact fromUsed_resolves targetFree
        (capturedTargetNames sourceEntries bindings)
        (capturedTargetNames_contains_image sourceEntries bindings
          variableSort position membership) assigned
    · exact accepted.1
    · intro rejected
      simp [rejected] at accepted
  choose sigma supported receipts using imagesReify
  exact ⟨sigma, supported, fun variableSort position =>
    (receipts variableSort position).symm⟩

/-- The finite target-image gate makes the variable-only intrinsic
substitution algorithm total on its stated fragment. Source images must
actually be free variables; their target sorts are obtained from the
authored checker result, not supplied as an extra target resolver. -/
theorem reifyVariableImages?_complete_of_gate
    (sourceEntries : List (String × TypeExpr))
    (targetFree : FreeTypeContext) (bindings : Bindings)
    (admitted : checkBindingImages targetFree bindings
      (contextSorts sourceEntries) (names sourceEntries) = true)
    (variableImages : ∀ sort
      (position : Var (contextSorts sourceEntries) sort),
      ∃ targetName,
        applyBindings bindings (.fvar (names sourceEntries sort position)) =
          .fvar targetName) :
    (reifyVariableImages?
      (fromUsed targetFree (capturedTargetNames sourceEntries bindings))
      bindings sourceEntries).isSome = true := by
  apply reifyVariableImages?_complete_of_resolved
  intro sort position
  obtain ⟨targetName, image⟩ := variableImages sort position
  have checked := (checkBindingImage_iff targetFree bindings
    (names sourceEntries) sort position).mp
      ((checkBindingImages_iff_all targetFree bindings
        (contextSorts sourceEntries) (names sourceEntries)).mp admitted
        sort position) |>.1
  have assigned : targetFree targetName = some sort := by
    rw [image] at checked
    have typed := checkHasType_sound checked
    cases typed with
    | fvar lookup => exact lookup
  have imageMember : targetName ∈
      (applyBindings bindings (.fvar (names sourceEntries sort position))).freeFvarNames := by
    rw [image]
    simp [Pattern.freeFvarNames]
  have inventoryMember : targetName ∈
      capturedTargetNames sourceEntries bindings :=
    capturedTargetNames_contains_image sourceEntries bindings sort position
      imageMember
  exact ⟨targetName, image,
    lookupPosition?_fromUsed_complete targetFree
      (capturedTargetNames sourceEntries bindings) inventoryMember assigned⟩

/-- Every free target name actually encountered by an admitted captured image
has a base sort declared in the authored combined language. -/
theorem checkBindingImages_used_sorts_declared
    {Γ : Ctx CombinedSignature}
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (targetFree : FreeTypeContext) (bindings : Bindings)
    (admitted : checkBindingImages targetFree bindings Γ sourceNames = true)
    (sort : TypeExpr) (position : Var Γ sort)
    (variableName : String)
    (used : variableName ∈
      (applyBindings bindings (.fvar (sourceNames sort position))).freeFvarNames) :
    ∃ tag, targetFree variableName = some (.base tag) ∧
      tag ∈ CombinedLang.types := by
  have image := (checkBindingImages_iff_all targetFree bindings Γ sourceNames).mp
    admitted sort position
  have declared := ((checkBindingImage_iff targetFree bindings sourceNames
    sort position).mp image).2.2
  exact (checkUsedFreeSortsDeclared_iff CombinedLang targetFree _).mp declared
    variableName used

/-- A checked source match whose captured target images separately pass the
authored checker and first-order compiler has a supported intrinsic target
and its model value. Raw matching alone is insufficient: the image checks
are the exact additional admission boundary. -/
theorem checkedOpen_match_denotes_of_checked_images
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) {sort : TypeExpr}
    (sourceResolvesUsed : ∀ {variableName : String} {variableSort : TypeExpr},
      variableName ∈ pattern.freeFvarNames →
      sourceFree variableName = some variableSort →
        ∃ position : Var Γ variableSort,
          sourceNames variableSort position = variableName)
    (targetResolves : ∀ {variableSort : TypeExpr} {variableName : String},
      targetFree variableName = some variableSort →
        ∃ position : Var Δ variableSort,
          targetNames variableSort position = variableName)
    (sourceChecked : checkHasType CombinedLang sourceFree [] pattern sort = true)
    (sourceCompiled : compilePattern? pattern ≠ none)
    (bindings : Bindings) (concrete : Pattern)
    (matched : bindings ∈ matchPattern pattern concrete)
    (imagesChecked : ∀ variableSort (position : Var Γ variableSort),
      checkHasType CombinedLang targetFree []
        (applyBindings bindings (.fvar (sourceNames variableSort position)))
        variableSort = true)
    (imagesCompiled : ∀ variableSort (position : Var Γ variableSort),
      compilePattern?
        (applyBindings bindings (.fvar (sourceNames variableSort position))) ≠ none) :
    ∃ (sigma : Sub CombinedSignature Γ Δ)
      (supported : ∀ variableSort (position : Var Γ variableSort),
        FirstOrder (sigma variableSort position))
      (term : Term CombinedSignature Γ sort) (fragment : FirstOrder term),
      namedErase sourceNames fragment = pattern ∧
      ∃ targetCertificate : FirstOrder (bind sigma term),
        namedErase targetNames targetCertificate = concrete ∧
          FirstOrder.denote reading environment targetCertificate =
            FirstOrder.denote reading
              (fun variableSort position => FirstOrder.denote reading environment
                (supported variableSort position)) fragment := by
  obtain ⟨sigma, supported, receipts⟩ :=
    checkedBindingImages_reify sourceNames targetNames targetFree targetResolves
      bindings imagesChecked imagesCompiled
  obtain ⟨term, fragment, sourceNamed, targetCertificate, targetNamed, value⟩ :=
    checkedOpen_match_denotes reading environment sourceNames targetNames
      sourceFree pattern sourceResolvesUsed sourceChecked sourceCompiled bindings
      sigma supported receipts concrete matched
  exact ⟨sigma, supported, term, fragment, sourceNamed,
    targetCertificate, targetNamed, value⟩

/-- The finite image gate, rather than hand-written per-handle proofs or
target certificates, is enough to interpret an actual checked WM match.
Compiler support and declared used sorts are both checked by the gate. -/
theorem checkedOpen_match_denotes_of_gate
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) {sort : TypeExpr}
    (sourceResolvesUsed : ∀ {variableName : String} {variableSort : TypeExpr},
      variableName ∈ pattern.freeFvarNames →
      sourceFree variableName = some variableSort →
        ∃ position : Var Γ variableSort,
          sourceNames variableSort position = variableName)
    (targetResolves : ∀ {variableSort : TypeExpr} {variableName : String},
      targetFree variableName = some variableSort →
        ∃ position : Var Δ variableSort,
          targetNames variableSort position = variableName)
    (sourceChecked : checkHasType CombinedLang sourceFree [] pattern sort = true)
    (sourceCompiled : compilePattern? pattern ≠ none)
    (bindings : Bindings) (concrete : Pattern)
    (matched : bindings ∈ matchPattern pattern concrete)
    (admitted : checkBindingImages targetFree bindings Γ sourceNames = true) :
    ∃ (sigma : Sub CombinedSignature Γ Δ)
      (supported : ∀ variableSort (position : Var Γ variableSort),
        FirstOrder (sigma variableSort position))
      (term : Term CombinedSignature Γ sort) (fragment : FirstOrder term),
      namedErase sourceNames fragment = pattern ∧
      ∃ targetCertificate : FirstOrder (bind sigma term),
        namedErase targetNames targetCertificate = concrete ∧
          FirstOrder.denote reading environment targetCertificate =
            FirstOrder.denote reading
              (fun variableSort position => FirstOrder.denote reading environment
                (supported variableSort position)) fragment := by
  obtain ⟨sigma, supported, receipts⟩ :=
    checkedBindingImages_reify_of_gate sourceNames targetNames targetFree
      targetResolves bindings admitted
  obtain ⟨term, fragment, sourceNamed, targetCertificate, targetNamed, value⟩ :=
    checkedOpen_match_denotes reading environment sourceNames targetNames
      sourceFree pattern sourceResolvesUsed sourceChecked sourceCompiled bindings
      sigma supported receipts concrete matched
  exact ⟨sigma, supported, term, fragment, sourceNamed,
    targetCertificate, targetNamed, value⟩

/-- Execute an existing first-order plan and retain only bindings whose raw
images pass the authored target checker, compiler, and used-sort declaration
test. This is a filter on real plan results, not a second matching engine. -/
def checkedPlanAnswers
    {Γ : Ctx CombinedSignature}
    (targetFree : FreeTypeContext)
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (plan : PatternPlan) (concrete : Pattern) : List Bindings :=
  (plan.run concrete).filter fun bindings =>
    checkBindingImages targetFree bindings Γ sourceNames

/-- The checked executor returns exactly the original plan answers that pass
the finite target-image gate. -/
theorem checkedPlanAnswers_mem_iff
    {Γ : Ctx CombinedSignature}
    (targetFree : FreeTypeContext)
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (plan : PatternPlan) (concrete : Pattern) (bindings : Bindings) :
    bindings ∈ checkedPlanAnswers targetFree sourceNames plan concrete ↔
      bindings ∈ plan.run concrete ∧
        checkBindingImages targetFree bindings Γ sourceNames = true := by
  simp [checkedPlanAnswers, and_comm]

/-- An accepted checked plan answer has the combined WM model value of its
checked source schema. The operational hypothesis is membership in the
executed plan's *filtered* answers, not hand-supplied matcher membership. -/
theorem checkedPlanAnswers_denotes
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) {sort : TypeExpr}
    (sourceResolvesUsed : ∀ {variableName : String} {variableSort : TypeExpr},
      variableName ∈ pattern.freeFvarNames →
      sourceFree variableName = some variableSort →
        ∃ position : Var Γ variableSort,
          sourceNames variableSort position = variableName)
    (targetResolves : ∀ {variableSort : TypeExpr} {variableName : String},
      targetFree variableName = some variableSort →
        ∃ position : Var Δ variableSort,
          targetNames variableSort position = variableName)
    (sourceChecked : checkHasType CombinedLang sourceFree [] pattern sort = true)
    (plan : PatternPlan)
    (compiled : compilePattern? pattern = some plan)
    (bindings : Bindings) (concrete : Pattern)
    (returned : bindings ∈
      checkedPlanAnswers targetFree sourceNames plan concrete) :
    ∃ (sigma : Sub CombinedSignature Γ Δ)
      (supported : ∀ variableSort (position : Var Γ variableSort),
        FirstOrder (sigma variableSort position))
      (term : Term CombinedSignature Γ sort) (fragment : FirstOrder term),
      namedErase sourceNames fragment = pattern ∧
      ∃ targetCertificate : FirstOrder (bind sigma term),
        namedErase targetNames targetCertificate = concrete ∧
          FirstOrder.denote reading environment targetCertificate =
            FirstOrder.denote reading
              (fun variableSort position => FirstOrder.denote reading environment
                (supported variableSort position)) fragment := by
  obtain ⟨ran, admitted⟩ :=
    (checkedPlanAnswers_mem_iff targetFree sourceNames plan concrete bindings).mp
      returned
  have matched : bindings ∈ matchPattern pattern concrete := by
    rw [← run_compilePattern? pattern concrete plan compiled]
    exact ran
  have sourceCompiled : compilePattern? pattern ≠ none := by
    simp [compiled]
  exact checkedOpen_match_denotes_of_gate reading environment sourceNames
    targetNames sourceFree targetFree pattern sourceResolvesUsed targetResolves
    sourceChecked sourceCompiled bindings concrete matched admitted

/-- The executable checked plan interface with its source context derived
from the pattern's actual free names and their authored type assignments.
Every generated position names a used occurrence, by the generic
`fromUsed_positions_named_in_input` theorem. -/
def checkedPlanAnswersFromPattern
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) (plan : PatternPlan) (concrete : Pattern) :
    List Bindings :=
  let entries := fromUsed sourceFree pattern.freeFvarNames
  checkedPlanAnswers targetFree (names entries) plan concrete

/-- The context-free interface returns precisely the original plan's
bindings that pass the finite target-image scan on the automatically
constructed source context. -/
theorem checkedPlanAnswersFromPattern_mem_iff
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) (plan : PatternPlan) (concrete : Pattern)
    (bindings : Bindings) :
    bindings ∈ checkedPlanAnswersFromPattern sourceFree targetFree
        pattern plan concrete ↔
      bindings ∈ plan.run concrete ∧
        checkBindingImages targetFree bindings
          (contextSorts (fromUsed sourceFree pattern.freeFvarNames))
          (names (fromUsed sourceFree pattern.freeFvarNames)) = true := by
  exact checkedPlanAnswers_mem_iff targetFree
    (names (fromUsed sourceFree pattern.freeFvarNames)) plan concrete bindings

/-- A checked answer from the pattern-derived context has an intrinsic
first-order target and its combined-model value. No source context or source
name-resolution hypothesis is required from the caller. Target resolution
remains explicit; it is not inferred from raw matching. -/
theorem checkedPlanAnswersFromPattern_denotes
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Δ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) {sort : TypeExpr}
    (targetResolves : ∀ {variableSort : TypeExpr} {variableName : String},
      targetFree variableName = some variableSort →
        ∃ position : Var Δ variableSort,
          targetNames variableSort position = variableName)
    (sourceChecked : checkHasType CombinedLang sourceFree [] pattern sort = true)
    (plan : PatternPlan)
    (compiled : compilePattern? pattern = some plan)
    (bindings : Bindings) (concrete : Pattern)
    (returned : bindings ∈
      checkedPlanAnswersFromPattern sourceFree targetFree pattern plan concrete) :
    let entries := fromUsed sourceFree pattern.freeFvarNames
    ∃ (sigma : Sub CombinedSignature (contextSorts entries) Δ)
      (supported : ∀ variableSort
        (position : Var (contextSorts entries) variableSort),
        FirstOrder (sigma variableSort position))
      (term : Term CombinedSignature (contextSorts entries) sort)
      (fragment : FirstOrder term),
      namedErase (names entries) fragment = pattern ∧
      ∃ targetCertificate : FirstOrder (bind sigma term),
        namedErase targetNames targetCertificate = concrete ∧
          FirstOrder.denote reading environment targetCertificate =
            FirstOrder.denote reading
              (fun variableSort position => FirstOrder.denote reading environment
                (supported variableSort position)) fragment := by
  let entries := fromUsed sourceFree pattern.freeFvarNames
  have sourceResolvesUsed : ∀ {variableName : String}
      {variableSort : TypeExpr},
      variableName ∈ pattern.freeFvarNames →
      sourceFree variableName = some variableSort →
        ∃ position : Var (contextSorts entries) variableSort,
          (names entries) variableSort position = variableName := by
    intro variableName variableSort membership assigned
    exact fromUsed_resolves sourceFree pattern.freeFvarNames membership assigned
  exact checkedPlanAnswers_denotes reading environment (names entries)
    targetNames sourceFree targetFree pattern sourceResolvesUsed targetResolves
    sourceChecked plan compiled bindings concrete returned

/-- Run the executable admission stages from one authored source pattern:
source typing and declared free sorts, existing first-order compilation,
and target-image checks on the context computed from used names. The caller
supplies the expected result sort, not a pre-accepted plan. -/
def checkedOpenAnswers
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) (sort : TypeExpr) (concrete : Pattern) : List Bindings :=
  if checkHasType CombinedLang sourceFree [] pattern sort &&
      checkUsedFreeSortsDeclared CombinedLang sourceFree pattern then
    match compilePattern? pattern with
    | some plan =>
        checkedPlanAnswersFromPattern sourceFree targetFree pattern plan concrete
    | none => []
  else []

/-- The checked entry point returns exactly the compiled plan answers that
pass source typing, declared free sorts, and the target-image gate; no
separate matching semantics is introduced. -/
theorem checkedOpenAnswers_mem_iff
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) (sort : TypeExpr) (concrete : Pattern)
    (bindings : Bindings) :
    bindings ∈ checkedOpenAnswers sourceFree targetFree pattern sort concrete ↔
      ∃ plan, checkHasType CombinedLang sourceFree [] pattern sort = true ∧
        checkUsedFreeSortsDeclared CombinedLang sourceFree pattern = true ∧
        compilePattern? pattern = some plan ∧
        bindings ∈ checkedPlanAnswersFromPattern
          sourceFree targetFree pattern plan concrete := by
  constructor
  · intro returned
    by_cases typed : checkHasType CombinedLang sourceFree [] pattern sort = true
    · by_cases declared :
          checkUsedFreeSortsDeclared CombinedLang sourceFree pattern = true
      · cases compiled : compilePattern? pattern with
        | none =>
            simp [checkedOpenAnswers, typed, declared, compiled] at returned
        | some plan =>
            exact ⟨plan, typed, declared, rfl,
              by simpa [checkedOpenAnswers, typed, declared, compiled] using returned⟩
      · simp [checkedOpenAnswers, typed, declared] at returned
    · simp [checkedOpenAnswers, typed] at returned
  · rintro ⟨plan, typed, declared, compiled, returned⟩
    simpa [checkedOpenAnswers, typed, declared, compiled] using returned

/-- The same actual checked open answer computes a generic intrinsic source
term from the authored combined signature. Its declaration-derived named
erasure is exactly the submitted pattern; no source position resolver or
choice operation is supplied by the caller. -/
theorem checkedOpenAnswers_source_computes
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) (sort : TypeExpr) (concrete : Pattern)
    (bindings : Bindings)
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete) :
    ∃ term : Term CombinedSignature
        (contextSorts (fromUsed sourceFree pattern.freeFvarNames)) sort,
      reifyOpen? CombinedLang
        (fromUsed sourceFree pattern.freeFvarNames) pattern sort = some term ∧
      namedFirstOrderErase?
        (names (fromUsed sourceFree pattern.freeFvarNames)) term =
          some pattern := by
  obtain ⟨_, checked, _, compiled, _⟩ :=
    (checkedOpenAnswers_mem_iff sourceFree targetFree pattern sort concrete
      bindings).mp returned
  exact reifyOpen?_fromUsed_receipt (checkHasType_sound checked)
    (by simp [compiled])

/-- The finite checked target-image gate now supplies enough information
for a *computed* intrinsic substitution, including constructor-tree images.
The output lives in the declaration-derived binding signature; relating it
to the WM-specific semantic `FirstOrder` certificate is a separate seam. -/
theorem checkedOpenAnswers_all_images_compute
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) (sort : TypeExpr) (concrete : Pattern)
    (bindings : Bindings)
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete) :
    let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
    let targetEntries := fromUsed targetFree
      (capturedTargetNames sourceEntries bindings)
    (reifyOpenImages? CombinedLang targetEntries bindings
      sourceEntries).isSome = true := by
  let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
  let targetEntries := fromUsed targetFree
    (capturedTargetNames sourceEntries bindings)
  obtain ⟨plan, _, _, _, planReturned⟩ :=
    (checkedOpenAnswers_mem_iff sourceFree targetFree pattern sort concrete
      bindings).mp returned
  have admitted := (checkedPlanAnswersFromPattern_mem_iff sourceFree targetFree
    pattern plan concrete bindings).mp planReturned |>.2
  apply reifyOpenImages?_complete_of_images
  intro imageSort position
  let image := applyBindings bindings
    (.fvar (names sourceEntries imageSort position))
  obtain ⟨checked, compiledSome, _⟩ :=
    (checkBindingImage_iff targetFree bindings
      (names sourceEntries) imageSort position).mp
      ((checkBindingImages_iff_all targetFree bindings
        (contextSorts sourceEntries) (names sourceEntries)).mp admitted
        imageSort position)
  have compiled : compilePattern? image ≠ none := by
    intro rejected
    rw [rejected] at compiledSome
    simp at compiledSome
  exact reifyOpen?_complete (checkHasType_sound checked) compiled
    (by
      intro variableName membership variableSort assignment
      exact fromUsed_has_assigned_pair targetFree
        (capturedTargetNames sourceEntries bindings) variableName variableSort
        (capturedTargetNames_contains_image sourceEntries bindings
          imageSort position membership) assignment)

/-- A checked answer therefore has an actual computed simultaneous
substitution whose every image renders to the exact captured raw tree. -/
theorem checkedOpenAnswers_all_images_receipt
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) (sort : TypeExpr) (concrete : Pattern)
    (bindings : Bindings)
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete) :
    let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
    let targetEntries := fromUsed targetFree
      (capturedTargetNames sourceEntries bindings)
    ∃ sigma : Sub CombinedSignature
        (contextSorts sourceEntries) (contextSorts targetEntries),
      reifyOpenImages? CombinedLang targetEntries bindings sourceEntries =
        some sigma ∧
      ∀ imageSort (position : Var (contextSorts sourceEntries) imageSort),
        namedFirstOrderErase? (names targetEntries)
          (sigma imageSort position) =
            some (applyBindings bindings
              (.fvar (names sourceEntries imageSort position))) := by
  let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
  let targetEntries := fromUsed targetFree
    (capturedTargetNames sourceEntries bindings)
  have found := checkedOpenAnswers_all_images_compute sourceFree targetFree
    pattern sort concrete bindings returned
  change (reifyOpenImages? CombinedLang targetEntries bindings
    sourceEntries).isSome = true at found
  change ∃ sigma : Sub CombinedSignature (contextSorts sourceEntries)
      (contextSorts targetEntries),
    reifyOpenImages? CombinedLang targetEntries bindings sourceEntries =
      some sigma ∧
    ∀ imageSort (position : Var (contextSorts sourceEntries) imageSort),
      namedFirstOrderErase? (names targetEntries)
        (sigma imageSort position) =
          some (applyBindings bindings
            (.fvar (names sourceEntries imageSort position)))
  cases computed : reifyOpenImages? CombinedLang targetEntries bindings
      sourceEntries with
  | none => simp [computed] at found
  | some sigma =>
      exact ⟨sigma, rfl,
        reifyOpenImages?_named CombinedLang targetEntries bindings
          sourceEntries computed⟩

/-- An answer returned by the actual checked executor has a computed
intrinsic substitution whenever each captured image is a renamed free
variable. The finite gate supplies the target-sort checks needed by the
generic variable lookup. -/
theorem checkedOpenAnswers_variable_substitution_computes
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) (sort : TypeExpr) (concrete : Pattern)
    (bindings : Bindings)
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete)
    (variableImages : ∀ variableSort
      (position : Var
        (contextSorts (fromUsed sourceFree pattern.freeFvarNames)) variableSort),
      ∃ targetName,
        applyBindings bindings
          (.fvar (names (fromUsed sourceFree pattern.freeFvarNames)
            variableSort position)) = .fvar targetName) :
    (reifyVariableImages?
      (fromUsed targetFree
        (capturedTargetNames
          (fromUsed sourceFree pattern.freeFvarNames) bindings))
      bindings (fromUsed sourceFree pattern.freeFvarNames)).isSome = true := by
  obtain ⟨plan, _, _, _, planReturned⟩ :=
    (checkedOpenAnswers_mem_iff sourceFree targetFree pattern sort concrete bindings).mp
      returned
  have admitted := (checkedPlanAnswersFromPattern_mem_iff sourceFree targetFree
    pattern plan concrete bindings).mp planReturned |>.2
  exact reifyVariableImages?_complete_of_gate
    (fromUsed sourceFree pattern.freeFvarNames) targetFree bindings
    admitted variableImages

/-- Every returned answer has an intrinsic supported target and the same
meaning as the source in any combined reading. Source typing and compilation
are obtained from the executable entry point, not extra caller certificates. -/
theorem checkedOpenAnswers_denotes
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Δ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) {sort : TypeExpr}
    (targetResolves : ∀ {variableSort : TypeExpr} {variableName : String},
      targetFree variableName = some variableSort →
        ∃ position : Var Δ variableSort,
          targetNames variableSort position = variableName)
    (bindings : Bindings) (concrete : Pattern)
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete) :
    let entries := fromUsed sourceFree pattern.freeFvarNames
    ∃ (sigma : Sub CombinedSignature (contextSorts entries) Δ)
      (supported : ∀ variableSort
        (position : Var (contextSorts entries) variableSort),
        FirstOrder (sigma variableSort position))
      (term : Term CombinedSignature (contextSorts entries) sort)
      (fragment : FirstOrder term),
      namedErase (names entries) fragment = pattern ∧
      ∃ targetCertificate : FirstOrder (bind sigma term),
        namedErase targetNames targetCertificate = concrete ∧
          FirstOrder.denote reading environment targetCertificate =
            FirstOrder.denote reading
              (fun variableSort position => FirstOrder.denote reading environment
                (supported variableSort position)) fragment := by
  obtain ⟨plan, sourceChecked, _, compiled, planReturned⟩ :=
    (checkedOpenAnswers_mem_iff sourceFree targetFree pattern sort concrete bindings).mp
      returned
  exact checkedPlanAnswersFromPattern_denotes reading environment targetNames
    sourceFree targetFree pattern targetResolves sourceChecked plan compiled
    bindings concrete planReturned

/-- The fully context-derived semantic endpoint for the checked first-order
fragment. Source positions come from the source pattern; target positions
come from the names actually used by captured images. Successful executable
admission supplies both intrinsic receipts and their denotational equality,
without either source or target name-resolution premises. -/
theorem checkedOpenAnswers_denotes_canonical
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) {sort : TypeExpr}
    (bindings : Bindings) (concrete : Pattern)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts (fromUsed targetFree
        (capturedTargetNames
          (fromUsed sourceFree pattern.freeFvarNames) bindings))))
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete) :
    let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
    let targetEntries := fromUsed targetFree
      (capturedTargetNames sourceEntries bindings)
    ∃ (sigma : Sub CombinedSignature (contextSorts sourceEntries)
        (contextSorts targetEntries))
      (supported : ∀ variableSort
        (position : Var (contextSorts sourceEntries) variableSort),
        FirstOrder (sigma variableSort position))
      (term : Term CombinedSignature (contextSorts sourceEntries) sort)
      (fragment : FirstOrder term),
      namedErase (names sourceEntries) fragment = pattern ∧
      ∃ targetCertificate : FirstOrder (bind sigma term),
        namedErase (names targetEntries) targetCertificate = concrete ∧
          FirstOrder.denote reading environment targetCertificate =
            FirstOrder.denote reading
              (fun variableSort position => FirstOrder.denote reading environment
                (supported variableSort position)) fragment := by
  let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
  let targetEntries := fromUsed targetFree
    (capturedTargetNames sourceEntries bindings)
  obtain ⟨plan, sourceChecked, _, compiled, planReturned⟩ :=
    (checkedOpenAnswers_mem_iff sourceFree targetFree pattern sort concrete bindings).mp
      returned
  obtain ⟨ran, admitted⟩ :=
    (checkedPlanAnswersFromPattern_mem_iff sourceFree targetFree pattern plan
      concrete bindings).mp planReturned
  have matched : bindings ∈ matchPattern pattern concrete := by
    rw [← run_compilePattern? pattern concrete plan compiled]
    exact ran
  have sourceResolvesUsed : ∀ {variableName : String}
      {variableSort : TypeExpr},
      variableName ∈ pattern.freeFvarNames →
      sourceFree variableName = some variableSort →
        ∃ position : Var (contextSorts sourceEntries) variableSort,
          (names sourceEntries) variableSort position = variableName := by
    intro variableName variableSort membership assigned
    exact fromUsed_resolves sourceFree pattern.freeFvarNames membership assigned
  obtain ⟨sigma, supported, receipts⟩ :=
    checkedBindingImages_reify_canonical_target sourceEntries targetFree
      bindings admitted
  obtain ⟨term, fragment, sourceNamed, targetCertificate, targetNamed, value⟩ :=
    checkedOpen_match_denotes reading environment (names sourceEntries)
      (names targetEntries) sourceFree pattern sourceResolvesUsed sourceChecked
      (by simp [compiled]) bindings sigma supported receipts concrete matched
  exact ⟨sigma, supported, term, fragment, sourceNamed,
    targetCertificate, targetNamed, value⟩

/-- On the variable-image fragment, the semantic theorem uses an *actual
computed substitution* returned by `reifyVariableImages?`. The source and
final substituted-term receipts are still obtained by the existing
propositional first-order matcher theorem; this does not claim a general
executable constructor-tree reifier. -/
theorem checkedOpenAnswers_denotes_of_computed_variable_images
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) {sort : TypeExpr}
    (bindings : Bindings) (concrete : Pattern)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts (fromUsed targetFree
        (capturedTargetNames
          (fromUsed sourceFree pattern.freeFvarNames) bindings))))
    (receipt : SupportedSubstitution
      (fromUsed sourceFree pattern.freeFvarNames)
      (fromUsed targetFree (capturedTargetNames
        (fromUsed sourceFree pattern.freeFvarNames) bindings)))
    (computed : reifyVariableImages?
      (fromUsed targetFree (capturedTargetNames
        (fromUsed sourceFree pattern.freeFvarNames) bindings))
      bindings (fromUsed sourceFree pattern.freeFvarNames) = some receipt)
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete) :
    let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
    let targetEntries := fromUsed targetFree
      (capturedTargetNames sourceEntries bindings)
    ∃ (term : Term CombinedSignature (contextSorts sourceEntries) sort)
      (fragment : FirstOrder term),
      namedErase (names sourceEntries) fragment = pattern ∧
      ∃ targetCertificate : FirstOrder (bind receipt.1 term),
        namedErase (names targetEntries) targetCertificate = concrete ∧
          FirstOrder.denote reading environment targetCertificate =
            FirstOrder.denote reading
              (fun variableSort position => FirstOrder.denote reading environment
                (receipt.2 variableSort position)) fragment := by
  let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
  let targetEntries := fromUsed targetFree
    (capturedTargetNames sourceEntries bindings)
  obtain ⟨plan, sourceChecked, _, compiled, planReturned⟩ :=
    (checkedOpenAnswers_mem_iff sourceFree targetFree pattern sort concrete bindings).mp
      returned
  obtain ⟨ran, _⟩ :=
    (checkedPlanAnswersFromPattern_mem_iff sourceFree targetFree pattern plan
      concrete bindings).mp planReturned
  have matched : bindings ∈ matchPattern pattern concrete := by
    rw [← run_compilePattern? pattern concrete plan compiled]
    exact ran
  have sourceResolvesUsed : ∀ {variableName : String}
      {variableSort : TypeExpr},
      variableName ∈ pattern.freeFvarNames →
      sourceFree variableName = some variableSort →
        ∃ position : Var (contextSorts sourceEntries) variableSort,
          (names sourceEntries) variableSort position = variableName := by
    intro variableName variableSort membership assigned
    exact fromUsed_resolves sourceFree pattern.freeFvarNames membership assigned
  exact checkedOpen_match_denotes reading environment (names sourceEntries)
    (names targetEntries) sourceFree pattern sourceResolvesUsed sourceChecked
    (by simp [compiled]) bindings receipt.1 receipt.2
    (reifyVariableImages?_named targetEntries bindings sourceEntries computed)
    concrete matched

/-- The converse for the same checked open fragment: a supplied supported
intrinsic substitution with its raw binding receipts is discoverable by the
actual matcher, without a hand-supplied source certificate. Returned values
are constrained exactly on the source pattern's used names. -/
theorem checkedOpen_match_complete_for_substitution
    {Γ Δ : Ctx CombinedSignature}
    (sourceNames : (sort : TypeExpr) → Var Γ sort → String)
    (targetNames : (sort : TypeExpr) → Var Δ sort → String)
    (free : FreeTypeContext) (pattern : Pattern) {sort : TypeExpr}
    (resolvesUsed : ∀ {variableName : String} {variableSort : TypeExpr},
      variableName ∈ pattern.freeFvarNames →
      free variableName = some variableSort →
        ∃ position : Var Γ variableSort,
          sourceNames variableSort position = variableName)
    (checked : checkHasType CombinedLang free [] pattern sort = true)
    (compiled : compilePattern? pattern ≠ none)
    (bindings : Bindings)
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ variableSort (position : Var Γ variableSort),
      FirstOrder (sigma variableSort position))
    (variableReceipt : ∀ variableSort (position : Var Γ variableSort),
      applyBindings bindings (.fvar (sourceNames variableSort position)) =
        namedErase targetNames (supported variableSort position)) :
    ∃ (term : Term CombinedSignature Γ sort) (fragment : FirstOrder term)
      (returned : Bindings),
      namedErase sourceNames fragment = pattern ∧
      returned ∈ matchPattern pattern
        (namedErase targetNames
          (FirstOrder.substitute sigma supported fragment)) ∧
      BindingsValued returned (lookupOrFvar bindings) := by
  obtain ⟨term, fragment, sourceNamed⟩ :=
    checkedOpen_reifies_on_used_names sourceNames free pattern resolvesUsed checked compiled
  obtain ⟨returned, matched, valued⟩ :=
    matchPattern_namedErase_open_complete_for_substitution
      sourceNames targetNames bindings sigma supported variableReceipt fragment
  exact ⟨term, fragment, returned, sourceNamed,
    by simpa only [sourceNamed] using matched, valued⟩

private abbrev EvidenceHandleContext : Ctx CombinedSignature :=
  [.base "BinaryEvidence"]

private def evidenceHandleName :
    (sort : TypeExpr) → Var EvidenceHandleContext sort → String :=
  fun _ position => match position with
    | .zero => "e"
    | .succ earlier => nomatch earlier

private def noTargetNames :
    (sort : TypeExpr) → Var ([] : Ctx CombinedSignature) sort → String :=
  fun _ position => nomatch position

private def evidenceHandleFree : FreeTypeContext :=
  fun variableName =>
    if variableName == "e" then some (.base "BinaryEvidence") else none

/-- The finite target-image gate actually runs on a successful Evidence
capture. No per-variable certificate is supplied to the gate. -/
theorem evidence_capture_image_gate_passes :
    checkBindingImages FreeTypeContext.empty [("e", pEvidenceZero)]
      EvidenceHandleContext evidenceHandleName = true := by
  simp [checkBindingImages, checkBindingImage, evidenceHandleName,
    checkUsedFreeSortsDeclared, pEvidenceZero, applyBindings,
    FreeTypeContext.empty, Pattern.freeFvarNames]
  exact closed_evidence_checks_pass

/-- The actual executable plan retains the well-sorted Evidence capture. -/
theorem checked_evidence_plan_returns_capture :
    checkedPlanAnswers FreeTypeContext.empty evidenceHandleName
      (.metavariable "e") pEvidenceZero = [[("e", pEvidenceZero)]] := by
  simp [checkedPlanAnswers, PatternPlan.run, evidence_capture_image_gate_passes]

private def evidenceTree : Pattern :=
  pCombine pEvidenceZero pEvidenceZero

private def evidenceTreeBindings : Bindings :=
  [("e", evidenceTree)]

private theorem evidence_tree_target_checks :
    checkHasType CombinedLang FreeTypeContext.empty [] evidenceTree
        (.base "BinaryEvidence") = true ∧
      (compilePattern? evidenceTree).isSome = true := by
  decide +kernel

private theorem evidence_tree_image_gate_passes :
    checkBindingImages FreeTypeContext.empty evidenceTreeBindings
      EvidenceHandleContext evidenceHandleName = true := by
  simp [checkBindingImages, checkBindingImage, evidenceHandleName,
    evidenceTreeBindings, checkUsedFreeSortsDeclared, evidenceTree,
    pCombine, pEvidenceZero, applyBindings, FreeTypeContext.empty,
    Pattern.freeFvarNames]
  exact evidence_tree_target_checks

/-- The actual checked matcher accepts a compound constructor image for its
open Evidence handle. This exercises more than variable-only renaming. -/
theorem checked_evidence_tree_answers_returns_capture :
    evidenceTreeBindings ∈
      checkedOpenAnswers evidenceHandleFree FreeTypeContext.empty
        (.fvar "e") (.base "BinaryEvidence") evidenceTree := by
  apply (checkedOpenAnswers_mem_iff evidenceHandleFree FreeTypeContext.empty
    (.fvar "e") (.base "BinaryEvidence") evidenceTree
    evidenceTreeBindings).mpr
  refine ⟨.metavariable "e", ?_, ?_, rfl, ?_⟩
  · decide +kernel
  · simp [checkUsedFreeSortsDeclared, evidenceHandleFree, CombinedLang,
      combined_types, TypeDecl.plain, Pattern.freeFvarNames]
  · unfold checkedPlanAnswersFromPattern
    have sourceEntries : fromUsed evidenceHandleFree
        (Pattern.fvar "e").freeFvarNames =
          [("e", .base "BinaryEvidence")] := by
      simp [fromUsed, evidenceHandleFree, Pattern.freeFvarNames]
    have named : names [("e", .base "BinaryEvidence")] =
        evidenceHandleName := by
      funext variableSort position
      cases position with
      | zero => rfl
      | succ earlier => nomatch earlier
    change evidenceTreeBindings ∈ checkedPlanAnswers FreeTypeContext.empty
      (names (fromUsed evidenceHandleFree
        (Pattern.fvar "e").freeFvarNames)) (.metavariable "e") evidenceTree
    rw [sourceEntries]
    rw [named]
    apply (checkedPlanAnswers_mem_iff FreeTypeContext.empty evidenceHandleName
      (.metavariable "e") evidenceTree evidenceTreeBindings).mpr
    exact ⟨by simp [PatternPlan.run, evidenceTreeBindings],
      evidence_tree_image_gate_passes⟩

/-- The compound-image acceptance test with its concrete public inputs,
so downstream dependent-family consumers need no private example names. -/
theorem checked_compound_evidence_explicit :
    [("e", pCombine pEvidenceZero pEvidenceZero)] ∈
      checkedOpenAnswers
        (FreeTypeContext.ofList [("e", .base "BinaryEvidence")])
        FreeTypeContext.empty (.fvar "e") (.base "BinaryEvidence")
        (pCombine pEvidenceZero pEvidenceZero) := by
  have freeEq : evidenceHandleFree =
      FreeTypeContext.ofList [("e", .base "BinaryEvidence")] := by
    funext variableName
    by_cases equal : variableName = "e"
    · subst variableName
      simp [evidenceHandleFree, FreeTypeContext.ofList]
    · simp [evidenceHandleFree, FreeTypeContext.ofList, beq_iff_eq,
        equal, Ne.symm equal]
  rw [← freeEq]
  simpa [evidenceTreeBindings, evidenceTree] using
    checked_evidence_tree_answers_returns_capture

/-- That accepted compound capture computes an intrinsic substitution from
the authored Combine and EvidenceZero declarations, with exact raw erasure. -/
theorem checked_evidence_tree_computes_intrinsic_substitution :
    let sourceEntries := fromUsed evidenceHandleFree
      (Pattern.fvar "e").freeFvarNames
    let targetEntries := fromUsed FreeTypeContext.empty
      (capturedTargetNames sourceEntries evidenceTreeBindings)
    ∃ sigma : Sub CombinedSignature (contextSorts sourceEntries)
        (contextSorts targetEntries),
      reifyOpenImages? CombinedLang targetEntries evidenceTreeBindings
        sourceEntries = some sigma ∧
      ∀ imageSort (position : Var (contextSorts sourceEntries) imageSort),
        namedFirstOrderErase? (names targetEntries)
          (sigma imageSort position) =
            some (applyBindings evidenceTreeBindings
              (.fvar (names sourceEntries imageSort position))) := by
  exact checkedOpenAnswers_all_images_receipt evidenceHandleFree
    FreeTypeContext.empty (.fvar "e") (.base "BinaryEvidence")
    evidenceTree evidenceTreeBindings
    checked_evidence_tree_answers_returns_capture

/-- The generic open codec rejects an undeclared constructor label and a
cross-sort source image; neither can masquerade as a typed WM capture. -/
theorem generic_open_reifier_negative_controls :
    (reifyOpen? CombinedLang [] (.apply "UnknownWMConstructor" [])
      (.base "BinaryEvidence")).isSome = false ∧
    (reifyOpenImages? CombinedLang []
      [("w", pEvidenceZero)] [("w", .base "State")]).isSome = false := by
  decide +kernel

private def openHandlePlan : PatternPlan :=
  .application "Extract" [.metavariable "w", .metavariable "q"]

private def openHandleBindings : Bindings :=
  [("q", .fvar "q2"), ("w", .fvar "w2")]

/-- Renamed open State and Query handles pass the same finite image gate;
the target is genuinely open rather than a closed Evidence-only capture. -/
theorem open_handle_image_gate_passes :
    checkBindingImages openTargetFree openHandleBindings
      OpenHandleContext openHandleNames = true := by
  simp [checkBindingImages, checkBindingImage, openHandleNames,
    openHandleBindings, openTargetFree, checkUsedFreeSortsDeclared,
    Pattern.freeFvarNames, CombinedLang, combined_types, TypeDecl.plain,
    applyBindings]
  all_goals decide +kernel

/-- The authored checker accepts the open source at Evidence sort, and the
existing first-order compiler produces this exact executable plan. -/
theorem open_handle_source_checks_and_compiles :
    checkHasType CombinedLang openSourceFree []
      (pExtract (.fvar "w") (.fvar "q")) (.base "BinaryEvidence") = true ∧
    compilePattern? (pExtract (.fvar "w") (.fvar "q")) =
      some openHandlePlan := by
  constructor
  · decide +kernel
  · rfl

/-- The same open source uses only base sorts declared by the authored
combined WM language. -/
theorem open_handle_source_declared :
    checkUsedFreeSortsDeclared CombinedLang openSourceFree
      (pExtract (.fvar "w") (.fvar "q")) = true := by
  simp [checkUsedFreeSortsDeclared, openSourceFree, pExtract,
    Pattern.freeFvarNames, CombinedLang, combined_types, TypeDecl.plain]

/-- Executing and filtering the actual compiled plan retains the renamed,
well-sorted open State/Query capture. -/
theorem checked_open_handle_plan_returns_capture :
    openHandleBindings ∈ checkedPlanAnswers openTargetFree openHandleNames
      openHandlePlan (pExtract (.fvar "w2") (.fvar "q2")) := by
  apply (checkedPlanAnswers_mem_iff openTargetFree openHandleNames
    openHandlePlan (pExtract (.fvar "w2") (.fvar "q2")) openHandleBindings).mpr
  exact ⟨by decide +kernel, open_handle_image_gate_passes⟩

/-- The source-context constructor computes exactly the two open sorts and
names used by this State/Query example; it does not include spare slots. -/
theorem open_handle_canonical_context :
    fromUsed openSourceFree
      (pExtract (.fvar "w") (.fvar "q")).freeFvarNames =
        [("w", .base "State"), ("q", .base "Query")] := by
  simp [fromUsed, openSourceFree, pExtract, Pattern.freeFvarNames]

/-- The two open source handles obtain computed intrinsic variable receipts;
asking for the Query sort at the State handle fails. -/
theorem open_handle_variable_receipt_controls :
    (reifyOpenVariable?
      (fromUsed openSourceFree
        (pExtract (.fvar "w") (.fvar "q")).freeFvarNames)
      "w" (.base "State")).isSome = true ∧
    (reifyOpenVariable?
      (fromUsed openSourceFree
        (pExtract (.fvar "w") (.fvar "q")).freeFvarNames)
      "q" (.base "Query")).isSome = true ∧
    (reifyOpenVariable?
      (fromUsed openSourceFree
        (pExtract (.fvar "w") (.fvar "q")).freeFvarNames)
      "w" (.base "Query")).isSome = false := by
  rw [open_handle_canonical_context]
  decide +kernel

/-- The same checked plan answer is retained when source context and names
are computed from the authored source pattern rather than supplied manually. -/
theorem checked_open_handle_canonical_plan_returns_capture :
    openHandleBindings ∈
      checkedPlanAnswersFromPattern openSourceFree openTargetFree
        (pExtract (.fvar "w") (.fvar "q")) openHandlePlan
        (pExtract (.fvar "w2") (.fvar "q2")) := by
  unfold checkedPlanAnswersFromPattern
  rw [open_handle_canonical_context]
  change openHandleBindings ∈ checkedPlanAnswers openTargetFree openHandleNames
    openHandlePlan (pExtract (.fvar "w2") (.fvar "q2"))
  exact checked_open_handle_plan_returns_capture

/-- The source-typed, compiled, target-filtered entry point keeps the same
open State/Query answer without requiring a preaccepted plan argument. -/
theorem checked_open_handle_answers_returns_capture :
    openHandleBindings ∈
      checkedOpenAnswers openSourceFree openTargetFree
        (pExtract (.fvar "w") (.fvar "q")) (.base "BinaryEvidence")
        (pExtract (.fvar "w2") (.fvar "q2")) := by
  apply (checkedOpenAnswers_mem_iff openSourceFree openTargetFree
    (pExtract (.fvar "w") (.fvar "q")) (.base "BinaryEvidence")
    (pExtract (.fvar "w2") (.fvar "q2")) openHandleBindings).mpr
  exact ⟨openHandlePlan, open_handle_source_checks_and_compiles.1,
    open_handle_source_declared, open_handle_source_checks_and_compiles.2,
    checked_open_handle_canonical_plan_returns_capture⟩

/-- The target context derived from this retained answer has exactly the
renamed State and Query handles, in source-position order. -/
theorem open_handle_canonical_target_context :
    fromUsed openTargetFree
      (capturedTargetNames
        (fromUsed openSourceFree
          (pExtract (.fvar "w") (.fvar "q")).freeFvarNames)
        openHandleBindings) =
      [("w2", .base "State"), ("q2", .base "Query")] := by
  rw [open_handle_canonical_context]
  simp [capturedTargetNames, openHandleBindings, openTargetFree,
    applyBindings, Pattern.freeFvarNames, fromUsed]

/-- The actual renamed State/Query answer computes a supported intrinsic
substitution across both open source positions. This is not the general
constructor-tree reifier. -/
theorem open_handle_variable_substitution_computes :
    (reifyVariableImages?
      (fromUsed openTargetFree
        (capturedTargetNames
          (fromUsed openSourceFree
            (pExtract (.fvar "w") (.fvar "q")).freeFvarNames)
          openHandleBindings))
      openHandleBindings
      (fromUsed openSourceFree
        (pExtract (.fvar "w") (.fvar "q")).freeFvarNames)).isSome = true := by
  rw [open_handle_canonical_target_context, open_handle_canonical_context]
  decide +kernel

/-- A missing target variable and a constructor-tree image are both outside
the executable variable-only substitution fragment. The latter can still be
accepted by the more general checked image gate. -/
theorem variable_substitution_negative_controls :
    (reifyVariableImages? [] [("w", .fvar "w2")]
      [("w", .base "State")]).isSome = false ∧
    (reifyVariableImages?
      [("w2", .base "State"), ("w3", .base "State")]
      [("w", pRevise (.fvar "w2") (.fvar "w3"))]
      [("w", .base "State")]).isSome = false := by
  decide +kernel

/-- A compiled, checked open WM observation with renamed State/Query handles
has a supported intrinsic target and preserves its value in every combined
reading. No target `FirstOrder` certificate is supplied by the caller. -/
theorem checked_open_handle_plan_denotes
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) OpenHandleContext) :
    ∃ (sigma : Sub CombinedSignature OpenHandleContext OpenHandleContext)
      (supported : ∀ variableSort (position : Var OpenHandleContext variableSort),
        FirstOrder (sigma variableSort position))
      (term : Term CombinedSignature OpenHandleContext (.base "BinaryEvidence"))
      (fragment : FirstOrder term),
      namedErase openHandleNames fragment =
        pExtract (.fvar "w") (.fvar "q") ∧
      ∃ targetCertificate : FirstOrder (bind sigma term),
        namedErase openTargetNames targetCertificate =
          pExtract (.fvar "w2") (.fvar "q2") ∧
          FirstOrder.denote reading environment targetCertificate =
            FirstOrder.denote reading
              (fun variableSort position => FirstOrder.denote reading environment
                (supported variableSort position)) fragment := by
  refine checkedPlanAnswers_denotes reading environment openHandleNames
    openTargetNames openSourceFree openTargetFree
    (pExtract (.fvar "w") (.fvar "q")) ?_ ?_
    open_handle_source_checks_and_compiles.1 openHandlePlan
    open_handle_source_checks_and_compiles.2 openHandleBindings
    (pExtract (.fvar "w2") (.fvar "q2"))
    checked_open_handle_plan_returns_capture
  · intro variableName variableSort _ assigned
    exact openSourceResolves assigned
  · intro variableSort variableName assigned
    exact openTargetResolves assigned

/-- A real matcher capture of the closed evidence constant passes the target
image checks and therefore obtains a supported intrinsic substitution and
the same observation value in every combined reading. -/
theorem checked_evidence_capture_denotes
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) []) :
    ∃ (sigma : Sub CombinedSignature EvidenceHandleContext [])
      (supported : ∀ variableSort (position : Var EvidenceHandleContext variableSort),
        FirstOrder (sigma variableSort position))
      (term : Term CombinedSignature EvidenceHandleContext (.base "BinaryEvidence"))
      (fragment : FirstOrder term),
      namedErase evidenceHandleName fragment = .fvar "e" ∧
      ∃ targetCertificate : FirstOrder (bind sigma term),
        namedErase noTargetNames targetCertificate = pEvidenceZero ∧
          FirstOrder.denote reading environment targetCertificate =
            FirstOrder.denote reading
              (fun variableSort position => FirstOrder.denote reading environment
                (supported variableSort position)) fragment := by
  refine checkedOpen_match_denotes_of_gate reading environment
    evidenceHandleName noTargetNames evidenceHandleFree FreeTypeContext.empty
    (.fvar "e") ?_ ?_ ?_ ?_ [("e", pEvidenceZero)] pEvidenceZero ?_ ?_
  · intro variableName variableSort _ lookup
    have named : variableName = "e" := by
      by_contra different
      simp [evidenceHandleFree, different] at lookup
    subst variableName
    have sorted : variableSort = .base "BinaryEvidence" := by
      simpa [evidenceHandleFree] using lookup.symm
    subst variableSort
    exact ⟨.zero, rfl⟩
  · intro variableSort variableName lookup
    simp [FreeTypeContext.empty] at lookup
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact evidence_capture_image_gate_passes

private def extraEvidenceContextNames :
    (sort : TypeExpr) →
      Var ([.base "BinaryEvidence", .base "State"] : Ctx CombinedSignature) sort →
        String :=
  fun _ position => match position with
    | .zero => "e"
    | .succ .zero => "unusedState"
    | .succ (.succ earlier) => nomatch earlier

private theorem evidence_canonical_context :
    fromUsed evidenceHandleFree ((.fvar "e") : Pattern).freeFvarNames =
      [("e", .base "BinaryEvidence")] := by
  simp [fromUsed, evidenceHandleFree, Pattern.freeFvarNames]

/-- An Evidence handle cannot be admitted by the executable entry point at
the wrong source sort, even if its raw matcher plan could bind a term. -/
theorem checked_evidence_wrong_source_sort_returns_no_answers :
    checkedOpenAnswers evidenceHandleFree FreeTypeContext.empty
      (.fvar "e") (.base "State") pEvidenceZero = [] := by
  have rejected : checkHasType CombinedLang evidenceHandleFree []
      (.fvar "e") (.base "State") = false := by
    decide +kernel
  simp [checkedOpenAnswers, rejected]

/-- A checker-accepted external sort with no authored declaration is not
silently admitted by the executable entry point. -/
theorem checked_undeclared_source_sort_returns_no_answers :
    checkedOpenAnswers
      (FreeTypeContext.ofList [("ghost", .base "NotDeclared")])
      FreeTypeContext.empty (.fvar "ghost") (.base "NotDeclared")
      (.fvar "ghost") = [] := by
  simp [checkedOpenAnswers, undeclared_free_sort_rejected]

/-- The older caller-supplied context gate can reject an otherwise valid
capture because of one unused, unbound ambient State position. Constructing
the context from the source pattern retains the same Evidence answer. -/
theorem unused_context_gate_rejects_but_canonical_accepts :
    checkBindingImages FreeTypeContext.empty [("e", pEvidenceZero)]
      ([.base "BinaryEvidence", .base "State"] : Ctx CombinedSignature)
      extraEvidenceContextNames = false ∧
    [("e", pEvidenceZero)] ∈
      checkedPlanAnswersFromPattern evidenceHandleFree FreeTypeContext.empty
        (.fvar "e") (.metavariable "e") pEvidenceZero := by
  constructor
  · simp [checkBindingImages, checkBindingImage, extraEvidenceContextNames,
      applyBindings, checkUsedFreeSortsDeclared, Pattern.freeFvarNames,
      FreeTypeContext.empty]
  · apply (checkedPlanAnswersFromPattern_mem_iff evidenceHandleFree
      FreeTypeContext.empty (.fvar "e") (.metavariable "e") pEvidenceZero
      [("e", pEvidenceZero)]).mpr
    constructor
    · decide +kernel
    · rw [evidence_canonical_context]
      change checkBindingImages FreeTypeContext.empty
        [("e", pEvidenceZero)] EvidenceHandleContext evidenceHandleName = true
      exact evidence_capture_image_gate_passes

/-- The raw matcher accepts a State expression for an Evidence handle, but
the target image checker rejects that capture at its requested sort. -/
theorem cross_sort_capture_rejected_by_image_check :
    matchPattern (.fvar "e")
      (pRevise (.fvar "w1") (.fvar "w2")) ≠ [] ∧
    checkHasType CombinedLang
      (FreeTypeContext.ofList
        [("w1", .base "State"), ("w2", .base "State")]) []
      (pRevise (.fvar "w1") (.fvar "w2"))
      (.base "BinaryEvidence") = false := by
  constructor <;> decide +kernel

/-- The same bad Evidence capture is rejected by the runnable finite gate,
even though untyped structural matching succeeds. -/
theorem cross_sort_capture_image_gate_rejects :
    matchPattern (.fvar "e")
      (pRevise (.fvar "w1") (.fvar "w2")) ≠ [] ∧
    checkBindingImages
      (FreeTypeContext.ofList
        [("w1", .base "State"), ("w2", .base "State")])
      [("e", pRevise (.fvar "w1") (.fvar "w2"))]
      EvidenceHandleContext evidenceHandleName = false := by
  constructor <;> decide +kernel

/-- The same compiled plan does return the ill-sorted binding before the gate,
but the checked executor drops it. -/
theorem checked_evidence_plan_rejects_cross_sort :
    (.metavariable "e" : PatternPlan).run
      (pRevise (.fvar "w1") (.fvar "w2")) =
        [[("e", pRevise (.fvar "w1") (.fvar "w2"))]] ∧
    checkedPlanAnswers
      (FreeTypeContext.ofList
        [("w1", .base "State"), ("w2", .base "State")])
      evidenceHandleName (.metavariable "e")
      (pRevise (.fvar "w1") (.fvar "w2")) = [] := by
  constructor
  · rfl
  · simp [checkedPlanAnswers, PatternPlan.run,
      cross_sort_capture_image_gate_rejects.2]

#print axioms typedOpen_reifies
#print axioms checkUsedFreeSortsDeclared_iff
#print axioms checkedOpen_reifies
#print axioms checkedOpen_reifies_on_used_names
#print axioms open_extract_checked_compiled_reifies
#print axioms externally_assigned_sort_checks
#print axioms open_extract_used_sorts_declared
#print axioms undeclared_free_sort_rejected
#print axioms checkedOpen_match_denotes
#print axioms checkedOpen_match_complete_for_substitution
#print axioms checkedBindingImages_reify
#print axioms checkBindingImage_iff
#print axioms checkBindingImages_iff_all
#print axioms checkedBindingImages_reify_of_gate
#print axioms capturedTargetNames_contains_image
#print axioms checkedBindingImages_reify_canonical_target
#print axioms checkBindingImages_used_sorts_declared
#print axioms checkedOpen_match_denotes_of_checked_images
#print axioms checkedOpen_match_denotes_of_gate
#print axioms checkedPlanAnswers_mem_iff
#print axioms checkedPlanAnswers_denotes
#print axioms checkedOpen_reifies_canonical
#print axioms reifyOpenVariable?_named
#print axioms reifyOpenVariable?_fromUsed_complete
#print axioms reifyVariableImages?_named
#print axioms reifyVariableImages?_complete_of_resolved
#print axioms reifyVariableImages?_complete_of_gate
#print axioms checkedOpenAnswers_variable_substitution_computes
#print axioms checkedOpenAnswers_denotes_of_computed_variable_images
#print axioms checkedPlanAnswersFromPattern_denotes
#print axioms checkedOpenAnswers_mem_iff
#print axioms checkedOpenAnswers_denotes
#print axioms checkedOpenAnswers_denotes_canonical
#print axioms evidence_capture_image_gate_passes
#print axioms checked_evidence_plan_returns_capture
#print axioms open_handle_image_gate_passes
#print axioms open_handle_source_checks_and_compiles
#print axioms open_handle_source_declared
#print axioms checked_open_handle_plan_returns_capture
#print axioms checked_open_handle_canonical_plan_returns_capture
#print axioms open_handle_variable_receipt_controls
#print axioms checked_open_handle_answers_returns_capture
#print axioms open_handle_canonical_target_context
#print axioms open_handle_variable_substitution_computes
#print axioms variable_substitution_negative_controls
#print axioms checked_open_handle_plan_denotes
#print axioms checked_evidence_capture_denotes
#print axioms cross_sort_capture_rejected_by_image_check
#print axioms cross_sort_capture_image_gate_rejects
#print axioms checked_evidence_plan_rejects_cross_sort
#print axioms unused_context_gate_rejects_but_canonical_accepts
#print axioms checked_evidence_wrong_source_sort_returns_no_answers
#print axioms checked_undeclared_source_sort_returns_no_answers

end Mettapedia.OSLF.Framework.WMCalculusCombinedOpenReification
