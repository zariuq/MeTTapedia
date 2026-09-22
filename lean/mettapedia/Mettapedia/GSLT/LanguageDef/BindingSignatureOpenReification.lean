import Mettapedia.GSLT.LanguageDef.BindingSignatureReification
import Mettapedia.GSLT.LanguageDef.NamedFreeContext
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Open first-order reification from authored declarations

An open constructor pattern uses named free variables, while an intrinsic
binding term uses sorted context positions. This module searches the existing
language declarations and a finite named context. It neither introduces a
second constructor inventory nor interprets binders or collections as
first-order constructors.
-/

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.OpenReification

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.Reification
open Mettapedia.GSLT.LanguageDef.NamedFreeContext
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

set_option autoImplicit false

mutual
  /-- Render precisely the variable-and-simple-constructor fragment with
  explicit names for the free context positions. -/
  def namedFirstOrderErase? {language : LanguageDef} {Γ : Ctx (signatureOf language)}
      (names : (sort : TypeExpr) → Var Γ sort → String) :
      {sort : TypeExpr} → Term (signatureOf language) Γ sort → Option Pattern
    | _, .var position => some (.fvar (names _ position))
    | _, .op operator arguments =>
        match operator with
        | .constructor rule _ _ scopes =>
            (namedFirstOrderEraseArguments? names scopes arguments).map
              (.apply rule.label)
        | _ => none

  /-- Render only rows whose original declaration uses ordinary, nonbinding
  parameters. Every argument must itself be in the same first-order fragment. -/
  def namedFirstOrderEraseArguments? {language : LanguageDef}
      {Γ : Ctx (signatureOf language)}
      (names : (sort : TypeExpr) → Var Γ sort → String) :
      {parameters : List TermParam} →
      {arity : List (List TypeExpr × TypeExpr)} →
      ParameterScopes parameters arity →
      Args (signatureOf language) arity Γ → Option (List Pattern)
    | _, _, .nil, .nil => some []
    | _, _, .cons scope scopes, .cons head tail =>
        match scope with
        | .simple _ _ => do
            let first ← namedFirstOrderErase? names head
            let rest ← namedFirstOrderEraseArguments? names scopes tail
            pure (first :: rest)
        | _ => none
end

/-- The generic renderer follows an authored two-slot simple-parameter row
without inspecting the spelling of either result sort. -/
theorem namedFirstOrderEraseArguments?_simple_pair
    {language : LanguageDef} {Γ : Ctx (signatureOf language)}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (firstName secondName : String) (firstSort secondSort : TypeExpr)
    (first : Term (signatureOf language) Γ firstSort)
    (second : Term (signatureOf language) Γ secondSort) :
    namedFirstOrderEraseArguments? names
        (.cons (.simple firstName firstSort)
          (.cons (.simple secondName secondSort) .nil))
        (.cons first (.cons second .nil)) =
      (namedFirstOrderErase? names first).bind fun firstPattern =>
        (namedFirstOrderErase? names second).map fun secondPattern =>
          [firstPattern, secondPattern] := by
  cases hfirst : namedFirstOrderErase? names first <;>
    cases hsecond : namedFirstOrderErase? names second <;>
      simp [namedFirstOrderEraseArguments?, hfirst, hsecond, Option.bind, Option.map]

/-- The same row calculation for one authored three-slot constructor. -/
theorem namedFirstOrderEraseArguments?_simple_triple
    {language : LanguageDef} {Γ : Ctx (signatureOf language)}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    (firstName secondName thirdName : String)
    (firstSort secondSort thirdSort : TypeExpr)
    (first : Term (signatureOf language) Γ firstSort)
    (second : Term (signatureOf language) Γ secondSort)
    (third : Term (signatureOf language) Γ thirdSort) :
    namedFirstOrderEraseArguments? names
        (.cons (.simple firstName firstSort)
          (.cons (.simple secondName secondSort)
            (.cons (.simple thirdName thirdSort) .nil)))
        (.cons first (.cons second (.cons third .nil))) =
      (namedFirstOrderErase? names first).bind fun firstPattern =>
        (namedFirstOrderErase? names second).bind fun secondPattern =>
          (namedFirstOrderErase? names third).map fun thirdPattern =>
            [firstPattern, secondPattern, thirdPattern] := by
  cases hfirst : namedFirstOrderErase? names first <;>
    cases hsecond : namedFirstOrderErase? names second <;>
      cases hthird : namedFirstOrderErase? names third <;>
        simp [namedFirstOrderEraseArguments?, hfirst, hsecond, hthird,
          Option.bind, Option.map]

/-- A typed row reconstructed from the existing parameter declarations in
one arbitrary intrinsic free context. -/
structure OpenReifiedArguments (language : LanguageDef)
    (Γ : Ctx (signatureOf language)) (parameters : List TermParam) where
  arity : List (List TypeExpr × TypeExpr)
  scopes : ParameterScopes parameters arity
  arguments : Args (signatureOf language) arity Γ

/- Intrinsic evidence that a term uses only variables and authored ordinary
constructors with nonbinding parameters. This is a syntactic certificate,
not an interpretation of those constructors in a particular world model. -/
mutual
  inductive OpenFirstOrder (language : LanguageDef) :
      {Γ : Ctx (signatureOf language)} → {sort : TypeExpr} →
        Term (signatureOf language) Γ sort → Type where
    | variable {Γ : Ctx (signatureOf language)} {sort : TypeExpr}
        (position : Var Γ sort) : OpenFirstOrder language (.var position)
    | constructor {Γ : Ctx (signatureOf language)}
        (rule : GrammarRule) (member : rule ∈ language.terms)
        (ordinary : ¬ UsesBareCollection rule)
        {arity : List (List TypeExpr × TypeExpr)}
        (scopes : ParameterScopes rule.params arity)
        (arguments : Args (signatureOf language) arity Γ)
        (supported : OpenFirstOrderArguments language scopes arguments) :
        OpenFirstOrder language
          (.op (.constructor rule member ordinary scopes) arguments)

  /-- A row contains only ordinary, nonbinding parameters, and each child
term has the same first-order certificate. -/
  inductive OpenFirstOrderArguments (language : LanguageDef) :
      {Γ : Ctx (signatureOf language)} →
      {parameters : List TermParam} →
      {arity : List (List TypeExpr × TypeExpr)} →
      ParameterScopes parameters arity →
      Args (signatureOf language) arity Γ → Type where
    | nil {Γ : Ctx (signatureOf language)} :
        OpenFirstOrderArguments language .nil .nil
    | cons {Γ : Ctx (signatureOf language)}
        (name : String) (sort : TypeExpr)
        {parameters : List TermParam}
        {arity : List (List TypeExpr × TypeExpr)}
        (scopes : ParameterScopes parameters arity)
        (head : Term (signatureOf language) Γ sort)
        (tail : Args (signatureOf language) arity Γ)
        (headSupported : OpenFirstOrder language head)
        (tailSupported : OpenFirstOrderArguments language scopes tail) :
        OpenFirstOrderArguments language
          (.cons (.simple name sort) scopes) (.cons head tail)
end

/-- Test a retained authored declaration using recursive argument search. -/
def openConstructorCandidate? (language : LanguageDef)
    {Γ : Ctx (signatureOf language)}
    (label : String) (type : TypeExpr)
    (arguments : ∀ parameters, Option (OpenReifiedArguments language Γ parameters))
    (rule : {rule : GrammarRule // rule ∈ language.terms}) :
    Option (Term (signatureOf language) Γ type) :=
  if rule.val.label = label then
    if sameType : .base rule.val.category = type then
      if ordinaryCheck : usesBareCollection? rule.val = false then
        let ordinary : ¬ UsesBareCollection rule.val := fun bare => by
          have checked := (usesBareCollection?_eq_true_iff rule.val).mpr bare
          rw [ordinaryCheck] at checked
          cases checked
        (arguments rule.val.params).map fun receipt =>
          sameType ▸ Term.op
            (Operator.constructor rule.val rule.property ordinary receipt.scopes)
            receipt.arguments
      else none
    else none
  else none

mutual
  /-- Compute an intrinsic open first-order term by looking up named free
  positions and searching the original constructor declarations. -/
  def reifyOpen? (language : LanguageDef)
      (entries : List (String × TypeExpr))
      (pattern : Pattern) (type : TypeExpr) :
      Option (Term (signatureOf language) (contextSorts entries) type) :=
    match pattern with
    | .fvar name =>
        (lookupPosition? entries name type).map Term.var
    | .apply label arguments =>
        language.terms.attach.findSome?
          (openConstructorCandidate? language label type
            (fun parameters => reifyOpenArguments? language entries arguments parameters))
    | _ => none
  termination_by sizeOf pattern
  decreasing_by simp_wf

  /-- Reify a first-order argument row using only simple authored
  parameters; higher-order parameters remain outside this codec. -/
  def reifyOpenArguments? (language : LanguageDef)
      (entries : List (String × TypeExpr))
      (patterns : List Pattern) (parameters : List TermParam) :
      Option (OpenReifiedArguments language (contextSorts entries) parameters) :=
    match patterns, parameters with
    | [], [] => some ⟨[], .nil, .nil⟩
    | pattern :: patterns, .simple name type :: parameters => do
        let head ← reifyOpen? language entries pattern type
        let tail ← reifyOpenArguments? language entries patterns parameters
        pure ⟨([], type) :: tail.arity,
          .cons (.simple name type) tail.scopes, .cons head tail.arguments⟩
    | _, _ => none
  termination_by sizeOf patterns
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

theorem namedFirstOrderErase?_sort_cast {language : LanguageDef}
    {Γ : Ctx (signatureOf language)}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    {first second : TypeExpr} (same : first = second)
    (term : Term (signatureOf language) Γ first) :
    namedFirstOrderErase? names (same ▸ term) =
      namedFirstOrderErase? names term := by
  subst second
  rfl

/-- One accepted declaration preserves the exact named constructor pattern
when its recursively reified arguments do. -/
theorem openConstructorCandidate?_named
    {language : LanguageDef} {Γ : Ctx (signatureOf language)}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    {label : String} {type : TypeExpr} {patterns : List Pattern}
    {arguments : ∀ parameters, Option (OpenReifiedArguments language Γ parameters)}
    (roundtrip : ∀ parameters receipt, arguments parameters = some receipt →
      namedFirstOrderEraseArguments? names receipt.scopes receipt.arguments =
        some patterns)
    {rule : {rule : GrammarRule // rule ∈ language.terms}}
    {term : Term (signatureOf language) Γ type}
    (accepted : openConstructorCandidate? language label type arguments rule =
      some term) :
    namedFirstOrderErase? names term = some (.apply label patterns) := by
  unfold openConstructorCandidate? at accepted
  split at accepted
  · rename_i sameLabel
    split at accepted
    · rename_i sameType
      split at accepted
      · rename_i ordinary
        cases elaborated : arguments rule.val.params with
        | none => simp [elaborated] at accepted
        | some receipt =>
            simp only [elaborated, Option.map_some, Option.some.injEq] at accepted
            subst term
            rw [namedFirstOrderErase?_sort_cast]
            simp only [namedFirstOrderErase?]
            rw [roundtrip _ _ elaborated, sameLabel]
            rfl
      · simp at accepted
    · simp at accepted
  · simp at accepted

/-- A successful declaration candidate retains the ordinary-constructor
certificate supplied by its recursively reified argument row. -/
def openConstructorCandidate?_supported
    {language : LanguageDef} {Γ : Ctx (signatureOf language)}
    (label : String) (type : TypeExpr)
    (arguments : ∀ parameters,
      Option (OpenReifiedArguments language Γ parameters))
    (supported : ∀ parameters
      (receipt : OpenReifiedArguments language Γ parameters),
      arguments parameters = some receipt →
        OpenFirstOrderArguments language receipt.scopes receipt.arguments)
    (rule : {rule : GrammarRule // rule ∈ language.terms})
    {term : Term (signatureOf language) Γ type}
    (accepted : openConstructorCandidate? language label type arguments rule =
      some term) : OpenFirstOrder language term := by
  unfold openConstructorCandidate? at accepted
  split at accepted
  · split at accepted
    · rename_i sameType
      split at accepted
      · rename_i ordinary
        cases elaborated : arguments rule.val.params with
        | none => simp [elaborated] at accepted
        | some receipt =>
            simp only [elaborated, Option.map_some, Option.some.injEq] at accepted
            subst term
            cases sameType
            exact .constructor rule.val rule.property
              (fun bare => by
                have checked := (usesBareCollection?_eq_true_iff rule.val).mpr bare
                rw [ordinary] at checked
                cases checked)
              receipt.scopes receipt.arguments
              (supported rule.val.params receipt elaborated)
      · simp at accepted
    · simp at accepted
  · simp at accepted

mutual
  /-- Successful computed open reification renders to the precise input
pattern, including each authored free-variable name. -/
  theorem reifyOpen?_named {language : LanguageDef}
      {entries : List (String × TypeExpr)} {pattern : Pattern}
      {type : TypeExpr}
      {term : Term (signatureOf language) (contextSorts entries) type}
      (accepted : reifyOpen? language entries pattern type = some term) :
      namedFirstOrderErase? (names entries) term = some pattern := by
    cases pattern with
    | apply label patterns =>
        simp only [reifyOpen?] at accepted
        obtain ⟨rule, _, candidate⟩ := List.exists_of_findSome?_eq_some accepted
        exact openConstructorCandidate?_named (names entries)
          (fun parameters receipt elaborated =>
            reifyOpenArguments?_named elaborated) candidate
    | fvar name =>
        cases found : lookupPosition? entries name type with
        | none => simp [reifyOpen?, found] at accepted
        | some position =>
            simp [reifyOpen?, found] at accepted
            cases accepted
            simpa [namedFirstOrderErase?, names] using
              congrArg Pattern.fvar
                (lookupPosition?_sound entries name type found)
    | bvar index => simp [reifyOpen?] at accepted
    | lambda binder body => simp [reifyOpen?] at accepted
    | multiLambda count binders body => simp [reifyOpen?] at accepted
    | subst body replacement => simp [reifyOpen?] at accepted
    | collection kind elements rest => simp [reifyOpen?] at accepted
  termination_by sizeOf pattern
  decreasing_by
    all_goals (simp_all only [Pattern.apply.sizeOf_spec]; omega)

  /-- Every argument reconstructed by the open codec renders in its
original order and with its original free-variable names. -/
  theorem reifyOpenArguments?_named {language : LanguageDef}
      {entries : List (String × TypeExpr)}
      {patterns : List Pattern} {parameters : List TermParam}
      {receipt : OpenReifiedArguments language (contextSorts entries) parameters}
      (accepted : reifyOpenArguments? language entries patterns parameters =
        some receipt) :
      namedFirstOrderEraseArguments? (names entries) receipt.scopes
        receipt.arguments = some patterns := by
    cases patterns with
    | nil =>
        cases parameters with
        | nil =>
            simp only [reifyOpenArguments?, Option.some.injEq] at accepted
            subst receipt
            rfl
        | cons parameter parameters => simp [reifyOpenArguments?] at accepted
    | cons pattern patterns =>
        cases parameters with
        | nil => simp [reifyOpenArguments?] at accepted
        | cons parameter parameters =>
            cases parameter with
            | abstractionNamed binder name type =>
                simp [reifyOpenArguments?] at accepted
            | multiAbstractionNamed binders name type =>
                simp [reifyOpenArguments?] at accepted
            | simple name type =>
                cases head : reifyOpen? language entries pattern type with
                | none => simp [reifyOpenArguments?, head] at accepted
                | some term =>
                    cases tail : reifyOpenArguments? language entries patterns
                        parameters with
                    | none => simp [reifyOpenArguments?, head, tail] at accepted
                    | some rest =>
                        simp [reifyOpenArguments?, head, tail] at accepted
                        subst receipt
                        simp only [namedFirstOrderEraseArguments?]
                        rw [reifyOpen?_named head,
                          reifyOpenArguments?_named tail]
                        rfl
  termination_by sizeOf patterns
  decreasing_by
    all_goals (simp_all only [List.cons.sizeOf_spec]; omega)
end

mutual
  /-- Every typed, compilable open first-order pattern is found by the
  declaration-derived search when the finite context covers each used free
  name at the sort assigned by the original typing judgment. -/
  theorem reifyOpen?_complete
      {language : LanguageDef} {entries : List (String × TypeExpr)}
      {free : FreeTypeContext} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free [] pattern type)
      (compiled : compilePattern? pattern ≠ none)
      (covered : ∀ name, name ∈ pattern.freeFvarNames →
        ∀ sort, free name = some sort → (name, sort) ∈ entries) :
      (reifyOpen? language entries pattern type).isSome = true := by
    cases typed with
    | bvar lookup => simp at lookup
    | @fvar _ variableName _ lookup =>
        have membership : (variableName, type) ∈ entries :=
          covered variableName (by simp [Pattern.freeFvarNames]) type lookup
        have found := (lookupPosition?_isSome_iff entries variableName type).2
          membership
        cases result : lookupPosition? entries variableName type with
        | none => simp [result] at found
        | some position => simp [reifyOpen?, result]
    | @constructor _ rule patterns member ordinary argumentsTyped =>
        have argsCovered : ∀ name,
            name ∈ patterns.flatMap Pattern.freeFvarNames →
            ∀ sort, free name = some sort → (name, sort) ∈ entries := by
          intro name nameMember sort assignment
          exact covered name (by simpa [Pattern.freeFvarNames] using nameMember)
            sort assignment
        have argumentsSome := reifyOpenArguments?_complete argumentsTyped
          (compilePatterns?_ne_none_of_apply compiled) argsCovered
        simp only [reifyOpen?]
        apply List.findSome?_isSome_iff.mpr
        refine ⟨⟨rule, member⟩, List.mem_attach _ _, ?_⟩
        have ordinaryCheck : usesBareCollection? rule = false := by
          cases checked : usesBareCollection? rule with
          | false => rfl
          | true =>
              exact False.elim
                (ordinary ((usesBareCollection?_eq_true_iff rule).mp checked))
        simp only [openConstructorCandidate?, dif_pos ordinaryCheck]
        cases result : reifyOpenArguments? language entries patterns rule.params with
        | none => simp [result] at argumentsSome
        | some receipt => simp
    | lambda bodyTyped => simp [compilePattern?] at compiled
    | multiLambda bodyTyped => simp [compilePattern?] at compiled
    | subst bodyTyped replacementTyped => simp [compilePattern?] at compiled
    | collection elementsTyped => simp [compilePattern?] at compiled
    | collectionConstructor member shape elementsTyped =>
        simp [compilePattern?] at compiled
  termination_by sizeOf pattern
  decreasing_by
    all_goals (simp_all only [Pattern.apply.sizeOf_spec]; omega)

  /-- Recursion through an authored simple-parameter row preserves coverage
of every free name in each child pattern. -/
  theorem reifyOpenArguments?_complete
      {language : LanguageDef} {entries : List (String × TypeExpr)}
      {free : FreeTypeContext} {patterns : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free [] patterns parameters)
      (compiled : compilePatterns? patterns ≠ none)
      (covered : ∀ name,
        name ∈ patterns.flatMap Pattern.freeFvarNames →
        ∀ sort, free name = some sort → (name, sort) ∈ entries) :
      (reifyOpenArguments? language entries patterns parameters).isSome = true := by
    cases typed with
    | nil => simp [reifyOpenArguments?]
    | @cons _ pattern patterns parameter parameters expected representation
        expectedType patternTyped patternsTyped =>
        have headAccepted := compilePattern?_ne_none_of_cons compiled
        have tailAccepted := compilePatterns?_ne_none_of_cons compiled
        obtain ⟨name, type, rfl⟩ :=
          simple_parameter_of_firstOrder representation headAccepted
        simp only [parameterType?, Option.some.injEq] at expectedType
        subst expected
        have headCovered : ∀ variableName,
            variableName ∈ pattern.freeFvarNames →
            ∀ sort, free variableName = some sort →
              (variableName, sort) ∈ entries := by
          intro variableName membership sort assignment
          exact covered variableName
            (by simpa only [List.flatMap_cons, List.mem_append] using
              (Or.inl membership)) sort assignment
        have tailCovered : ∀ variableName,
            variableName ∈ patterns.flatMap Pattern.freeFvarNames →
            ∀ sort, free variableName = some sort →
              (variableName, sort) ∈ entries := by
          intro variableName membership sort assignment
          exact covered variableName
            (by simpa only [List.flatMap_cons, List.mem_append] using
              (Or.inr membership)) sort assignment
        have headSome := reifyOpen?_complete patternTyped headAccepted headCovered
        have tailSome := reifyOpenArguments?_complete patternsTyped tailAccepted
          tailCovered
        cases head : reifyOpen? language entries pattern type with
        | none => simp [head] at headSome
        | some term =>
            cases tail : reifyOpenArguments? language entries patterns parameters with
            | none => simp [tail] at tailSome
            | some receipt => simp [reifyOpenArguments?, head, tail]
  termination_by sizeOf patterns
  decreasing_by
    all_goals (simp_all only [List.cons.sizeOf_spec]; omega)
end

/-- The context generated from precisely the pattern's used names is enough
for the computed open codec whenever the original pattern is typed and in
the existing first-order compiler fragment. -/
theorem reifyOpen?_fromUsed_complete
    {language : LanguageDef} {free : FreeTypeContext}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free [] pattern type)
    (compiled : compilePattern? pattern ≠ none) :
    (reifyOpen? language (fromUsed free pattern.freeFvarNames)
      pattern type).isSome = true := by
  exact reifyOpen?_complete typed compiled (by
    intro name membership sort assignment
    exact fromUsed_has_assigned_pair free pattern.freeFvarNames
      name sort membership assignment)

/-- On a checked typed open pattern the computed intrinsic receipt is
available, with the exact original raw pattern as its named erasure. -/
theorem reifyOpen?_fromUsed_receipt
    {language : LanguageDef} {free : FreeTypeContext}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free [] pattern type)
    (compiled : compilePattern? pattern ≠ none) :
    ∃ term : Term (signatureOf language)
        (contextSorts (fromUsed free pattern.freeFvarNames)) type,
      reifyOpen? language (fromUsed free pattern.freeFvarNames)
        pattern type = some term ∧
      namedFirstOrderErase?
        (names (fromUsed free pattern.freeFvarNames)) term = some pattern := by
  have found := reifyOpen?_fromUsed_complete typed compiled
  cases result : reifyOpen? language (fromUsed free pattern.freeFvarNames)
      pattern type with
  | none => simp [result] at found
  | some term => exact ⟨term, rfl, reifyOpen?_named result⟩

/-- Compute a simultaneous intrinsic substitution for a finite row of raw
captured images. Unlike a variable-only codec, each image may be an arbitrary
typed first-order constructor tree searched from the authored declarations. -/
def reifyOpenImages? (language : LanguageDef)
    (targetEntries : List (String × TypeExpr)) (bindings : Bindings) :
    (sourceEntries : List (String × TypeExpr)) →
      Option (Sub (signatureOf language) (contextSorts sourceEntries)
        (contextSorts targetEntries))
  | [] => some (fun _ position => nomatch position)
  | (sourceName, sourceSort) :: rest => do
      let image ← reifyOpen? language targetEntries
        (applyBindings bindings (.fvar sourceName)) sourceSort
      let tail ← reifyOpenImages? language targetEntries bindings rest
      pure (fun sort position => match position with
        | .zero => image
        | .succ earlier => tail sort earlier)

/-- Every image of a computed open substitution renders to the exact raw
capture at that source position. This holds for constructor-tree images, not
only for variable renamings. -/
theorem reifyOpenImages?_named (language : LanguageDef)
    (targetEntries : List (String × TypeExpr)) (bindings : Bindings) :
    ∀ (sourceEntries : List (String × TypeExpr))
      {sigma : Sub (signatureOf language) (contextSorts sourceEntries)
        (contextSorts targetEntries)},
      reifyOpenImages? language targetEntries bindings sourceEntries =
        some sigma →
        ∀ sort (position : Var (contextSorts sourceEntries) sort),
          namedFirstOrderErase? (names targetEntries) (sigma sort position) =
            some (applyBindings bindings
              (.fvar (names sourceEntries sort position))) := by
  intro sourceEntries
  induction sourceEntries with
  | nil =>
      intro sigma _ sort position
      nomatch position
  | cons head rest ih =>
      rcases head with ⟨sourceName, sourceSort⟩
      intro sigma accepted sort position
      cases headResult : reifyOpen? language targetEntries
          (applyBindings bindings (.fvar sourceName)) sourceSort with
      | none => simp [reifyOpenImages?, headResult] at accepted
      | some image =>
          cases tailResult : reifyOpenImages? language targetEntries bindings rest with
          | none =>
              simp [reifyOpenImages?, headResult, tailResult] at accepted
          | some tail =>
              simp [reifyOpenImages?, headResult, tailResult] at accepted
              cases accepted
              cases position with
              | zero =>
                  simpa [names, nameAt] using reifyOpen?_named headResult
              | succ earlier =>
                  exact ih tailResult sort earlier

/-- The substitution algorithm succeeds exactly when every source-context
image has a successful computed open reification at its assigned sort. -/
theorem reifyOpenImages?_complete_of_images (language : LanguageDef)
    (targetEntries : List (String × TypeExpr)) (bindings : Bindings) :
    ∀ (sourceEntries : List (String × TypeExpr)),
      (∀ sort (position : Var (contextSorts sourceEntries) sort),
        (reifyOpen? language targetEntries
          (applyBindings bindings
            (.fvar (names sourceEntries sort position))) sort).isSome = true) →
      (reifyOpenImages? language targetEntries bindings sourceEntries).isSome =
        true := by
  intro sourceEntries
  induction sourceEntries with
  | nil =>
      intro _
      rfl
  | cons head rest ih =>
      rcases head with ⟨sourceName, sourceSort⟩
      intro imagesSome
      have headSome := imagesSome sourceSort .zero
      have tailSome : ∀ sort (position : Var (contextSorts rest) sort),
          (reifyOpen? language targetEntries
            (applyBindings bindings (.fvar (names rest sort position))) sort).isSome =
            true := by
        intro sort position
        exact imagesSome sort (.succ position)
      have restSome := ih tailSome
      cases headResult : reifyOpen? language targetEntries
          (applyBindings bindings (.fvar sourceName)) sourceSort with
      | none =>
          have absent : False := by
            simp [names, nameAt, headResult] at headSome
          exact absent.elim
      | some image =>
          cases tailResult : reifyOpenImages? language targetEntries bindings rest with
          | none => simp [tailResult] at restSome
          | some tail =>
              simp [reifyOpenImages?, headResult, tailResult]

/-- A successful finite `findSome?` retains a Type-valued certificate from
the candidate that actually returned the result. -/
def findSome?_supported {α β : Type} (items : List α)
    (candidate : α → Option β) (Supported : β → Type)
    (candidateSupported : ∀ item result,
      candidate item = some result → Supported result)
    {result : β} (accepted : items.findSome? candidate = some result) :
    Supported result := by
  induction items with
  | nil => simp [List.findSome?] at accepted
  | cons item rest ih =>
      cases found : candidate item with
      | none =>
          exact ih (by simpa [List.findSome?, found] using accepted)
      | some value =>
          have equal : value = result := by
            simpa [List.findSome?, found] using accepted
          subst result
          exact candidateSupported item value found

mutual
  /-- Computed open reification carries a proof-relevant certificate that
its result uses only variables and nonbinding authored constructors. -/
  def reifyOpen?_supported {language : LanguageDef}
      {entries : List (String × TypeExpr)} {pattern : Pattern}
      {type : TypeExpr}
      {term : Term (signatureOf language) (contextSorts entries) type}
      (accepted : reifyOpen? language entries pattern type = some term) :
      OpenFirstOrder language term := by
    cases pattern with
    | apply label patterns =>
        simp only [reifyOpen?] at accepted
        exact findSome?_supported language.terms.attach
          (openConstructorCandidate? language label type
            (fun parameters =>
              reifyOpenArguments? language entries patterns parameters))
          (OpenFirstOrder language)
          (fun rule result candidate =>
            openConstructorCandidate?_supported label type
              (fun parameters =>
                reifyOpenArguments? language entries patterns parameters)
              (fun parameters receipt elaborated =>
                reifyOpenArguments?_supported elaborated)
              rule candidate)
          accepted
    | fvar name =>
        cases found : lookupPosition? entries name type with
        | none => simp [reifyOpen?, found] at accepted
        | some position =>
            simp [reifyOpen?, found] at accepted
            cases accepted
            exact .variable position
    | bvar index => simp [reifyOpen?] at accepted
    | lambda binder body => simp [reifyOpen?] at accepted
    | multiLambda count binders body => simp [reifyOpen?] at accepted
    | subst body replacement => simp [reifyOpen?] at accepted
    | collection kind elements rest => simp [reifyOpen?] at accepted
  termination_by sizeOf pattern
  decreasing_by
    all_goals (simp_all only [Pattern.apply.sizeOf_spec]; omega)

  /-- A computed argument row preserves the corresponding proof-relevant
ordinary-constructor certificate for each child. -/
  def reifyOpenArguments?_supported {language : LanguageDef}
      {entries : List (String × TypeExpr)}
      {patterns : List Pattern} {parameters : List TermParam}
      {receipt : OpenReifiedArguments language
        (contextSorts entries) parameters}
      (accepted : reifyOpenArguments? language entries patterns parameters =
        some receipt) :
      OpenFirstOrderArguments language receipt.scopes receipt.arguments := by
    cases patterns with
    | nil =>
        cases parameters with
        | nil =>
            simp only [reifyOpenArguments?, Option.some.injEq] at accepted
            subst receipt
            exact OpenFirstOrderArguments.nil
              (language := language) (Γ := contextSorts entries)
        | cons parameter parameters => simp [reifyOpenArguments?] at accepted
    | cons pattern patterns =>
        cases parameters with
        | nil => simp [reifyOpenArguments?] at accepted
        | cons parameter parameters =>
            cases parameter with
            | abstractionNamed binder name type =>
                simp [reifyOpenArguments?] at accepted
            | multiAbstractionNamed binders name type =>
                simp [reifyOpenArguments?] at accepted
            | simple name type =>
                cases head : reifyOpen? language entries pattern type with
                | none => simp [reifyOpenArguments?, head] at accepted
                | some term =>
                    cases tail : reifyOpenArguments? language entries patterns
                        parameters with
                    | none => simp [reifyOpenArguments?, head, tail] at accepted
                    | some rest =>
                        simp [reifyOpenArguments?, head, tail] at accepted
                        subst receipt
                        exact .cons name type rest.scopes term rest.arguments
                          (reifyOpen?_supported head)
                          (reifyOpenArguments?_supported tail)
  termination_by sizeOf patterns
  decreasing_by
    all_goals (simp_all only [List.cons.sizeOf_spec]; omega)
end

/-- Every image in a computed constructor-tree substitution carries the
proof-relevant ordinary-constructor certificate produced by the same search. -/
def reifyOpenImages?_supported (language : LanguageDef)
    (targetEntries : List (String × TypeExpr)) (bindings : Bindings) :
    ∀ (sourceEntries : List (String × TypeExpr))
      {sigma : Sub (signatureOf language) (contextSorts sourceEntries)
        (contextSorts targetEntries)},
      reifyOpenImages? language targetEntries bindings sourceEntries =
        some sigma →
        ∀ sort (position : Var (contextSorts sourceEntries) sort),
          OpenFirstOrder language (sigma sort position) := by
  intro sourceEntries
  induction sourceEntries with
  | nil =>
      intro sigma _ sort position
      nomatch position
  | cons head rest ih =>
      rcases head with ⟨sourceName, sourceSort⟩
      intro sigma accepted sort position
      cases headResult : reifyOpen? language targetEntries
          (applyBindings bindings (.fvar sourceName)) sourceSort with
      | none => simp [reifyOpenImages?, headResult] at accepted
      | some image =>
          cases tailResult : reifyOpenImages? language targetEntries bindings rest with
          | none => simp [reifyOpenImages?, headResult, tailResult] at accepted
          | some tail =>
              simp [reifyOpenImages?, headResult, tailResult] at accepted
              cases accepted
              cases position with
              | zero => exact reifyOpen?_supported headResult
              | succ earlier => exact ih tailResult sort earlier

end Mettapedia.GSLT.LanguageDef.BindingSyntax.OpenReification
