import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef

/-!
# The core of a row reads the signature only

The core reduction of a rule or equation (`CoreReduction.reduceRule`) reads the row and the language's name, sorts and
constructor declarations. It does not read the language's other rows. So:
- a language with other rows reduces every row as the language does (`reduceRewrite_withRows`,
  `reduceEquation_withRows`);
- the core of a language reduces each row on its own (`reduce_withRows`).

A core's constructor declarations are their own core (`canonicalGrammar_canonicalGrammar`), and its rows declare their
binding, so they are their own cores. Hence the core of a core is itself (`reduce_reduce`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CoreReduction

open Syntax

/-- A language with the given equations and rewrites in place of its own. -/
def withRows (language : LanguageDef) (equations : List Equation) (rewrites : List RewriteRule) : LanguageDef :=
  { language with «equations» := equations, «rewrites» := rewrites }

variable (language : LanguageDef) (equations : List Equation) (rewrites : List RewriteRule)

@[simp] theorem paramsOf_withRows : paramsOf (withRows language equations rewrites) = paramsOf language := rfl

@[simp] theorem bareLabels_withRows : bareLabels (withRows language equations rewrites) = bareLabels language := rfl

/-! ## Metavariables in abstraction slots -/

mutual
  theorem slotDepths_withRows : ∀ pattern : Pattern,
      slotDepths (withRows language equations rewrites) pattern = slotDepths language pattern
    | .bvar _ => by simp only [slotDepths]
    | .fvar _ => by simp only [slotDepths]
    | .apply label arguments => by
        simp only [slotDepths, paramsOf_withRows]
        exact slotArguments_withRows _ arguments
    | .lambda _ body => by simp only [slotDepths]; exact slotDepths_withRows body
    | .multiLambda _ _ body => by simp only [slotDepths]; exact slotDepths_withRows body
    | .subst body replacement => by
        simp only [slotDepths]
        rw [slotDepths_withRows body, slotDepths_withRows replacement]
    | .collection _ elements _ => by simp only [slotDepths]; exact slotList_withRows elements
  termination_by pattern => (sizeOf pattern, 0)
  decreasing_by all_goals sizeOf_pattern_dec

  theorem slotArguments_withRows : ∀ (params : List TermParam) (patterns : List Pattern),
      slotArguments (withRows language equations rewrites) params patterns = slotArguments language params patterns
    | param :: params, pattern :: rest => by
        simp only [slotArguments]
        rw [slotIn_withRows (slotDepth param) pattern, slotArguments_withRows params rest]
    | [], patterns => by simp only [slotArguments]; exact slotList_withRows patterns
    | _ :: _, [] => by simp only [slotArguments]
  termination_by _ patterns => (sizeOf patterns, 1)
  decreasing_by all_goals sizeOf_pattern_dec

  theorem slotIn_withRows : ∀ (depth : Nat) (pattern : Pattern),
      slotIn (withRows language equations rewrites) depth pattern = slotIn language depth pattern
    | depth + 1, .lambda _ body => by simp only [slotIn]; exact slotIn_withRows depth body
    | depth, .multiLambda arity binders body => by
        simp only [slotIn]
        split
        · exact slotIn_withRows (depth - arity) body
        · exact slotDepths_withRows body
    | depth + 1, .fvar _ => by simp only [slotIn]
    | 0, .lambda binder body => by simp only [slotIn]; exact slotDepths_withRows (.lambda binder body)
    | 0, .fvar name => by simp only [slotIn]; exact slotDepths_withRows (.fvar name)
    | _, .bvar index => by simp only [slotIn]; exact slotDepths_withRows (.bvar index)
    | _, .apply label arguments => by simp only [slotIn]; exact slotDepths_withRows (.apply label arguments)
    | _, .subst body replacement => by simp only [slotIn]; exact slotDepths_withRows (.subst body replacement)
    | _, .collection kind elements rest => by
        simp only [slotIn]; exact slotDepths_withRows (.collection kind elements rest)
  termination_by _ pattern => (sizeOf pattern, 1)
  decreasing_by all_goals sizeOf_pattern_dec

  theorem slotList_withRows : ∀ patterns : List Pattern,
      slotList (withRows language equations rewrites) patterns = slotList language patterns
    | [] => by simp only [slotList]
    | pattern :: patterns => by
        simp only [slotList]
        rw [slotDepths_withRows pattern, slotList_withRows patterns]
  termination_by patterns => (sizeOf patterns, 0)
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## Eta-long abstractions -/

mutual
  theorem etaLong_withRows (expanded : List (String × Nat)) : ∀ pattern : Pattern,
      etaLong (withRows language equations rewrites) expanded pattern = etaLong language expanded pattern
    | .bvar _ => by simp only [etaLong]
    | .fvar _ => by simp only [etaLong]
    | .apply label arguments => by
        simp only [etaLong, paramsOf_withRows]
        rw [etaScope_withRows expanded arguments, etaArguments_withRows expanded _ arguments]
    | .lambda _ body => by simp only [etaLong]; rw [etaLong_withRows expanded body]
    | .multiLambda _ _ body => by simp only [etaLong]; rw [etaLong_withRows expanded body]
    | .subst body replacement => by
        simp only [etaLong]
        rw [etaLong_withRows expanded body, etaLong_withRows expanded replacement]
    | .collection _ elements _ => by simp only [etaLong]; rw [etaList_withRows expanded elements]
  termination_by pattern => (sizeOf pattern, 0)
  decreasing_by all_goals sizeOf_pattern_dec

  theorem etaArguments_withRows (expanded : List (String × Nat)) : ∀ (params : List TermParam)
      (patterns : List Pattern),
      etaArguments (withRows language equations rewrites) expanded params patterns =
        etaArguments language expanded params patterns
    | .simple _ (.collection _ _) :: params, .collection _ elements _ :: rest => by
        simp only [etaArguments]
        rw [etaList_withRows expanded elements, etaArguments_withRows expanded params rest]
    | .simple name (.collection kind type) :: params, (.bvar index) :: rest => by
        simp only [etaArguments]
        rw [etaIn_withRows expanded _ (.bvar index), etaArguments_withRows expanded params rest]
    | .simple name (.collection kind type) :: params, (.fvar var) :: rest => by
        simp only [etaArguments]
        rw [etaIn_withRows expanded _ (.fvar var), etaArguments_withRows expanded params rest]
    | .simple name (.collection kind type) :: params, (.apply label arguments) :: rest => by
        simp only [etaArguments]
        rw [etaIn_withRows expanded _ (.apply label arguments), etaArguments_withRows expanded params rest]
    | .simple name (.collection kind type) :: params, (.lambda binder body) :: rest => by
        simp only [etaArguments]
        rw [etaIn_withRows expanded _ (.lambda binder body), etaArguments_withRows expanded params rest]
    | .simple name (.collection kind type) :: params, (.multiLambda arity binders body) :: rest => by
        simp only [etaArguments]
        rw [etaIn_withRows expanded _ (.multiLambda arity binders body), etaArguments_withRows expanded params rest]
    | .simple name (.collection kind type) :: params, (.subst body replacement) :: rest => by
        simp only [etaArguments]
        rw [etaIn_withRows expanded _ (.subst body replacement), etaArguments_withRows expanded params rest]
    | .simple name (.base sort) :: params, pattern :: rest => by
        simp only [etaArguments]
        rw [etaIn_withRows expanded _ pattern, etaArguments_withRows expanded params rest]
    | .simple name (.arrow domain codomain) :: params, pattern :: rest => by
        simp only [etaArguments]
        rw [etaIn_withRows expanded _ pattern, etaArguments_withRows expanded params rest]
    | .simple name (.multiBinder domain) :: params, pattern :: rest => by
        simp only [etaArguments]
        rw [etaIn_withRows expanded _ pattern, etaArguments_withRows expanded params rest]
    | .abstractionNamed binder name type :: params, pattern :: rest => by
        simp only [etaArguments]
        rw [etaIn_withRows expanded _ pattern, etaArguments_withRows expanded params rest]
    | .multiAbstractionNamed binders name type :: params, pattern :: rest => by
        simp only [etaArguments]
        rw [etaIn_withRows expanded _ pattern, etaArguments_withRows expanded params rest]
    | [], patterns => by simp only [etaArguments]; exact etaList_withRows expanded patterns
    | _ :: _, [] => by simp only [etaArguments]
  termination_by _ patterns => (sizeOf patterns, 1)
  decreasing_by all_goals sizeOf_pattern_dec

  theorem etaIn_withRows (expanded : List (String × Nat)) : ∀ (depth : Nat) (pattern : Pattern),
      etaIn (withRows language equations rewrites) expanded depth pattern = etaIn language expanded depth pattern
    | depth + 1, .lambda _ body => by simp only [etaIn]; rw [etaIn_withRows expanded depth body]
    | depth, .multiLambda arity binders body => by
        simp only [etaIn]
        split
        · rw [etaIn_withRows expanded (depth - arity) body]
        · rw [etaLong_withRows expanded body]
    | depth + 1, .fvar _ => by simp only [etaIn]
    | 0, .lambda binder body => by simp only [etaIn]; exact etaLong_withRows expanded (.lambda binder body)
    | 0, .fvar name => by simp only [etaIn]; exact etaLong_withRows expanded (.fvar name)
    | _, .bvar index => by simp only [etaIn]; exact etaLong_withRows expanded (.bvar index)
    | _, .apply label arguments => by simp only [etaIn]; exact etaLong_withRows expanded (.apply label arguments)
    | _, .subst body replacement => by
        simp only [etaIn]; exact etaLong_withRows expanded (.subst body replacement)
    | _, .collection kind elements rest => by
        simp only [etaIn]; exact etaLong_withRows expanded (.collection kind elements rest)
  termination_by _ pattern => (sizeOf pattern, 1)
  decreasing_by all_goals sizeOf_pattern_dec

  theorem etaScope_withRows (expanded : List (String × Nat)) : ∀ patterns : List Pattern,
      etaScope (withRows language equations rewrites) expanded patterns = etaScope language expanded patterns
    | .fvar _ :: rest => by simp only [etaScope]; rw [etaList_withRows expanded rest]
    | .apply label arguments :: rest => by
        simp only [etaScope]
        rw [etaScope_withRows expanded arguments, etaLong_withRows expanded (.apply label arguments),
          etaList_withRows expanded rest]
    | [] => by simp only [etaScope]; exact etaList_withRows expanded []
    | .bvar index :: rest => by simp only [etaScope]; exact etaList_withRows expanded (.bvar index :: rest)
    | .lambda binder body :: rest => by
        simp only [etaScope]; exact etaList_withRows expanded (.lambda binder body :: rest)
    | .multiLambda arity binders body :: rest => by
        simp only [etaScope]; exact etaList_withRows expanded (.multiLambda arity binders body :: rest)
    | .subst body replacement :: rest => by
        simp only [etaScope]; exact etaList_withRows expanded (.subst body replacement :: rest)
    | .collection kind elements tail :: rest => by
        simp only [etaScope]; exact etaList_withRows expanded (.collection kind elements tail :: rest)
  termination_by patterns => (sizeOf patterns, 1)
  decreasing_by all_goals sizeOf_pattern_dec

  theorem etaList_withRows (expanded : List (String × Nat)) : ∀ patterns : List Pattern,
      etaList (withRows language equations rewrites) expanded patterns = etaList language expanded patterns
    | [] => by simp only [etaList]
    | pattern :: patterns => by
        simp only [etaList]
        rw [etaLong_withRows expanded pattern, etaList_withRows expanded patterns]
  termination_by patterns => (sizeOf patterns, 0)
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## Sorts at an address -/

theorem headType?_withRows (context : List (String × TypeExpr)) : ∀ (bound : List TypeExpr) (pattern : Pattern),
    GeneralRuleBindingGrammar.headType? (withRows language equations rewrites) context bound pattern =
      GeneralRuleBindingGrammar.headType? language context bound pattern
  | _, .fvar _ => rfl
  | _, .bvar _ => rfl
  | _, .apply _ _ => rfl
  | _, .collection _ _ _ => rfl
  | _, .lambda _ _ => rfl
  | _, .multiLambda _ _ _ => rfl
  | bound, .subst body replacement => by
      have inner : ∀ outer : List TypeExpr,
          GeneralRuleBindingGrammar.headType? (withRows language equations rewrites) context outer body =
            GeneralRuleBindingGrammar.headType? language context outer body :=
        fun outer => headType?_withRows context outer body
      simp only [GeneralRuleBindingGrammar.headType?, headType?_withRows context bound replacement, inner]

theorem contextAt?_withRows (context : List (String × TypeExpr)) (address : List Nat) :
    ∀ (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern),
      GeneralRuleBindingGrammar.contextAt? (withRows language equations rewrites) context bound expected pattern
          address =
        GeneralRuleBindingGrammar.contextAt? language context bound expected pattern address := by
  induction address with
  | nil =>
      intro bound expected pattern
      rw [GeneralRuleBindingGrammar.contextAt?.eq_def, GeneralRuleBindingGrammar.contextAt?.eq_def]
      cases pattern <;> rfl
  | cons index rest ih =>
      intro bound expected pattern
      rw [GeneralRuleBindingGrammar.contextAt?.eq_def, GeneralRuleBindingGrammar.contextAt?.eq_def]
      cases pattern <;> rcases index with _ | _ | index <;> (try simp only [headType?_withRows, ih]) <;> rfl

theorem typesAt_withRows (context : List (String × TypeExpr)) (pattern : Pattern) (path : List Nat) :
    typesAt (withRows language equations rewrites) context pattern path = typesAt language context pattern path := by
  simp only [typesAt, headType?_withRows, contextAt?_withRows]

theorem bindingAt_withRows (context : List (String × TypeExpr)) (bound : List String) (premises : List Premise)
    (pattern : Pattern) (site : Site) :
    bindingAt (withRows language equations rewrites) context bound premises pattern site =
      bindingAt language context bound premises pattern site := by
  simp only [bindingAt, typesAt_withRows]

@[simp] theorem collectionElement?_withRows :
    GeneralRuleBindingGrammar.collectionElement? (withRows language equations rewrites) =
      GeneralRuleBindingGrammar.collectionElement? language := rfl

@[simp] theorem dependencySortsDeclared_withRows :
    RuleBinding.dependencySortsDeclared (withRows language equations rewrites) =
      RuleBinding.dependencySortsDeclared language := rfl

/-! ## Rows -/

theorem lowerPremise_withRows (rule : AuthoredRule) (bare : List (String × CollType))
    (expanded : List (String × Nat)) (authoredPremises : List Premise) (bound : List String) (index : Nat)
    (premise : Premise) : ∀ (depth : Nat) (known : List Binding),
      reduceRule.lowerPremise (withRows language equations rewrites) rule bare expanded authoredPremises bound index
          depth known premise =
        reduceRule.lowerPremise language rule bare expanded authoredPremises bound index depth known premise := by
  induction premise with
  | freshness condition => intro depth known; simp only [reduceRule.lowerPremise]
  | congruence source target =>
      intro depth known
      cases source <;> cases target <;>
        simp only [reduceRule.lowerPremise, etaLong_withRows, bindingAt_withRows]
  | scopedStep step => intro depth known; simp only [reduceRule.lowerPremise]
  | relationQuery relation patterns =>
      intro depth known
      simp only [reduceRule.lowerPremise, etaLong_withRows, bindingAt_withRows]
  | forAll collection parameter body inner =>
      intro depth known
      simp only [reduceRule.lowerPremise, inner, collectionElement?_withRows]

theorem lowerPremises_withRows (rule : AuthoredRule) (bare : List (String × CollType))
    (expanded : List (String × Nat)) (authoredPremises : List Premise) (bound : List String)
    (premises : List Premise) : ∀ (index : Nat) (known : List Binding),
      reduceRule.lowerPremises (withRows language equations rewrites) rule bare expanded authoredPremises bound index
          known premises =
        reduceRule.lowerPremises language rule bare expanded authoredPremises bound index known premises := by
  induction premises with
  | nil => intro index known; simp only [reduceRule.lowerPremises]
  | cons premise premises inner =>
      intro index known
      simp only [reduceRule.lowerPremises, lowerPremise_withRows, inner]

/-- **The core of a row reads the language's signature only.** -/
theorem reduceRule_withRows (rule : AuthoredRule) :
    reduceRule (withRows language equations rewrites) rule = reduceRule language rule := by
  simp only [reduceRule, bareLabels_withRows, slotDepths_withRows, etaLong_withRows, bindingAt_withRows,
    lowerPremises_withRows]

theorem reduceRewrite_withRows :
    reduceRewrite (withRows language equations rewrites) = reduceRewrite language := by
  funext rule
  simp only [reduceRewrite, reduceRule_withRows, dependencySortsDeclared_withRows]
  rfl

theorem reduceEquation_withRows :
    reduceEquation (withRows language equations rewrites) = reduceEquation language := by
  funext equation
  simp only [reduceEquation, reduceRule_withRows, dependencySortsDeclared_withRows]
  rfl

/-- The constructor declarations of a language with other rows are its own. -/
theorem canonicalGrammar_withRows :
    canonicalGrammar (withRows language equations rewrites) = withRows (canonicalGrammar language) equations rewrites :=
  rfl

/-- **The core of a language reduces each row on its own**: in a language with other rows, every row reduces as it
does in the language. -/
theorem reduce_withRows :
    reduce (withRows language equations rewrites) =
      (do
        let rewritten ← rewrites.mapM (reduceRewrite (canonicalGrammar language))
        let equated ← equations.mapM (reduceEquation (canonicalGrammar language))
        return { canonicalGrammar language with «rewrites» := rewritten, «equations» := equated }) := by
  simp only [reduce, canonicalGrammar_withRows, reduceRewrite_withRows, reduceEquation_withRows]
  rfl

/-! ## The core of a core -/

mutual
  theorem mentionsAny_nil : ∀ items : List SyntaxItem, mentionsAny [] items = false
    | [] => by simp only [mentionsAny]
    | .nonTerminal _ :: rest => by simp only [mentionsAny, List.contains_nil, Bool.false_or]; exact mentionsAny_nil rest
    | .op (.var _) :: rest => by simp only [mentionsAny, List.contains_nil, Bool.false_or]; exact mentionsAny_nil rest
    | .op (.opt inner) :: rest => by
        simp only [mentionsAny, mentionsAny_nil inner, mentionsAny_nil rest, Bool.or_self]
    | .terminal _ :: rest => by simp only [mentionsAny]; exact mentionsAny_nil rest
    | .separator _ :: rest => by simp only [mentionsAny]; exact mentionsAny_nil rest
    | .delimiter _ _ :: rest => by simp only [mentionsAny]; exact mentionsAny_nil rest
    | .op (.sep _ _ _) :: rest => by simp only [mentionsAny]; exact mentionsAny_nil rest
    | .op (.zip _ _) :: rest => by simp only [mentionsAny]; exact mentionsAny_nil rest
    | .op (.map _ _ _) :: rest => by simp only [mentionsAny]; exact mentionsAny_nil rest
end

/-- Syntax prunes nothing when no binder name is dropped. -/
theorem pruneItems_nil : ∀ items : List SyntaxItem, pruneItems [] items = items
  | [] => by simp only [pruneItems]
  | .nonTerminal _ :: rest => by
      simp only [pruneItems, List.contains_nil, Bool.false_eq_true, if_false, List.singleton_append,
        pruneItems_nil rest]
  | .op (.var _) :: rest => by
      simp only [pruneItems, List.contains_nil, Bool.false_eq_true, if_false, List.singleton_append,
        pruneItems_nil rest]
  | .op (.opt inner) :: rest => by
      simp only [pruneItems, mentionsAny_nil, Bool.false_and, Bool.false_eq_true, if_false, List.singleton_append,
        pruneItems_nil inner, pruneItems_nil rest]
  | .terminal _ :: rest => by simp only [pruneItems, pruneItems_nil rest]
  | .separator _ :: rest => by simp only [pruneItems, pruneItems_nil rest]
  | .delimiter _ _ :: rest => by simp only [pruneItems, pruneItems_nil rest]
  | .op (.sep _ _ _) :: rest => by simp only [pruneItems, pruneItems_nil rest]
  | .op (.zip _ _) :: rest => by simp only [pruneItems, pruneItems_nil rest]
  | .op (.map _ _ _) :: rest => by simp only [pruneItems, pruneItems_nil rest]

/-- A core parameter is its own core and drops no binder name. -/
theorem canonicalParam_canonicalParam (param : TermParam) :
    canonicalParam (canonicalParam param).1 = ((canonicalParam param).1, []) := by
  cases param with
  | multiAbstractionNamed names body type =>
      by_cases deep : 0 < telescopeDepth type
      · simp only [canonicalParam, deep, if_true]
      · simp only [canonicalParam, deep, if_false]
  | simple _ _ => rfl
  | abstractionNamed _ _ _ => rfl

theorem canonicalGrammarRule_canonicalGrammarRule (rule : GrammarRule) :
    canonicalGrammarRule (canonicalGrammarRule rule) = canonicalGrammarRule rule := by
  have dropped : ∀ params : List TermParam,
      (params.map fun param => ((canonicalParam param).1, ([] : List String))).flatMap (·.2) = [] := by
    simp
  simp [canonicalGrammarRule, canonicalParam_canonicalParam, Function.comp_def, dropped, pruneItems_nil]

/-- **The constructor declarations of a core are their own core.** -/
theorem canonicalGrammar_canonicalGrammar (language : LanguageDef) :
    canonicalGrammar (canonicalGrammar language) = canonicalGrammar language := by
  simp only [canonicalGrammar, List.map_map]
  congr 1
  exact List.map_congr_left fun rule _ => canonicalGrammarRule_canonicalGrammarRule rule

/-- A rewrite with a binding declaration is its own core. -/
theorem reduceRewrite_of_declared {rule : RewriteRule} {spec : RuleBindingSpec} (declared : rule.bindings = some spec) :
    reduceRewrite language rule = .ok rule := by
  simp only [reduceRewrite, declared]
  rfl

/-- An equation with a binding declaration is its own core. -/
theorem reduceEquation_of_declared {equation : Equation} {spec : RuleBindingSpec}
    (declared : equation.bindings = some spec) : reduceEquation language equation = .ok equation := by
  simp only [reduceEquation, declared]
  rfl

/-- The core of a rewrite declares its binding. -/
theorem reduceRewrite_declared {rule result : RewriteRule} (reduced : reduceRewrite language rule = .ok result) :
    result.bindings.isSome := by
  unfold reduceRewrite at reduced
  cases declared : rule.bindings with
  | some spec =>
      simp only [declared] at reduced
      cases reduced
      simp [declared]
  | none =>
      simp only [declared] at reduced
      cases lowered : reduceRule language ⟨rule.name, rule.typeContext, rule.premises, rule.left, rule.right⟩ with
      | error problem => simp only [lowered, bind, Except.bind] at reduced; cases reduced
      | ok parts =>
          simp only [lowered, bind, Except.bind] at reduced
          split at reduced
          · cases reduced; rfl
          · cases reduced

/-- The core of an equation declares its binding. -/
theorem reduceEquation_declared {equation result : Equation}
    (reduced : reduceEquation language equation = .ok result) : result.bindings.isSome := by
  unfold reduceEquation at reduced
  cases declared : equation.bindings with
  | some spec =>
      simp only [declared] at reduced
      cases reduced
      simp [declared]
  | none =>
      simp only [declared] at reduced
      cases lowered :
          reduceRule language ⟨equation.name, equation.typeContext, equation.premises, equation.left, equation.right⟩ with
      | error problem => simp only [lowered, bind, Except.bind] at reduced; cases reduced
      | ok parts =>
          simp only [lowered, bind, Except.bind] at reduced
          split at reduced
          · cases reduced; rfl
          · cases reduced

/-- Rows that are each their own image map to themselves. -/
theorem mapM_self {α ε : Type} (step : α → Except ε α) :
    ∀ rows : List α, (∀ row ∈ rows, step row = .ok row) → rows.mapM step = .ok rows
  | [], _ => rfl
  | row :: rows, fixed => by
      simp only [List.mapM_cons, fixed row (List.mem_cons_self ..),
        mapM_self step rows fun other mem => fixed other (List.mem_cons_of_mem _ mem)]
      rfl

/-- Every row a mapping produces is an image of a row. -/
theorem mapM_images {α β ε : Type} (step : α → Except ε β) :
    ∀ (rows : List α) (images : List β), rows.mapM step = .ok images →
      ∀ image ∈ images, ∃ row, step row = .ok image
  | [], images, mapped => by
      simp only [List.mapM_nil] at mapped
      cases mapped
      simp
  | row :: rows, images, mapped => by
      simp only [List.mapM_cons] at mapped
      cases first : step row with
      | error problem => simp only [first] at mapped; cases mapped
      | ok first' =>
          cases others : rows.mapM step with
          | error problem => simp only [first, others] at mapped; cases mapped
          | ok rest =>
              simp only [first, others] at mapped
              cases mapped
              intro image mem
              rcases List.mem_cons.mp mem with here | there
              · exact ⟨row, here ▸ first⟩
              · exact mapM_images step rows rest others image there

/-- **The core of a core is itself.** -/
theorem reduce_reduce {authored core : LanguageDef} (reduced : reduce authored = .ok core) :
    reduce core = .ok core := by
  unfold reduce at reduced
  cases rewritten : (canonicalGrammar authored).rewrites.mapM (reduceRewrite (canonicalGrammar authored)) with
  | error problem => simp only [rewritten] at reduced; cases reduced
  | ok rewrites =>
      cases equated : (canonicalGrammar authored).equations.mapM (reduceEquation (canonicalGrammar authored)) with
      | error problem => simp only [rewritten, equated] at reduced; cases reduced
      | ok equations =>
          simp only [rewritten, equated] at reduced
          cases reduced
          have shape : { canonicalGrammar authored with «rewrites» := rewrites, «equations» := equations } =
              withRows (canonicalGrammar authored) equations rewrites := rfl
          rw [shape, reduce_withRows, canonicalGrammar_canonicalGrammar]
          have rewritesFixed := mapM_self (reduceRewrite (canonicalGrammar authored)) rewrites fun row mem => by
            obtain ⟨source, image⟩ := mapM_images _ _ _ rewritten row mem
            obtain ⟨spec, declared⟩ := Option.isSome_iff_exists.mp (reduceRewrite_declared _ image)
            exact reduceRewrite_of_declared _ declared
          have equationsFixed := mapM_self (reduceEquation (canonicalGrammar authored)) equations fun row mem => by
            obtain ⟨source, image⟩ := mapM_images _ _ _ equated row mem
            obtain ⟨spec, declared⟩ := Option.isSome_iff_exists.mp (reduceEquation_declared _ image)
            exact reduceEquation_of_declared _ declared
          simp only [rewritesFixed, equationsFixed]
          rfl

end Mettapedia.OSLF.MeTTaIL.CoreReduction
