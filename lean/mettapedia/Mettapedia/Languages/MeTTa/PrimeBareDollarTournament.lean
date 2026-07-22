import Std

/-!
# Prime bare-dollar semantics tournament

This module separates three questions that are easy to conflate:

* matching power: an ordinary variable can match every value represented here,
  including a grounded reference;
* identity: repeated occurrences may denote one variable or distinct variables;
* scope: a root bare-dollar binder may introduce an implicit lexical name for
  its body while nested pattern occurrences remain discard slots.

The four policies expose the discriminating behavior.  The final section
states the public anonymous-discard requirements and proves that `fresh` is
the unique policy among these contenders that satisfies them.
-/

namespace Mettapedia.Languages.MeTTa.PrimeBareDollarTournament

inductive Value where
  | symbol : Nat → Value
  | reference : Nat → Value
  | pair : Value → Value → Value
  | quotedDollar : Value
deriving Repr, DecidableEq

def dollarSymbol : Nat := 0
def acceptedSymbol : Nat := 1
def outerSymbol : Nat := 2
def innerSymbol : Nat := 3

inductive VarKey where
  | named : Nat → VarKey
  | structural : Nat → VarKey
  | anonymous : Nat → VarKey
  | sharedDollar : VarKey
deriving Repr

def keyEq (left right : VarKey) : Bool :=
  match left with
  | .named leftName =>
      match right with
      | .named rightName => Nat.beq leftName rightName
      | _ => false
  | .structural leftName =>
      match right with
      | .structural rightName => Nat.beq leftName rightName
      | _ => false
  | .anonymous leftName =>
      match right with
      | .anonymous rightName => Nat.beq leftName rightName
      | _ => false
  | .sharedDollar =>
      match right with
      | .sharedDollar => true
      | _ => false

def valueEq (left right : Value) : Bool :=
  match left with
  | .symbol leftName =>
      match right with
      | .symbol rightName => Nat.beq leftName rightName
      | _ => false
  | .reference leftName =>
      match right with
      | .reference rightName => Nat.beq leftName rightName
      | _ => false
  | .pair left₁ right₁ =>
      match right with
      | .pair left₂ right₂ =>
          valueEq left₁ left₂ && valueEq right₁ right₂
      | _ => false
  | .quotedDollar =>
      match right with
      | .quotedDollar => true
      | _ => false

abbrev Bindings := List (VarKey × Value)

def emptyBindings : Bindings := []

def lookup : Bindings → VarKey → Option Value
  | [], _ => none
  | (key, value) :: rest, query =>
      if keyEq query key then some value else lookup rest query

def setBinding (bindings : Bindings) (key : VarKey) (value : Value) : Bindings :=
  (key, value) :: bindings

def bind (bindings : Bindings) (key : VarKey) (value : Value) : Option Bindings :=
  match lookup bindings key with
  | none => some (setBinding bindings key value)
  | some previous => if valueEq previous value then some bindings else none

inductive Pattern where
  | literal : Value → Pattern
  | var : VarKey → Pattern
  | pair : Pattern → Pattern → Pattern
deriving Repr

def matchPattern (pattern : Pattern) (actual : Value)
    (bindings : Bindings) : Option Bindings :=
  match pattern with
  | .literal expected =>
      if valueEq expected actual then some bindings else none
  | .var key => bind bindings key actual
  | .pair left right =>
      match actual with
      | .pair leftValue rightValue => do
          let bindings ← matchPattern left leftValue bindings
          matchPattern right rightValue bindings
      | _ => none

inductive Term where
  | value : Value → Term
  | var : VarKey → Term
  | pair : Term → Term → Term
  | letE : Pattern → Term → Term → Term
deriving Repr

def eval (term : Term) (bindings : Bindings) : Option Value :=
  match term with
  | .value value => some value
  | .var key => lookup bindings key
  | .pair left right => do
      let leftValue ← eval left bindings
      let rightValue ← eval right bindings
      pure (.pair leftValue rightValue)
  | .letE pattern source body => do
      let sourceValue ← eval source bindings
      let extended ← matchPattern pattern sourceValue bindings
      eval body extended

inductive SurfacePattern where
  | dollar : SurfacePattern
  | named : Nat → SurfacePattern
  | structural : Nat → SurfacePattern
  | literal : Value → SurfacePattern
  | pair : SurfacePattern → SurfacePattern → SurfacePattern
deriving Repr

inductive SurfaceTerm where
  | dollar : SurfaceTerm
  | named : Nat → SurfaceTerm
  | structural : Nat → SurfaceTerm
  | value : Value → SurfaceTerm
  | pair : SurfaceTerm → SurfaceTerm → SurfaceTerm
  | letE : SurfacePattern → SurfaceTerm → SurfaceTerm → SurfaceTerm
  | quoteDollar : SurfaceTerm
deriving Repr

inductive BareDollarPolicy where
  | literal
  | fresh
  | shared
  | rootBinder
deriving Repr

def elaboratePattern (policy : BareDollarPolicy) :
    SurfacePattern → Nat → Pattern × Nat
  | .dollar, next =>
      match policy with
      | .literal => (.literal (.symbol dollarSymbol), next)
      | .shared => (.var .sharedDollar, next)
      | .fresh | .rootBinder => (.var (.anonymous next), next + 1)
  | .named name, next => (.var (.named name), next)
  | .structural name, next => (.var (.structural name), next)
  | .literal value, next => (.literal value, next)
  | .pair left right, next =>
      let leftResult := elaboratePattern policy left next
      let rightResult := elaboratePattern policy right leftResult.2
      (.pair leftResult.1 rightResult.1, rightResult.2)

def elaborateTerm (policy : BareDollarPolicy) :
    SurfaceTerm → List VarKey → Nat → Term × Nat
  | .dollar, scope, next =>
      match policy with
      | .literal => (.value (.symbol dollarSymbol), next)
      | .fresh => (.var (.anonymous next), next + 1)
      | .shared => (.var .sharedDollar, next)
      | .rootBinder =>
          match scope with
          | key :: _ => (.var key, next)
          | [] => (.var (.anonymous next), next + 1)
  | .named name, _, next => (.var (.named name), next)
  | .structural name, _, next => (.var (.structural name), next)
  | .value value, _, next => (.value value, next)
  | .pair left right, scope, next =>
      let leftResult := elaborateTerm policy left scope next
      let rightResult := elaborateTerm policy right scope leftResult.2
      (.pair leftResult.1 rightResult.1, rightResult.2)
  | .letE pattern source body, scope, next =>
      let sourceResult := elaborateTerm policy source scope next
      match policy with
      | .rootBinder =>
          match pattern with
          | .dollar =>
              let key := VarKey.anonymous sourceResult.2
              let bodyResult := elaborateTerm policy body (key :: scope)
                (sourceResult.2 + 1)
              (.letE (.var key) sourceResult.1 bodyResult.1, bodyResult.2)
          | _ =>
              let patternResult := elaboratePattern policy pattern sourceResult.2
              let bodyResult := elaborateTerm policy body scope patternResult.2
              (.letE patternResult.1 sourceResult.1 bodyResult.1, bodyResult.2)
      | .literal | .fresh | .shared =>
          let patternResult := elaboratePattern policy pattern sourceResult.2
          let bodyResult := elaborateTerm policy body scope patternResult.2
          (.letE patternResult.1 sourceResult.1 bodyResult.1, bodyResult.2)
  | .quoteDollar, _, next => (.value .quotedDollar, next)

def elaborateClosed (policy : BareDollarPolicy) (term : SurfaceTerm) : Term :=
  (elaborateTerm policy term [] 0).1

def namedProjection (bindings : Bindings) (name : Nat) : Option Value :=
  lookup bindings (.named name)

/-! ## Matching and identity laws -/

theorem anonymous_matches_reference (name : Nat) :
    matchPattern (.var (.anonymous 0)) (.reference name) emptyBindings =
      some [(.anonymous 0, .reference name)] := by
  rfl

theorem variable_match_power_is_key_independent
    (leftKey rightKey : VarKey) (value : Value) :
    (matchPattern (.var leftKey) value emptyBindings).isSome =
      (matchPattern (.var rightKey) value emptyBindings).isSome := by
  rfl

theorem anonymous_reference_is_not_named (referenceName : Nat) (name : Nat) :
    namedProjection
        [(.anonymous 0, .reference referenceName)] name = none := by
  rfl

theorem independent_anonymous_slots_match (left right : Value) :
    (matchPattern
      (.pair (.var (.anonymous 0)) (.var (.anonymous 1)))
      (.pair left right) emptyBindings).isSome := by
  rfl

theorem shared_slot_rejects_unequal {left right : Value}
    (h : valueEq left right = false) :
    matchPattern
      (.pair (.var .sharedDollar) (.var .sharedDollar))
      (.pair left right) emptyBindings = none := by
  simp [matchPattern, bind, lookup, keyEq, setBinding, emptyBindings, h]

theorem repeated_named_slot_rejects_unequal
    {left right : Value} (name : Nat) (h : valueEq left right = false) :
    matchPattern
      (.pair (.var (.named name)) (.var (.named name)))
      (.pair left right) emptyBindings = none := by
  simp [matchPattern, bind, lookup, keyEq, setBinding, emptyBindings, h]

theorem fresh_pair_has_two_distinct_anonymous_keys :
    elaborateClosed .fresh (.pair .dollar .dollar) =
      .pair (.var (.anonymous 0)) (.var (.anonymous 1)) := by
  rfl

theorem shared_pair_has_one_key :
    elaborateClosed .shared (.pair .dollar .dollar) =
      .pair (.var .sharedDollar) (.var .sharedDollar) := by
  rfl

theorem literal_pair_has_no_variable_keys :
    elaborateClosed .literal (.pair .dollar .dollar) =
      .pair (.value (.symbol dollarSymbol)) (.value (.symbol dollarSymbol)) := by
  rfl

/-! ## Binder-sensitive laws -/

def passReference (referenceName : Nat) : SurfaceTerm :=
  .letE .dollar (.value (.reference referenceName)) .dollar

theorem root_binder_passes_reference (name : Nat) :
    eval (elaborateClosed .rootBinder (passReference name)) emptyBindings =
      some (.reference name) := by
  rfl

theorem shared_dollar_passes_reference (name : Nat) :
    eval (elaborateClosed .shared (passReference name)) emptyBindings =
      some (.reference name) := by
  rfl

theorem fresh_dollar_does_not_refer_back (name : Nat) :
    eval (elaborateClosed .fresh (passReference name)) emptyBindings = none := by
  rfl

theorem literal_dollar_does_not_match_reference (name : Nat) :
    eval (elaborateClosed .literal (passReference name)) emptyBindings = none := by
  rfl

def structuredDiscard (left right : Value) : SurfaceTerm :=
  .letE (.pair .dollar .dollar) (.value (.pair left right))
    (.value (.symbol acceptedSymbol))

theorem root_binder_keeps_structured_discards_independent
    (left right : Value) :
    eval (elaborateClosed .rootBinder (structuredDiscard left right))
      emptyBindings = some (.symbol acceptedSymbol) := by
  rfl

theorem shared_dollar_overconstrains_structured_discards
    {left right : Value} (h : valueEq left right = false) :
    eval (elaborateClosed .shared (structuredDiscard left right))
      emptyBindings = none := by
  simp [structuredDiscard, elaborateClosed, elaborateTerm, elaboratePattern,
    eval, matchPattern, bind, lookup, keyEq, setBinding, emptyBindings, h]

def nestedRootBinders : SurfaceTerm :=
  .letE .dollar (.value (.symbol outerSymbol))
    (.pair
      (.letE .dollar (.value (.symbol innerSymbol)) .dollar)
      .dollar)

theorem nested_root_binders_shadow :
    eval (elaborateClosed .rootBinder nestedRootBinders) emptyBindings =
      some (.pair (.symbol innerSymbol) (.symbol outerSymbol)) := by
  rfl

def quotedRootBinder (referenceName : Nat) : SurfaceTerm :=
  .letE .dollar (.value (.reference referenceName)) .quoteDollar

theorem quotation_is_a_scope_barrier (name : Nat) :
    eval (elaborateClosed .rootBinder (quotedRootBinder name)) emptyBindings =
      some .quotedDollar := by
  rfl

/-! ## Lexical and matcher substitution beneath quotation

The native evaluator has two independently observable substitution classes.
Object-language lexical substitution stops at quote, whereas matcher/template
substitution may instantiate a matching variable inside quoted syntax.  The
distinction is not special to bare dollar: named variables exhibit it too.

This small syntax model makes the consequence for the binder-sensitive
contender explicit.  A root binder can be recovered under matcher substitution
but not under lexical substitution.  Uniformly fresh anonymous occurrences do
not recover the earlier binding under either class because their identities
are different.
-/

inductive SyntaxTemplate where
  | atom : Value → SyntaxTemplate
  | var : VarKey → SyntaxTemplate
  | pair : SyntaxTemplate → SyntaxTemplate → SyntaxTemplate
  | quote : SyntaxTemplate → SyntaxTemplate
  | unquote : SyntaxTemplate → SyntaxTemplate
deriving Repr

inductive SubstitutionClass where
  | lexical
  | matcher
deriving Repr, DecidableEq

def substitute (mode : SubstitutionClass) (key : VarKey)
    (replacement : SyntaxTemplate) : SyntaxTemplate → SyntaxTemplate
  | .atom value => .atom value
  | .var query =>
      if keyEq query key then replacement else .var query
  | .pair left right =>
      .pair (substitute mode key replacement left)
        (substitute mode key replacement right)
  | .quote body =>
      match mode with
      | .lexical => .quote body
      | .matcher => .quote (substitute .matcher key replacement body)
  | .unquote body =>
      .unquote (substitute mode key replacement body)

/-- One explicit unquote step.  It does not itself perform substitution. -/
def unquoteOnce : SyntaxTemplate → SyntaxTemplate
  | .unquote (.quote body) => body
  | term => term

theorem keyEq_self (key : VarKey) : keyEq key key = true := by
  cases key <;> simp [keyEq]

theorem lexical_substitution_stops_at_quote
    (key : VarKey) (replacement body : SyntaxTemplate) :
    substitute .lexical key replacement (.quote body) = .quote body := by
  rfl

theorem matcher_substitution_crosses_quote_for_same_key
    (key : VarKey) (replacement : SyntaxTemplate) :
    substitute .matcher key replacement (.quote (.var key)) =
      .quote replacement := by
  simp [substitute, keyEq_self]

theorem matcher_substitution_preserves_different_quoted_key
    {binderKey bodyKey : VarKey} (replacement : SyntaxTemplate)
    (different : keyEq bodyKey binderKey = false) :
    substitute .matcher binderKey replacement (.quote (.var bodyKey)) =
      .quote (.var bodyKey) := by
  simp [substitute, different]

theorem lexical_unquote_cannot_recover_quoted_binding
    (key : VarKey) (replacement : SyntaxTemplate) :
    unquoteOnce
        (substitute .lexical key replacement (.unquote (.quote (.var key)))) =
      .var key := by
  rfl

theorem matcher_unquote_exposes_quoted_binding
    (key : VarKey) (replacement : SyntaxTemplate) :
    unquoteOnce
        (substitute .matcher key replacement (.unquote (.quote (.var key)))) =
      replacement := by
  simp [substitute, unquoteOnce, keyEq_self]

def rootBinderKey : VarKey := .anonymous 0
def freshBodyKey : VarKey := .anonymous 1

theorem root_binder_quote_depends_on_substitution_class (name : Nat) :
    substitute .lexical rootBinderKey (.atom (.reference name))
        (.quote (.var rootBinderKey)) = .quote (.var rootBinderKey) ∧
    substitute .matcher rootBinderKey (.atom (.reference name))
        (.quote (.var rootBinderKey)) = .quote (.atom (.reference name)) := by
  constructor
  · exact lexical_substitution_stops_at_quote _ _ _
  · exact matcher_substitution_crosses_quote_for_same_key _ _

theorem uniformly_fresh_quote_never_recovers_prior_binding (name : Nat) :
    substitute .lexical rootBinderKey (.atom (.reference name))
        (.quote (.var freshBodyKey)) = .quote (.var freshBodyKey) ∧
    substitute .matcher rootBinderKey (.atom (.reference name))
        (.quote (.var freshBodyKey)) = .quote (.var freshBodyKey) := by
  constructor
  · exact lexical_substitution_stops_at_quote _ _ _
  · apply matcher_substitution_preserves_different_quoted_key
    rfl

theorem named_variable_obeys_same_substitution_classes (name reference : Nat) :
    substitute .lexical (.named name) (.atom (.reference reference))
        (.quote (.var (.named name))) = .quote (.var (.named name)) ∧
    substitute .matcher (.named name) (.atom (.reference reference))
        (.quote (.var (.named name))) =
      .quote (.atom (.reference reference)) := by
  constructor
  · exact lexical_substitution_stops_at_quote _ _ _
  · exact matcher_substitution_crosses_quote_for_same_key _ _

/-! ## Ratification

Bare dollar is an anonymous discard variable.  Its matching power is the same
as an ordinary variable, including grounded references; separate occurrences
must not impose equality; and a discarded binding must not become implicitly
referenceable from a later bare-dollar occurrence.

These requirements use distinct concrete witnesses for the three independent
properties.  They do not define the selected policy in terms of itself.
-/

def RatificationRequirements (policy : BareDollarPolicy) : Prop :=
  (matchPattern (elaboratePattern policy .dollar 0).1
      (.reference 11) emptyBindings).isSome = true ∧
  eval
      (elaborateClosed policy
        (structuredDiscard (.symbol outerSymbol) (.symbol innerSymbol)))
      emptyBindings = some (.symbol acceptedSymbol) ∧
  eval (elaborateClosed policy (passReference 11)) emptyBindings = none

theorem fresh_satisfies_ratification_requirements :
    RatificationRequirements .fresh := by
  constructor
  · rfl
  constructor <;> rfl

theorem literal_fails_ratification_requirements :
    ¬ RatificationRequirements .literal := by
  intro requirements
  have impossible : false = true := requirements.1
  cases impossible

theorem shared_fails_ratification_requirements :
    ¬ RatificationRequirements .shared := by
  intro requirements
  have impossible : (none : Option Value) = some (.symbol acceptedSymbol) :=
    requirements.2.1
  cases impossible

theorem root_binder_fails_ratification_requirements :
    ¬ RatificationRequirements .rootBinder := by
  intro requirements
  have impossible : some (.reference 11) = (none : Option Value) :=
    requirements.2.2
  cases impossible

theorem ratification_requirements_select_fresh
    (policy : BareDollarPolicy) (requirements : RatificationRequirements policy) :
    policy = .fresh := by
  cases policy with
  | literal => exact False.elim (literal_fails_ratification_requirements requirements)
  | fresh => rfl
  | shared => exact False.elim (shared_fails_ratification_requirements requirements)
  | rootBinder =>
      exact False.elim (root_binder_fails_ratification_requirements requirements)

theorem unbound_root_dollar_is_fresh :
    elaborateClosed .rootBinder .dollar = .var (.anonymous 0) := by
  rfl

theorem unbound_root_dollar_does_not_fabricate_a_value :
    eval (elaborateClosed .rootBinder .dollar) emptyBindings = none := by
  rfl

/-! Named and structurally named variables are independent of the policy. -/

theorem named_term_preserved (policy : BareDollarPolicy)
    (scope : List VarKey) (next name : Nat) :
    elaborateTerm policy (.named name) scope next =
      (.var (.named name), next) := by
  cases policy <;> rfl

theorem structural_term_preserved (policy : BareDollarPolicy)
    (scope : List VarKey) (next name : Nat) :
    elaborateTerm policy (.structural name) scope next =
      (.var (.structural name), next) := by
  cases policy <;> rfl

theorem named_pattern_preserved (policy : BareDollarPolicy)
    (next name : Nat) :
    elaboratePattern policy (.named name) next =
      (.var (.named name), next) := by
  cases policy <;> rfl

theorem structural_pattern_preserved (policy : BareDollarPolicy)
    (next name : Nat) :
    elaboratePattern policy (.structural name) next =
      (.var (.structural name), next) := by
  cases policy <;> rfl

end Mettapedia.Languages.MeTTa.PrimeBareDollarTournament
