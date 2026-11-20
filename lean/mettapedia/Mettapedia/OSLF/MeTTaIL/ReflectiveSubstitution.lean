import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.ReflectionProfile
import Mettapedia.OSLF.MeTTaIL.PatternCode

/-!
# Compiling declarative reflective substitution

This module interprets `ReflectivePresentationDecl` and `ReflectiveRuleDecl`
as data.  It does not attach a Lean callback to a language definition.
Languages without a uniquely selected substitution presentation retain the
ordinary syntactic `applyBindings` behavior.

Substitution respects the declaration's equations. It first resolves every
quotation whose payload is a drop, modulo the declared parallel unit and
nesting (`resolveQuotes`), and then substitutes structurally
(`substituteResolved`):

* a whole name is compared using the declaration's structural equations;
* literal quotation is opaque to substitution;
* a drop collapses only when this substitution replaced the dropped bound
  name with a quotation;
* every other drop is substituted through.

The canonicalizer is shared by the substitution compiler and the
declaration-selected matcher. Recognizing a name is not running its code.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Reflection

/-! ## Rule and presentation lookup -/

/-- Fail-closed lookup of a rule-local reflective selection. -/
def reflectiveRuleForRule? (profile : ReflectionProfile) (rule : RewriteRule) :
    Option ReflectiveRuleDecl :=
  match profile.rules.filter fun declaration =>
      declaration.rewriteRule == rule.name with
  | [declaration] => some declaration
  | _ => none

/-- Fail-closed lookup of a reusable reflective presentation by name. -/
def presentationNamed? (profile : ReflectionProfile) (name : String) :
    Option ReflectivePresentationDecl :=
  match profile.presentations.filter fun declaration =>
      declaration.name == name with
  | [declaration] => some declaration
  | _ => none

/-- Presentation used to compare repeated metavariable occurrences. -/
def matchingPresentationForRule?
    (profile : ReflectionProfile) (rule : RewriteRule) :
    Option ReflectivePresentationDecl :=
  match reflectiveRuleForRule? profile rule with
  | some selection => presentationNamed? profile selection.matchingPresentation
  | none => none

/-- Presentation used to interpret explicit substitution in a contractum. -/
def substitutionPresentationForRule?
    (profile : ReflectionProfile) (rule : RewriteRule) :
    Option ReflectivePresentationDecl :=
  match reflectiveRuleForRule? profile rule with
  | some selection => presentationNamed? profile selection.substitutionPresentation
  | none => none

/-- Rule-local lookup depends only on the two reflective data tables. -/
theorem matchingPresentationForRule?_eq_of_reflectiveData_eq
    {profile₁ profile₂ : ReflectionProfile}
    (samePresentations : profile₁.presentations = profile₂.presentations)
    (sameRules : profile₁.rules = profile₂.rules)
    (rule : RewriteRule) :
    matchingPresentationForRule? profile₁ rule =
      matchingPresentationForRule? profile₂ rule := by
  simp [matchingPresentationForRule?, reflectiveRuleForRule?,
    presentationNamed?, samePresentations, sameRules]

theorem substitutionPresentationForRule?_eq_of_reflectiveData_eq
    {profile₁ profile₂ : ReflectionProfile}
    (samePresentations : profile₁.presentations = profile₂.presentations)
    (sameRules : profile₁.rules = profile₂.rules)
    (rule : RewriteRule) :
    substitutionPresentationForRule? profile₁ rule =
      substitutionPresentationForRule? profile₂ rule := by
  simp [substitutionPresentationForRule?, reflectiveRuleForRule?,
    presentationNamed?, samePresentations, sameRules]

@[simp] theorem matchingPresentationForRule?_eq_none_of_no_presentations
    {profile : ReflectionProfile} (empty : profile.presentations = [])
    (rule : RewriteRule) :
    matchingPresentationForRule? profile rule = none := by
  unfold matchingPresentationForRule?
  cases reflectiveRuleForRule? profile rule <;>
    simp [presentationNamed?, empty]

@[simp] theorem matchingPresentationForRule?_eq_none_of_no_rules
    {profile : ReflectionProfile} (empty : profile.rules = [])
    (rule : RewriteRule) :
    matchingPresentationForRule? profile rule = none := by
  simp [matchingPresentationForRule?, reflectiveRuleForRule?, empty]

@[simp] theorem substitutionPresentationForRule?_eq_none_of_no_presentations
    {profile : ReflectionProfile} (empty : profile.presentations = [])
    (rule : RewriteRule) :
    substitutionPresentationForRule? profile rule = none := by
  unfold substitutionPresentationForRule?
  cases reflectiveRuleForRule? profile rule <;>
    simp [presentationNamed?, empty]

@[simp] theorem substitutionPresentationForRule?_eq_none_of_no_rules
    {profile : ReflectionProfile} (empty : profile.rules = [])
    (rule : RewriteRule) :
    substitutionPresentationForRule? profile rule = none := by
  simp [substitutionPresentationForRule?, reflectiveRuleForRule?, empty]

/-! ## Static quote-drop normalization -/

/-- Apply the declared quote-drop equation after an application's children
have been normalized. -/
def finishNormalizeReflectiveApply
    (declaration : ReflectivePresentationDecl)
    (constructor : String) (normalizedArguments : List Pattern) : Pattern :=
  if constructor == declaration.quoteConstructor then
    match normalizedArguments with
    | [.apply drop [name]] =>
        if drop == declaration.dropConstructor then name
        else .apply constructor normalizedArguments
    | _ => .apply constructor normalizedArguments
  else
    .apply constructor normalizedArguments

mutual
  /-- Normalize the declared quote-drop equation throughout a pattern.  This
  is the equational operation; it never orients `drop (quote process)` into a
  process step.  Children are normalized before the outer equation is tested,
  so nested quote-drop equations cannot be hidden by an enclosing constructor. -/
  def normalizeReflective
      (declaration : ReflectivePresentationDecl) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        finishNormalizeReflectiveApply declaration constructor
          (normalizeReflectiveList declaration arguments)
    | .lambda binderName body =>
        .lambda binderName (normalizeReflective declaration body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames (normalizeReflective declaration body)
    | .subst body replacement =>
        .subst (normalizeReflective declaration body)
          (normalizeReflective declaration replacement)
    | .collection collectionType elements rest =>
        .collection collectionType
          (normalizeReflectiveList declaration elements) rest

  /-- List recursion for `normalizeReflective`. -/
  def normalizeReflectiveList
      (declaration : ReflectivePresentationDecl) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        normalizeReflective declaration pattern ::
          normalizeReflectiveList declaration patterns
end

/-- Normalize an operational substitution replacement while preserving a
quotation introduced by the rewrite rule itself.  The quoted process is
normalized, but the provenance-carrying outer quote is not cancelled. -/
def normalizeReflectiveReplacement
    (declaration : ReflectivePresentationDecl) (replacement : Pattern) : Pattern :=
  match replacement with
  | .apply constructor [payload] =>
      if constructor == declaration.quoteConstructor then
        .apply constructor [normalizeReflective declaration payload]
      else
        normalizeReflective declaration replacement
  | _ => normalizeReflective declaration replacement

end Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (finishNormalizeReflectiveApply)

/-- Splice a normalized occurrence of the declared parallel collection into
its parent parallel collection. -/
def parallelSplice (declaration : ReflectivePresentationDecl) : Pattern → List Pattern
  | pattern@(.collection collectionType elements none) =>
      if collectionType == declaration.parallelCollection then elements else [pattern]
  | pattern => [pattern]

/-- Normalize an already-recursively-normalized parallel element list. -/
def normalizeParallelElements
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) : List Pattern :=
  PatternCode.sortPatterns
    ((patterns.flatMap (parallelSplice declaration)).filter fun pattern =>
      pattern ≠ .apply declaration.parallelUnitConstructor [])

/-- Rebuild the declared parallel composition without representation-only
empty and singleton wrappers. -/
def collapseParallel (declaration : ReflectivePresentationDecl) : List Pattern → Pattern
  | [] => .apply declaration.parallelUnitConstructor []
  | [pattern] => pattern
  | patterns => .collection declaration.parallelCollection patterns none

mutual
  /-- Canonical representative compiled solely from a reflective declaration.

  It recursively orients the declaration's quote/drop equation and presents
  its parallel collection as a flattened, unit-free, structurally sorted bag.
  No executable drop step is introduced. -/
  def canonicalize
      (declaration : ReflectivePresentationDecl) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        finishNormalizeReflectiveApply declaration constructor
          (canonicalizeList declaration arguments)
    | .lambda binderName body =>
        .lambda binderName (canonicalize declaration body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames (canonicalize declaration body)
    | .subst body replacement =>
        .subst (canonicalize declaration body) (canonicalize declaration replacement)
    | .collection collectionType elements none =>
        let normalizedElements := canonicalizeList declaration elements
        if collectionType == declaration.parallelCollection then
          collapseParallel declaration
            (normalizeParallelElements declaration normalizedElements)
        else
          .collection collectionType normalizedElements none
    | .collection collectionType elements rest =>
        .collection collectionType (canonicalizeList declaration elements) rest

  def canonicalizeList
      (declaration : ReflectivePresentationDecl) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        canonicalize declaration pattern :: canonicalizeList declaration patterns
end

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Reflection

/-! ## Provenance-sensitive substitution -/

/-- The information about a canonical term that can expose a whole binder.
Parallel composition only needs to distinguish its unit, one surviving
term, and two or more terms; the order and payloads of the latter cannot
affect binder recognition. A drop retains this information about its name
because an enclosing quote can remove that drop. -/
inductive BinderHead where
  | index (level : Nat)
  | unit
  | drop (name : BinderHead)
  | opaque
  deriving DecidableEq

namespace BinderHead

/-- Parallel composition at the binder-observation boundary. -/
def join : BinderHead → BinderHead → BinderHead
  | .unit, right => right
  | left, .unit => left
  | _, _ => .opaque

@[simp] theorem unit_join (head : BinderHead) : join .unit head = head := rfl

@[simp] theorem join_unit (head : BinderHead) : join head .unit = head := by
  cases head <;> rfl

@[simp] theorem opaque_join (head : BinderHead) : join .opaque head = .opaque := by
  cases head <;> rfl

@[simp] theorem join_opaque (head : BinderHead) : join head .opaque = .opaque := by
  cases head <;> rfl

theorem join_comm (left right : BinderHead) : join left right = join right left := by
  cases left <;> cases right <;> rfl

theorem join_assoc (first second third : BinderHead) :
    join (join first second) third = join first (join second third) := by
  cases first <;> cases second <;> cases third <;> rfl

theorem join_of_ne_unit {left right : BinderHead}
    (leftNonunit : left ≠ .unit) (rightNonunit : right ≠ .unit) :
    join left right = .opaque := by
  cases left <;> cases right <;> simp_all [join]

theorem fold_append (left right : List BinderHead) :
    (left ++ right).foldr join .unit =
      join (left.foldr join .unit) (right.foldr join .unit) := by
  induction left with
  | nil => simp
  | cons head rest ih => simp [ih, join_assoc]

theorem fold_perm {left right : List BinderHead} (permutation : left.Perm right) :
    left.foldr join .unit = right.foldr join .unit :=
  permutation.foldr_eq' (fun a _ b _ rest => by
    rw [← join_assoc, join_comm b a, join_assoc]) _

/-- Read an application whose outer constructor is retained. -/
def rigid (declaration : ReflectivePresentationDecl) (constructor : String) :
    List BinderHead → BinderHead
  | [] => if constructor = declaration.parallelUnitConstructor then .unit else .opaque
  | [argument] => if constructor = declaration.dropConstructor then .drop argument else .opaque
  | _ => .opaque

/-- The quote/drop equation, followed by the observation of an application. -/
def apply (declaration : ReflectivePresentationDecl) (constructor : String)
    (arguments : List BinderHead) : BinderHead :=
  match arguments with
  | [.drop name] =>
      if constructor = declaration.quoteConstructor then name else rigid declaration constructor arguments
  | _ => rigid declaration constructor arguments

mutual
  /-- Compute precisely the head information needed for whole-name lookup,
  without sorting a parallel collection. -/
  def ofPattern (declaration : ReflectivePresentationDecl) : Pattern → BinderHead
    | .bvar level => .index level
    | .apply constructor arguments => apply declaration constructor (ofList declaration arguments)
    | .collection kind elements none =>
        if kind = declaration.parallelCollection then
          (ofList declaration elements).foldr join .unit
        else .opaque
    | _ => .opaque

  def ofList (declaration : ReflectivePresentationDecl) : List Pattern → List BinderHead
    | [] => []
    | head :: tail => ofPattern declaration head :: ofList declaration tail
end

theorem ofList_eq_map (declaration : ReflectivePresentationDecl) (terms : List Pattern) :
    ofList declaration terms = terms.map (ofPattern declaration) := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [ofList, ih]

end BinderHead

/-- Recognize the selected binder under the declaration's equations.
The caller shares ordinary name normalization between this test and
the retained spelling on a miss. -/
def matchesBinder (declaration : ReflectivePresentationDecl) (depth : Nat)
    (normalized : Pattern) : Bool :=
  decide (BinderHead.ofPattern declaration normalized = .index depth)

@[simp] theorem matchesBinder_bvar (declaration : ReflectivePresentationDecl) (depth level : Nat) :
    matchesBinder declaration depth (.bvar level) = (level == depth) := by
  apply Bool.eq_iff_iff.mpr
  simp [matchesBinder, BinderHead.ofPattern]

@[simp] theorem matchesBinder_fvar (declaration : ReflectivePresentationDecl) (depth : Nat) (name : String) :
    matchesBinder declaration depth (.fvar name) = false := rfl

/-! ## Resolving quotations of drops -/

mutual
  /-- The members of the declared parallel composition: nested occurrences
  are flattened and the declared unit contributes nothing. Every other term
  is a single member. -/
  def parallelLeaves (declaration : ReflectivePresentationDecl) : Pattern → List Pattern
    | .bvar index => [.bvar index]
    | .fvar name => [.fvar name]
    | .apply constructor [] =>
        if constructor = declaration.parallelUnitConstructor then []
        else [.apply constructor []]
    | .apply constructor (argument :: arguments) => [.apply constructor (argument :: arguments)]
    | .lambda binder body => [.lambda binder body]
    | .multiLambda arity binders body => [.multiLambda arity binders body]
    | .subst body replacement => [.subst body replacement]
    | .collection kind elements none =>
        if kind = declaration.parallelCollection then parallelLeavesList declaration elements
        else [.collection kind elements none]
    | .collection kind elements (some rest) => [.collection kind elements (some rest)]

  /-- List recursion for `parallelLeaves`. -/
  def parallelLeavesList (declaration : ReflectivePresentationDecl) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        parallelLeaves declaration pattern ++ parallelLeavesList declaration patterns
end

/-- The drop exposed by a parallel composition with exactly one member. -/
def exposedDrop? (declaration : ReflectivePresentationDecl) (pattern : Pattern) : Option Pattern :=
  match parallelLeaves declaration pattern with
  | [.apply constructor [name]] =>
      if constructor = declaration.dropConstructor then some name else none
  | _ => none

/-- The quote-drop equation, seen through the declared parallel unit and
nesting, at an application whose arguments are already resolved. -/
def finishResolveApply (declaration : ReflectivePresentationDecl) (constructor : String) :
    List Pattern → Pattern
  | [] => .apply constructor []
  | [payload] =>
      if constructor = declaration.quoteConstructor then
        match exposedDrop? declaration payload with
        | some name => name
        | none => .apply constructor [payload]
      else .apply constructor [payload]
  | first :: second :: rest => .apply constructor (first :: second :: rest)

mutual
  /-- Resolve every quotation whose payload is a drop modulo the declared
  parallel unit and nesting. Children are resolved first. Recognizing a
  name is not running its code: no drop is executed. -/
  def resolveQuotes (declaration : ReflectivePresentationDecl) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        finishResolveApply declaration constructor (resolveQuotesList declaration arguments)
    | .lambda binder body => .lambda binder (resolveQuotes declaration body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (resolveQuotes declaration body)
    | .subst body replacement =>
        .subst (resolveQuotes declaration body) (resolveQuotes declaration replacement)
    | .collection kind elements rest =>
        .collection kind (resolveQuotesList declaration elements) rest

  /-- List recursion for `resolveQuotes`. -/
  def resolveQuotesList (declaration : ReflectivePresentationDecl) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        resolveQuotes declaration pattern :: resolveQuotesList declaration patterns
end

/-! ## Provenance-sensitive substitution -/

/-- A drop that received the selected name: a received quotation runs. -/
def receive (declaration : ReflectivePresentationDecl) (constructor : String)
    (name : Pattern) : Pattern :=
  match name with
  | .apply quote [process] =>
      if quote = declaration.quoteConstructor then process else .apply constructor [name]
  | _ => .apply constructor [name]

mutual
  /-- Substitute structurally in a term whose quotations are resolved.
  `atIndex depth index` is what a bound index becomes under `depth`
  binders; `atIndex depth depth` is the name a selected drop receives.
  A literal quotation is opaque. A drop of the selected name receives it;
  every other drop is substituted through. -/
  def substituteResolved (declaration : ReflectivePresentationDecl)
      (atIndex : Nat → Nat → Pattern) : Nat → Pattern → Pattern
    | depth, .bvar index => atIndex depth index
    | _, .fvar name => .fvar name
    | _, .apply constructor [] => .apply constructor []
    | depth, .apply constructor [payload] =>
        if constructor = declaration.quoteConstructor then .apply constructor [payload]
        else if constructor = declaration.dropConstructor then
          if matchesBinder declaration depth payload then
            receive declaration constructor (atIndex depth depth)
          else .apply constructor [substituteResolved declaration atIndex depth payload]
        else .apply constructor [substituteResolved declaration atIndex depth payload]
    | depth, .apply constructor (first :: second :: rest) =>
        .apply constructor
          (substituteResolvedList declaration atIndex depth (first :: second :: rest))
    | depth, .lambda binder body =>
        .lambda binder (substituteResolved declaration atIndex (depth + 1) body)
    | depth, .multiLambda arity binders body =>
        .multiLambda arity binders (substituteResolved declaration atIndex (depth + arity) body)
    | depth, .subst body value =>
        .subst (substituteResolved declaration atIndex (depth + 1) body)
          (substituteResolved declaration atIndex depth value)
    | depth, .collection kind elements rest =>
        .collection kind (substituteResolvedList declaration atIndex depth elements) rest

  /-- List recursion for `substituteResolved`. -/
  def substituteResolvedList (declaration : ReflectivePresentationDecl)
      (atIndex : Nat → Nat → Pattern) : Nat → List Pattern → List Pattern
    | _, [] => []
    | depth, pattern :: patterns =>
        substituteResolved declaration atIndex depth pattern ::
          substituteResolvedList declaration atIndex depth patterns
end

/-- Compile paper-style reflective substitution on a process body: resolve
quotations of drops, then substitute structurally. The bound index at
`depth` becomes the replacement; every other index is unchanged. -/
def substituteReflective
    (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacementName body : Pattern) : Pattern :=
  substituteResolved declaration
    (fun level index => if index = level then replacementName else .bvar index) depth
    (resolveQuotes declaration body)

theorem parallelLeavesList_eq_flatMap (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    parallelLeavesList declaration patterns = patterns.flatMap (parallelLeaves declaration) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp [parallelLeavesList, ih]

theorem resolveQuotesList_eq_map (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    resolveQuotesList declaration patterns = patterns.map (resolveQuotes declaration) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp [resolveQuotesList, ih]

theorem substituteResolvedList_eq_map (declaration : ReflectivePresentationDecl)
    (atIndex : Nat → Nat → Pattern) (depth : Nat) (patterns : List Pattern) :
    substituteResolvedList declaration atIndex depth patterns =
      patterns.map (substituteResolved declaration atIndex depth) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp [substituteResolvedList, ih]

/-- Substitute a whole name modulo the declared equations. The mark records
whether this occurrence was supplied by the communication; any other name is
substituted like a term, so a quotation keeps its resolved spelling. -/
def substituteNameMark
    (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacementName name : Pattern) : Pattern × Bool :=
  if matchesBinder declaration depth (resolveQuotes declaration name) then
    (replacementName, true)
  else
    (substituteReflective declaration depth replacementName name, false)

/-- Pointwise `substituteReflective`. -/
def substituteReflectiveList
    (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacementName : Pattern) (patterns : List Pattern) : List Pattern :=
  patterns.map (substituteReflective declaration depth replacementName)

/-! ## Substitution under a declared quote scope -/

mutual
  /-- Substitute in a term whose quotations are resolved. `atIndex depth index`
  is what a bound index becomes outside quotations; `insideQuote` is the action
  used throughout a genuine quotation, which is entered. A drop of the selected
  binder receives `atIndex depth depth` (inside a quotation, `insideQuote depth
  depth`); every other drop is substituted through. `depth` counts the binders
  between the eliminated one and the current position, quotations included:
  a quotation is not a binder. -/
  def substituteViewed (declaration : ReflectivePresentationDecl)
      (insideQuote : Nat → Nat → Pattern) :
      (Nat → Nat → Pattern) → Nat → Pattern → Pattern
    | atIndex, depth, .bvar index => atIndex depth index
    | _, _, .fvar name => .fvar name
    | _, _, .apply constructor [] => .apply constructor []
    | atIndex, depth, .apply constructor [payload] =>
        if constructor = declaration.quoteConstructor then
          .apply constructor [substituteViewed declaration insideQuote insideQuote depth payload]
        else if constructor = declaration.dropConstructor then
          if matchesBinder declaration depth payload then
            receive declaration constructor (atIndex depth depth)
          else .apply constructor [substituteViewed declaration insideQuote atIndex depth payload]
        else .apply constructor [substituteViewed declaration insideQuote atIndex depth payload]
    | atIndex, depth, .apply constructor (first :: second :: rest) =>
        .apply constructor
          (substituteViewedList declaration insideQuote atIndex depth (first :: second :: rest))
    | atIndex, depth, .lambda binder body =>
        .lambda binder (substituteViewed declaration insideQuote atIndex (depth + 1) body)
    | atIndex, depth, .multiLambda arity binders body =>
        .multiLambda arity binders
          (substituteViewed declaration insideQuote atIndex (depth + arity) body)
    | atIndex, depth, .subst body value =>
        .subst (substituteViewed declaration insideQuote atIndex (depth + 1) body)
          (substituteViewed declaration insideQuote atIndex depth value)
    | atIndex, depth, .collection kind elements rest =>
        .collection kind (substituteViewedList declaration insideQuote atIndex depth elements) rest

  /-- List recursion for `substituteViewed`. -/
  def substituteViewedList (declaration : ReflectivePresentationDecl)
      (insideQuote : Nat → Nat → Pattern) :
      (Nat → Nat → Pattern) → Nat → List Pattern → List Pattern
    | _, _, [] => []
    | atIndex, depth, pattern :: patterns =>
        substituteViewed declaration insideQuote atIndex depth pattern ::
          substituteViewedList declaration insideQuote atIndex depth patterns
end

theorem substituteViewedList_eq_map (declaration : ReflectivePresentationDecl)
    (insideQuote atIndex : Nat → Nat → Pattern) (depth : Nat) (patterns : List Pattern) :
    substituteViewedList declaration insideQuote atIndex depth patterns =
      patterns.map (substituteViewed declaration insideQuote atIndex depth) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp [substituteViewedList, ih]

/-- What a bound index becomes inside a genuine quotation under a view, given the
action `outside` used outside quotations. Only the selected binder is treated
differently. -/
def _root_.Mettapedia.OSLF.MeTTaIL.Syntax.QuoteView.inside : QuoteView → (Nat → Nat → Pattern) → Nat → Nat → Pattern
  | .apply, outside => outside
  | .freeze frozen, outside => fun level index =>
      if index = level then frozen.spelling else outside level index
  | .closure context, outside => fun level index =>
      if index = level then .apply context [outside level level] else outside level index

/-- Substitution under a quote scope, on a body whose quotations are not yet
resolved. A closed scope keeps every genuine quotation opaque; a reaching scope
enters it with the view's inside action. -/
def substituteScoped (declaration : ReflectivePresentationDecl) :
    QuoteScope → (Nat → Nat → Pattern) → Nat → Pattern → Pattern
  | .closed, atIndex, depth, body =>
      substituteResolved declaration atIndex depth (resolveQuotes declaration body)
  | .reaching view, atIndex, depth, body =>
      substituteViewed declaration (view.inside atIndex) atIndex depth (resolveQuotes declaration body)

/-- **The substitution a presentation declares.** The bound index at `depth`
becomes the replacement and every other index is unchanged; at a genuine
quotation the presentation's quote scope decides. -/
def substituteDeclared (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacementName body : Pattern) : Pattern :=
  substituteScoped declaration declaration.quoteScope
    (fun level index => if index = level then replacementName else .bvar index) depth body

/-- A closed presentation declares `substituteReflective`. -/
@[simp] theorem substituteDeclared_of_closed {declaration : ReflectivePresentationDecl}
    (closed : declaration.quoteScope = .closed) (depth : Nat) (replacementName body : Pattern) :
    substituteDeclared declaration depth replacementName body =
      substituteReflective declaration depth replacementName body := by
  simp only [substituteDeclared, closed, substituteScoped, substituteReflective]

mutual
  /-- Every quotation of a term is closed code. On a resolved term every
  quotation is genuine. -/
  def closedCode (declaration : ReflectivePresentationDecl) : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply _ [] => true
    | .apply constructor [payload] =>
        if constructor = declaration.quoteConstructor then
          payload.isWellScopedAt 0 && closedCode declaration payload
        else closedCode declaration payload
    | .apply _ (first :: second :: rest) => closedCodeList declaration (first :: second :: rest)
    | .lambda _ body => closedCode declaration body
    | .multiLambda _ _ body => closedCode declaration body
    | .subst body value => closedCode declaration body && closedCode declaration value
    | .collection _ elements _ => closedCodeList declaration elements

  /-- List recursion for `closedCode`. -/
  def closedCodeList (declaration : ReflectivePresentationDecl) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => closedCode declaration pattern && closedCodeList declaration patterns
end

/-- **Quote admission of a closed scope.** On the resolved term, no genuine
quotation mentions an object binder bound outside it. -/
def QuotesClosed (declaration : ReflectivePresentationDecl) (term : Pattern) : Prop :=
  closedCode declaration (resolveQuotes declaration term) = true

instance (declaration : ReflectivePresentationDecl) (term : Pattern) :
    Decidable (QuotesClosed declaration term) :=
  inferInstanceAs (Decidable (_ = true))

/-- **Admission of a quotation.** Under a closed scope a quotation's code is
closed with respect to object binders, as CMTT types the body of `box` in the
empty object context; a quotation whose payload exposes a drop denotes that
name and is not code. A reaching scope admits every quotation. -/
def quoteAdmits (declaration : ReflectivePresentationDecl) (payload : Pattern) : Bool :=
  match declaration.quoteScope with
  | .closed => closedCode declaration (resolveQuotes declaration (.apply declaration.quoteConstructor [payload]))
  | .reaching _ => true

theorem quoteAdmits_of_reaching {declaration : ReflectivePresentationDecl} {view : QuoteView}
    (reaching : declaration.quoteScope = .reaching view) (payload : Pattern) :
    quoteAdmits declaration payload = true := by
  simp [quoteAdmits, reaching]

theorem quoteAdmits_of_closed {declaration : ReflectivePresentationDecl}
    (closed : declaration.quoteScope = .closed) (payload : Pattern) :
    quoteAdmits declaration payload = true ↔
      QuotesClosed declaration (.apply declaration.quoteConstructor [payload]) := by
  simp [quoteAdmits, closed, QuotesClosed]

/-! ## Binding application -/

mutual
  /-- Apply matcher bindings while interpreting explicit `.subst` nodes using
  the selected reflective declaration.  All other binding behavior, including
  collection-rest handling, matches `Match.applyBindings`. -/
  def applyBindingsReflective
      (declaration : ReflectivePresentationDecl)
      (bindings : Bindings) : Pattern → Pattern
    | .fvar name =>
        match bindings.find? (·.1 == name) with
        | some (_, value) => value
        | none => .fvar name
    | .bvar index => .bvar index
    | .apply constructor arguments =>
        .apply constructor
          (applyBindingsReflectiveList declaration bindings arguments)
    | .lambda binderName body =>
        .lambda binderName (applyBindingsReflective declaration bindings body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames
          (applyBindingsReflective declaration bindings body)
    | .subst body replacement =>
        let body' := applyBindingsReflective declaration bindings body
        let replacement' :=
          normalizeReflectiveReplacement declaration
            (applyBindingsReflective declaration bindings replacement)
        substituteDeclared declaration 0 replacement' body'
    | .collection collectionType elements rest =>
        let elements' :=
          applyBindingsReflectiveList declaration bindings elements
        let (restElements, unresolvedRest) := match rest with
          | some restName =>
              match bindings.find? (·.1 == restName) with
              | some (_, .collection boundType boundElements none) =>
                  if boundType == collectionType then (boundElements, none)
                  else ([], some restName)
              | _ => ([], some restName)
          | none => ([], none)
        .collection collectionType (elements' ++ restElements) unresolvedRest

  /-- List recursion for reflective binding application. -/
  def applyBindingsReflectiveList
      (declaration : ReflectivePresentationDecl)
      (bindings : Bindings) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        applyBindingsReflective declaration bindings pattern ::
          applyBindingsReflectiveList declaration bindings patterns
end

/-- Rule-aware binding application using one explicit reflection profile. -/
def applyBindingsForRuleUsing
    (profile : ReflectionProfile) (rule : RewriteRule)
    (bindings : Bindings) : Pattern :=
  match substitutionPresentationForRule? profile rule with
  | some declaration => applyBindingsReflective declaration bindings rule.right
  | none => Match.applyRuleBindings rule bindings

/-- An empty reflection profile selects ordinary syntactic substitution, made
scope-correct: a matched value is shifted from the depth at which the rule's
left-hand side captured it to the depth at which its right-hand side uses it. -/
@[simp] theorem applyBindingsForRuleUsing_empty
    (rule : RewriteRule) (bindings : Bindings) :
    applyBindingsForRuleUsing .empty rule bindings =
      Match.applyRuleBindings rule bindings := by
  simp [applyBindingsForRuleUsing, ReflectionProfile.empty]

/-- On a rule that never moves a metavariable across a binder this is the plain
applier, so nothing changes for such a rule. -/
theorem applyBindingsForRuleUsing_empty_eq_applyBindings
    (rule : RewriteRule) (bindings : Bindings)
    (aligned : Match.ruleDepthAligned rule = true) :
    applyBindingsForRuleUsing .empty rule bindings =
      applyBindings bindings rule.right := by
  rw [applyBindingsForRuleUsing_empty]
  exact Match.applyRuleBindings_eq_applyBindings rule bindings aligned

/-- Binding application for the five-field core.  Reflection-free operation
is definitionally ordinary syntactic substitution. -/
def applyBindingsForRule
    (_language : LanguageDef) (rule : RewriteRule)
    (bindings : Bindings) : Pattern :=
  applyBindingsForRuleUsing .empty rule bindings

/-- Rule-aware substitution is unchanged when two languages share both
reflective data tables. -/
theorem applyBindingsForRuleUsing_eq_of_reflectiveData_eq
    {profile₁ profile₂ : ReflectionProfile}
    (samePresentations : profile₁.presentations = profile₂.presentations)
    (sameRules : profile₁.rules = profile₂.rules)
    (rule : RewriteRule) (bindings : Bindings) :
    applyBindingsForRuleUsing profile₁ rule bindings =
      applyBindingsForRuleUsing profile₂ rule bindings := by
  simp only [applyBindingsForRuleUsing]
  rw [substitutionPresentationForRule?_eq_of_reflectiveData_eq
    samePresentations sameRules rule]

theorem applyBindingsForRule_eq_syntactic_of_no_presentation
    {profile : ReflectionProfile} {rule : RewriteRule}
    (missing : substitutionPresentationForRule? profile rule = none)
    (bindings : Bindings) :
    applyBindingsForRuleUsing profile rule bindings =
      Match.applyRuleBindings rule bindings := by
  simp [applyBindingsForRuleUsing, missing]

@[simp] theorem applyBindingsForRule_eq_syntactic_of_no_presentations
    {profile : ReflectionProfile} (empty : profile.presentations = [])
    (rule : RewriteRule) (bindings : Bindings) :
    applyBindingsForRuleUsing profile rule bindings =
      Match.applyRuleBindings rule bindings := by
  apply applyBindingsForRule_eq_syntactic_of_no_presentation
  exact substitutionPresentationForRule?_eq_none_of_no_presentations empty rule

@[simp] theorem applyBindingsForRule_eq_syntactic_of_no_reflectiveRules
    {profile : ReflectionProfile} (empty : profile.rules = [])
    (rule : RewriteRule) (bindings : Bindings) :
    applyBindingsForRuleUsing profile rule bindings =
      Match.applyRuleBindings rule bindings := by
  apply applyBindingsForRule_eq_syntactic_of_no_presentation
  exact substitutionPresentationForRule?_eq_none_of_no_rules empty rule

@[simp] theorem applyBindingsForRule_eq_syntactic
    (language : LanguageDef) (rule : RewriteRule) (bindings : Bindings) :
    applyBindingsForRule language rule bindings =
      Match.applyRuleBindings rule bindings := by
  simp [applyBindingsForRule, applyBindingsForRuleUsing,
    ReflectionProfile.empty, substitutionPresentationForRule?,
    reflectiveRuleForRule?]

/-- And on a rule that never moves a metavariable across a binder it is the
plain applier, so a depth-aligned language is unaffected. -/
theorem applyBindingsForRule_eq_applyBindings
    (language : LanguageDef) (rule : RewriteRule) (bindings : Bindings)
    (aligned : Match.ruleDepthAligned rule = true) :
    applyBindingsForRule language rule bindings =
      applyBindings bindings rule.right := by
  rw [applyBindingsForRule_eq_syntactic]
  exact Match.applyRuleBindings_eq_applyBindings rule bindings aligned

/-! ## Executable boundary examples -/

private def fixtureDeclaration : ReflectivePresentationDecl where
  name := "fixture"
  processSort := "Proc"
  nameSort := "Name"
  quoteConstructor := "NQuote"
  dropConstructor := "PDrop"
  parallelCollection := .hashBag
  parallelUnitConstructor := "PZero"
  quoteDropEquation := "QuoteDrop"
  -- Closed, as rho, whose COMM-supplied quotations these examples exercise.
  quoteScope := .closed

/-- Positive: a COMM-supplied quotation exposes the matched dropped name. -/
example :
    substituteReflective fixtureDeclaration 0
        (.apply "NQuote" [.apply "PZero" []])
        (.apply "PDrop" [.bvar 0]) =
      .apply "PZero" [] := by
  decide +kernel

/-- Regression: normalization must see a quote-drop equation nested beneath
an ordinary drop, without turning the outer drop into an executable step. -/
example :
    normalizeReflective fixtureDeclaration
        (.apply "PDrop"
          [.apply "NQuote" [.apply "PDrop" [.fvar "x"]]]) =
      .apply "PDrop" [.fvar "x"] := by
  rfl

/-- Regression: a quote introduced by COMM remains present even when its
payload is a drop; only the payload is statically normalized. -/
example :
    let payload := .apply "PDrop"
      [.apply "NQuote" [.apply "PZero" []]]
    substituteReflective fixtureDeclaration 0
        (normalizeReflectiveReplacement fixtureDeclaration
          (.apply "NQuote" [payload]))
        (.apply "PDrop" [.bvar 0]) =
      payload := by
  rfl

/-- Negative: a free dropped quotation is not an executable reduction. -/
example :
    substituteReflective fixtureDeclaration 0
        (.apply "NQuote" [.apply "PZero" []])
        (.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]) =
      .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]] := by
  rfl

/-- Negative: substitution does not enter literal quoted code. -/
example :
    substituteReflective fixtureDeclaration 0
        (.apply "NQuote" [.apply "PZero" []])
        (.apply "NQuote"
          [.apply "POutput" [.bvar 0, .apply "PZero" []]]) =
      .apply "NQuote"
        [.apply "POutput" [.bvar 0, .apply "PZero" []]] := by
  rfl

/-- Regression: a free drop around quoted code remains inert, and substitution
does not enter the quoted process through the outer unary constructor. -/
example :
    substituteReflective fixtureDeclaration 0
        (.apply "NQuote" [.apply "PZero" []])
        (.apply "PDrop"
          [.apply "NQuote"
            [.apply "POutput" [.bvar 0, .apply "PZero" []]]]) =
      .apply "PDrop"
        [.apply "NQuote"
          [.apply "POutput" [.bvar 0, .apply "PZero" []]]] := by
  rfl

/-- Positive: `@(*(*y))` is the name `*y`, so the bound drop inside it
receives the communicated quotation. -/
example :
    substituteReflective fixtureDeclaration 0
        (.apply "NQuote" [.apply "PZero" []])
        (.apply "NQuote" [.apply "PDrop" [.apply "PDrop" [.bvar 0]]]) =
      .apply "PZero" [] := by
  decide +kernel

/-- Positive: a drop of a compound name that is not the bound name is
substituted through. -/
example :
    substituteReflective fixtureDeclaration 0
        (.apply "NQuote" [.apply "PZero" []])
        (.apply "PDrop" [.apply "POutput" [.bvar 0, .apply "PZero" []]]) =
      .apply "PDrop" [.apply "POutput"
        [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []]] := by
  decide +kernel

end Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Reflection

private theorem normalize_list_eq_map (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) : normalizeReflectiveList declaration patterns =
      patterns.map (normalizeReflective declaration) := by
  induction patterns with
  | nil => rfl
  | cons head tail ih => simp only [normalizeReflectiveList, List.map_cons, ih]

theorem finish_normalize_free_names (declaration : ReflectivePresentationDecl)
    (constructor : String) (arguments : List Pattern) :
    (finishNormalizeReflectiveApply declaration constructor arguments).freeFvarNames =
      arguments.flatMap Pattern.freeFvarNames := by
  unfold finishNormalizeReflectiveApply
  split
  · split
    · split <;> simp only [Pattern.freeFvarNames, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    · simp only [Pattern.freeFvarNames]
  · simp only [Pattern.freeFvarNames]

theorem normalize_reflective_free_names (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) : (normalizeReflective declaration pattern).freeFvarNames =
      pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments ih =>
      simp only [normalizeReflective, finish_normalize_free_names, normalize_list_eq_map,
        Pattern.freeFvarNames, List.flatMap_map]
      exact List.flatMap_congr (fun pattern member => ih pattern member)
  | hlambda binder body ih => simpa only [normalizeReflective, Pattern.freeFvarNames] using ih
  | hmultiLambda arity binders body ih => simpa only [normalizeReflective, Pattern.freeFvarNames] using ih
  | hsubst body replacement ihBody ihReplacement =>
      simp only [normalizeReflective, Pattern.freeFvarNames, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      simp only [normalizeReflective, normalize_list_eq_map, Pattern.freeFvarNames, List.flatMap_map]
      exact congrArg (· ++ rest.toList) (List.flatMap_congr (fun pattern member => ih pattern member))

theorem normalize_replacement_free_names (declaration : ReflectivePresentationDecl)
    (replacement : Pattern) :
    (normalizeReflectiveReplacement declaration replacement).freeFvarNames =
      replacement.freeFvarNames := by
  unfold normalizeReflectiveReplacement
  split
  · split
    · simp only [Pattern.freeFvarNames, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, normalize_reflective_free_names]
    · exact normalize_reflective_free_names declaration _
  · exact normalize_reflective_free_names declaration _

theorem parallel_leaves_free_names (declaration : ReflectivePresentationDecl)
    {pattern member : Pattern} (membership : member ∈ parallelLeaves declaration pattern) :
    ∀ free ∈ member.freeFvarNames, free ∈ pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hcollection kind elements rest ih =>
      cases rest with
      | some rest =>
          simp only [parallelLeaves, List.mem_singleton] at membership
          subst membership; exact fun _ => id
      | none =>
          by_cases parallel : kind = declaration.parallelCollection
          · simp only [parallelLeaves, parallel, if_true, parallelLeavesList_eq_flatMap,
              List.mem_flatMap] at membership
            obtain ⟨element, elementMember, membership⟩ := membership
            intro free occurs
            simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
            exact .inl ⟨element, elementMember, ih element elementMember membership free occurs⟩
          · simp only [parallelLeaves, parallel, if_false, List.mem_singleton] at membership
            subst membership; exact fun _ => id
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          by_cases unit : constructor = declaration.parallelUnitConstructor
          · simp [parallelLeaves, unit] at membership
          · simp only [parallelLeaves, unit, if_false, List.mem_singleton] at membership
            subst membership; exact fun _ => id
      | cons argument arguments =>
          simp only [parallelLeaves, List.mem_singleton] at membership
          subst membership; exact fun _ => id
  | hbvar index =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fun _ => id
  | hfvar name =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fun _ => id
  | hlambda binder body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fun _ => id
  | hmultiLambda arity binders body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fun _ => id
  | hsubst body replacement ihBody ihReplacement =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact fun _ => id

/-- Resolving quotations introduces no free name. -/
theorem resolve_quotes_free_names (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    ∀ free ∈ (resolveQuotes declaration pattern).freeFvarNames, free ∈ pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => exact fun _ => id
  | hfvar name => exact fun _ => id
  | hlambda binder body ih => simpa only [resolveQuotes, Pattern.freeFvarNames] using ih
  | hmultiLambda arity binders body ih => simpa only [resolveQuotes, Pattern.freeFvarNames] using ih
  | hsubst body replacement ihBody ihReplacement =>
      intro free occurs
      simp only [resolveQuotes, Pattern.freeFvarNames, List.mem_append] at occurs ⊢
      exact occurs.imp (ihBody free) (ihReplacement free)
  | hcollection kind elements rest ih =>
      intro free occurs
      simp only [resolveQuotes, resolveQuotesList_eq_map, Pattern.freeFvarNames, List.mem_append,
        List.flatMap_map, List.mem_flatMap] at occurs ⊢
      rcases occurs with ⟨element, member, occurs⟩ | occurs
      · exact .inl ⟨element, member, ih element member free occurs⟩
      · exact .inr occurs
  | happly constructor arguments ih =>
      have mapped : ∀ free ∈ (arguments.map (resolveQuotes declaration)).flatMap Pattern.freeFvarNames,
          free ∈ arguments.flatMap Pattern.freeFvarNames := by
        intro free occurs
        simp only [List.flatMap_map, List.mem_flatMap] at occurs ⊢
        obtain ⟨argument, member, occurs⟩ := occurs
        exact ⟨argument, member, ih argument member free occurs⟩
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      intro free occurs
      simp only [Pattern.freeFvarNames]
      apply mapped free
      revert occurs
      generalize arguments.map (resolveQuotes declaration) = resolved
      intro occurs
      match resolved, occurs with
      | [], occurs => simp [finishResolveApply, Pattern.freeFvarNames] at occurs
      | first :: second :: rest, occurs =>
          simpa [finishResolveApply, Pattern.freeFvarNames] using occurs
      | [payload], occurs =>
          simp only [finishResolveApply] at occurs
          split at occurs
          · split at occurs
            · rename_i name exposed
              have leaves : parallelLeaves declaration payload =
                  [.apply declaration.dropConstructor [name]] := by
                unfold exposedDrop? at exposed
                split at exposed
                · rename_i drop argument same
                  split at exposed
                  · rename_i dropped
                    cases exposed
                    rw [same, dropped]
                  · cases exposed
                · cases exposed
              have inDrop := parallel_leaves_free_names declaration
                (by rw [leaves]; exact List.mem_singleton_self _) free
                (by simpa [Pattern.freeFvarNames] using occurs)
              simpa using inDrop
            · simpa [Pattern.freeFvarNames] using occurs
          · simpa [Pattern.freeFvarNames] using occurs

#print axioms Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finish_normalize_free_names
#print axioms Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.normalize_reflective_free_names
#print axioms Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.normalize_replacement_free_names
#print axioms Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolve_quotes_free_names

end Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
