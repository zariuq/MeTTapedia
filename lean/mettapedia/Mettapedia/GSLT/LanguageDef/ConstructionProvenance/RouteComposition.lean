import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

/-!
# Composition of open construction routes

Closed construction trees record completed language-engineering histories.
This module supplies their compositional source: open, many-sorted routes with
typed variables.  A substitution replaces each variable by a route of exactly
the required kind.  Identity and associative substitution make route
composition lawful before any route is evaluated or flattened.
-/

namespace Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

universe uKind uObject uSource uOperation

/-- A de Bruijn position proving that one kind occurs in an ordered kind
context. -/
inductive ConstructionVariable {Kind : Type uKind} :
    List Kind → Kind → Type uKind where
  | here {kind : Kind} {kinds : List Kind} :
      ConstructionVariable (kind :: kinds) kind
  | there {kind other : Kind} {kinds : List Kind} :
      ConstructionVariable kinds kind →
        ConstructionVariable (other :: kinds) kind

variable (algebra :
  ManySortedConstructionAlgebra.{uKind, uObject, uSource, uOperation})

mutual
  /-- A well-sorted construction route with typed open inputs. -/
  inductive OpenConstructionRoute
      (algebra :
        ManySortedConstructionAlgebra.{uKind, uObject, uSource, uOperation})
      (context : List algebra.Kind) :
      algebra.Kind → Type (max uKind (max uSource uOperation))
    | input {kind : algebra.Kind}
        (position : ConstructionVariable context kind) :
        OpenConstructionRoute algebra context kind
    | source {kind : algebra.Kind} (value : algebra.Source kind) :
        OpenConstructionRoute algebra context kind
    | apply {inputs : List algebra.Kind} {output : algebra.Kind}
        (operation : algebra.Operation inputs output)
        (arguments : OpenConstructionArguments algebra context inputs) :
        OpenConstructionRoute algebra context output

  /-- Ordered children of an open construction operation. -/
  inductive OpenConstructionArguments
      (algebra :
        ManySortedConstructionAlgebra.{uKind, uObject, uSource, uOperation})
      (context : List algebra.Kind) :
      List algebra.Kind → Type (max uKind (max uSource uOperation))
    | nil : OpenConstructionArguments algebra context []
    | cons {kind : algebra.Kind} {kinds : List algebra.Kind}
        (head : OpenConstructionRoute algebra context kind)
        (tail : OpenConstructionArguments algebra context kinds) :
        OpenConstructionArguments algebra context (kind :: kinds)
end

/-- Read one family value at a typed variable position. -/
def ConstructionVariable.lookup
    {Kind : Type uKind} {Family : Kind → Type uObject}
    {context : List Kind} {kind : Kind}
    (position : ConstructionVariable context kind)
    (values : FamilyList Family context) : Family kind :=
  match position, values with
  | .here, .cons head _ => head
  | .there tailPosition, .cons _ tail => tailPosition.lookup tail

namespace OpenConstructionRoute

/-! ## Evaluation -/

mutual
  /-- Universe-lifted evaluator used by the mutual route/argument recursion. -/
  def evaluateLifted {context : List algebra.Kind} {output : algebra.Kind}
      (environment : FamilyList algebra.Object context) :
      OpenConstructionRoute algebra context output →
        ULift.{uKind} (algebra.Object output)
    | .input position => .up (position.lookup environment)
    | .source value => .up (algebra.interpretSource value)
    | .apply operation arguments =>
        .up (algebra.interpretOperation operation
          (OpenConstructionArguments.evaluate environment arguments))

  /-- Evaluate the ordered children of an open operation. -/
  def OpenConstructionArguments.evaluate
      {context inputs : List algebra.Kind}
      (environment : FamilyList algebra.Object context) :
      OpenConstructionArguments algebra context inputs →
        FamilyList algebra.Object inputs
    | .nil => .nil
    | .cons head tail =>
        .cons (evaluateLifted environment head).down
          (OpenConstructionArguments.evaluate environment tail)
end

/-- Evaluate an open route under a value for every typed variable. -/
def evaluate {context : List algebra.Kind} {output : algebra.Kind}
    (environment : FamilyList algebra.Object context)
    (route : OpenConstructionRoute algebra context output) :
    algebra.Object output :=
  (evaluateLifted algebra environment route).down

/-! ## Closed-route inclusion and closure -/

mutual
  /-- Regard a closed construction tree as an open route in any context. -/
  def ofClosed {context : List algebra.Kind} {output : algebra.Kind} :
      ConstructionTree algebra output →
        OpenConstructionRoute algebra context output
    | .source value => .source value
    | .apply operation arguments =>
        .apply operation (OpenConstructionArguments.ofClosed arguments)

  /-- Include all children of a closed operation. -/
  def OpenConstructionArguments.ofClosed
      {context inputs : List algebra.Kind} :
      ConstructionArguments algebra inputs →
        OpenConstructionArguments algebra context inputs
    | .nil => .nil
    | .cons head tail =>
        .cons (ofClosed head)
          (OpenConstructionArguments.ofClosed tail)
end

mutual
  /-- Close a route with no remaining context. -/
  def close {output : algebra.Kind} :
      OpenConstructionRoute algebra [] output → ConstructionTree algebra output
    | .input position => nomatch position
    | .source value => .source value
    | .apply operation arguments =>
        .apply operation (OpenConstructionArguments.close arguments)

  /-- Close all children of a variable-free operation. -/
  def OpenConstructionArguments.close {inputs : List algebra.Kind} :
      OpenConstructionArguments algebra [] inputs →
        ConstructionArguments algebra inputs
    | .nil => .nil
    | .cons head tail =>
        .cons (close head) (OpenConstructionArguments.close tail)
end

/-! ## Weakening and substitution -/

mutual
  /-- Add one unused typed variable to the front of an open route's context. -/
  def weaken {context : List algebra.Kind} {output newKind : algebra.Kind} :
      OpenConstructionRoute algebra context output →
        OpenConstructionRoute algebra (newKind :: context) output
    | .input position => .input (.there position)
    | .source value => .source value
    | .apply operation arguments =>
        .apply operation (OpenConstructionArguments.weaken arguments)

  /-- Weaken all children of an open operation. -/
  def OpenConstructionArguments.weaken
      {context inputs : List algebra.Kind} {newKind : algebra.Kind} :
      OpenConstructionArguments algebra context inputs →
        OpenConstructionArguments algebra (newKind :: context) inputs
    | .nil => .nil
    | .cons head tail =>
        .cons (weaken head)
          (OpenConstructionArguments.weaken tail)
end

/-- A typed simultaneous substitution from one variable context to another. -/
abbrev ConstructionSubstitution
    (fromVariables toVariables : List algebra.Kind) :=
  FamilyList
    (fun kind => OpenConstructionRoute algebra toVariables kind)
    fromVariables

mutual
  /-- Substitute an open route for each typed variable. -/
  def substitute {fromVariables toVariables : List algebra.Kind}
      {output : algebra.Kind}
      (route : OpenConstructionRoute algebra fromVariables output)
      (substitution :
        ConstructionSubstitution algebra fromVariables toVariables) :
      OpenConstructionRoute algebra toVariables output :=
    match route with
    | .input position => position.lookup substitution
    | .source value => .source value
    | .apply operation arguments =>
        .apply operation
          (OpenConstructionArguments.substitute arguments substitution)

  /-- Substitute through every child of an open operation. -/
  def OpenConstructionArguments.substitute
      {fromVariables toVariables inputs : List algebra.Kind}
      (arguments : OpenConstructionArguments algebra fromVariables inputs)
      (substitution :
        ConstructionSubstitution algebra fromVariables toVariables) :
      OpenConstructionArguments algebra toVariables inputs :=
    match arguments with
    | .nil => .nil
    | .cons head tail =>
        .cons (substitute head substitution)
          (OpenConstructionArguments.substitute tail substitution)
end

/-- Identity substitution for a typed variable context. -/
def identitySubstitution : (context : List algebra.Kind) →
    ConstructionSubstitution algebra context context
  | [] => .nil
  | _ :: context =>
      .cons (.input .here)
        (FamilyList.map
          (fun _ route => weaken (algebra := algebra) route)
          (identitySubstitution context))

/-- Sequential composition of typed substitutions. -/
def composeSubstitution
    {firstVariables middleVariables lastVariables : List algebra.Kind}
    (first :
      ConstructionSubstitution algebra firstVariables middleVariables)
    (second :
      ConstructionSubstitution algebra middleVariables lastVariables) :
    ConstructionSubstitution algebra firstVariables lastVariables :=
  FamilyList.map (fun _ route => substitute (algebra := algebra) route second) first

/-! ## Composition laws -/

@[simp] theorem ConstructionVariable.lookup_map
    {Kind : Type uKind}
    {First : Kind → Type uObject} {Second : Kind → Type uSource}
    (function : ∀ kind, First kind → Second kind)
    {context : List Kind} {kind : Kind}
    (position : ConstructionVariable context kind)
    (values : FamilyList First context) :
    position.lookup (FamilyList.map function values) =
      function kind (position.lookup values) := by
  induction position with
  | here => cases values; rfl
  | there position inductionHypothesis =>
      cases values with
      | cons _ tail => exact inductionHypothesis tail

@[simp] theorem lookup_identitySubstitution
    {context : List algebra.Kind} {kind : algebra.Kind}
    (position : ConstructionVariable context kind) :
    position.lookup (identitySubstitution (algebra := algebra) context) =
      OpenConstructionRoute.input position := by
  induction position with
  | here => rfl
  | @there kind other context position inductionHypothesis =>
      change
        position.lookup
            (FamilyList.map
              (fun _ route => weaken (algebra := algebra) route)
              (identitySubstitution (algebra := algebra) context)) =
          .input (.there position)
      rw [ConstructionVariable.lookup_map, inductionHypothesis]
      rfl

mutual
  @[simp] theorem substitute_identity
      {context : List algebra.Kind} {output : algebra.Kind}
      (route : OpenConstructionRoute algebra context output) :
      substitute (algebra := algebra) route
          (identitySubstitution (algebra := algebra) context) = route := by
    cases route with
    | input position =>
        exact lookup_identitySubstitution (algebra := algebra) position
    | source value => rfl
    | apply operation arguments =>
        simp only [substitute]
        rw [OpenConstructionArguments.substitute_identity arguments]

  @[simp] theorem OpenConstructionArguments.substitute_identity
      {context inputs : List algebra.Kind}
      (arguments : OpenConstructionArguments algebra context inputs) :
      OpenConstructionArguments.substitute (algebra := algebra) arguments
          (identitySubstitution (algebra := algebra) context) = arguments := by
    cases arguments with
    | nil => rfl
    | cons head tail =>
        simp only [OpenConstructionArguments.substitute]
        rw [substitute_identity head,
          OpenConstructionArguments.substitute_identity tail]
end

mutual
  theorem substitute_assoc
      {firstVariables middleVariables lastVariables : List algebra.Kind}
      {output : algebra.Kind}
      (route : OpenConstructionRoute algebra firstVariables output)
      (first :
        ConstructionSubstitution algebra firstVariables middleVariables)
      (second :
        ConstructionSubstitution algebra middleVariables lastVariables) :
      substitute (algebra := algebra)
          (substitute (algebra := algebra) route first) second =
        substitute (algebra := algebra) route
          (composeSubstitution (algebra := algebra) first second) := by
    cases route with
    | input position =>
        exact (ConstructionVariable.lookup_map
          (fun _ route => substitute (algebra := algebra) route second) position first).symm
    | source value => rfl
    | apply operation arguments =>
        simp only [substitute]
        rw [OpenConstructionArguments.substitute_assoc arguments first second]

  theorem OpenConstructionArguments.substitute_assoc
      {firstVariables middleVariables lastVariables inputs : List algebra.Kind}
      (arguments : OpenConstructionArguments algebra firstVariables inputs)
      (first :
        ConstructionSubstitution algebra firstVariables middleVariables)
      (second :
        ConstructionSubstitution algebra middleVariables lastVariables) :
      OpenConstructionArguments.substitute (algebra := algebra)
          (OpenConstructionArguments.substitute (algebra := algebra) arguments first) second =
        OpenConstructionArguments.substitute (algebra := algebra) arguments
          (composeSubstitution (algebra := algebra) first second) := by
    cases arguments with
    | nil => rfl
    | cons head tail =>
        simp only [OpenConstructionArguments.substitute]
        rw [substitute_assoc head first second,
          OpenConstructionArguments.substitute_assoc tail first second]
end

/-- Substitution composition is associative because route substitution is. -/
theorem composeSubstitution_assoc
    {firstVariables secondVariables thirdVariables fourthVariables :
      List algebra.Kind}
    (first :
      ConstructionSubstitution algebra firstVariables secondVariables)
    (second :
      ConstructionSubstitution algebra secondVariables thirdVariables)
    (third :
      ConstructionSubstitution algebra thirdVariables fourthVariables) :
    composeSubstitution (algebra := algebra)
        (composeSubstitution (algebra := algebra) first second) third =
      composeSubstitution (algebra := algebra) first
        (composeSubstitution (algebra := algebra) second third) := by
  induction first with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [composeSubstitution, FamilyList.map]
      rw [substitute_assoc algebra head second third]
      simp only [composeSubstitution]
      congr 1

/-! ## Grafting closed routes -/

/-- Convert ordered closed inputs into a closing substitution. -/
def closingSubstitution {context : List algebra.Kind} :
    ConstructionArguments algebra context →
      ConstructionSubstitution algebra context []
  | .nil => .nil
  | .cons head tail =>
      .cons (ofClosed algebra head) (closingSubstitution tail)

/-- Graft closed construction routes into every typed hole of an open route. -/
def graft {context : List algebra.Kind} {output : algebra.Kind}
    (route : OpenConstructionRoute algebra context output)
    (arguments : ConstructionArguments algebra context) :
    ConstructionTree algebra output :=
  close (algebra := algebra)
    (substitute (algebra := algebra) route (closingSubstitution (algebra := algebra) arguments))

/-! ## Positive and negative controls -/

namespace CompositionCanary

open Canary

def addVariables :
    OpenConstructionRoute arithmetic [.number, .number] .number :=
  .apply Operation.addition
    (.cons (.input .here)
      (.cons (.input (.there .here)) .nil))

def oneAndTwo : ConstructionArguments arithmetic [.number, .number] :=
  .cons one.route (.cons twoBySuccessor.route .nil)

/-- Positive: typed grafting produces the expected closed arithmetic route. -/
theorem graft_add_evaluates :
    arithmetic.evaluate (graft arithmetic addVariables oneAndTwo) =
      (show Canary.Object .number from (3 : Nat)) :=
  rfl

def reverseVariables :
    ConstructionSubstitution arithmetic [.number, .number] [.number, .number] :=
  .cons (.input (.there .here)) (.cons (.input .here) .nil)

/-- Negative: a non-identity substitution is not silently treated as the
identity route composition. -/
theorem reverse_not_identity :
    reverseVariables ≠ identitySubstitution arithmetic [.number, .number] := by
  intro equality
  have heads := congrArg
    (fun substitution =>
      (ConstructionVariable.here.lookup substitution)) equality
  cases heads

#print axioms substitute_identity
#print axioms substitute_assoc
#print axioms composeSubstitution_assoc
#print axioms graft_add_evaluates
#print axioms reverse_not_identity

end CompositionCanary

end OpenConstructionRoute

end Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
