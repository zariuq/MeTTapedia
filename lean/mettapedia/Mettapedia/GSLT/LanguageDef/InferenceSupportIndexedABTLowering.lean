import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.GSLT.LanguageDef.ContextSupport

/-!
# Support-indexed ABT lowering for inference instances

The generic inference checker assigns each schema metavariable one exact
occurrence depth.  This module shows that its ordered rule instantiation is a
special case of the existing support-indexed ABT substitution: a formal's
declared depth is its binder support, and its corresponding proof argument is
the supported assignment value.

The bridge is intentionally stated for successful checker instantiations.
Invalid or incomplete schemas continue to fail closed; the total ABT action
does not manufacture an interpretation for them.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceSupportIndexedABTLowering

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Only the length of a formal's support context is operational at this
boundary.  Its object-language types remain in the authored typing layer. -/
def supportMarker : TypeExpr := .base "InferenceSupport"

/-- Finite formal declarations interpreted as an ABT support function. -/
def supportOfFormals : List (String × Nat) → ContextSupport.Support
  | [], _ => []
  | (name, depth) :: formals, target =>
      if name = target then List.replicate depth supportMarker
      else supportOfFormals formals target

/-- Ordered rule arguments interpreted as the assignment paired with the
formal table.  Missing entries remain visibly free; the main refinement
theorem is only applicable after checker instantiation has succeeded. -/
def assignmentOfArguments :
    List (String × Nat) → List Pattern → ContextSupport.Assignment
  | (name, _) :: formals, argument :: arguments, target =>
      if name = target then argument
      else assignmentOfArguments formals arguments target
  | _, _, target => .fvar target

/-- If a name is absent from the formal table, exact-depth lookup cannot
resolve it at any depth. -/
theorem lookupArgumentAt?_eq_none_of_name_not_mem
    {formals : List (String × Nat)} {arguments : List Pattern}
    {name : String} {depth : Nat}
    (absent : name ∉ formals.map Prod.fst) :
    lookupArgumentAt? formals arguments name depth = none := by
  induction formals generalizing arguments with
  | nil => simp [lookupArgumentAt?]
  | cons formal formals inductionHypothesis =>
      rcases formal with ⟨formalName, formalDepth⟩
      have headNe : formalName ≠ name := by
        intro equality
        apply absent
        simp [equality]
      have tailAbsent : name ∉ formals.map Prod.fst := by
        intro membership
        apply absent
        simp [membership]
      cases arguments with
      | nil => simp [lookupArgumentAt?]
      | cons argument arguments =>
          simp [lookupArgumentAt?, headNe,
            inductionHypothesis tailAbsent]

/-- A successful exact-depth lookup selects the same support depth and value
as the finite ABT environment.  Unique formal names are the essential
representability condition: one free name denotes one support fibre. -/
theorem lookupArgumentAt?_selects_support_and_assignment
    {formals : List (String × Nat)} {arguments : List Pattern}
    {name : String} {depth : Nat} {argument : Pattern}
    (namesUnique : (formals.map Prod.fst).Nodup)
    (sameLength : formals.length = arguments.length)
    (lookup : lookupArgumentAt? formals arguments name depth = some argument) :
    (supportOfFormals formals name).length = depth ∧
      assignmentOfArguments formals arguments name = argument := by
  induction formals generalizing arguments with
  | nil => simp [lookupArgumentAt?] at lookup
  | cons formal formals inductionHypothesis =>
      rcases formal with ⟨formalName, formalDepth⟩
      cases arguments with
      | nil => simp at sameLength
      | cons headArgument arguments =>
          have tailLength : formals.length = arguments.length := by
            simpa using Nat.succ.inj sameLength
          change (formalName :: formals.map Prod.fst).Nodup at namesUnique
          have uniqueParts := List.nodup_cons.mp namesUnique
          have headAbsent : formalName ∉ formals.map Prod.fst := uniqueParts.1
          have tailUnique : (formals.map Prod.fst).Nodup := uniqueParts.2
          by_cases sameName : formalName = name
          · subst formalName
            have targetAbsent : name ∉ formals.map Prod.fst := headAbsent
            by_cases sameDepth : formalDepth = depth
            · subst formalDepth
              have argumentEq : headArgument = argument := by
                simpa [lookupArgumentAt?] using lookup
              subst argument
              simp [supportOfFormals, assignmentOfArguments,
                supportMarker]
            · have tailNone := lookupArgumentAt?_eq_none_of_name_not_mem
                (arguments := arguments) (depth := depth) targetAbsent
              simp [lookupArgumentAt?, sameDepth, tailNone] at lookup
          · have tailLookup :
                lookupArgumentAt? formals arguments name depth =
                  some argument := by
                simpa [lookupArgumentAt?, sameName] using lookup
            obtain ⟨supportLength, assignmentEq⟩ :=
              inductionHypothesis tailUnique tailLength tailLookup
            simpa [supportOfFormals, assignmentOfArguments, sameName] using
              And.intro supportLength assignmentEq

mutual

/-- Every declarative checker instantiation is exactly the corresponding
support-indexed ABT substitution. -/
theorem instantiatesAt_eq_supportSubstitution
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schema result : Pattern}
    (instantiation : InstantiatesAt formals arguments depth schema result)
    (namesUnique : (formals.map Prod.fst).Nodup)
    (sameLength : formals.length = arguments.length) :
    ContextSupport.substituteAt
      (supportOfFormals formals)
      (assignmentOfArguments formals arguments) depth schema = result := by
  cases instantiation with
  | bvar => simp [ContextSupport.substituteAt]
  | fvar lookup =>
      obtain ⟨supportLength, assignmentEq⟩ :=
        lookupArgumentAt?_selects_support_and_assignment
          namesUnique sameLength lookup
      simp [ContextSupport.substituteAt, supportLength, assignmentEq,
        liftBVars_zero]
  | apply items =>
      simp [ContextSupport.substituteAt,
        instantiatesListAt_eq_supportSubstitution items namesUnique sameLength]
  | lambda inner =>
      simp [ContextSupport.substituteAt,
        instantiatesAt_eq_supportSubstitution inner namesUnique sameLength]
  | multiLambda inner =>
      simp [ContextSupport.substituteAt,
        instantiatesAt_eq_supportSubstitution inner namesUnique sameLength]
  | subst left right =>
      simp [ContextSupport.substituteAt,
        instantiatesAt_eq_supportSubstitution left namesUnique sameLength,
        instantiatesAt_eq_supportSubstitution right namesUnique sameLength]
  | collection items =>
      simp [ContextSupport.substituteAt,
        instantiatesListAt_eq_supportSubstitution items namesUnique sameLength]

/-- List-valued instantiation lowers pointwise through the same finite ABT
environment. -/
theorem instantiatesListAt_eq_supportSubstitution
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schemas results : List Pattern}
    (instantiation :
      InstantiatesListAt formals arguments depth schemas results)
    (namesUnique : (formals.map Prod.fst).Nodup)
    (sameLength : formals.length = arguments.length) :
    schemas.map
        (ContextSupport.substituteAt
          (supportOfFormals formals)
          (assignmentOfArguments formals arguments) depth) = results := by
  cases instantiation with
  | nil => rfl
  | cons head tail =>
      simp [instantiatesAt_eq_supportSubstitution head namesUnique sameLength,
        instantiatesListAt_eq_supportSubstitution tail namesUnique sameLength]

end

/-- Executable checker instantiation lowers to the generic support-indexed
ABT action without changing the resulting pattern. -/
theorem instantiateSchemaAt?_eq_supportSubstitution
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schema result : Pattern}
    (namesUnique : (formals.map Prod.fst).Nodup)
    (sameLength : formals.length = arguments.length)
    (checked :
      instantiateSchemaAt? formals arguments depth schema = some result) :
    ContextSupport.substituteAt
      (supportOfFormals formals)
      (assignmentOfArguments formals arguments) depth schema = result :=
  instantiatesAt_eq_supportSubstitution
    (instantiateSchemaAt?_sound checked) namesUnique sameLength

/-- Top-level form used by proof-rule lowering. -/
theorem instantiateSchema?_eq_supportSubstitution
    {formals : List (String × Nat)} {arguments : List Pattern}
    {schema result : Pattern}
    (namesUnique : (formals.map Prod.fst).Nodup)
    (sameLength : formals.length = arguments.length)
    (checked : instantiateSchema? formals arguments schema = some result) :
    ContextSupport.substituteAt
      (supportOfFormals formals)
      (assignmentOfArguments formals arguments) 0 schema = result :=
  instantiateSchemaAt?_eq_supportSubstitution namesUnique sameLength checked

/-- V1 rule admission supplies the unique-name premise required by finite
support lowering. -/
theorem ruleSchema_formalNames_nodup_of_validV1
    {rule : RuleSchema}
    (valid : InferenceChecker.RuleSchema.isValidV1 rule = true) :
    (rule.metavariables.map Prod.fst).Nodup := by
  unfold InferenceChecker.RuleSchema.isValidV1 at valid
  simp only [Bool.and_eq_true] at valid
  exact (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup
    (InferenceChecker.RuleSchema.metavariableNames rule)).mp
      valid.1.1.1.1.1.2

/-- Successful argument validation supplies the positional coverage required
by ordered support and assignment tables. -/
theorem argumentsValidAt_length_eq
    {formals : List (String × Nat)} {arguments : List Pattern}
    (valid : argumentsValidAt formals arguments = true) :
    formals.length = arguments.length := by
  induction formals generalizing arguments with
  | nil =>
      cases arguments with
      | nil => rfl
      | cons argument arguments => simp [argumentsValidAt] at valid
  | cons formal formals inductionHypothesis =>
      cases arguments with
      | nil => simp [argumentsValidAt] at valid
      | cons argument arguments =>
          simp only [argumentsValidAt, Bool.and_eq_true] at valid
          simpa using inductionHypothesis valid.2

/-- An admitted rule instance therefore lowers to the support-indexed ABT
action with no additional trusted binding premise. -/
theorem ruleSchema_instantiate_eq_supportSubstitution
    {rule : RuleSchema} {arguments : List Pattern}
    {schema result : Pattern}
    (ruleValid : InferenceChecker.RuleSchema.isValidV1 rule = true)
    (argumentsValid :
      argumentsValidAt rule.metavariables arguments = true)
    (checked :
      instantiateSchema? rule.metavariables arguments schema = some result) :
    ContextSupport.substituteAt
      (supportOfFormals rule.metavariables)
      (assignmentOfArguments rule.metavariables arguments) 0 schema = result :=
  instantiateSchema?_eq_supportSubstitution
    (ruleSchema_formalNames_nodup_of_validV1 ruleValid)
    (argumentsValidAt_length_eq argumentsValid) checked

/-! ## Generic physical ABT carrier

The physical checker uses one generic ABT engine whose constructor signature
records the number of binders crossed by each field.  The following distinct
carrier isolates that representation from `Pattern`: indices are leaves, and
every structural child carries its field depth.  This is the mathematical
lowering implemented by a native adapter; it is not a second substitution
definition over `Pattern`.
-/

/-- Structural identities retained by the physical ABT carrier. -/
inductive PatternABTHead where
  | free (name : String)
  | apply (constructor : String)
  | lambda (binder : Option String)
  | multiLambda (arity : Nat) (binders : List String)
  | subst
  | collection (collectionType : CollType) (rest : Option String)
deriving Repr

mutual

/-- A signature-indexed ABT tree. -/
inductive PatternABT where
  | idx (value : Nat)
  | node (head : PatternABTHead) (fields : PatternABTFields)

/-- Structural fields paired with the number of binders crossed on entry. -/
inductive PatternABTFields where
  | nil
  | cons (depth : Nat) (term : PatternABT) (rest : PatternABTFields)

end

namespace PatternABT

mutual

/-- Exact structural lowering from locally nameless patterns to field-indexed
ABT nodes. -/
def encode : Pattern → PatternABT
  | .bvar index => .idx index
  | .fvar name => .node (.free name) .nil
  | .apply constructor arguments =>
      .node (.apply constructor) (encodeFields 0 arguments)
  | .lambda binder body =>
      .node (.lambda binder) (.cons 1 (encode body) .nil)
  | .multiLambda arity binders body =>
      .node (.multiLambda arity binders) (.cons arity (encode body) .nil)
  | .subst body replacement =>
      .node .subst
        (.cons 1 (encode body) (.cons 0 (encode replacement) .nil))
  | .collection collectionType elements rest =>
      .node (.collection collectionType rest) (encodeFields 0 elements)

/-- Lower one homogeneous Pattern list at a common field depth. -/
def encodeFields (depth : Nat) : List Pattern → PatternABTFields
  | [] => .nil
  | pattern :: patterns =>
      .cons depth (encode pattern) (encodeFields depth patterns)

end

mutual

/-- Partial inverse, rejecting a carrier whose field-depth signature does not
describe the retained Pattern constructor. -/
def decode? : PatternABT → Option Pattern
  | .idx index => some (.bvar index)
  | .node (.free name) .nil => some (.fvar name)
  | .node (.apply constructor) fields =>
      return .apply constructor (← decodeFieldsAt? 0 fields)
  | .node (.lambda binder) (.cons 1 body .nil) =>
      return .lambda binder (← decode? body)
  | .node (.multiLambda arity binders) (.cons depth body .nil) =>
      if depth = arity then
        return .multiLambda arity binders (← decode? body)
      else none
  | .node .subst (.cons 1 body (.cons 0 replacement .nil)) =>
      return .subst (← decode? body) (← decode? replacement)
  | .node (.collection collectionType rest) fields =>
      return .collection collectionType (← decodeFieldsAt? 0 fields) rest
  | .node _ _ => none

def decodeFieldsAt? (depth : Nat) :
    PatternABTFields → Option (List Pattern)
  | .nil => some []
  | .cons fieldDepth term rest =>
      if fieldDepth = depth then
        return (← decode? term) :: (← decodeFieldsAt? depth rest)
      else none

end

mutual

  theorem decode_encode (pattern : Pattern) :
      decode? (encode pattern) = some pattern := by
    cases pattern with
    | bvar index => rfl
    | fvar name => rfl
    | apply constructor arguments =>
        simp [encode, decode?, decodeFields_encodeFields arguments]
    | lambda binder body =>
        simp [encode, decode?, decode_encode body]
    | multiLambda arity binders body =>
        simp [encode, decode?, decode_encode body]
    | subst body replacement =>
        simp [encode, decode?, decode_encode body, decode_encode replacement]
    | collection collectionType elements rest =>
        simp [encode, decode?, decodeFields_encodeFields elements]

  theorem decodeFields_encodeFields (patterns : List Pattern) :
      decodeFieldsAt? 0 (encodeFields 0 patterns) = some patterns := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp [encodeFields, decodeFieldsAt?, decode_encode,
          decodeFields_encodeFields]

end


theorem encode_injective : Function.Injective encode := by
  intro left right equality
  have decoded := congrArg decode? equality
  simpa [decode_encode] using decoded

mutual

/-- Generic ABT shift.  Constructor-specific binding behavior is read only
from field depths. -/
def lift (cutoff shift : Nat) : PatternABT → PatternABT
  | .idx index =>
      if index ≥ cutoff then .idx (index + shift) else .idx index
  | .node head fields => .node head (liftFields cutoff shift fields)

def liftFields (cutoff shift : Nat) : PatternABTFields → PatternABTFields
  | .nil => .nil
  | .cons depth term rest =>
      .cons depth (lift (cutoff + depth) shift term)
        (liftFields cutoff shift rest)

end

mutual

/-- Generic ABT binder-eliminating substitution. -/
def instantiateAt (depth : Nat) (replacement : PatternABT) :
    PatternABT → PatternABT
  | .idx index =>
      if index < depth then .idx index
      else if index = depth then lift 0 depth replacement
      else .idx (index - 1)
  | .node head fields =>
      .node head (instantiateFieldsAt depth replacement fields)

def instantiateFieldsAt (depth : Nat) (replacement : PatternABT) :
    PatternABTFields → PatternABTFields
  | .nil => .nil
  | .cons fieldDepth term rest =>
      .cons fieldDepth
        (instantiateAt (depth + fieldDepth) replacement term)
        (instantiateFieldsAt depth replacement rest)

end

mutual

/-- Generic ABT removal of an unused binder. -/
def dropAt? (cutoff : Nat) : PatternABT → Option PatternABT
  | .idx index =>
      if index < cutoff then some (.idx index)
      else if index = cutoff then none
      else some (.idx (index - 1))
  | .node head fields => return .node head (← dropFieldsAt? cutoff fields)

def dropFieldsAt? (cutoff : Nat) :
    PatternABTFields → Option PatternABTFields
  | .nil => some .nil
  | .cons fieldDepth term rest => do
      let term ← dropAt? (cutoff + fieldDepth) term
      let rest ← dropFieldsAt? cutoff rest
      pure (.cons fieldDepth term rest)

end

mutual

  /-- The physical field-depth encoding commutes with ordinary de Bruijn
  lifting. -/
  theorem encode_liftBVars (cutoff shift : Nat) (pattern : Pattern) :
      encode (liftBVars cutoff shift pattern) =
        lift cutoff shift (encode pattern) := by
    cases pattern with
    | bvar index =>
        by_cases shifts : cutoff ≤ index <;>
          simp [encode, liftBVars, lift, shifts]
    | fvar name => simp [encode, liftBVars, lift, liftFields]
    | apply constructor arguments =>
        simp [encode, liftBVars, lift,
          encodeFields_liftBVars cutoff shift arguments]
    | lambda binder body =>
        simp [encode, liftBVars, lift, liftFields,
          encode_liftBVars (cutoff + 1) shift body]
    | multiLambda arity binders body =>
        simp [encode, liftBVars, lift, liftFields,
          encode_liftBVars (cutoff + arity) shift body]
    | subst body replacement =>
        simp [encode, liftBVars, lift, liftFields,
          encode_liftBVars (cutoff + 1) shift body,
          encode_liftBVars cutoff shift replacement]
    | collection collectionType elements rest =>
        simp [encode, liftBVars, lift,
          encodeFields_liftBVars cutoff shift elements]

  theorem encodeFields_liftBVars (cutoff shift : Nat)
      (patterns : List Pattern) :
      encodeFields 0 (patterns.map (liftBVars cutoff shift)) =
        liftFields cutoff shift (encodeFields 0 patterns) := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp [encodeFields, liftFields, encode_liftBVars,
          encodeFields_liftBVars]

end

mutual

  /-- The generic ABT substitution computes exactly the checker-side Pattern
  substitution after lowering. -/
  theorem encode_instantiateBVarAt
      (depth : Nat) (replacement body : Pattern) :
      encode (instantiateBVarAt depth replacement body) =
        instantiateAt depth (encode replacement) (encode body) := by
    cases body with
    | bvar index =>
        by_cases below : index < depth
        · simp [encode, instantiateBVarAt, instantiateAt, below]
        · by_cases equal : index = depth <;>
            simp [encode, instantiateBVarAt, instantiateAt, below, equal,
              encode_liftBVars]
    | fvar name =>
        simp [encode, instantiateBVarAt, instantiateAt,
          instantiateFieldsAt]
    | apply constructor arguments =>
        simp [encode, instantiateBVarAt, instantiateAt,
          encodeFields_instantiateBVarAt depth replacement arguments]
    | lambda binder body =>
        simp [encode, instantiateBVarAt, instantiateAt,
          instantiateFieldsAt,
          encode_instantiateBVarAt (depth + 1) replacement body]
    | multiLambda arity binders body =>
        simp [encode, instantiateBVarAt, instantiateAt,
          instantiateFieldsAt,
          encode_instantiateBVarAt (depth + arity) replacement body]
    | subst body nestedReplacement =>
        simp [encode, instantiateBVarAt, instantiateAt,
          instantiateFieldsAt,
          encode_instantiateBVarAt (depth + 1) replacement body,
          encode_instantiateBVarAt depth replacement nestedReplacement]
    | collection collectionType elements rest =>
        simp [encode, instantiateBVarAt, instantiateAt,
          encodeFields_instantiateBVarAt depth replacement elements]

  theorem encodeFields_instantiateBVarAt
      (depth : Nat) (replacement : Pattern) (patterns : List Pattern) :
      encodeFields 0
          (patterns.map (instantiateBVarAt depth replacement)) =
        instantiateFieldsAt depth (encode replacement)
          (encodeFields 0 patterns) := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp [encodeFields, instantiateFieldsAt,
          encode_instantiateBVarAt,
          encodeFields_instantiateBVarAt]

end

mutual

  /-- The generic ABT unused-binder operation computes exactly `dropBVarAt?`
  after lowering. -/
  theorem encode_dropBVarAt? (cutoff : Nat) (body : Pattern) :
      (dropBVarAt? cutoff body).map encode =
        dropAt? cutoff (encode body) := by
    cases body with
    | bvar index =>
        by_cases below : index < cutoff
        · simp [encode, dropBVarAt?, dropAt?, below]
        · by_cases equal : index = cutoff <;>
            simp [encode, dropBVarAt?, dropAt?, below, equal]
    | fvar name => simp [encode, dropBVarAt?, dropAt?, dropFieldsAt?]
    | apply constructor arguments =>
        simp [encode, dropBVarAt?, dropAt?,
          ← encodeFields_dropBVarAt cutoff arguments,
          Option.map_eq_bind, Option.bind_assoc]
    | lambda binder body =>
        simp [encode, dropBVarAt?, dropAt?, dropFieldsAt?,
          ← encode_dropBVarAt? (cutoff + 1) body,
          Option.map_eq_bind, Option.bind_assoc]
    | multiLambda arity binders body =>
        simp [encode, dropBVarAt?, dropAt?, dropFieldsAt?,
          ← encode_dropBVarAt? (cutoff + arity) body,
          Option.map_eq_bind, Option.bind_assoc]
    | subst body replacement =>
        simp [encode, dropBVarAt?, dropAt?, dropFieldsAt?,
          ← encode_dropBVarAt? (cutoff + 1) body,
          ← encode_dropBVarAt? cutoff replacement,
          Option.map_eq_bind, Option.bind_assoc]
    | collection collectionType elements rest =>
        simp [encode, dropBVarAt?, dropAt?,
          ← encodeFields_dropBVarAt cutoff elements,
          Option.map_eq_bind, Option.bind_assoc]

  theorem encodeFields_dropBVarAt (cutoff : Nat)
      (patterns : List Pattern) :
      ((patterns.mapM (dropBVarAt? cutoff)).map (encodeFields 0)) =
        dropFieldsAt? cutoff (encodeFields 0 patterns) := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp [encodeFields, dropFieldsAt?,
          ← encode_dropBVarAt? cutoff pattern,
          ← encodeFields_dropBVarAt cutoff patterns,
          Option.map_eq_bind, Option.bind_assoc]

end

theorem encode_instantiateBVar (replacement body : Pattern) :
    encode (instantiateBVar replacement body) =
      instantiateAt 0 (encode replacement) (encode body) := by
  exact encode_instantiateBVarAt 0 replacement body

theorem encode_dropBVar? (body : Pattern) :
    (dropBVar? body).map encode = dropAt? 0 (encode body) := by
  exact encode_dropBVarAt? 0 body

/-- A physical ABT equality witnesses exactly the same successful explicit
substitution as the logical side condition. -/
theorem instantiateAt_zero_eq_iff
    (replacement body result : Pattern) :
    instantiateAt 0 (encode replacement) (encode body) = encode result ↔
      instantiateBVar replacement body = result := by
  rw [← encode_instantiateBVar]
  constructor
  · intro equality
    exact encode_injective equality
  · intro equality
    exact congrArg encode equality

/-- A physical ABT unused-binder result exists exactly when the logical
side condition returns that Pattern. -/
theorem dropAt_zero_eq_some_iff (body result : Pattern) :
    dropAt? 0 (encode body) = some (encode result) ↔
      dropBVar? body = some result := by
  rw [← encode_dropBVar?]
  cases dropped : dropBVar? body with
  | none => simp
  | some actual =>
      simp only [Option.map, Option.some.injEq]
      constructor
      · intro equality
        exact encode_injective equality
      · intro equality
        exact congrArg encode equality

/-! ## Physical support validation

The native provider first lowers exact Pattern wire data to the distinct ABT
carrier, then applies the generic field-depth scope checker.  Canonical binder
metadata is retained by ABT heads and checked independently. -/

mutual

/-- Generic scope validation driven only by ABT field depths.  Free schema
variables and collection-rest metavariables are not executable arguments. -/
def supportedAt : Nat → PatternABT → Bool
  | depth, .idx index => decide (index < depth)
  | _, .node (.free _) _ => false
  | depth, .node (.collection _ rest) fields =>
      rest.isNone && fieldsSupportedAt depth fields
  | depth, .node _ fields => fieldsSupportedAt depth fields

/-- Scope validation of structural fields at their declared binder depths. -/
def fieldsSupportedAt : Nat → PatternABTFields → Bool
  | _, .nil => true
  | depth, .cons fieldDepth term rest =>
      supportedAt (depth + fieldDepth) term &&
        fieldsSupportedAt depth rest

end

mutual

/-- Canonical locally-nameless metadata on the physical ABT carrier. -/
def hasCanonicalMetadata : PatternABT → Bool
  | .idx _ => true
  | .node (.lambda binder) fields =>
      binder.isNone && fieldsHaveCanonicalMetadata fields
  | .node (.multiLambda _ binders) fields =>
      binders.isEmpty && fieldsHaveCanonicalMetadata fields
  | .node _ fields => fieldsHaveCanonicalMetadata fields

/-- Canonical metadata is checked pointwise through ABT fields. -/
def fieldsHaveCanonicalMetadata : PatternABTFields → Bool
  | .nil => true
  | .cons _ term rest =>
      hasCanonicalMetadata term && fieldsHaveCanonicalMetadata rest

end


mutual

/-- Exact Pattern lowering preserves binder support. -/
theorem supportedAt_encode (depth : Nat) (pattern : Pattern) :
    supportedAt depth (encode pattern) = pattern.isGroundAt depth := by
  cases pattern with
  | bvar index => simp [supportedAt, encode, Pattern.isGroundAt]
  | fvar name => simp [supportedAt, encode, Pattern.isGroundAt]
  | apply constructor arguments =>
      simp [supportedAt, encode, Pattern.isGroundAt,
        fieldsSupportedAt_encodeFields depth 0 arguments]
  | lambda binder body =>
      simp [supportedAt, fieldsSupportedAt, encode, Pattern.isGroundAt,
        supportedAt_encode (depth + 1) body]
  | multiLambda arity binders body =>
      simp [supportedAt, fieldsSupportedAt, encode, Pattern.isGroundAt,
        supportedAt_encode (depth + arity) body]
  | subst body replacement =>
      simp [supportedAt, fieldsSupportedAt, encode, Pattern.isGroundAt,
        supportedAt_encode (depth + 1) body,
        supportedAt_encode depth replacement]
  | collection collectionType elements rest =>
      simp [supportedAt, encode, Pattern.isGroundAt,
        fieldsSupportedAt_encodeFields depth 0 elements,
        Bool.and_comm]

/-- Homogeneous Pattern fields lower to the corresponding field-depth support
check. -/
theorem fieldsSupportedAt_encodeFields (depth fieldDepth : Nat)
    (patterns : List Pattern) :
    fieldsSupportedAt depth (encodeFields fieldDepth patterns) =
      Pattern.isGroundListAt (depth + fieldDepth) patterns := by
  cases patterns with
  | nil => rfl
  | cons pattern patterns =>
      simp [fieldsSupportedAt, encodeFields, Pattern.isGroundListAt,
        supportedAt_encode,
        fieldsSupportedAt_encodeFields depth fieldDepth patterns]

end

mutual

/-- Exact Pattern lowering retains precisely the canonical binder metadata. -/
theorem hasCanonicalMetadata_encode (pattern : Pattern) :
    hasCanonicalMetadata (encode pattern) =
      pattern.hasCanonicalBinderMetadata := by
  cases pattern with
  | bvar index => simp [hasCanonicalMetadata, encode,
      Pattern.hasCanonicalBinderMetadata]
  | fvar name => simp [hasCanonicalMetadata, encode,
      fieldsHaveCanonicalMetadata, Pattern.hasCanonicalBinderMetadata]
  | apply constructor arguments =>
      simp [hasCanonicalMetadata, encode,
        Pattern.hasCanonicalBinderMetadata,
        fieldsCanonical_encodeFields 0 arguments]
  | lambda binder body =>
      simp [hasCanonicalMetadata, fieldsHaveCanonicalMetadata, encode,
        Pattern.hasCanonicalBinderMetadata,
        hasCanonicalMetadata_encode body]
  | multiLambda arity binders body =>
      simp [hasCanonicalMetadata, fieldsHaveCanonicalMetadata, encode,
        Pattern.hasCanonicalBinderMetadata,
        hasCanonicalMetadata_encode body]
  | subst body replacement =>
      simp [hasCanonicalMetadata, fieldsHaveCanonicalMetadata, encode,
        Pattern.hasCanonicalBinderMetadata,
        hasCanonicalMetadata_encode body,
        hasCanonicalMetadata_encode replacement]
  | collection collectionType elements rest =>
      simp [hasCanonicalMetadata, encode,
        Pattern.hasCanonicalBinderMetadata,
        fieldsCanonical_encodeFields 0 elements]

/-- Field lowering preserves canonical metadata pointwise. -/
theorem fieldsCanonical_encodeFields (fieldDepth : Nat)
    (patterns : List Pattern) :
    fieldsHaveCanonicalMetadata (encodeFields fieldDepth patterns) =
      Pattern.hasCanonicalBinderMetadataList patterns := by
  cases patterns with
  | nil => rfl
  | cons pattern patterns =>
      simp [fieldsHaveCanonicalMetadata, encodeFields,
        Pattern.hasCanonicalBinderMetadataList,
        hasCanonicalMetadata_encode,
        fieldsCanonical_encodeFields fieldDepth patterns]

end


/-- Physical argument validation on the generic ABT carrier. -/
def argumentSupportedAt (depth : Nat) (pattern : Pattern) : Bool :=
  supportedAt depth (encode pattern) &&
    hasCanonicalMetadata (encode pattern)

/-- The physical ABT provider accepts exactly the logical support-indexed
argument predicate used by inference replay. -/
theorem argumentSupportedAt_eq_argumentValidAt
    (depth : Nat) (pattern : Pattern) :
    argumentSupportedAt depth pattern = argumentValidAt depth pattern := by
  simp [argumentSupportedAt, argumentValidAt, supportedAt_encode,
    hasCanonicalMetadata_encode]

/-- Ordered physical support checking for a complete rule-argument vector. -/
def argumentsSupportedAt :
    List (String × Nat) → List Pattern → Bool
  | [], [] => true
  | (_, depth) :: formals, argument :: arguments =>
      argumentSupportedAt depth argument &&
        argumentsSupportedAt formals arguments
  | _, _ => false

/-- The physical ABT argument vector has exactly the support discipline used
by logical rule replay. -/
theorem argumentsSupportedAt_eq_argumentsValidAt
    (formals : List (String × Nat)) (arguments : List Pattern) :
    argumentsSupportedAt formals arguments =
      InferenceChecker.argumentsValidAt formals arguments := by
  induction formals generalizing arguments with
  | nil =>
      cases arguments <;> rfl
  | cons formal formals inductionHypothesis =>
      cases arguments with
      | nil => rfl
      | cons argument arguments =>
          simp [argumentsSupportedAt, InferenceChecker.argumentsValidAt,
            argumentSupportedAt_eq_argumentValidAt,
            inductionHypothesis]

end PatternABT

/-! ## Whole-rule physical lowering -/

/-- One authenticated logical rule application, lowered through a single
support-indexed ABT environment.  Premise order, the instantiated conclusion,
the exact rule occurrence, physical argument support, and side-condition
evidence are all retained. -/
inductive ABTRuleApplication (presentation : ValidatedPresentation)
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern) : Prop where
  | intro (rule : RuleSchema)
      (lookup : presentation.1.lookupRule? ruleInstance.ruleId = some rule)
      (argumentsSupported :
        PatternABT.argumentsSupportedAt
          rule.metavariables ruleInstance.arguments = true)
      (sideConditionsValid :
        RuleSchema.sideConditionsHold rule ruleInstance.arguments = true)
      (premisesLowered :
        rule.premises.map
          (ContextSupport.substituteAt
            (supportOfFormals rule.metavariables)
            (assignmentOfArguments
              rule.metavariables ruleInstance.arguments) 0) = premises)
      (conclusionLowered :
        ContextSupport.substituteAt
            (supportOfFormals rule.metavariables)
            (assignmentOfArguments
              rule.metavariables ruleInstance.arguments) 0 rule.conclusion =
          conclusion) :
      ABTRuleApplication presentation ruleInstance premises conclusion

/-- Every declarative application admitted by NIK has one whole-rule physical
ABT lowering.  No additional uniqueness, coverage, or binding premise is
trusted at this boundary. -/
theorem ruleApplication_toABTRuleApplication
    {presentation : ValidatedPresentation} {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (application :
      RuleApplication presentation ruleInstance premises conclusion) :
    ABTRuleApplication presentation ruleInstance premises conclusion := by
  cases application with
  | intro rule lookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
      have validIn := rule_isValidIn_of_lookup presentation lookup
      have validV1 : RuleSchema.isValidV1 rule = true := by
        simp only [RuleSchema.isValidIn, Bool.and_eq_true] at validIn
        exact validIn.1
      have namesUnique := ruleSchema_formalNames_nodup_of_validV1 validV1
      have sameLength := argumentsValidAt_length_eq argumentsValid
      exact .intro rule lookup (by
          rw [PatternABT.argumentsSupportedAt_eq_argumentsValidAt]
          exact argumentsValid)
        sideConditionsValid
        (instantiatesListAt_eq_supportSubstitution premisesInstantiate
          namesUnique sameLength)
        (instantiatesAt_eq_supportSubstitution conclusionInstantiates
          namesUnique sameLength)

/-- Successful executable rule replay therefore produces the same whole-rule
support-indexed ABT certificate. -/
theorem instantiateRule?_eq_some_implies_abt
    {presentation : ValidatedPresentation} {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (checked :
      instantiateRule? presentation ruleInstance =
        some (premises, conclusion)) :
    ABTRuleApplication presentation ruleInstance premises conclusion :=
  ruleApplication_toABTRuleApplication
    (instantiateRule?_eq_some_iff_application.mp checked)

mutual

/-- A proof-relevant derivation whose every local application is represented
by the physical support-indexed ABT lowering. -/
inductive ABTDerivation
    (presentation : ValidatedPresentation) : Pattern → Type where
  | byRule (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern}
      (application :
        ABTRuleApplication presentation ruleInstance premises conclusion)
      (children : ABTDerivationList presentation premises) :
      ABTDerivation presentation conclusion

inductive ABTDerivationList
    (presentation : ValidatedPresentation) : List Pattern → Type where
  | nil : ABTDerivationList presentation []
  | cons {premise : Pattern} {premises : List Pattern}
      (head : ABTDerivation presentation premise)
      (tail : ABTDerivationList presentation premises) :
      ABTDerivationList presentation (premise :: premises)

end

mutual

/-- Lower every authenticated node of a logical derivation through the same
physical ABT interpretation. -/
def derivationToABT
    {presentation : ValidatedPresentation} {goal : Pattern} :
    Derivation presentation goal → ABTDerivation presentation goal
  | .byRule ruleInstance application children =>
      .byRule ruleInstance (ruleApplication_toABTRuleApplication application)
        (derivationListToABT children)

def derivationListToABT
    {presentation : ValidatedPresentation} {premises : List Pattern} :
    DerivationList presentation premises →
      ABTDerivationList presentation premises
  | .nil => .nil
  | .cons head tail => .cons (derivationToABT head) (derivationListToABT tail)

end


mutual

/-- Erase a physical ABT derivation to the same chronological proof article. -/
def ABTDerivation.erase
    {presentation : ValidatedPresentation} {goal : Pattern} :
    ABTDerivation presentation goal → RawProof
  | .byRule ruleInstance _ children =>
      .node ruleInstance (ABTDerivationList.erase children)

def ABTDerivationList.erase
    {presentation : ValidatedPresentation} {premises : List Pattern} :
    ABTDerivationList presentation premises → List RawProof
  | .nil => []
  | .cons head tail => head.erase :: tail.erase

end

mutual

/-- Whole-derivation ABT lowering is observationally exact at the proof wire. -/
@[simp] theorem derivationToABT_erase
    {presentation : ValidatedPresentation} {goal : Pattern}
    (derivation : Derivation presentation goal) :
    ABTDerivation.erase (derivationToABT derivation) =
      Derivation.erase derivation := by
  cases derivation with
  | byRule ruleInstance application children =>
      simp [derivationToABT, ABTDerivation.erase,
        derivationListToABT_erase children, Derivation.erase]

@[simp] theorem derivationListToABT_erase
    {presentation : ValidatedPresentation} {premises : List Pattern}
    (derivations : DerivationList presentation premises) :
    ABTDerivationList.erase (derivationListToABT derivations) =
      DerivationList.erase derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp [derivationListToABT, ABTDerivationList.erase,
        derivationToABT_erase head, derivationListToABT_erase tail,
        DerivationList.erase]

end

/-! ## Binding canaries -/

namespace Canary

def binderFormals : List (String × Nat) := [("body", 1), ("value", 0)]

def binderArguments : List Pattern :=
  [.bvar 0, .apply "Unit" []]

def binderSchema : Pattern :=
  .apply "HasType"
    [.lambda none (.fvar "body"), .fvar "value"]

/-- An open argument supported by the lambda's binder remains the same index
when inserted at its declared occurrence depth. -/
theorem binder_argument_lowers_exactly :
    ContextSupport.substituteAt
      (supportOfFormals binderFormals)
      (assignmentOfArguments binderFormals binderArguments) 0 binderSchema =
        .apply "HasType"
          [.lambda none (.bvar 0), .apply "Unit" []] := by
  simp [binderFormals, binderArguments, binderSchema, supportOfFormals,
    assignmentOfArguments, ContextSupport.substituteAt, supportMarker,
    liftBVars]

/-- The same open argument is rejected by the inference checker if supplied
for a depth-zero formal. -/
theorem open_argument_at_wrong_support_rejected :
    argumentsValidAt [("body", 0)] [.bvar 0] = false := by
  rfl

/-- The physical provider independently rejects the same unsupported index. -/
theorem physical_open_argument_at_wrong_support_rejected :
    PatternABT.argumentSupportedAt 0 (.bvar 0) = false := by
  rfl

/-- Ordered physical support admits the exact depth-one argument vector. -/
theorem physical_argument_vector_accepts_exact_support :
    PatternABT.argumentsSupportedAt binderFormals binderArguments = true := by
  rfl

/-- Ordered physical support rejects the same index at depth zero. -/
theorem physical_argument_vector_rejects_wrong_support :
    PatternABT.argumentsSupportedAt [("body", 0)] [.bvar 0] = false := by
  rfl

/-- A display binder name is outside the canonical wire profile even when its
body is locally closed. -/
theorem physical_named_binder_rejected :
    PatternABT.argumentSupportedAt 0 (.lambda (some "x") (.bvar 0)) =
      false := by
  rfl

/-- Duplicate formal names cannot be represented as one support function. -/
theorem duplicate_formal_names_rejected_by_lowering_precondition :
    ¬ (([("x", 0), ("x", 1)] : List (String × Nat)).map Prod.fst).Nodup := by
  simp

end Canary

end Mettapedia.GSLT.LanguageDef.InferenceSupportIndexedABTLowering
