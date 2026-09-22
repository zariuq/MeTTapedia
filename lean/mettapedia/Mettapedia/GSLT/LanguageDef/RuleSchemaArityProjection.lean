import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Rule-schema arity projection

Project the fixed data-constructor arities and outer judgment arities of an
ordered rule list into a structural companion for the existing inference
checker. Names of the single data sort and companion language are explicit
profile data, independent of any candidate or runtime calibration.

Traversal preserves first-occurrence order and rejects inconsistent arities
or non-application judgments. It does not parse source, assign object-logic
semantics, validate a rule package, or validate its own projected cache.
Independent cache-agreement and checker-validity evidence remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Names used in the structural companion. No particular profile is selected
by the generic projection. -/
structure CacheProfile where
  dataSort : String
  cacheName : String
deriving Repr, DecidableEq

abbrev ArityTable := List (String × Nat)

inductive ProjectionError where
  | constructorArityConflict
  | judgmentArityConflict
  | judgmentMustBeApplication
deriving Repr, DecidableEq

def lookupArity? (table : ArityTable) (head : String) : Option Nat :=
  (table.find? fun entry => entry.1 == head).map (·.2)

def insertArity (conflict : ProjectionError)
    (table : ArityTable) (head : String) (arity : Nat) :
    Except ProjectionError ArityTable :=
  match lookupArity? table head with
  | none => .ok (table ++ [(head, arity)])
  | some prior => if prior = arity then .ok table else .error conflict

mutual

def collectFixed (constructors : ArityTable) :
    Pattern → Except ProjectionError ArityTable
  | .bvar _ | .fvar _ => .ok constructors
  | .apply head arguments => do
      let next ← insertArity .constructorArityConflict
        constructors head arguments.length
      collectFixedList next arguments
  | .lambda _ body => collectFixed constructors body
  | .multiLambda _ _ body => collectFixed constructors body
  | .subst body replacement => do
      let next ← collectFixed constructors body
      collectFixed next replacement
  | .collection _ elements _ => collectFixedList constructors elements
termination_by pattern => sizeOf pattern

def collectFixedList (constructors : ArityTable) :
    List Pattern → Except ProjectionError ArityTable
  | [] => .ok constructors
  | pattern :: patterns => do
      let next ← collectFixed constructors pattern
      collectFixedList next patterns
termination_by patterns => sizeOf patterns

end

def collectJudgment (constructors judgments : ArityTable)
    (pattern : Pattern) :
    Except ProjectionError (ArityTable × ArityTable) :=
  match pattern with
  | .apply head arguments => do
      let nextJudgments ← insertArity .judgmentArityConflict
        judgments head arguments.length
      let nextConstructors ← collectFixedList constructors arguments
      pure (nextConstructors, nextJudgments)
  | _ => .error .judgmentMustBeApplication

def collectJudgments (constructors judgments : ArityTable) :
    List Pattern → Except ProjectionError (ArityTable × ArityTable)
  | [] => .ok (constructors, judgments)
  | pattern :: patterns => do
      let (nextConstructors, nextJudgments) ←
        collectJudgment constructors judgments pattern
      collectJudgments nextConstructors nextJudgments patterns

def collectRules (constructors judgments : ArityTable) :
    List RuleSchema → Except ProjectionError (ArityTable × ArityTable)
  | [] => .ok (constructors, judgments)
  | rule :: rules => do
      let (nextConstructors, nextJudgments) ←
        collectJudgments constructors judgments
          (rule.premises ++ [rule.conclusion])
      collectRules nextConstructors nextJudgments rules

def dataConstructor (profile : CacheProfile) (label : String) (arity : Nat) :
    GrammarRule :=
  { label
    category := profile.dataSort
    params := (List.range arity).map fun index =>
      .simple ("argument" ++ toString index) (.base profile.dataSort)
    syntaxPattern := [] }

def cacheLanguage (profile : CacheProfile) (constructors : ArityTable) :
    LanguageDef :=
  { name := profile.cacheName
    types := [TypeDecl.plain profile.dataSort]
    terms := constructors.map fun (label, arity) =>
      dataConstructor profile label arity
    equations := []
    rewrites := [] }

@[simp] def cacheDefinition (profile : CacheProfile) (constructors : ArityTable)
    (judgments : List JudgmentDecl) (rules : List RuleSchema) :
    CalculusLanguageDef :=
  CalculusLanguageDef.extend (cacheLanguage profile constructors) { judgments, rules }

/-- Deterministically project the structural companion for an authored rule
list. The explicit profile controls only the data-sort and cache-name fields.
Projection does not establish that the resulting definition is valid. -/
def project (profile : CacheProfile) (rules : List RuleSchema) :
    Except ProjectionError CalculusLanguageDef := do
  let (constructors, judgments) ← collectRules [] [] rules
  pure <| cacheDefinition profile constructors
    (judgments.map fun (head, arity) => { head, arity }) rules

/-- Exact cache agreement is deliberately propositional.  An implementation
may compare a canonical serialization, but a cache never validates itself. -/
def CacheAgrees (profile : CacheProfile) (rules : List RuleSchema)
    (cached : CalculusLanguageDef) : Prop :=
  project profile rules = .ok cached

/-- Once an exact projected definition is admitted and its raw checker
accepts a proof, the existing checker reconstructs a typed derivation with the
same proof tree. -/
theorem projected_check_sound
    {profile : CacheProfile}
    {rules : List RuleSchema} {definition : CalculusLanguageDef}
    {goal : Pattern} {proof : RawProof}
    (hagrees : CacheAgrees profile rules definition)
    (hvalid : definition.isValid = true)
    (hcheck : checkRaw ⟨definition, hvalid⟩ goal proof = true) :
    CacheAgrees profile rules definition ∧
      ∃ derivation : Derivation ⟨definition, hvalid⟩ goal,
        derivation.erase = proof := by
  exact ⟨hagrees,
    checkRaw_exists_derivation_with_exact_erasure hcheck⟩

end Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection

#print axioms Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection.projected_check_sound
