import Mettapedia.GSLT.LanguageDef.ContextualInferenceRule
import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Exact instantiation of explicit contextual sequents

The inference checker instantiates ordinary `Pattern` schemas.  Contextual
rules encode an ordered `ContextSchema` inside those patterns, so semantic
proofs need a typed view of the same operation.  This module supplies that
view without defining a second substitution engine.

Explicit formula rows are instantiated position by position with the
checker's existing `instantiateSchemaAt?`.  Ambient context holes are accepted
only when their checker argument decodes as a canonical context.  Consequently
order, duplicate occurrences, and the boundary between an explicit formula
and an ambient context remain visible after instantiation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContextualInferenceInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Instantiate one explicit context at the same binder depth used by the
ordinary checker.  A context hole is not an arbitrary pattern position: its
argument must decode as a canonical context. -/
def instantiateContextAt? (formals : List (String × Nat))
    (arguments : List Pattern) (depth : Nat) :
    ContextSchema → Option ContextSchema
  | .empty => some .empty
  | .hole name => do
      let wire ← lookupArgumentAt? formals arguments name depth
      decodeContext? wire
  | .extend formula tail => do
      let instantiatedFormula ←
        instantiateSchemaAt? formals arguments depth formula
      let instantiatedTail ←
        instantiateContextAt? formals arguments depth tail
      some (.extend instantiatedFormula instantiatedTail)
termination_by context => sizeOf context

/-- Top-level contextual instantiation. -/
def instantiateContext? (formals : List (String × Nat))
    (arguments : List Pattern) (context : ContextSchema) :
    Option ContextSchema :=
  instantiateContextAt? formals arguments 0 context

/-- Instantiating an encoded context through the typed contextual view gives
exactly the ordinary checker result. -/
theorem instantiateSchemaAt?_encodeContext_of_context
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {source target : ContextSchema}
    (instantiated :
      instantiateContextAt? formals arguments depth source = some target) :
    instantiateSchemaAt? formals arguments depth (encodeContext source) =
      some (encodeContext target) := by
  induction source generalizing target with
  | empty =>
      simp [instantiateContextAt?] at instantiated
      subst target
      simp [encodeContext, instantiateSchemaAt?, instantiateSchemasAt?]
  | hole name =>
      simp only [instantiateContextAt?] at instantiated
      cases lookup : lookupArgumentAt? formals arguments name depth with
      | none => simp [lookup] at instantiated
      | some wire =>
          have decoded : decodeContext? wire = some target := by
            simpa [lookup] using instantiated
          have encoded := encodeContext_of_decodeContext?_eq_some decoded
          simp [encodeContext, instantiateSchemaAt?, lookup, encoded]
  | extend formula tail inductionHypothesis =>
      simp only [instantiateContextAt?] at instantiated
      cases formulaResult :
          instantiateSchemaAt? formals arguments depth formula with
      | none => simp [formulaResult] at instantiated
      | some instantiatedFormula =>
          cases tailResult :
              instantiateContextAt? formals arguments depth tail with
          | none => simp [formulaResult, tailResult] at instantiated
          | some instantiatedTail =>
              have targetExact :
                  target = .extend instantiatedFormula instantiatedTail := by
                simpa [formulaResult, tailResult] using instantiated.symm
              subst target
              have encodedTail := inductionHypothesis tailResult
              simp [encodeContext, instantiateSchemaAt?, instantiateSchemasAt?,
                formulaResult, encodedTail]

/-- Conversely, whenever ordinary checker instantiation produces a canonical
encoded context, the typed contextual instantiator reconstructs that exact
context. -/
theorem instantiateContextAt?_of_encodeContext
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {source target : ContextSchema}
    (instantiated :
      instantiateSchemaAt? formals arguments depth (encodeContext source) =
        some (encodeContext target)) :
    instantiateContextAt? formals arguments depth source = some target := by
  induction source generalizing target with
  | empty =>
      simp only [encodeContext, instantiateSchemaAt?] at instantiated
      cases target with
      | empty => simp [instantiateContextAt?]
      | hole name => simp [encodeContext, instantiateSchemasAt?] at instantiated
      | extend formula tail =>
          simp [encodeContext, instantiateSchemasAt?] at instantiated
  | hole name =>
      simp only [encodeContext, instantiateSchemaAt?] at instantiated
      simp [instantiateContextAt?, instantiated, decodeContext?_encodeContext]
  | extend formula tail inductionHypothesis =>
      simp only [encodeContext, instantiateSchemaAt?, instantiateSchemasAt?]
        at instantiated
      cases formulaResult :
          instantiateSchemaAt? formals arguments depth formula with
      | none => simp [formulaResult] at instantiated
      | some instantiatedFormula =>
          cases tailWire :
              instantiateSchemaAt? formals arguments depth
                (encodeContext tail) with
          | none => simp [formulaResult, tailWire] at instantiated
          | some instantiatedTailWire =>
              cases target with
              | empty =>
                  simp [formulaResult, tailWire, encodeContext] at instantiated
              | hole name =>
                  simp [formulaResult, tailWire, encodeContext] at instantiated
              | extend targetFormula targetTail =>
                  have parts :
                      instantiatedFormula = targetFormula ∧
                        instantiatedTailWire = encodeContext targetTail := by
                    simpa [formulaResult, tailWire, encodeContext] using
                      instantiated
                  have targetFormulaExact :
                      targetFormula = instantiatedFormula := parts.1.symm
                  subst targetFormula
                  rw [parts.2] at tailWire
                  have tailContext := inductionHypothesis tailWire
                  simp [instantiateContextAt?, formulaResult, tailContext]

/-- Exact executable correspondence: the contextual instantiator is neither
weaker nor stronger than ordinary checker instantiation on canonical context
encodings. -/
theorem instantiateContextAt?_eq_some_iff
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {source target : ContextSchema} :
    instantiateContextAt? formals arguments depth source = some target ↔
      instantiateSchemaAt? formals arguments depth (encodeContext source) =
        some (encodeContext target) :=
  ⟨instantiateSchemaAt?_encodeContext_of_context,
    instantiateContextAt?_of_encodeContext⟩

/-- Instantiating an explicit prefix preserves its exact row order and
multiplicity before instantiating the ambient tail. -/
theorem instantiateContextAt?_prepend
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {formulas instantiatedFormulas : List Pattern}
    {tail instantiatedTail : ContextSchema}
    (formulasExact :
      instantiateSchemasAt? formals arguments depth formulas =
        some instantiatedFormulas)
    (tailExact :
      instantiateContextAt? formals arguments depth tail =
        some instantiatedTail) :
    instantiateContextAt? formals arguments depth
        (ContextSchema.prepend formulas tail) =
      some (ContextSchema.prepend instantiatedFormulas instantiatedTail) := by
  induction formulas generalizing instantiatedFormulas with
  | nil =>
      simp [instantiateSchemasAt?] at formulasExact
      subst instantiatedFormulas
      exact tailExact
  | cons formula formulas inductionHypothesis =>
      simp only [instantiateSchemasAt?] at formulasExact
      cases formulaResult :
          instantiateSchemaAt? formals arguments depth formula with
      | none => simp [formulaResult] at formulasExact
      | some instantiatedFormula =>
          cases tailResults :
              instantiateSchemasAt? formals arguments depth formulas with
          | none => simp [formulaResult, tailResults] at formulasExact
          | some instantiatedRest =>
              have listExact :
                  instantiatedFormulas =
                    instantiatedFormula :: instantiatedRest := by
                simpa [formulaResult, tailResults] using formulasExact.symm
              subst instantiatedFormulas
              have restExact :=
                inductionHypothesis tailResults
              simp [ContextSchema.prepend, instantiateContextAt?,
                formulaResult, restExact]

/-- Instantiate every component of one contextual sequent through the same
ordered checker argument vector. -/
def instantiateSequentAt? (formals : List (String × Nat))
    (arguments : List Pattern) (depth : Nat) (sequent : Sequent) :
    Option Sequent := do
  let variableContext ←
    instantiateContextAt? formals arguments depth sequent.variableContext
  let relationContext ←
    instantiateContextAt? formals arguments depth sequent.relationContext
  let conclusion ←
    instantiateSchemaAt? formals arguments depth sequent.conclusion
  some { variableContext, relationContext, conclusion }

/-- Top-level sequent instantiation. -/
def instantiateSequent? (formals : List (String × Nat))
    (arguments : List Pattern) (sequent : Sequent) : Option Sequent :=
  instantiateSequentAt? formals arguments 0 sequent

/-- Typed sequent instantiation commutes exactly with the ordinary checker
on the canonical contextual-judgment encoding. -/
theorem instantiateSchemaAt?_lowerSequent_of_sequent
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {source target : Sequent}
    (instantiated :
      instantiateSequentAt? formals arguments depth source = some target) :
    instantiateSchemaAt? formals arguments depth (lowerSequent source) =
      some (lowerSequent target) := by
  rcases source with ⟨sourceVariables, sourceRelations, sourceConclusion⟩
  rcases target with ⟨targetVariables, targetRelations, targetConclusion⟩
  simp only [instantiateSequentAt?] at instantiated
  cases variablesExact :
      instantiateContextAt? formals arguments depth sourceVariables with
  | none => simp [variablesExact] at instantiated
  | some instantiatedVariables =>
      cases relationsExact :
          instantiateContextAt? formals arguments depth sourceRelations with
      | none => simp [variablesExact, relationsExact] at instantiated
      | some instantiatedRelations =>
          cases conclusionExact :
              instantiateSchemaAt? formals arguments depth sourceConclusion with
          | none =>
              simp [variablesExact, relationsExact, conclusionExact]
                at instantiated
          | some conclusion =>
              have targetExact :
                  instantiatedVariables = targetVariables ∧
                    instantiatedRelations = targetRelations ∧
                    conclusion = targetConclusion := by
                simpa [variablesExact, relationsExact, conclusionExact] using
                  instantiated
              rcases targetExact with ⟨rfl, rfl, rfl⟩
              have variablesWire :=
                instantiateSchemaAt?_encodeContext_of_context variablesExact
              have relationsWire :=
                instantiateSchemaAt?_encodeContext_of_context relationsExact
              simp [lowerSequent, instantiateSchemaAt?,
                instantiateSchemasAt?, variablesWire, relationsWire,
                conclusionExact]

/-- Conversely, an ordinary checker instantiation whose result is a canonical
lowered sequent reconstructs the exact structured sequent instantiation.  This
is the inversion boundary needed by semantic proofs: they may recover both
ordered contexts and the conclusion without defining a second substitution
operation. -/
theorem instantiateSequentAt?_of_lowerSequent
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {source target : Sequent}
    (instantiated :
      instantiateSchemaAt? formals arguments depth (lowerSequent source) =
        some (lowerSequent target)) :
    instantiateSequentAt? formals arguments depth source = some target := by
  rcases source with ⟨sourceVariables, sourceRelations, sourceConclusion⟩
  rcases target with ⟨targetVariables, targetRelations, targetConclusion⟩
  simp only [lowerSequent, instantiateSchemaAt?, instantiateSchemasAt?]
    at instantiated
  cases variablesWire :
      instantiateSchemaAt? formals arguments depth
        (encodeContext sourceVariables) with
  | none => simp [variablesWire] at instantiated
  | some instantiatedVariablesWire =>
      cases relationsWire :
          instantiateSchemaAt? formals arguments depth
            (encodeContext sourceRelations) with
      | none => simp [variablesWire, relationsWire] at instantiated
      | some instantiatedRelationsWire =>
          cases conclusionWire :
              instantiateSchemaAt? formals arguments depth sourceConclusion with
          | none =>
              simp [variablesWire, relationsWire, conclusionWire]
                at instantiated
          | some instantiatedConclusion =>
              have components :
                  instantiatedVariablesWire = encodeContext targetVariables ∧
                    instantiatedRelationsWire =
                      encodeContext targetRelations ∧
                    instantiatedConclusion = targetConclusion := by
                simpa [variablesWire, relationsWire, conclusionWire] using
                  instantiated
              rw [components.1] at variablesWire
              rw [components.2.1] at relationsWire
              rw [components.2.2] at conclusionWire
              have variablesExact :=
                instantiateContextAt?_of_encodeContext variablesWire
              have relationsExact :=
                instantiateContextAt?_of_encodeContext relationsWire
              simp [instantiateSequentAt?, variablesExact, relationsExact,
                conclusionWire]

/-- Exact executable correspondence between structured sequent instantiation
and the ordinary checker on canonical lowered sequents. -/
theorem instantiateSequentAt?_eq_some_iff
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {source target : Sequent} :
    instantiateSequentAt? formals arguments depth source = some target ↔
      instantiateSchemaAt? formals arguments depth (lowerSequent source) =
        some (lowerSequent target) :=
  ⟨instantiateSchemaAt?_lowerSequent_of_sequent,
    instantiateSequentAt?_of_lowerSequent⟩

/-! ## Discriminating controls -/

private def duplicateFormula : Pattern :=
  .apply "context-instantiation:duplicate" [.fvar "x"]

/-- Duplicate formula occurrences remain duplicate positions after one shared
substitution; the contextual view does not quotient them into a set. -/
theorem duplicate_prefix_preserved :
    instantiateContext? [("x", 0)] [.apply "value" []]
        (ContextSchema.prepend [duplicateFormula, duplicateFormula] .empty) =
      some (ContextSchema.prepend
        [.apply "context-instantiation:duplicate" [.apply "value" []],
          .apply "context-instantiation:duplicate" [.apply "value" []]]
        .empty) := by
  simp [instantiateContext?, instantiateContextAt?, duplicateFormula,
    instantiateSchemaAt?, instantiateSchemasAt?, lookupArgumentAt?]

/-- A ground but non-context argument cannot inhabit an ambient context hole.
This prevents malformed checker data from being silently treated as an empty
or opaque context. -/
theorem noncanonical_hole_rejected :
    instantiateContext? [("Gamma", 0)]
        [.apply "not-a-context" [.apply "extra" []]]
        (.hole "Gamma") = none := by
  simp [instantiateContext?, instantiateContextAt?, lookupArgumentAt?,
    decodeContext?]

#print axioms instantiateSchemaAt?_encodeContext_of_context
#print axioms instantiateContextAt?_of_encodeContext
#print axioms instantiateContextAt?_eq_some_iff
#print axioms instantiateContextAt?_prepend
#print axioms instantiateSchemaAt?_lowerSequent_of_sequent
#print axioms instantiateSequentAt?_of_lowerSequent
#print axioms instantiateSequentAt?_eq_some_iff
#print axioms duplicate_prefix_preserved
#print axioms noncanonical_hole_rejected

end Mettapedia.GSLT.LanguageDef.ContextualInferenceInstantiation
