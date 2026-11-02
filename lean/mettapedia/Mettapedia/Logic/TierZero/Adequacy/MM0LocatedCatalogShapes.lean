import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedActivation

/-!
# A canonical physical layout for constructive MM0 completeness

This module chooses locations for the closed source values used to construct
a witness run. It is not a runtime authority test: public clients cannot turn
their data into protected occurrences by presenting one of these shapes.
Actual system soundness continues to use immutable physical locations and
send rights independently of this constructive layout.

The source catalog's rigid judgment tags prove routing for every actual
matcher instance. No proof search or derivability test classifies a value.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0LocatedCatalogShapes

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport
open MM0Rewriting
open MM0ConstraintCatalog

def layout : Tm → Space
  | .node (.judgment tag) _ => if tag = "pf" ∨ tag = "cv" then .judgments else .requests
  | _ => .requests

theorem proof_layout (target : Context) (expression : Preterm) : layout (proofValue target expression) = .judgments := by
  simp [layout, proofValue, judgment]

theorem request_layout (name : String) (arguments : List Tm) : layout (requestValue name arguments) = .requests := by
  simp [layout, requestValue, judgment, requestTag_ne_proof, requestTag_ne_conversion]

def Routed (space : Space) (pattern : Pat) : Prop :=
  ∀ assignment value, ContextualPatterns.layer.inst assignment pattern = some value → layout value = space

theorem judgment_routed (width : Nat) (tag : String) (expressions : List Preterm) :
    Routed (if tag = "pf" ∨ tag = "cv" then .judgments else .requests)
      (judgmentPattern width tag expressions) := by
  intro assignment value instantiated
  have raw := ((ContextualPatterns.Pattern.inst_iff assignment (judgmentPattern width tag expressions) value).mp instantiated).1
  change ((expressionFields width expressions).inst
    (ContextualPatterns.Pattern.atOccurrence assignment)).map (Term.node (.judgment tag)) = some value at raw
  obtain ⟨fields, _, same⟩ := Option.map_eq_some_iff.mp raw
  rw [← same]
  rfl

theorem proof_routed (width : Nat) (expression : Preterm) : Routed .judgments (proofPattern width expression) := by
  simpa only [proofPattern, true_or, ↓reduceIte] using judgment_routed width "pf" [expression]

theorem conversion_routed (width sort : Nat) (left right : Preterm) :
    Routed .judgments (conversionPattern width sort left right) := by
  simpa only [conversionPattern, or_true, ↓reduceIte] using judgment_routed width "cv" [.term sort, left, right]

theorem request_routed (width arity : Nat) (name : String) : Routed .requests (theoremRequest width arity name) := by
  simpa only [theoremRequest, requestTag_ne_proof, requestTag_ne_conversion, or_self, ↓reduceIte] using
    judgment_routed width (requestTag name) (formals arity)

private theorem congruence_routed (width : Nat) (binders : Context) (left right : Nat) :
    ∀ pattern ∈ congruencePremises width left right binders, Routed .judgments pattern := by
  induction binders generalizing left right with
  | nil => intro pattern member; cases member
  | cons binder rest earlier =>
      intro pattern member
      rcases List.mem_cons.mp member with rfl | member
      · exact conversion_routed _ _ _ _
      · exact earlier (left + 1) (right + 1) pattern member

theorem schema_routed (theory : Theory) (target : Context) (key : RuleKey) {schema : Schema}
    (compiled : schemaFor theory target key = some schema) :
    (∀ pattern ∈ schema.premises, Routed .judgments pattern) ∧ Routed .judgments schema.conclusion := by
  cases key with
  | theorem_ index =>
      cases known : theory.theoremSignature index with
      | none => simp [schemaFor, known] at compiled
      | some declaration =>
          have same : theoremSchema theory.termSignature target declaration = schema := by simpa [schemaFor, known] using compiled
          subst schema
          constructor
          · intro pattern member
            obtain ⟨expression, _, rfl⟩ := List.mem_map.mp member
            exact proof_routed _ _
          · exact proof_routed _ _
  | basic kind sort =>
      cases compiled
      cases kind <;> constructor
      all_goals try exact proof_routed _ _
      all_goals try exact conversion_routed _ _ _ _
      all_goals intro pattern member
      all_goals simp only [basicSchema, argumentSchema, BasicConversion.premises, List.mem_cons,
        List.not_mem_nil, or_false] at member
      all_goals rcases member with rfl | rfl
      all_goals first | exact proof_routed _ _ | exact conversion_routed _ _ _ _
  | congruence symbol =>
      cases known : theory.termSignature symbol with
      | none => simp [schemaFor, known] at compiled
      | some declaration =>
          have same : congruenceSchema theory.termSignature target symbol declaration = schema := by simpa [schemaFor, known] using compiled
          subst schema
          exact ⟨congruence_routed _ _ _ _, conversion_routed _ _ _ _⟩
  | unfolding symbol =>
      cases known : theory.termSignature symbol with
      | none => simp [schemaFor, known] at compiled
      | some declaration =>
          cases defined : theory.definitionSignature symbol with
          | none => simp [schemaFor, known, defined] at compiled
          | some body =>
              have same : unfoldingSchema theory.termSignature target symbol declaration body = schema := by
                simpa [schemaFor, known, defined] using compiled
              subst schema
              constructor
              · intro pattern member
                cases member
              · exact conversion_routed _ _ _ _

end Mettapedia.Logic.TierZero.Adequacy.MM0LocatedCatalogShapes
