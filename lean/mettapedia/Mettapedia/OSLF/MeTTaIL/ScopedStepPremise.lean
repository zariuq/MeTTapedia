import Mettapedia.OSLF.MeTTaIL.ContextSubstitution

/-!
# Scoped step premises in the authored pattern carrier

A local binder prefix belongs to a step premise, separately from the
metavariable dependency context and from any binders within its endpoint
patterns. Ambient substitution acts below that prefix. The root constructor
records the previous binder-free case with an explicit endpoint sort.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax

open Mettapedia.OSLF.MeTTaIL.ContextSubstitution

/-- Both endpoints must be scoped in the same local extension of the ambient
rule context. This check concerns de Bruijn scope; sorted typing is a separate
judgment against the authored grammar. -/
def ScopedStepPremise.isWellScopedAt (ambient : Nat)
    (premise : ScopedStepPremise) : Bool :=
  premise.source.isWellScopedAt (premise.binders.length + ambient) &&
    premise.target.isWellScopedAt (premise.binders.length + ambient)

/-- Transport only ambient variables; all premise-local binders stay fixed. -/
def ScopedStepPremise.map (assignment : Assignment)
    (premise : ScopedStepPremise) : ScopedStepPremise where
  binders := premise.binders
  resultType := premise.resultType
  source := substitute (lift premise.binders.length assignment) premise.source
  target := substitute (lift premise.binders.length assignment) premise.target

@[simp] theorem ScopedStepPremise.map_binders (assignment : Assignment)
    (premise : ScopedStepPremise) :
    (premise.map assignment).binders = premise.binders := rfl

@[simp] theorem ScopedStepPremise.map_resultType (assignment : Assignment)
    (premise : ScopedStepPremise) :
    (premise.map assignment).resultType = premise.resultType := rfl

/-- The identity ambient assignment changes neither endpoint nor metadata. -/
theorem ScopedStepPremise.map_id (premise : ScopedStepPremise) :
    premise.map Pattern.bvar = premise := by
  cases premise with
  | mk binders resultType source target =>
      simp [ScopedStepPremise.map, lift_identity, substitute_id]

/-- Consecutive ambient substitutions act like their composition, including
when the premise itself opens several binders. -/
theorem ScopedStepPremise.map_comp (first second : Assignment)
    (premise : ScopedStepPremise) :
    (premise.map first).map second =
      premise.map (fun index => substitute second (first index)) := by
  cases premise with
  | mk binders resultType source target =>
      simp [ScopedStepPremise.map, substitute_comp, lift_comp]

/-- A scoped ambient substitution preserves both endpoint scope judgments,
including when the premise opens multiple local binders. -/
theorem ScopedStepPremise.map_wellScoped
    {source target : Nat} {assignment : Assignment}
    (wellScoped : WellScopedAssignment source target assignment)
    (premise : ScopedStepPremise)
    (premiseScoped : premise.isWellScopedAt source = true) :
    (premise.map assignment).isWellScopedAt target = true := by
  simp only [ScopedStepPremise.isWellScopedAt,
    Bool.and_eq_true] at premiseScoped ⊢
  have lifted := wellScoped.lift premise.binders.length
  constructor
  · have sourceScoped :
        premise.source.isWellScopedAt
          (source + premise.binders.length) = true := by
      simpa only [Nat.add_comm] using premiseScoped.1
    have mapped := substitute_wellScoped lifted sourceScoped
    simpa only [ScopedStepPremise.map, Nat.add_comm] using mapped
  · have targetScoped :
        premise.target.isWellScopedAt
          (source + premise.binders.length) = true := by
      simpa only [Nat.add_comm] using premiseScoped.2
    have mapped := substitute_wellScoped lifted targetScoped
    simpa only [ScopedStepPremise.map, Nat.add_comm] using mapped

/-- Root premises retain the old unscoped substitution action exactly. -/
theorem ScopedStepPremise.root_map (resultType : TypeExpr)
    (source target : Pattern) (assignment : Assignment) :
    (ScopedStepPremise.root resultType source target).map assignment =
      ScopedStepPremise.root resultType
        (substitute assignment source) (substitute assignment target) := by
  simp [ScopedStepPremise.root, ScopedStepPremise.map]

/-- The root constructor is faithful to its sort and both endpoints. -/
theorem ScopedStepPremise.root_injective
    {resultType₁ resultType₂ : TypeExpr}
    {source₁ target₁ source₂ target₂ : Pattern}
    (h : ScopedStepPremise.root resultType₁ source₁ target₁ =
      ScopedStepPremise.root resultType₂ source₂ target₂) :
    resultType₁ = resultType₂ ∧ source₁ = source₂ ∧ target₁ = target₂ := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- Erasing display names commutes with shifting de Bruijn indices below any
existing local binder prefix. -/
theorem eraseBinderMetadata_liftBVars (cutoff shift : Nat)
    (pattern : Pattern) :
    (Substitution.liftBVars cutoff shift pattern).eraseBinderMetadata =
      Substitution.liftBVars cutoff shift pattern.eraseBinderMetadata := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      simp [Substitution.liftBVars, Pattern.eraseBinderMetadata]
      split <;> simp [Pattern.eraseBinderMetadata]
  | hfvar name =>
      simp [Substitution.liftBVars, Pattern.eraseBinderMetadata]
  | happly constructor arguments inductionHypothesis =>
      simp only [Substitution.liftBVars,
        Substitution.liftBVarsList_eq_map,
        Pattern.eraseBinderMetadata, List.map_map,
        Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership cutoff
  | hlambda binder body inductionHypothesis =>
      simp only [Substitution.liftBVars, Pattern.eraseBinderMetadata]
      exact congrArg (Pattern.lambda none)
        (inductionHypothesis (cutoff + 1))
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [Substitution.liftBVars, Pattern.eraseBinderMetadata]
      exact congrArg (Pattern.multiLambda arity [])
        (inductionHypothesis (cutoff + arity))
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [Substitution.liftBVars, Pattern.eraseBinderMetadata]
      exact congrArg₂ Pattern.subst
        (bodyInduction (cutoff + 1)) (replacementInduction cutoff)
  | hcollection kind elements rest inductionHypothesis =>
      simp only [Substitution.liftBVars,
        Substitution.liftBVarsList_eq_map,
        Pattern.eraseBinderMetadata, List.map_map,
        Pattern.collection.injEq, true_and]
      constructor
      · apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership cutoff
      · trivial

/-- Canonicalizing an assignment commutes with lifting it beneath any number
of premise-local binders. -/
theorem eraseBinderMetadata_lift_assignment (arity : Nat)
    (assignment : Assignment) :
    (fun index => (lift arity assignment index).eraseBinderMetadata) =
      lift arity (fun index => (assignment index).eraseBinderMetadata) := by
  funext index
  by_cases inside : index < arity
  · simp [lift, inside, Pattern.eraseBinderMetadata]
  · simp [lift, inside, eraseBinderMetadata_liftBVars]

/-- Binder-name erasure respects arbitrary simultaneous substitution of
de Bruijn context variables. The supplied terms are canonicalized too. -/
theorem eraseBinderMetadata_substitute (assignment : Assignment)
    (pattern : Pattern) :
    (substitute assignment pattern).eraseBinderMetadata =
      substitute (fun index => (assignment index).eraseBinderMetadata)
        pattern.eraseBinderMetadata := by
  induction pattern using Pattern.inductionOn generalizing assignment with
  | hbvar index =>
      simp [substitute, Pattern.eraseBinderMetadata]
  | hfvar name =>
      simp [substitute, Pattern.eraseBinderMetadata]
  | happly constructor arguments inductionHypothesis =>
      simp only [substitute, substituteList_eq_map,
        Pattern.eraseBinderMetadata, List.map_map,
        Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership assignment
  | hlambda binder body inductionHypothesis =>
      simp only [substitute, Pattern.eraseBinderMetadata,
        Pattern.lambda.injEq, true_and]
      rw [inductionHypothesis (lift 1 assignment),
        eraseBinderMetadata_lift_assignment]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [substitute, Pattern.eraseBinderMetadata,
        Pattern.multiLambda.injEq, true_and]
      rw [inductionHypothesis (lift arity assignment),
        eraseBinderMetadata_lift_assignment]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [substitute, Pattern.eraseBinderMetadata,
        Pattern.subst.injEq]
      constructor
      · rw [bodyInduction (lift 1 assignment),
          eraseBinderMetadata_lift_assignment]
      · exact replacementInduction assignment
  | hcollection kind elements rest inductionHypothesis =>
      simp only [substitute, substituteList_eq_map,
        Pattern.eraseBinderMetadata, List.map_map,
        Pattern.collection.injEq, true_and]
      constructor
      · apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership assignment
      · trivial

/-- Canonicalize only endpoint display names; binder sorts and the endpoint
sort remain author-supplied data. -/
def ScopedStepPremise.canonicalize (premise : ScopedStepPremise) :
    ScopedStepPremise where
  binders := premise.binders
  resultType := premise.resultType
  source := premise.source.eraseBinderMetadata
  target := premise.target.eraseBinderMetadata

theorem ScopedStepPremise.canonicalize_idempotent
    (premise : ScopedStepPremise) :
    premise.canonicalize.canonicalize = premise.canonicalize := by
  cases premise
  simp [ScopedStepPremise.canonicalize,
    Pattern.eraseBinderMetadata_idempotent]

private theorem isWellScopedListAt_map_eq (depth : Nat)
    (patterns : List Pattern) (f : Pattern → Pattern)
    (hf : ∀ pattern ∈ patterns,
      (f pattern).isWellScopedAt depth = pattern.isWellScopedAt depth) :
    Pattern.isWellScopedListAt depth (patterns.map f) =
      Pattern.isWellScopedListAt depth patterns := by
  induction patterns with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, Pattern.isWellScopedListAt]
      rw [hf head (by simp)]
      exact congrArg (Bool.and (head.isWellScopedAt depth))
        (inductionHypothesis (by
          intro pattern membership
          exact hf pattern (by simp [membership])))

/-- Erasing binder display names leaves all de Bruijn scope checks unchanged. -/
theorem eraseBinderMetadata_isWellScopedAt (depth : Nat)
    (pattern : Pattern) :
    pattern.eraseBinderMetadata.isWellScopedAt depth =
      pattern.isWellScopedAt depth := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simp [Pattern.eraseBinderMetadata]
  | hfvar name => simp [Pattern.eraseBinderMetadata]
  | happly constructor arguments inductionHypothesis =>
      simpa only [Pattern.eraseBinderMetadata, Pattern.isWellScopedAt] using
        isWellScopedListAt_map_eq depth arguments
          Pattern.eraseBinderMetadata
          (fun argument membership =>
            inductionHypothesis argument membership depth)
  | hlambda binder body inductionHypothesis =>
      simpa only [Pattern.eraseBinderMetadata, Pattern.isWellScopedAt] using
        inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa only [Pattern.eraseBinderMetadata, Pattern.isWellScopedAt] using
        inductionHypothesis (depth + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [Pattern.eraseBinderMetadata, Pattern.isWellScopedAt,
        bodyInduction (depth + 1), replacementInduction depth]
  | hcollection kind elements rest inductionHypothesis =>
      simpa only [Pattern.eraseBinderMetadata, Pattern.isWellScopedAt] using
        isWellScopedListAt_map_eq depth elements
          Pattern.eraseBinderMetadata
          (fun element membership =>
            inductionHypothesis element membership depth)

/-- Canonicalizing a step premise does not alter its local scope judgment. -/
theorem ScopedStepPremise.canonicalize_isWellScopedAt (ambient : Nat)
    (premise : ScopedStepPremise) :
    premise.canonicalize.isWellScopedAt ambient =
      premise.isWellScopedAt ambient := by
  simp only [ScopedStepPremise.isWellScopedAt,
    ScopedStepPremise.canonicalize,
    eraseBinderMetadata_isWellScopedAt]

/-- Source-level local-scope admission is invariant under canonical display
names for every authored binder prefix. -/
theorem ScopedStepPremise.canonicalize_premiseLocallyScoped
    (premise : ScopedStepPremise) :
    LanguageDef.premiseLocallyScoped (.scopedStep premise.canonicalize) =
      LanguageDef.premiseLocallyScoped (.scopedStep premise) := by
  simpa only [LanguageDef.premiseLocallyScoped,
    ScopedStepPremise.isWellScopedAt, Nat.add_zero] using
    premise.canonicalize_isWellScopedAt 0

/-- The canonical scoped carrier is natural under ambient substitution.
The local binder prefix remains fixed on both sides of the equation. -/
theorem ScopedStepPremise.canonicalize_map
    (assignment : Assignment) (premise : ScopedStepPremise) :
    (premise.map assignment).canonicalize =
      (premise.canonicalize).map
        (fun index => (assignment index).eraseBinderMetadata) := by
  cases premise with
  | mk binders resultType source target =>
      simp [ScopedStepPremise.map, ScopedStepPremise.canonicalize,
        eraseBinderMetadata_substitute,
        eraseBinderMetadata_lift_assignment]

/-- A locally bound variable is available to a lambda-body premise. -/
def lamCongBody : ScopedStepPremise where
  binders := [.base "Term"]
  resultType := .base "Term"
  source := .apply "app" [.lambda (some "y") (.bvar 0), .bvar 0]
  target := .bvar 0

example : lamCongBody.isWellScopedAt 0 = true := by decide

/-- An index past the local binder is rejected in an empty ambient context. -/
example : ({ lamCongBody with target := .bvar 1 }).isWellScopedAt 0 = false := by
  decide

/-- An ambient variable is transported while the local variable stays put. -/
example :
    ({ lamCongBody with source := .bvar 1, target := .bvar 0 }).map
        (fun _ => .apply "z" []) =
      { lamCongBody with source := .apply "z" [], target := .bvar 0 } := by
  rfl

/-- A well-scoped ambient image preserves the open premise's local scope. -/
example :
    (({ lamCongBody with source := .bvar 1, target := .bvar 0 }).map
        (fun _ => .bvar 0)).isWellScopedAt 1 = true := by
  apply ScopedStepPremise.map_wellScoped
    (source := 1) (target := 1)
    (assignment := fun _ => .bvar 0)
  · intro index inSource
    exact decide_eq_true (by omega)
  · decide

/-- The assignment-scoping hypothesis matters: an escaping ambient image
remains an escaping index when carried below the local binder. -/
example :
    (({ lamCongBody with source := .bvar 1, target := .bvar 0 }).map
        (fun _ => .bvar 1)).isWellScopedAt 1 = false := by
  decide

end Mettapedia.OSLF.MeTTaIL.Syntax
