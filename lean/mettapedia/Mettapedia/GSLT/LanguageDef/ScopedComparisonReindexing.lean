import Mathlib.Data.List.GetD
import Mettapedia.GSLT.LanguageDef.EquationSubstitution
import Mettapedia.OSLF.MeTTaIL.RuleBinding
import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveComparison

/-!
# Canonical repeated-capture comparison under context reindexing

The ordinary scoped matcher recovers contextual bodies using variable-valued
assignments. Its supported occurrence spines also instantiate by such
assignments. Canonical comparison is preserved by these actual actions,
including nonempty spines and noninjective ambient renamings. Stored patterns
are unchanged; only the comparison observes their canonical representatives.

Re-canonicalization is essential: renaming can change the chosen parallel
order. These results concern ordinary binder scope, not quotation sealing or
arbitrary term-valued reflective substitution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopedComparisonReindexing

open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding Reflection ReflectiveCanonical ScopedReflectiveComparison

/-- The simultaneous context action agrees with the existing ambient
renaming operation, including its exact binder lifts. -/
theorem substitute_bvars_lift (rename : Nat → Nat) (pattern : Pattern)
    (depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift depth
        (fun index => .bvar (rename index))) pattern =
      ContextSubstitution.renameAmbientBVarsAt rename depth pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      by_cases below : index < depth
      · simp [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
          Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift,
          ContextSubstitution.renameAmbientBVarsAt, below]
      · simp [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
          Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift,
          ContextSubstitution.renameAmbientBVarsAt, below,
          Substitution.liftBVars, Nat.add_comm]
  | hfvar _ => simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
      ContextSubstitution.renameAmbientBVarsAt]
  | happly constructor arguments ih =>
      simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
        Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map,
        ContextSubstitution.renameAmbientBVarsAt]
      exact congrArg (Pattern.apply constructor)
        (List.map_congr_left fun p hp => ih p hp depth)
  | hlambda binder body ih =>
      simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
        Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift,
        ContextSubstitution.renameAmbientBVarsAt, ih]
  | hmultiLambda arity binders body ih =>
      simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
        Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift,
        ContextSubstitution.renameAmbientBVarsAt, ih]
  | hsubst body replacement ihBody ihReplacement =>
      simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
        Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift,
        ContextSubstitution.renameAmbientBVarsAt, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
        Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map,
        ContextSubstitution.renameAmbientBVarsAt]
      exact congrArg (fun xs => Pattern.collection kind xs rest)
        (List.map_congr_left fun p hp => ih p hp depth)

theorem substitute_bvars (rename : Nat → Nat) (pattern : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
      (fun index => .bvar (rename index)) pattern =
      ContextSubstitution.renameAmbientBVarsAt rename 0 pattern := by
  simpa only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_zero] using
    substitute_bvars_lift rename pattern 0

/-- Canonical equality survives arbitrary ambient index maps. No converse
is claimed when the map identifies distinct indices. -/
theorem canonicalEquivalent_rename
    (declaration : ReflectivePresentationDecl)
    (distinct : declaration.quoteConstructor ≠ declaration.dropConstructor)
    (rename : Nat → Nat) (depth : Nat) {left right : Pattern}
    (accepted : canonicalEquivalent declaration left right = true) :
    canonicalEquivalent declaration
      (ContextSubstitution.renameAmbientBVarsAt rename depth left)
      (ContextSubstitution.renameAmbientBVarsAt rename depth right) = true := by
  apply canonicalEquivalent_eq_true_iff.mpr
  rw [WellSorted.canonicalize_renameAmbientBVarsAt_factor declaration distinct rename depth left,
    WellSorted.canonicalize_renameAmbientBVarsAt_factor declaration distinct rename depth right,
    canonicalEquivalent_eq_true_iff.mp accepted]

/-- Literal slots and source-selected canonical Name slots are both stable
under the same reindexing. Only a selected declaration needs separation of
its quotation and drop constructors. -/
theorem bodyComparison_rename
    (profile : ReflectionProfile) (rule : RewriteRule)
    (distinct : ∀ declaration,
      ReflectiveSubstitution.matchingPresentationForRule? profile rule = some declaration →
      declaration.quoteConstructor ≠ declaration.dropConstructor)
    (name : String) (rename : Nat → Nat) (depth : Nat) {left right : Pattern}
    (accepted : bodyComparison profile rule name left right = true) :
    bodyComparison profile rule name
      (ContextSubstitution.renameAmbientBVarsAt rename depth left)
      (ContextSubstitution.renameAmbientBVarsAt rename depth right) = true := by
  unfold bodyComparison at accepted ⊢
  split at accepted
  · apply beq_iff_eq.mpr
    exact congrArg (ContextSubstitution.renameAmbientBVarsAt rename depth)
      (beq_iff_eq.mp accepted)
  · next declaration selected =>
      split at accepted
      · split at accepted
        · next nameSort =>
            simp only [nameSort, if_true]
            exact canonicalEquivalent_rename declaration (distinct declaration selected)
              rename depth accepted
        · next otherSort =>
            simp only [otherSort]
            exact beq_iff_eq.mpr (congrArg
              (ContextSubstitution.renameAmbientBVarsAt rename depth)
              (beq_iff_eq.mp accepted))
      · exact beq_iff_eq.mpr (congrArg
          (ContextSubstitution.renameAmbientBVarsAt rename depth)
          (beq_iff_eq.mp accepted))

theorem bodyComparison_substitute_bvars
    (profile : ReflectionProfile) (rule : RewriteRule)
    (distinct : ∀ declaration,
      ReflectiveSubstitution.matchingPresentationForRule? profile rule = some declaration →
      declaration.quoteConstructor ≠ declaration.dropConstructor)
    (name : String) (rename : Nat → Nat) {left right : Pattern}
    (accepted : bodyComparison profile rule name left right = true) :
    bodyComparison profile rule name
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (fun index => .bvar (rename index)) left)
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (fun index => .bvar (rename index)) right) = true := by
  simpa only [substitute_bvars] using
    bodyComparison_rename profile rule distinct name rename 0 accepted

private theorem recoveryAssignment_bvars (depth dependencies ambient : Nat)
    (indices : List Nat) :
    recoveryAssignment depth dependencies ambient indices =
      fun index => .bvar
        (if index < depth then
          if index ∈ indices then indices.idxOf index else dependencies + ambient
        else dependencies + (index - depth)) := by
  funext index
  simp only [recoveryAssignment]
  split
  · split <;> rfl
  · rfl

/-- Successful recovery exposes the exact inverse-spine action it used. -/
theorem recoverValue?_body (dependencies : List TypeExpr) (ambient depth : Nat)
    (arguments : List Pattern) (target : Pattern) (value : ContextualValue)
    (recovered : recoverValue? dependencies ambient depth arguments target = some value) :
    ∃ indices, variableSpine? depth arguments = some indices ∧
      value.body = Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (recoveryAssignment depth dependencies.length ambient indices) target := by
  unfold recoverValue? at recovered
  split at recovered <;> try cases recovered
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered
  rcases recovered with ⟨indices, spine, recovered⟩
  split at recovered <;> try cases recovered
  split at recovered <;> cases recovered
  exact ⟨indices, spine, rfl⟩

/-- Comparing two successful captures at one occurrence preserves source
comparison. Both contextual values retain their declared dependency and
ambient metadata; recovery does not replace them with canonical trees. -/
theorem bodyComparison_recover
    (profile : ReflectionProfile) (rule : RewriteRule)
    (distinct : ∀ declaration,
      ReflectiveSubstitution.matchingPresentationForRule? profile rule = some declaration →
      declaration.quoteConstructor ≠ declaration.dropConstructor)
    (name : String) (dependencies : List TypeExpr) (ambient depth : Nat)
    (arguments : List Pattern) {left right : Pattern} {leftValue rightValue : ContextualValue}
    (leftRecovered : recoverValue? dependencies ambient depth arguments left = some leftValue)
    (rightRecovered : recoverValue? dependencies ambient depth arguments right = some rightValue)
    (accepted : bodyComparison profile rule name left right = true) :
    leftValue.dependencies = dependencies ∧ rightValue.dependencies = dependencies ∧
      leftValue.ambient = ambient ∧ rightValue.ambient = ambient ∧
      bodyComparison profile rule name leftValue.body rightValue.body = true := by
  obtain ⟨indices, spine, leftBody⟩ := recoverValue?_body _ _ _ _ _ _ leftRecovered
  obtain ⟨otherIndices, otherSpine, rightBody⟩ := recoverValue?_body _ _ _ _ _ _ rightRecovered
  have same : otherIndices = indices := Option.some.inj (otherSpine.symm.trans spine)
  subst otherIndices
  have leftContext := recoverValue?_context _ _ _ _ _ _ leftRecovered
  have rightContext := recoverValue?_context _ _ _ _ _ _ rightRecovered
  refine ⟨leftContext.1, rightContext.1, leftContext.2, rightContext.2, ?_⟩
  rw [leftBody, rightBody, recoveryAssignment_bvars]
  exact bodyComparison_substitute_bvars profile rule distinct name _ accepted

private theorem variableSpine_mapM {depth : Nat} {arguments : List Pattern}
    {indices : List Nat}
    (mapped : arguments.mapM (fun argument => match argument with
      | .bvar index => if index < depth then some index else none
      | _ => none) = some indices) :
    arguments = indices.map Pattern.bvar := by
  induction arguments generalizing indices with
  | nil => simpa using congrArg (Option.map (List.map Pattern.bvar)) mapped
  | cons argument arguments ih =>
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at mapped
      rcases mapped with ⟨index, head, rest, tail, result⟩
      have argument_eq : argument = .bvar index := by
        cases argument <;> simp_all
      subst argument
      cases result
      simp only [List.map_cons, ih tail]

/-- Every successful matcher spine consists of precisely the returned bound
variable indices, in the original occurrence order. -/
theorem variableSpine?_arguments (depth : Nat) (arguments : List Pattern)
    (indices : List Nat) (spine : variableSpine? depth arguments = some indices) :
    arguments = indices.map Pattern.bvar := by
  unfold variableSpine? at spine
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at spine
  rcases spine with ⟨found, mapped, spine⟩
  split at spine <;> cases spine
  exact variableSpine_mapM mapped

private theorem occurrenceAssignment_bvars (dependencies depth : Nat)
    (indices : List Nat) :
    occurrenceAssignment dependencies depth (indices.map Pattern.bvar) =
      fun index => .bvar (if index < dependencies then indices.getD index 0
        else depth + (index - dependencies)) := by
  funext index
  simp only [occurrenceAssignment]
  split
  · simp only [List.getD_map]
  · rfl

/-- A successful occurrence exposes the same simultaneous substitution used
by the executable scoped matcher. -/
theorem instantiateValue?_body (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) (result : Pattern)
    (instantiated : instantiateValue? value ambient depth arguments = some result) :
    result = Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
      (occurrenceAssignment value.dependencies.length depth arguments) value.body := by
  unfold instantiateValue? at instantiated
  split at instantiated <;> try cases instantiated
  split at instantiated <;> try cases instantiated
  split at instantiated <;> try cases instantiated
  split at instantiated <;> try cases instantiated
  dsimp only at instantiated
  split at instantiated <;> cases instantiated
  rfl

/-- Repeated captured Name comparison is stable at any common supported
occurrence spine, including nonempty spines. Scope and exact roundtrip checks
remain the existing executable checks. -/
theorem bodyComparison_instantiate
    (profile : ReflectionProfile) (rule : RewriteRule)
    (distinct : ∀ declaration,
      ReflectiveSubstitution.matchingPresentationForRule? profile rule = some declaration →
      declaration.quoteConstructor ≠ declaration.dropConstructor)
    (name : String) (ambient depth : Nat) (arguments : List Pattern) (indices : List Nat)
    (spine : variableSpine? depth arguments = some indices)
    {leftValue rightValue : ContextualValue}
    (dependencies : leftValue.dependencies = rightValue.dependencies)
    {left right : Pattern}
    (leftInstantiated : instantiateValue? leftValue ambient depth arguments = some left)
    (rightInstantiated : instantiateValue? rightValue ambient depth arguments = some right)
    (accepted : bodyComparison profile rule name leftValue.body rightValue.body = true) :
    bodyComparison profile rule name left right = true := by
  rw [instantiateValue?_body _ _ _ _ _ leftInstantiated,
    instantiateValue?_body _ _ _ _ _ rightInstantiated,
    variableSpine?_arguments _ _ _ spine, dependencies, occurrenceAssignment_bvars]
  exact bodyComparison_substitute_bvars profile rule distinct name _ accepted

/-- On two successful recoveries through the same spine, comparison is
equivalent before and after capture. The reverse direction uses the checked
forward roundtrip, not injectivity of an arbitrary index map. -/
theorem bodyComparison_recover_iff
    (profile : ReflectionProfile) (rule : RewriteRule)
    (distinct : ∀ declaration,
      ReflectiveSubstitution.matchingPresentationForRule? profile rule = some declaration →
      declaration.quoteConstructor ≠ declaration.dropConstructor)
    (name : String) (dependencies : List TypeExpr) (ambient depth : Nat)
    (arguments : List Pattern) {left right : Pattern} {leftValue rightValue : ContextualValue}
    (leftRecovered : recoverValue? dependencies ambient depth arguments left = some leftValue)
    (rightRecovered : recoverValue? dependencies ambient depth arguments right = some rightValue) :
    bodyComparison profile rule name leftValue.body rightValue.body = true ↔
      bodyComparison profile rule name left right = true := by
  constructor
  · intro accepted
    obtain ⟨indices, spine, _⟩ := recoverValue?_body _ _ _ _ _ _ leftRecovered
    exact bodyComparison_instantiate profile rule distinct name ambient depth arguments indices
      spine ((recoverValue?_context _ _ _ _ _ _ leftRecovered).1.trans
        (recoverValue?_context _ _ _ _ _ _ rightRecovered).1.symm)
      (recoverValue?_forward _ _ _ _ _ _ leftRecovered)
      (recoverValue?_forward _ _ _ _ _ _ rightRecovered) accepted
  · intro accepted
    exact (bodyComparison_recover profile rule distinct name dependencies ambient depth
      arguments leftRecovered rightRecovered accepted).2.2.2.2

/-- Context reindexing respects the actual ordinary scope checker whenever
each ambient source index has a target index. Local binders remain fixed. -/
theorem rename_wellScoped (rename : Nat → Nat) (source target depth : Nat)
    (bounded : ∀ index, index < source → rename index < target)
    {pattern : Pattern} (wellScoped : pattern.isWellScopedAt (source + depth) = true) :
    (ContextSubstitution.renameAmbientBVarsAt rename depth pattern).isWellScopedAt
      (target + depth) = true := by
  rw [← substitute_bvars_lift]
  apply Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_wellScoped
    (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.WellScopedAssignment.lift
      (assignment := fun index => .bvar (rename index)) ?_ depth) wellScoped
  intro index inSource
  exact decide_eq_true (bounded index inSource)

end Mettapedia.GSLT.LanguageDef.ScopedComparisonReindexing
