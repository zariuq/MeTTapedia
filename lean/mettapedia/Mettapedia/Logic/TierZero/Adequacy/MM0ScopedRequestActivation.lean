import Mettapedia.Logic.TierZero.Adequacy.MM0ScopedPatterns
import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintCatalog

/-!
# Activating requests with actual restricted contextual bodies

The source constructor trees are reinterfaced using each formal's allowed
spine. Activation consumes the body list returned by structural construction;
sorting remains its actual executable data check. No pairwise dependency
Boolean is called by this activation path.

For independently admissible arguments, actual native rule instances coincide
with the qualified source-data compatibility profile. Conversely successful
natural activation supplies independent admissibility through body existence.
The comparison preserves every premise and conclusion template.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ScopedRequestActivation

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport
open MM0Rewriting
open MM0ScopedPatterns
open MM0ConstraintTheoremApplication (falseHead trueHead)

def recipe (signature : TermSignature) (formal target : Context) (name : String)
    (premises : List Pat) (conclusion : Pat) (expressions : List Preterm) : RequestActivation.Recipe Nat Head Pat where
  request := reinterface formal target expressions (theoremRequest target.length formal.length name)
  premises := premises.map (reinterface formal target expressions)
  conclusion := reinterface formal target expressions conclusion
  dataCondition := fun _ => Substitution.checkArguments signature target expressions formal

def activate (signature : TermSignature) (formal target : Context) (name : String)
    (premises : List Pat) (conclusion : Pat) (expressions : List Preterm) : Option (RuleInstance Tm) := do
  let bodies ← MM0ScopedArgumentAdmission.construct signature formal target expressions
  RequestActivation.activate ContextualPatterns.layer falseHead trueHead
    (recipe signature formal target name premises conclusion expressions) (suppliedAssignment bodies)

theorem successful_arguments {sorts : SortSignature} (signature : TermSignature) (formal target : Context)
    (formed : Context.WellFormed sorts target) (name : String) (premises : List Pat) (conclusion : Pat)
    (expressions : List Preterm) {rule : RuleInstance Tm}
    (computed : activate signature formal target name premises conclusion expressions = some rule) :
    Substitution.Admissible signature formal target expressions := by
  cases constructed : MM0ScopedArgumentAdmission.construct signature formal target expressions with
  | none => simp [activate, constructed] at computed
  | some bodies =>
      exact (MM0ScopedArgumentAdmission.construct_isSome_iff signature formal target formed expressions).mp
        (by rw [constructed]; rfl)

theorem premise_instances {sorts : SortSignature} {signature : TermSignature} {formal target : Context}
    {expressions : List Preterm} (formed : Context.WellFormed sorts target)
    (admitted : Substitution.Admissible signature formal target expressions) (premises : List Pat)
    (original : ∀ pattern ∈ premises, Ambient target.length pattern) :
    instTemplate ContextualPatterns.layer (assignment formal target expressions)
        (premises.map (reinterface formal target expressions)) =
      instTemplate ContextualPatterns.layer (expressionAssignment target expressions) premises := by
  induction premises with
  | nil => rfl
  | cons pattern rest earlier =>
      have head := reinterface_inst formed admitted pattern (original pattern (by simp))
      have tail := earlier (fun other member => original other (by simp [member]))
      simp only [instTemplate] at tail
      simp only [instTemplate, List.map_cons, List.mapM_cons]
      rw [show ContextualPatterns.layer.inst (assignment formal target expressions)
          (reinterface formal target expressions pattern) =
          ContextualPatterns.layer.inst (expressionAssignment target expressions) pattern from head, tail]

theorem activate_eq_source_of_admissible {sorts : SortSignature} (signature : TermSignature)
    (formal target : Context) (formed : Context.WellFormed sorts target) (name : String)
    (premises : List Pat) (conclusion : Pat) (expressions : List Preterm)
    (admitted : Substitution.Admissible signature formal target expressions)
    (premisesOriginal : ∀ pattern ∈ premises, Ambient target.length pattern)
    (conclusionOriginal : Ambient target.length conclusion) :
    activate signature formal target name premises conclusion expressions =
      RequestActivation.activate ContextualPatterns.layer falseHead trueHead
        ((MM0ConstraintCatalog.argumentSchema signature target formal premises conclusion).requestRecipe target name)
        (expressionAssignment target expressions) := by
  obtain ⟨bodies, constructed⟩ := Option.isSome_iff_exists.mp
    ((MM0ScopedArgumentAdmission.construct_isSome_iff signature formal target formed expressions).mpr admitted)
  have actualBodies := suppliedAssignment_eq constructed
  have requestInstance : ContextualPatterns.layer.inst (assignment formal target expressions)
      (reinterface formal target expressions (theoremRequest target.length formal.length name)) =
      ContextualPatterns.layer.inst (expressionAssignment target expressions) (theoremRequest target.length formal.length name) :=
    reinterface_inst formed admitted (theoremRequest target.length formal.length name)
      (judgmentPattern_ambient target.length (requestTag name) (formals formal.length))
  have premiseInstances := premise_instances formed admitted premises premisesOriginal
  have conclusionInstance : ContextualPatterns.layer.inst (assignment formal target expressions)
      (reinterface formal target expressions conclusion) =
      ContextualPatterns.layer.inst (expressionAssignment target expressions) conclusion :=
    reinterface_inst formed admitted conclusion conclusionOriginal
  have sorted := (Substitution.checkArguments_iff _ _ _ _).mpr admitted.typed
  have sourceData := (admitArguments_iff signature formal target (expressionAssignment target expressions) expressions).mpr
    ⟨admitted, fun _ _ => rfl⟩
  unfold activate
  rw [constructed]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [actualBodies]
  simp only [RequestActivation.activate, recipe, MM0ConstraintCatalog.argumentSchema,
    MM0ConstraintCatalog.Schema.requestRecipe]
  rw [requestInstance, premiseInstances, conclusionInstance]
  simp only [sorted, sourceData, Option.isSome_some]

theorem activate_reflects_source {sorts : SortSignature} (signature : TermSignature) (formal target : Context)
    (formed : Context.WellFormed sorts target) (name : String) (premises : List Pat) (conclusion : Pat)
    (expressions : List Preterm) (premisesOriginal : ∀ pattern ∈ premises, Ambient target.length pattern)
    (conclusionOriginal : Ambient target.length conclusion) {rule : RuleInstance Tm}
    (computed : activate signature formal target name premises conclusion expressions = some rule) :
    RequestActivation.activate ContextualPatterns.layer falseHead trueHead
      ((MM0ConstraintCatalog.argumentSchema signature target formal premises conclusion).requestRecipe target name)
      (expressionAssignment target expressions) = some rule := by
  rw [← activate_eq_source_of_admissible signature formal target formed name premises conclusion expressions
    (successful_arguments signature formal target formed name premises conclusion expressions computed)
    premisesOriginal conclusionOriginal]
  exact computed

end Mettapedia.Logic.TierZero.Adequacy.MM0ScopedRequestActivation
