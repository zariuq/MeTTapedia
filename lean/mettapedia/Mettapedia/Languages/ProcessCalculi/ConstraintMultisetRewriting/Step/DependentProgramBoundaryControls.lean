import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentProgramControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SchemaComprehension
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulativePrincipal

/-!
# Binder, closed-inhabitation and nonprincipal boundaries

The dependent schema machinery must preserve the existing language's
distinctions: substitution under a lambda does not capture its bound
variable; symbolic solutions are not closed inhabitants; ill-typed makes
are refused; and comprehension does not repair the cumulative counterexample
to a universal principal-unifier claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentProgram.BoundaryControls

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentTwins DependentFull
open Controls

noncomputable def capturedFunction (Γ : Context Tower.rules) : TotalTerm (outputContext Γ) :=
  let domain := DependentFull.Controls.groundType (outputContext Γ)
  let weakening := projectionHom (outputContext Γ) domain
  let codomain := (valueRow Γ).1.reindex weakening
  let body := (valueRow Γ).2.reindex weakening
  ⟨DependentTypes.rawPi levels domain codomain, Products.rawLam levels body⟩

/-- The output lambda returns the outer supplied value, not its own argument. -/
theorem instantiated_lambda_keeps_outer_variable {Γ : Context Tower.rules}
    (baseMap : DependentFull.Controls.point ⟶ Γ) :
    ((capturedFunction Γ).reindex (model baseMap)).2.code = .lam (.var 1) := rfl

theorem instantiated_lambda_is_not_captured {Γ : Context Tower.rules}
    (baseMap : DependentFull.Controls.point ⟶ Γ) :
    ((capturedFunction Γ).reindex (model baseMap)).2.code ≠ .lam (.var 0) := by
  rw [instantiated_lambda_keeps_outer_variable]
  intro same
  have bodies := Tm.lam.inj same
  have indices := Tm.var.inj bodies
  exact (by decide : (1 : Fin 2) ≠ 0) indices

noncomputable def functionSchema (Γ : Context Tower.rules) : Schema levels Nat Γ :=
  { schema Γ 0 1 1 with makes := [Make.ofRow (capturedFunction Γ)] }

noncomputable def functionTable : Program levels Nat := fun Γ => [functionSchema Γ]

def functionCandidate : Candidate functionTable start where
  ruleIndex := ⟨0, by decide⟩
  pick := ⟨⟨[], [0], [7]⟩, rfl⟩

theorem function_admitted : functionCandidate.schema.Admits functionCandidate.pick := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, ?_⟩,
    first_admitted.2.1, first_admitted.2.2.1, first_admitted.2.2.2⟩
  intro made member
  obtain rfl := List.mem_singleton.mp member
  exact Make.ofRow_wellTyped _

def functionPermission : {state : State Tower.rules Nat} → Candidate functionTable state → Prop :=
  fun _ => True

noncomputable def functionExecution : functionTable.Execution functionPermission start :=
  .cons functionCandidate function_admitted True.intro
    (.nil (functionCandidate.schema.publish functionCandidate.pick function_admitted.1))

theorem function_execution_is_one_actual_event : functionExecution.toRun.word.length = 1 := by
  rw [Program.Execution.toRun_word]
  rfl

/-- No closed substitution can supply the Ground helper in this tower.
The earlier admitted symbolic executions therefore do not certify a closed proof. -/
theorem no_closed_helper_model (Γ : Context Tower.rules) :
    ¬ Nonempty (empty Tower.rules ⟶ outputContext Γ) := by
  rintro ⟨substitution⟩
  have typed := substitution.typed (0 : Fin (outputContext Γ).arity)
  change Typed Tower.rules .nil (substitution.substitution 0)
    (.head .legacyGround) at typed
  exact ContextualDependentClosedBoundary.Controls.ground_uninhabited typed

def illTypedSchema : Schema levels Nat DependentFull.Controls.emptyState.frame where
  helpers := .nil _
  takes := []
  reads := []
  makes := [⟨DependentFull.Controls.groundType _, .head (.sort Tower.zero)⟩]
  tells := []
  guards := []
  queries := []

def illTypedPick : Pick illTypedSchema := ⟨⟨[], [], [1]⟩, rfl⟩

theorem illTyped_compiles_to_the_existing_control :
    illTypedSchema.compile (s := DependentFull.Controls.emptyState) illTypedPick =
      DependentFull.Controls.illTypedFiring := rfl

theorem illTyped_schema_is_refused :
    ¬ illTypedSchema.Admits (s := DependentFull.Controls.emptyState) illTypedPick := by
  intro admitted
  have native := (illTypedSchema.compile_admits_iff illTypedPick).mpr admitted
  rw [illTyped_compiles_to_the_existing_control] at native
  exact DependentFull.Controls.illTyped_refused native

/-- The same cumulative cross-store remains nonprincipal in the schema adapter. -/
theorem cumulative_cross_stays_nonprincipal
    {Δ : Context ContextualDependentWorklist.Controls.setting.R}
    (answer : Δ ⟶ ContextualDependentSweep.Witnesses.ctxCross) :
    ¬ (SchemaComprehension.typedEquality
        ContextualDependentWorklist.Controls.setting.levels).frames.Principal
      ContextualDependentSweep.Witnesses.crossStore answer := by
  rw [SchemaComprehension.typed_frames]
  exact ContextualDependentSweep.Witnesses.cross_no_principal answer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentProgram.BoundaryControls
