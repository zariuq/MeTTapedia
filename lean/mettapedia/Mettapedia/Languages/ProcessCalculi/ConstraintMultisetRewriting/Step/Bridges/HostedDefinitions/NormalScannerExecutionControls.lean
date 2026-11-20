import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProbeControls

/-!
# Concrete normal scanner executions and a beta redex beneath a binder

The actual compiler for the empty development supplies the rule table. Its
normal lambda, Pi and identity-type examples reach finished live scanner
branches. A beta redex beneath a lambda has a genuine native reduction; its
inner root test rejects every branch while retaining the lambda child frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerExecutionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

theorem constant_normal {n : Nat} (name : DeclName) :
    NormalStructure.Normal ExecutionControls.built (.const name : Tower.Tm n) := by
  intro output reduction
  cases reduction with
  | root edge =>
      obtain ⟨head, spine, positive, _⟩ :=
        Definitions.dev_root_spine ExecutionControls.empty_checked ExecutionControls.built.native edge
      change some (name, 0) = some (head, Definitions.devArity [] head) at spine
      have arity : 0 = Definitions.devArity [] head := (Prod.mk.inj (Option.some.inj spine)).2
      omega

theorem lambda_normal : NormalStructure.Normal ExecutionControls.built NormalScanner.lambdaExample :=
  ExecutionControls.identity_normal

theorem pi_normal : NormalStructure.Normal ExecutionControls.built NormalScanner.piExample := by
  intro output reduction
  cases reduction with
  | root edge =>
      obtain ⟨head, spine, _, _⟩ :=
        Definitions.dev_root_spine ExecutionControls.empty_checked ExecutionControls.built.native edge
      simp [NormalScanner.piExample, ConstructorSystem.spineHead] at spine
  | congPiDom edge => exact constant_normal _ _ edge
  | congPiCod edge => exact constant_normal _ _ edge

theorem id_normal : NormalStructure.Normal ExecutionControls.built NormalScanner.idExample := by
  intro output reduction
  cases reduction with
  | root edge =>
      obtain ⟨head, spine, _, _⟩ :=
        Definitions.dev_root_spine ExecutionControls.empty_checked ExecutionControls.built.native edge
      simp [NormalScanner.idExample, ConstructorSystem.spineHead] at spine
  | congIdTy edge => exact constant_normal _ _ edge
  | congIdLeft edge => exact constant_normal _ _ edge
  | congIdRight edge => exact constant_normal _ _ edge

theorem named_normal (term : Tower.Tm 0)
    (selected : term ∈ [NormalScanner.lambdaExample, NormalScanner.piExample, NormalScanner.idExample]) :
    NormalStructure.Normal ExecutionControls.built term := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl
  · exact lambda_normal
  · exact pi_normal
  · exact id_normal

theorem named_normal_executes (D : Discipline MSig [] ()) (supply : Nat → MClosed)
    (term : Tower.Tm 0)
    (selected : term ∈ [NormalScanner.lambdaExample, NormalScanner.piExample, NormalScanner.idExample]) :
    ∃ next branch,
      Runs D (NormalProgram.program ExecutionControls.built D) supply
        (Config.initial (fun _ => 0) (NormalScanner.query ExecutionControls.built (encodeTm term))) next ∧
      branch ∈ next.branches ∧ branch.Finished (D := D) ∧ Solvable branch.store ∧
      (csym NormalScanner.markerTag) ∈ branch.answer (D := D) :=
  NormalScannerExecution.normal_executes ExecutionControls.built D supply term (named_normal term selected)

def betaBody : Tower.Tm 1 := .app (.lam (.var 0)) (.var 0)

def betaBelowBinder : Tower.Tm 0 := .lam betaBody

theorem beta_below_binder_reduces :
    StrongNormalization.Reduces (Definitions.devPackage [] ExecutionControls.built.nativeRows)
      betaBelowBinder NormalScanner.lambdaExample :=
  .congLam (.betaPi (.var 0) (.var 0))

theorem beta_below_binder_not_normal :
    ¬ NormalStructure.Normal ExecutionControls.built betaBelowBinder := by
  intro normal
  exact normal _ beta_below_binder_reduces

def lambdaChildFrame (D : Discipline MSig [] ()) :
    Frame (BinderCore.keys ExecutionControls.built.rules) [] () D.Ty :=
  .bindTo (NormalScanner.site ExecutionControls.built 2)
    (NormalScanner.marker (fam (BinderCore.keys ExecutionControls.built.rules)))
    (.ret (NormalScanner.marker (fam (BinderCore.keys ExecutionControls.built.rules))))

theorem lambda_child_frame_exact (D : Discipline MSig [] ()) :
    NormalScanner.childTests ExecutionControls.built (Ty := D.Ty) .lam =
      .let_ (NormalScanner.site ExecutionControls.built 2)
        (NormalScanner.marker (fam (BinderCore.keys ExecutionControls.built.rules)))
        (.apply (NormalScanner.scanAt (NormalScanner.datum ExecutionControls.built 0)))
        (.ret (NormalScanner.marker (fam (BinderCore.keys ExecutionControls.built.rules)))) := rfl

theorem beta_child_gate_dies (D : Discipline MSig [] ()) (supply : Nat → MClosed) :
    ∃ after : Config (BinderCore.keys ExecutionControls.built.rules) [] () D.Ty,
      Runs D (NormalProgram.program ExecutionControls.built D) supply
        ⟨⟨0, 0, fun _ => 0⟩,
          {(⟨[], .eval (NormalScanner.rootTest ExecutionControls.built
            (Rigid.includeTerm (fam (BinderCore.keys ExecutionControls.built.rules)) (encodeTm betaBody))
            (.ret (NormalScanner.marker (fam (BinderCore.keys ExecutionControls.built.rules))))),
            [lambdaChildFrame D], []⟩ :
            Branch (BinderCore.keys ExecutionControls.built.rules) [] () D.Ty)}⟩ after ∧
      ∀ branch ∈ after.branches, ¬ Solvable branch.store := by
  obtain ⟨world, dead, executed, rejected⟩ :=
    NormalProbeExecution.matched_runs_dead ExecutionControls.built D supply
      (⟨0, 0, fun _ => 0⟩ : World (BinderCore.keys ExecutionControls.built.rules) [] ()) []
      (Rigid.includeTerm (fam (BinderCore.keys ExecutionControls.built.rules)) (encodeTm betaBody))
      (.ret (NormalScanner.marker (fam (BinderCore.keys ExecutionControls.built.rules))))
      [lambdaChildFrame D] [] 0 (NormalProbeControls.empty_live ExecutionControls.built)
      (NormalProbeControls.beta_probe_enabled ExecutionControls.built D 0
        (.var 0 : Tower.Tm 2) (.var 0 : Tower.Tm 1))
  exact ⟨⟨world, dead⟩, by simpa [betaBody] using executed, rejected⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerExecutionControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerExecutionControls.named_normal_executes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerExecutionControls.beta_child_gate_dies
