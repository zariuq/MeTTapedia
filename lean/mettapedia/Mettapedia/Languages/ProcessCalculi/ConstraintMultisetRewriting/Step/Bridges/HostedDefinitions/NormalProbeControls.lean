import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProbeFreshness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProbeExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalStructure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ExecutionControls

/-!
# Actual root-test executions and redexes beneath native constructors

The normal identity passes the actual root gate; a beta redex leaves only
dead gate branches. Beta beneath a lambda, a dependent codomain or the third
identity field is not a native normal form. These controls concern the root
gate and its structural specification; the complete recursive scanner law
is not inferred from them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

theorem empty_live {dev : Definitions.Development} (built : Compiled dev) :
    Solvable ([] : List (Constraint (BinderCore.keys built.rules) [] ())) :=
  ⟨Empty, ProgramBinders.ground MSig, ProgramBinders.close (fam (BinderCore.keys built.rules)),
    fun _ inside => False.elim (List.not_mem_nil inside)⟩

theorem beta_probe_enabled {dev : Definitions.Development} (built : Compiled dev)
    (D : Discipline MSig [] ()) (scope : Nat) {n : Nat}
    (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
    NormalRootMatching.Enabled built D scope []
      (NormalScanner.rootAt
        (Rigid.includeTerm (fam (BinderCore.keys built.rules)) (encodeTm (.app (.lam body) argument)))) := by
  rw [← NormalScanner.include_rootAt]
  exact (NormalProbeFreshness.initial_probe_iff built D scope _ (csym NormalScanner.stopTag)).mpr
    ⟨.beta body argument, rfl, rfl⟩

theorem beta_gate_dies {dev : Definitions.Development} (built : Compiled dev)
    (D : Discipline MSig [] ()) (supply : Nat → MClosed) {n : Nat}
    (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
    ∃ after : Config (BinderCore.keys built.rules) [] () D.Ty,
      Runs D (NormalProgram.program built D) supply
        (Config.initial (fun _ => 0)
          (NormalScanner.rootTest built
            (Rigid.includeTerm (fam (BinderCore.keys built.rules)) (encodeTm (.app (.lam body) argument)))
            (.ret (NormalScanner.marker (fam (BinderCore.keys built.rules)))))) after ∧
      ∀ branch ∈ after.branches, ¬ Solvable branch.store := by
  obtain ⟨world, dead, executed, rejected⟩ := NormalProbeExecution.matched_runs_dead built D supply
    (⟨0, 0, fun _ => 0⟩ : World (BinderCore.keys built.rules) [] ()) []
    (Rigid.includeTerm (fam (BinderCore.keys built.rules)) (encodeTm (.app (.lam body) argument)))
    (.ret (NormalScanner.marker (fam (BinderCore.keys built.rules)))) [] [] 0
    (empty_live built) (beta_probe_enabled built D 0 body argument)
  exact ⟨⟨world, dead⟩, by simpa [Config.initial] using executed, rejected⟩

theorem identity_gate_passes (D : Discipline MSig [] ()) (supply : Nat → MClosed) :
    ∃ world K,
      Runs D (NormalProgram.program ExecutionControls.built D) supply
        (Config.initial (fun _ => 0)
          (NormalScanner.rootTest ExecutionControls.built
            (Rigid.includeTerm (fam (BinderCore.keys ExecutionControls.built.rules))
              (encodeTm ExecutionControls.identity))
            (.ret (NormalScanner.marker (fam (BinderCore.keys ExecutionControls.built.rules))))))
        ⟨world, {(⟨K, .value (NormalScanner.marker (fam (BinderCore.keys ExecutionControls.built.rules))), [], []⟩ :
          Branch (BinderCore.keys ExecutionControls.built.rules) [] () D.Ty)}⟩ ∧ Solvable K := by
  let built := ExecutionControls.built
  let term := Rigid.includeTerm (fam (BinderCore.keys built.rules)) (encodeTm ExecutionControls.identity)
  let marker := NormalScanner.marker (fam (BinderCore.keys built.rules))
  let world : World (BinderCore.keys built.rules) [] () := ⟨0, 0, fun _ => 0⟩
  have disabled : ¬ NormalRootMatching.Enabled built D 0 [] (NormalScanner.rootAt term) := by
    rw [← NormalScanner.include_rootAt, NormalProbeFreshness.initial_probe_iff]
    exact NormalStructure.normal_no_root built ExecutionControls.identity ExecutionControls.identity_normal
  have fixes : instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) 0) term = term :=
    Rigid.instantiate_include _ _
  obtain ⟨executed, live⟩ := NormalProbeExecution.unmatched_fixed_runs built D supply world [] term
    (.ret marker) [] [] 0 (empty_live built) disabled fixes rfl
  let K := [(NormalScanner.probeAt term, NormalScanner.probeAt term)]
  have returned : SourceLanguage.Step D (NormalProgram.program built D) supply
      ⟨world.fresh, {(⟨K, .eval (.ret marker), [], []⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty)}⟩
      ⟨world.fresh, {(⟨K, .value marker, [], []⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty)}⟩ :=
    SourceLanguage.Step.single live (.ret world.fresh K marker [] [])
  refine ⟨world.fresh, K, ?_, live⟩
  refine Relation.ReflTransGen.tail ?_ returned
  simpa [Config.initial, K] using executed

theorem lambda_beta_not_normal {dev : Definitions.Development} (built : Compiled dev) {n : Nat}
    (body : Tower.Tm (n + 2)) (argument : Tower.Tm (n + 1)) :
    ¬ NormalStructure.Normal built (.lam (.app (.lam body) argument)) := by
  intro normal
  exact normal _ (.congLam (.betaPi body argument))

theorem codomain_beta_not_normal {dev : Definitions.Development} (built : Compiled dev) {n : Nat}
    (domain : Tower.Tm n) (body : Tower.Tm (n + 2)) (argument : Tower.Tm (n + 1)) :
    ¬ NormalStructure.Normal built (.pi domain (.app (.lam body) argument)) := by
  intro normal
  exact normal _ (.congPiCod (.betaPi body argument))

theorem third_id_child_beta_not_normal {dev : Definitions.Development} (built : Compiled dev) {n : Nat}
    (carrier left : Tower.Tm n) (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
    ¬ NormalStructure.Normal built (.id carrier left (.app (.lam body) argument)) := by
  intro normal
  exact normal _ (.congIdRight (.betaPi body argument))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeControls.beta_gate_dies
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeControls.identity_gate_passes
