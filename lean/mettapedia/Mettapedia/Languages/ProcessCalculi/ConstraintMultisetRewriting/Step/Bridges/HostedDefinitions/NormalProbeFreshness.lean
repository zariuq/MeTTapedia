import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalRootMatching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProgramFormation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Hygiene

/-!
# Probe admission through the existing source freshness invariant

Fresh source copies are combined with the old branch by the hosting layer's
grafting theorem. This uses its semantic `StoreBelow` and `DependsBelow`
invariants, so the probe interface does not require every incoming datum to
have the more restrictive single-equation origin. The closed initial probe
discharges both freshness and determination directly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeFreshness

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

variable {dev : Definitions.Development} (built : Compiled dev)

def equationAssignment {X : Type} (target : X → MetaArity MSig)
    (index : Fin built.rules.length) (environment : (built.rules.get index).Ground) :
    Assignment (fam (BinderCore.keys built.rules)) target :=
  fun name => Rigid.includeTerm target
    (ProgramBinders.extendGround built.rules.get index environment name.key)

theorem read_embedded {X : Type} (target : X → MetaArity MSig)
    (index : Fin built.rules.length) (environment : (built.rules.get index).Ground)
    (term : Term (signature MSig (built.rules.get index).arity) [] ()) :
    instantiate (equationAssignment built target index environment)
      (instantiate (BinderCore.embedAt built.rules index) term) =
      instantiate ((built.rules.get index).assign environment target) term := by
  rw [instantiate_comp]
  congr 1
  funext hole
  rw [BinderCore.embedAt, instantiate_generator]
  change Rigid.includeTerm target (ProgramBinders.extendGround built.rules.get index environment ⟨index, hole⟩) = _
  rw [congrFun (ProgramBinders.extendGround_at built.rules.get index environment) hole]
  rfl

theorem selected_enables_below (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ()) (call : MClosed)
    (storeBelow : Hosting.StoreBelow scope K) (callBelow : Hosting.DependsBelow scope term)
    (read : Reads K term call) (selected : NormalRootMatching.Selected built call) :
    NormalRootMatching.Enabled built D scope K term := by
  obtain ⟨index, inside, answer, environment, matched, _⟩ := selected
  obtain ⟨X, target, model, solved, reads⟩ := read
  have leftReads : instantiate (equationAssignment built target index environment)
      (BinderCore.embedEquation built.rules (Ty := D.Ty) index).lhs = Rigid.includeTerm target call := by
    exact (read_embedded built target index environment (built.rules.get index).lhs).trans
      (((built.rules.get index).reads_in_frame environment (built.rules.get index).lhs call target).mp matched)
  have live := (Hosting.solvable_copy_iff
    (BinderCore.embedEquation built.rules (Ty := D.Ty) index).lhs storeBelow callBelow).mpr
      ⟨X, target, model, equationAssignment built target index environment, solved, leftReads.trans reads.symm⟩
  refine ⟨NormalProbe.equation (BinderCore.embedEquation built.rules index),
    List.mem_map.mpr ⟨index, inside, rfl⟩, ?_⟩
  exact (NormalProbe.copied_match_iff (BinderCore.embedEquation built.rules index) scope K term).mpr live

theorem enabled_iff_below (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ()) (call : MClosed)
    (storeBelow : Hosting.StoreBelow scope K) (callBelow : Hosting.DependsBelow scope term)
    (determined : Determines K term call) :
    NormalRootMatching.Enabled built D scope K term ↔ NormalRootMatching.Selected built call :=
  ⟨NormalRootMatching.selected_of_enabled built D scope K term call determined,
    selected_enables_below built D scope K term call storeBelow callBelow
      ((determined.reads_iff call).mpr rfl)⟩

theorem probe_iff_redex_below (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) {n : Nat} (term : Tower.Tm n)
    (continuation : MClosed)
    (storeBelow : Hosting.StoreBelow scope K) (callBelow : Hosting.DependsBelow scope datum)
    (determined : Determines K datum (rootC (encodeTm term) continuation)) :
    NormalRootMatching.Enabled built D scope K datum ↔ NormalRootMatching.Redex built term :=
  (enabled_iff_below built D scope K datum _ storeBelow callBelow determined).trans
    (NormalRootMatching.selected_iff_redex built term continuation)

theorem determines_include (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (live : Solvable K) (call : MClosed) :
    Determines K (Rigid.includeTerm (fam (BinderCore.keys built.rules)) call) call :=
  ⟨live, fun _ _ _ => Rigid.instantiate_include _ call⟩

theorem included_below (scope : Nat) (call : MClosed) :
    Hosting.DependsBelow scope (Rigid.includeTerm (fam (BinderCore.keys built.rules)) call) := by
  apply Hosting.dependsBelow_of_unopened
  intro name member
  rw [Rigid.support_include] at member
  cases member

theorem initial_probe_iff (D : Discipline MSig [] ()) (scope : Nat)
    {n : Nat} (term : Tower.Tm n) (continuation : MClosed) :
    NormalRootMatching.Enabled built D scope []
      (Rigid.includeTerm (fam (BinderCore.keys built.rules)) (rootC (encodeTm term) continuation)) ↔
      NormalRootMatching.Redex built term := by
  apply probe_iff_redex_below built D scope [] _ term continuation
  · intro equation inside
    cases inside
  · exact included_below built scope _
  · apply determines_include built []
    exact ⟨Empty, ProgramBinders.ground MSig, ProgramBinders.close (fam (BinderCore.keys built.rules)),
      fun _ inside => False.elim (List.not_mem_nil inside)⟩

theorem scoped_call_below {scope : Nat}
    {D : Discipline MSig [] ()} {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    {pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)}
    (runtimeScope : Hosting.Scoping scope (⟨K, .eval (.apply datum), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty)) :
    Hosting.StoreBelow scope K ∧ Hosting.DependsBelow scope datum := by
  obtain ⟨visible, level, levels, invariant⟩ := runtimeScope
  constructor
  · intro equation member
    constructor
    all_goals
      intro X target first second agree
      apply instantiate_congr
      intro name used
      apply agree name
    · exact invariant.visibleBelow name ((invariant.store equation member).1 name used)
    · exact invariant.visibleBelow name ((invariant.store equation member).2 name used)
  · intro X target first second agree
    apply instantiate_congr
    intro name used
    exact agree name (invariant.visibleBelow name (invariant.focus name used))

theorem query_call_below (D : Discipline MSig [] ()) (supply : Nat → MClosed)
    (input : Tower.Tm 0) {configuration : Config (BinderCore.keys built.rules) [] () D.Ty}
    (executed : Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built input)) configuration)
    {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    {pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)}
    (member : (⟨K, .eval (.apply datum), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ configuration.branches) :
    Hosting.StoreBelow configuration.world.scope K ∧ Hosting.DependsBelow configuration.world.scope datum := by
  apply scoped_call_below built
  exact Hosting.scoping_reachable (fun _ => 0) (NormalProgram.query built input)
    (NormalProgramFormation.equations_formed built D)
    (NormalProgramFormation.query_scoped built input)
    (NormalProgramFormation.query_distinct built input)
    (NormalProgramFormation.query_arrows built input) configuration executed _ member

theorem below_unwrapped {scope : Nat} {datum : Data (BinderCore.keys built.rules) [] ()}
    (below : Hosting.DependsBelow scope (NormalProbe.wrap datum)) : Hosting.DependsBelow scope datum := by
  intro X target first second agree
  have same := below first second agree
  rw [NormalProbe.instantiate_wrap, NormalProbe.instantiate_wrap] at same
  exact (NormalProbe.wrap_eq_iff _ _).mp same

theorem reached_probe_iff (D : Discipline MSig [] ()) (supply : Nat → MClosed)
    (input : Tower.Tm 0) {configuration : Config (BinderCore.keys built.rules) [] () D.Ty}
    (executed : Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built input)) configuration)
    {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    {pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)}
    (member : (⟨K, .eval (.apply (NormalProbe.wrap datum)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ configuration.branches)
    {n : Nat} (term : Tower.Tm n) (continuation : MClosed)
    (determined : Determines K datum (rootC (encodeTm term) continuation)) :
    NormalRootMatching.Enabled built D configuration.world.scope K datum ↔ NormalRootMatching.Redex built term := by
  obtain ⟨storeBelow, callBelow⟩ := query_call_below built D supply input executed member
  exact probe_iff_redex_below built D configuration.world.scope K datum term continuation storeBelow
    (below_unwrapped built callBelow) determined

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeFreshness

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeFreshness.probe_iff_redex_below
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeFreshness.initial_probe_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeFreshness.reached_probe_iff
