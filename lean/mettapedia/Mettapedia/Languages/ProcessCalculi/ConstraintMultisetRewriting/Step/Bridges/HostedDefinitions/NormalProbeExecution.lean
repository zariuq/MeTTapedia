import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProgramIsolation

/-!
# The root-test gate through actual source runs

An unmatched probe returns its original wrapped call and enters the opened
continuation through the real let bind. A matched live alternative returns
the redex marker; its bind has an inconsistent store. Finite runs retain all
generated siblings, including dead alternatives, and any surrounding bag.
Opening fixes are explicit when an unchanged continuation is requested.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open NativeTypesOnTheStep.Computing

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)

def gateFrame (term : Data (BinderCore.keys built.rules) [] ())
    (continuation : Comp (BinderCore.keys built.rules) [] () D.Ty) :
    Frame (BinderCore.keys built.rules) [] () D.Ty :=
  .bindTo (NormalScanner.site built 1) (NormalScanner.probeAt term) continuation

def boundBranch (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (value term : Data (BinderCore.keys built.rules) [] ())
    (continuation : Comp (BinderCore.keys built.rules) [] () D.Ty)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)) :
    Branch (BinderCore.keys built.rules) [] () D.Ty :=
  ⟨K ++ [(instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) scope)
      (NormalScanner.probeAt term), value)],
    .eval (continuation.inst (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) scope)),
    frames, pending⟩

theorem redex_bind_unsolvable (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ()) :
    ¬ Solvable (K ++ [(instantiate
      (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) scope)
      (NormalScanner.probeAt term), NormalProbe.marker (fam (BinderCore.keys built.rules)))]) := by
  rintro ⟨X, target, assignment, solved⟩
  have same := (models_singleton assignment _).mp ((models_append assignment _ _).mp solved).2
  rw [NormalScanner.instantiate_probeAt, NormalScanner.instantiate_probeAt] at same
  change NormalProbe.wrap _ = NormalProbe.marker target at same
  exact NormalProbe.marker_ne_wrapped target _ same.symm

theorem redex_value_move (world : World (BinderCore.keys built.rules) [] ())
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ())
    (continuation : Comp (BinderCore.keys built.rules) [] () D.Ty)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    {afterWorld : World (BinderCore.keys built.rules) [] ()}
    {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .value (NormalProbe.marker (fam (BinderCore.keys built.rules))),
        gateFrame built D term continuation :: frames, pending⟩ afterWorld children) :
    afterWorld = world.fresh ∧ ∀ child ∈ children, ¬ Solvable child.store := by
  cases moved with
  | letBind =>
      refine ⟨rfl, ?_⟩
      intro child member
      rw [Multiset.mem_singleton.mp member]
      exact redex_bind_unsolvable built world.scope K term

theorem unmatched_runs (world : World (BinderCore.keys built.rules) [] ())
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ())
    (continuation : Comp (BinderCore.keys built.rules) [] () D.Ty)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (rest : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty))
    (live : Solvable K)
    (disabled : ¬ NormalRootMatching.Enabled built D world.scope K (NormalScanner.rootAt term)) :
    Runs D (NormalProgram.program built D) supply
      ⟨world, (⟨K, .eval (NormalScanner.rootTest built term continuation), frames, pending⟩ ::ₘ rest)⟩
      ⟨world.fresh, boundBranch built D world.scope K (NormalScanner.probeAt term) term
        continuation frames pending ::ₘ rest⟩ := by
  let entered : Branch (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨K, .eval (.apply (NormalScanner.probeAt term)), gateFrame built D term continuation :: frames, pending⟩
  let replied : Branch (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨K, .value (NormalScanner.probeAt term), gateFrame built D term continuation :: frames, pending⟩
  have start : SourceLanguage.Step D (NormalProgram.program built D) supply
      ⟨world, (⟨K, .eval (NormalScanner.rootTest built term continuation), frames, pending⟩ ::ₘ rest)⟩
      ⟨world, entered ::ₘ rest⟩ :=
    SourceLanguage.Step.of_eq rfl rfl live (.letStart world K (NormalScanner.site built 1)
      (NormalScanner.probeAt term) (.apply (NormalScanner.probeAt term)) continuation frames pending)
  have reply : SourceLanguage.Step D (NormalProgram.program built D) supply
      ⟨world, entered ::ₘ rest⟩ ⟨world, replied ::ₘ rest⟩ :=
    SourceLanguage.Step.of_eq rfl rfl live (.unmatched world K (NormalScanner.probeAt term)
      (gateFrame built D term continuation :: frames) pending
      (NormalProgramIsolation.no_probe_matches built D world.scope K (NormalScanner.rootAt term) disabled))
  have bind : SourceLanguage.Step D (NormalProgram.program built D) supply
      ⟨world, replied ::ₘ rest⟩
      ⟨world.fresh, boundBranch built D world.scope K (NormalScanner.probeAt term) term
        continuation frames pending ::ₘ rest⟩ :=
    SourceLanguage.Step.of_eq rfl rfl live (.letBind world K (NormalScanner.probeAt term)
      (NormalScanner.site built 1) (NormalScanner.probeAt term) continuation frames pending)
  exact ((Relation.ReflTransGen.single start).tail reply).tail bind

theorem unmatched_bound_live (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ())
    (continuation : Comp (BinderCore.keys built.rules) [] () D.Ty)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (live : Solvable K)
    (fixes : instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) scope) term = term) :
    Solvable (boundBranch built D scope K (NormalScanner.probeAt term) term continuation frames pending).store := by
  change Solvable (K ++ [(instantiate
    (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) scope)
    (NormalScanner.probeAt term), NormalScanner.probeAt term)])
  rw [NormalScanner.instantiate_probeAt, fixes]
  obtain ⟨X, target, assignment, solved⟩ := live
  exact ⟨X, target, assignment, (models_append assignment _ _).mpr
    ⟨solved, (models_singleton assignment _).mpr rfl⟩⟩

theorem unmatched_fixed_runs (world : World (BinderCore.keys built.rules) [] ())
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ())
    (continuation : Comp (BinderCore.keys built.rules) [] () D.Ty)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (rest : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty))
    (live : Solvable K)
    (disabled : ¬ NormalRootMatching.Enabled built D world.scope K (NormalScanner.rootAt term))
    (fixesTerm : instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) world.scope) term = term)
    (fixesBody : continuation.inst
      (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) world.scope) = continuation) :
    Runs D (NormalProgram.program built D) supply
      ⟨world, (⟨K, .eval (NormalScanner.rootTest built term continuation), frames, pending⟩ ::ₘ rest)⟩
      ⟨world.fresh, (⟨K ++ [(NormalScanner.probeAt term, NormalScanner.probeAt term)],
        .eval continuation, frames, pending⟩ ::ₘ rest)⟩ ∧
      Solvable (K ++ [(NormalScanner.probeAt term, NormalScanner.probeAt term)]) := by
  have executed := unmatched_runs built D supply world K term continuation frames pending rest live disabled
  have alive := unmatched_bound_live built D world.scope K term continuation frames pending live fixesTerm
  simp only [boundBranch, NormalScanner.instantiate_probeAt, fixesTerm, fixesBody] at executed alive
  exact ⟨executed, alive⟩

theorem reject_reply_runs (world : World (BinderCore.keys built.rules) [] ())
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ())
    (continuation : Comp (BinderCore.keys built.rules) [] () D.Ty)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (rest : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)) (live : Solvable K) :
    Runs D (NormalProgram.program built D) supply
      ⟨world, (⟨K, .eval (.ret (NormalProbe.marker (fam (BinderCore.keys built.rules)))),
        gateFrame built D term continuation :: frames, pending⟩ ::ₘ rest)⟩
      ⟨world.fresh, boundBranch built D world.scope K (NormalProbe.marker (fam (BinderCore.keys built.rules)))
        term continuation frames pending ::ₘ rest⟩ := by
  let replied : Branch (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨K, .value (NormalProbe.marker (fam (BinderCore.keys built.rules))),
      gateFrame built D term continuation :: frames, pending⟩
  have reply : SourceLanguage.Step D (NormalProgram.program built D) supply
      ⟨world, (⟨K, .eval (.ret (NormalProbe.marker (fam (BinderCore.keys built.rules)))),
        gateFrame built D term continuation :: frames, pending⟩ ::ₘ rest)⟩
      ⟨world, replied ::ₘ rest⟩ :=
    SourceLanguage.Step.of_eq rfl rfl live (.ret world K _ _ _)
  have bind : SourceLanguage.Step D (NormalProgram.program built D) supply
      ⟨world, replied ::ₘ rest⟩
      ⟨world.fresh, boundBranch built D world.scope K (NormalProbe.marker (fam (BinderCore.keys built.rules)))
        term continuation frames pending ::ₘ rest⟩ :=
    SourceLanguage.Step.of_eq rfl rfl live (.letBind world K _ (NormalScanner.site built 1)
      (NormalScanner.probeAt term) continuation frames pending)
  exact (Relation.ReflTransGen.single reply).tail bind

theorem reject_children (term : Data (BinderCore.keys built.rules) [] ())
    (continuation : Comp (BinderCore.keys built.rules) [] () D.Ty)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (children : List (Branch (BinderCore.keys built.rules) [] () D.Ty))
    (shape : ∀ child ∈ children,
      child.frames = gateFrame built D term continuation :: frames ∧ child.pending = pending ∧
      (Solvable child.store → child.focus = .eval (.ret (NormalProbe.marker (fam (BinderCore.keys built.rules))))))
    (world : World (BinderCore.keys built.rules) [] ())
    (rest : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)) :
    ∃ finalWorld dead,
      Runs D (NormalProgram.program built D) supply ⟨world, (children : Multiset _) + rest⟩
        ⟨finalWorld, dead + rest⟩ ∧ ∀ child ∈ dead, ¬ Solvable child.store := by
  classical
  induction children generalizing world rest with
  | nil =>
      refine ⟨world, 0, ?_, ?_⟩
      · exact .refl
      · intro child member
        exact (Multiset.notMem_zero _ member).elim
  | cons child children ih =>
      have later : ∀ next ∈ children,
          next.frames = gateFrame built D term continuation :: frames ∧ next.pending = pending ∧
          (Solvable next.store → next.focus = .eval (.ret (NormalProbe.marker (fam (BinderCore.keys built.rules))))) :=
        fun next member => shape next (List.mem_cons_of_mem _ member)
      obtain ⟨middleWorld, previous, runs, previousDead⟩ := ih later world (child ::ₘ rest)
      have before : Runs D (NormalProgram.program built D) supply
          ⟨world, ((child :: children : List _) : Multiset _) + rest⟩
          ⟨middleWorld, child ::ₘ (previous + rest)⟩ := by
        simpa only [← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons] using runs
      by_cases live : Solvable child.store
      · obtain ⟨knownFrames, knownPending, knownFocus⟩ := shape child List.mem_cons_self
        have focus := knownFocus live
        rcases child with ⟨K, current, actualFrames, actualPending⟩
        dsimp only at knownFrames knownPending focus live
        subst actualFrames actualPending current
        let rejected := boundBranch built D middleWorld.scope K
          (NormalProbe.marker (fam (BinderCore.keys built.rules))) term continuation frames pending
        refine ⟨middleWorld.fresh, rejected ::ₘ previous, ?_, ?_⟩
        · have tail := reject_reply_runs built D supply middleWorld K term continuation frames pending
            (previous + rest) live
          simpa only [Multiset.cons_add] using before.trans tail
        · intro next member
          rcases Multiset.mem_cons.mp member with rfl | kept
          · exact redex_bind_unsolvable built middleWorld.scope K term
          · exact previousDead next kept
      · refine ⟨middleWorld, child ::ₘ previous, ?_, ?_⟩
        · simpa only [Multiset.cons_add] using before
        · intro next member
          rcases Multiset.mem_cons.mp member with rfl | kept
          · exact live
          · exact previousDead next kept

theorem matched_runs_dead (world : World (BinderCore.keys built.rules) [] ())
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (term : Data (BinderCore.keys built.rules) [] ())
    (continuation : Comp (BinderCore.keys built.rules) [] () D.Ty)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (rest : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty))
    (live : Solvable K)
    (enabled : NormalRootMatching.Enabled built D world.scope K (NormalScanner.rootAt term)) :
    ∃ finalWorld dead,
      Runs D (NormalProgram.program built D) supply
        ⟨world, (⟨K, .eval (NormalScanner.rootTest built term continuation), frames, pending⟩ ::ₘ rest)⟩
        ⟨finalWorld, dead + rest⟩ ∧ ∀ child ∈ dead, ¬ Solvable child.store := by
  let entered : Branch (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨K, .eval (.apply (NormalScanner.probeAt term)), gateFrame built D term continuation :: frames, pending⟩
  let children := (NormalProgram.program built D).equations.map
    (callBranch D world.scope K (NormalScanner.probeAt term)
      (gateFrame built D term continuation :: frames) pending)
  have start : SourceLanguage.Step D (NormalProgram.program built D) supply
      ⟨world, (⟨K, .eval (NormalScanner.rootTest built term continuation), frames, pending⟩ ::ₘ rest)⟩
      ⟨world, entered ::ₘ rest⟩ :=
    SourceLanguage.Step.of_eq rfl rfl live (.letStart world K (NormalScanner.site built 1)
      (NormalScanner.probeAt term) (.apply (NormalScanner.probeAt term)) continuation frames pending)
  have applied : SourceLanguage.Step D (NormalProgram.program built D) supply
      ⟨world, entered ::ₘ rest⟩ ⟨world.fresh, (children : Multiset _) + rest⟩ :=
    SourceLanguage.Step.of_eq rfl rfl live (.apply world K (NormalScanner.probeAt term)
      (gateFrame built D term continuation :: frames) pending
      ((NormalProgramIsolation.probe_admission_iff built D world.scope K (NormalScanner.rootAt term)).mpr enabled))
  have replies : ∀ child ∈ children,
      child.frames = gateFrame built D term continuation :: frames ∧ child.pending = pending ∧
      (Solvable child.store → child.focus = .eval (.ret (NormalProbe.marker (fam (BinderCore.keys built.rules))))) := by
    intro child member
    obtain ⟨clause, included, rfl⟩ := List.mem_map.mp member
    exact ⟨rfl, rfl, NormalProgramIsolation.live_callBranch_reply built D world.scope K
      (NormalScanner.rootAt term) (gateFrame built D term continuation :: frames) pending included⟩
  obtain ⟨finalWorld, dead, rejected, allDead⟩ :=
    reject_children built D supply term continuation frames pending children replies world.fresh rest
  exact ⟨finalWorld, dead, ((Relation.ReflTransGen.single start).tail applied).trans rejected, allDead⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeExecution

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeExecution.unmatched_runs
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeExecution.unmatched_fixed_runs
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbeExecution.matched_runs_dead
