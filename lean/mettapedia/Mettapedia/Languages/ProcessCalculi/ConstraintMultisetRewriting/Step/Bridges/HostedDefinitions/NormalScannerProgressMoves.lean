import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerProgressRank

/-!
# Every live child of an actual scanner move has less work

The comparison uses annotations of the existing phase certificates and typed
parent stack. Each source alternative is covered individually. No uniqueness
of certificates or native scope erasure is needed to choose a child rank.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerProgressMoves

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration Hosting
open NativeTypesOnTheStep.Computing
open NormalChildViews (Child Job)
open NormalScannerStack (Stack Fields copiedPattern copiedField copiedChain childFrame)
open NormalScannerCertificates (Certificate rootFrame)
open NormalScannerProgressRank (Score StackScore scanCost chainCost)

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())

abbrev Ranked (outer : Child) (branch : Branch (BinderCore.keys built.rules) [] () D.Ty) (work : Nat) : Prop :=
  ∃ known : Certificate built D outer branch, Score built D known work

variable (supply : Nat → MClosed)

theorem move {outer : Child} {before : Branch (BinderCore.keys built.rules) [] () D.Ty}
    {known : Certificate built D outer before} {work : Nat}
    {world nextWorld : World (BinderCore.keys built.rules) [] ()}
    {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}
    (scored : Score built D known work) (fresh : NormalScannerReflection.FreshCalls built D world.scope before)
    (moved : Move D (NormalProgram.program built D) supply world before nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork,
      Ranked built D outer child childWork ∧ childWork < work := by
  cases scored with
  | @scan K datum current frames input outside work scored =>
      obtain ⟨storeBelow, callBelow⟩ := fresh _ rfl
      intro child member live
      cases moved with
      | apply =>
          obtain ⟨clause, included, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
          have same := NormalScannerCoverage.live_clause built D world.scope _ datum frames [] included live current.2 input
          subst clause
          let ctor := NormalScannerGrounding.kind current.2
          have fields : Fields built (NormalScannerGrounding.matchStore built world.scope K datum ctor)
              current world.scope := by
            intro index used
            exact NormalScannerGrounding.copied_field_determines built world.scope _ datum ctor
              (NormalScannerGrounding.values current.2) (encodeTm current.2)
              (NormalScannerGrounding.encode_instance current.2) input live index used
          have continued := Stack.extend built D outside live
          have continuedScore := StackScore.extend built D scored live
          rw [NormalScannerGrounding.callBranch_shape, NormalScannerGrounding.childTests_eq_chain]
          refine ⟨_, ⟨.start current world.scope frames fields continued,
            .start current world.scope frames fields continued continuedScore⟩, ?_⟩
          have cost := NormalScannerProgressRank.scanCost_eq current.2
          omega
      | unmatched =>
          have noMatch : ∀ clause ∈ (NormalProgram.program built D).equations,
              ¬ Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) world.scope) clause.lhs,
                NormalScanner.scanAt datum)]) := by assumption
          have matched := NormalScannerGrounding.match_live built world.scope _ datum
            (NormalScannerGrounding.kind current.2) (NormalScannerGrounding.values current.2) (encodeTm current.2)
            (NormalScannerGrounding.encode_instance current.2) storeBelow callBelow input
          exact False.elim (noMatch _ (NormalProgramFormation.scanner_mem built D _) matched)
  | start current scope frames fields outside scored =>
      cases moved with
      | letStart =>
          intro child member _
          rw [Multiset.mem_singleton.mp member]
          exact ⟨_, ⟨.probing current scope frames fields outside,
            .probing current scope frames fields outside scored⟩, by omega⟩
  | @probing K current scope frames fields outside work scored =>
      obtain ⟨storeBelow, callBelow⟩ := fresh _ rfl
      intro child member live
      cases moved with
      | apply =>
          obtain ⟨clause, included, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
          have reply := NormalProgramIsolation.live_callBranch_reply built D world.scope K
            (NormalScanner.rootAt (copiedPattern built scope current)) (rootFrame built D scope current :: frames)
            [] included live
          change (callBranch D world.scope K (NormalScanner.probeAt (copiedPattern built scope current))
            (rootFrame built D scope current :: frames) [] clause).focus =
              .eval (.ret (NormalProbe.marker (fam (BinderCore.keys built.rules)))) at reply
          change ∃ childWork, Ranked built D outer
            ⟨_, (callBranch D world.scope K (NormalScanner.probeAt (copiedPattern built scope current))
              (rootFrame built D scope current :: frames) [] clause).focus,
              rootFrame built D scope current :: frames, []⟩ childWork ∧ _
          rw [reply]
          refine ⟨2, ⟨.redexReturning _ (copiedPattern built scope current)
            (copiedChain built D scope (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2))) frames,
            .redexReturning _ _ _ _⟩, ?_⟩
          have positive := NormalScannerProgressRank.chainCost_positive current.2
            (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2))
          omega
      | unmatched =>
          have noMatch : ∀ clause ∈ (NormalProgram.program built D).equations,
              ¬ Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) world.scope) clause.lhs,
                NormalScanner.probeAt (copiedPattern built scope current))]) := by assumption
          rw [Multiset.mem_singleton.mp member] at live ⊢
          have pattern := Fields.pattern built fields live
          have rooted := NormalScannerGrounding.determines_root built pattern
          have disabled : ¬ NormalRootMatching.Enabled built D world.scope K
              (NormalScanner.rootAt (copiedPattern built scope current)) := by
            rintro ⟨clause, probe, matched⟩
            exact noMatch clause ((NormalProgramFormation.equation_mem_iff built D clause).mpr
              (.inr (.inl probe))) matched
          have noRoot := NormalReachableProbes.disabled_refutes_read_redex built D world.scope K
            (NormalScanner.rootAt (copiedPattern built scope current)) storeBelow
            (NormalProbeFreshness.below_unwrapped built callBelow) disabled current.2 (csym NormalScanner.stopTag)
            ((rooted.reads_iff _).mpr rfl)
          exact ⟨_, ⟨.probed current scope frames noRoot fields outside,
            .probed current scope frames noRoot fields outside scored⟩, by omega⟩
  | probed current scope frames root fields outside scored =>
      change Move D (NormalProgram.program built D) supply world
        ⟨_, .value (NormalScanner.probeAt (copiedPattern built scope current)),
          .bindTo (NormalScanner.site built 1) (NormalScanner.probeAt (copiedPattern built scope current))
            (copiedChain built D scope (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2))) ::
              frames, []⟩ nextWorld children at moved
      cases moved with
      | letBind =>
          intro child member live
          rw [Multiset.mem_singleton.mp member] at live ⊢
          have fixed : (copiedChain built D scope
              (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2))).inst
                (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) world.scope) =
              copiedChain built D scope (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2)) :=
            NormalScannerGrounding.open_copied_chain built _ scope world.scope 1 (by decide)
          rw [fixed]
          have fields' := Fields.extend built fields live
          have outside' := Stack.extend built D outside live
          have scored' := StackScore.extend built D scored live
          exact ⟨_, ⟨.chain current scope [] _ frames rfl root (NormalChildViews.jobsNormal_nil built _) fields' outside',
            .chain current scope [] _ frames rfl root (NormalChildViews.jobsNormal_nil built _) fields' outside' scored'⟩,
            by dsimp only [NormalScannerGrounding.childJobs]; omega⟩
  | redexReturning K datum body frames =>
      cases moved with
      | ret =>
          intro child member _
          rw [Multiset.mem_singleton.mp member]
          exact ⟨1, ⟨.redexValue K datum body frames, .redexValue K datum body frames⟩, by omega⟩
  | redexValue K datum body frames =>
      have dead := (NormalProbeExecution.redex_value_move built D supply world K datum body frames [] moved).2
      intro child member live
      exact False.elim (dead child member live)
  | chain current scope checkedJobs jobs frames partition root checked fields outside scored =>
      cases jobs with
      | nil =>
          change Move D (NormalProgram.program built D) supply world
            ⟨_, .eval (.ret (NormalScanner.marker (fam (BinderCore.keys built.rules)))), frames, []⟩
            nextWorld children at moved
          cases moved with
          | ret =>
              intro child member _
              rw [Multiset.mem_singleton.mp member]
              have complete : NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2) = checkedJobs := by
                simpa only [List.append_nil] using partition
              have normal := NormalScannerStack.all_checked_normal built current checkedJobs complete root checked
              exact ⟨_, ⟨.normalValue current frames normal outside,
                .normalValue current frames normal outside scored⟩, by simp only [chainCost]; omega⟩
      | cons job suffix =>
          change Move D (NormalProgram.program built D) supply world
            ⟨_, .eval (.let_ (NormalScanner.site built job.1) (NormalScanner.marker (fam (BinderCore.keys built.rules)))
              (.apply (NormalScanner.scanAt (copiedField built scope job.2)))
              (copiedChain built D scope suffix)), frames, []⟩ nextWorld children at moved
          cases moved with
          | letStart =>
              intro child member _
              rw [Multiset.mem_singleton.mp member]
              have inside : job ∈ NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2) := by
                rw [partition]
                exact List.mem_append_right _ List.mem_cons_self
              obtain ⟨selected, found⟩ := NormalChildViews.child_of_job current.2 job inside
              have valid := NormalScannerGrounding.childJobs_sites (NormalScannerGrounding.kind current.2) job inside
              have input := fields job.2 valid.2
              rw [NormalChildViews.child_value current.2 job.2 selected found] at input
              have continued := Stack.child scope checkedJobs job suffix partition found root checked fields outside
              have continuedScore := StackScore.child scope checkedJobs job suffix partition found root checked fields outside scored
              refine ⟨_, ⟨.scan (copiedField built scope job.2) selected _ input continued,
                .scan (copiedField built scope job.2) selected _ input continued continuedScore⟩, ?_⟩
              have cost := NormalScannerProgressRank.chainCost_cons current.2 job suffix selected found
              omega
  | normalValue current frames normal outside scored =>
      cases scored with
      | done => exact False.elim (Move.value_still moved)
      | @child parent nativeChild parentFrames scope checkedJobs job suffix partition selected root checked fields parentStack work scored =>
          change Move D (NormalProgram.program built D) supply world
            ⟨_, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))),
              .bindTo (NormalScanner.site built job.1) (NormalScanner.marker (fam (BinderCore.keys built.rules)))
                (copiedChain built D scope suffix) :: parentFrames, []⟩ nextWorld children at moved
          cases moved with
          | letBind =>
              intro child member live
              rw [Multiset.mem_singleton.mp member] at live ⊢
              have inside : job ∈ NormalScannerGrounding.childJobs (NormalScannerGrounding.kind parent.2) := by
                rw [partition]
                exact List.mem_append_right _ List.mem_cons_self
              have valid := NormalScannerGrounding.childJobs_sites (NormalScannerGrounding.kind parent.2) job inside
              have fixed : (copiedChain built D scope suffix).inst
                    (openAt (BinderCore.keys built.rules) (NormalScanner.site built job.1) world.scope) =
                  copiedChain built D scope suffix :=
                NormalScannerGrounding.open_copied_chain built suffix scope world.scope job.1 valid.1
              rw [fixed]
              have newPartition : NormalScannerGrounding.childJobs (NormalScannerGrounding.kind parent.2) =
                  (checkedJobs ++ [job]) ++ suffix := by
                simpa only [List.append_assoc, List.singleton_append] using partition
              have checked' := NormalChildViews.advance_prefix built parent.2 checkedJobs job checked
                (NormalScannerStack.job_checked built job selected normal)
              have fields' := Fields.extend built fields live
              have outside' := Stack.extend built D parentStack live
              have scored' := StackScore.extend built D scored live
              exact ⟨_, ⟨.chain parent scope (checkedJobs ++ [job]) suffix parentFrames newPartition root checked' fields' outside',
                .chain parent scope (checkedJobs ++ [job]) suffix parentFrames newPartition root checked' fields' outside' scored'⟩,
                by omega⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerProgressMoves

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerProgressMoves.move
