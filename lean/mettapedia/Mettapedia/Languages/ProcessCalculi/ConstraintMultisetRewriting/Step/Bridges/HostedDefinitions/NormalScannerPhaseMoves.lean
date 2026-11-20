import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerCertificates

/-!
# Non-call source moves preserve scanner certificates

The clauses cover entry to a root gate, both kinds of probe reply, the actual
child sequence, and a normal child's return to its parent. Every live child
of the actual source move is retained. Parent fields and their outer stack
are transported through the bind's real appended constraint store; completing
a child advances the canonical native prefix. Call admission is separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerPhaseMoves

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open NormalChildViews (Child Job)
open NormalScannerStack (Stack Fields copiedPattern copiedField copiedChain childFrame)
open NormalScannerCertificates (Certificate rootFrame)

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)
  {outer : Child} {K : List (Constraint (BinderCore.keys built.rules) [] ())}
  {world nextWorld : World (BinderCore.keys built.rules) [] ()}
  {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}

theorem start_move (current : Child) (copyScope : Nat)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (fields : Fields built K current copyScope) (outside : Stack built D outer K frames current)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (NormalScanner.rootTest built (copiedPattern built copyScope current)
        (copiedChain built D copyScope (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2)))),
        frames, []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D outer child := by
  cases moved with
  | letStart =>
      intro child member _
      rw [Multiset.mem_singleton.mp member]
      exact .probing current copyScope frames fields outside

theorem probed_move (current : Child) (copyScope : Nat)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (root : ¬ NormalRootMatching.Redex built current.2)
    (fields : Fields built K current copyScope) (outside : Stack built D outer K frames current)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .value (NormalScanner.probeAt (copiedPattern built copyScope current)),
        rootFrame built D copyScope current :: frames, []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D outer child := by
  change Move D (NormalProgram.program built D) supply world
    ⟨K, .value (NormalScanner.probeAt (copiedPattern built copyScope current)),
      .bindTo (NormalScanner.site built 1) (NormalScanner.probeAt (copiedPattern built copyScope current))
        (copiedChain built D copyScope (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2))) ::
          frames, []⟩ nextWorld children at moved
  cases moved with
  | letBind =>
      intro child member live
      rw [Multiset.mem_singleton.mp member] at live ⊢
      have fixed :
          (copiedChain built D copyScope
            (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2))).inst
              (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) world.scope) =
            copiedChain built D copyScope
              (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2)) :=
        NormalScannerGrounding.open_copied_chain built _ copyScope world.scope 1 (by decide)
      rw [fixed]
      exact .chain current copyScope [] _ frames rfl root (NormalChildViews.jobsNormal_nil built _)
        (Fields.extend built fields live) (Stack.extend built D outside live)

theorem redexReturning_move (store : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (body : Comp (BinderCore.keys built.rules) [] () D.Ty)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨store, .eval (.ret (NormalProbe.marker (fam (BinderCore.keys built.rules)))),
        NormalProbeExecution.gateFrame built D datum body :: frames, []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D outer child := by
  cases moved with
  | ret =>
      intro child member _
      rw [Multiset.mem_singleton.mp member]
      exact .redexValue store datum body frames

theorem redexValue_move (store : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (body : Comp (BinderCore.keys built.rules) [] () D.Ty)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨store, .value (NormalProbe.marker (fam (BinderCore.keys built.rules))),
        NormalProbeExecution.gateFrame built D datum body :: frames, []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D outer child := by
  have dead := (NormalProbeExecution.redex_value_move built D supply world store datum body frames [] moved).2
  intro child member live
  exact False.elim (dead child member live)

theorem chain_move (current : Child) (copyScope : Nat) (checkedJobs jobs : List Job)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (partition : NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2) = checkedJobs ++ jobs)
    (root : ¬ NormalRootMatching.Redex built current.2)
    (checked : NormalChildViews.JobsNormal built current.2 checkedJobs)
    (fields : Fields built K current copyScope) (outside : Stack built D outer K frames current)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (copiedChain built D copyScope jobs), frames, []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D outer child := by
  cases jobs with
  | nil =>
      change Move D (NormalProgram.program built D) supply world
        ⟨K, .eval (.ret (NormalScanner.marker (fam (BinderCore.keys built.rules)))), frames, []⟩
        nextWorld children at moved
      cases moved with
      | ret =>
          intro child member _
          rw [Multiset.mem_singleton.mp member]
          have complete : NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2) = checkedJobs := by
            simpa only [List.append_nil] using partition
          exact .normalValue current frames
            (NormalScannerStack.all_checked_normal built current checkedJobs complete root checked) outside
  | cons job suffix =>
      change Move D (NormalProgram.program built D) supply world
        ⟨K, .eval (.let_ (NormalScanner.site built job.1) (NormalScanner.marker (fam (BinderCore.keys built.rules)))
          (.apply (NormalScanner.scanAt (copiedField built copyScope job.2)))
          (copiedChain built D copyScope suffix)), frames, []⟩ nextWorld children at moved
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
          exact .scan (copiedField built copyScope job.2) selected _ input
            (.child copyScope checkedJobs job suffix partition found root checked fields outside)

theorem normalValue_move (current : Child)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (normal : NormalStructure.Normal built current.2) (outside : Stack built D outer K frames current)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))), frames, []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D outer child := by
  cases outside with
  | done => exact False.elim (Move.value_still moved)
  | @child parent nativeChild parentFrames copyScope checkedJobs job suffix partition selected root checked fields parentStack =>
      change Move D (NormalProgram.program built D) supply world
        ⟨K, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))),
          .bindTo (NormalScanner.site built job.1) (NormalScanner.marker (fam (BinderCore.keys built.rules)))
            (copiedChain built D copyScope suffix) :: parentFrames, []⟩ nextWorld children at moved
      cases moved with
      | letBind =>
          intro child member live
          rw [Multiset.mem_singleton.mp member] at live ⊢
          have inside : job ∈ NormalScannerGrounding.childJobs (NormalScannerGrounding.kind parent.2) := by
            rw [partition]
            exact List.mem_append_right _ List.mem_cons_self
          have valid := NormalScannerGrounding.childJobs_sites (NormalScannerGrounding.kind parent.2) job inside
          have fixed : (copiedChain built D copyScope suffix).inst
                (openAt (BinderCore.keys built.rules) (NormalScanner.site built job.1) world.scope) =
              copiedChain built D copyScope suffix :=
            NormalScannerGrounding.open_copied_chain built suffix copyScope world.scope job.1 valid.1
          rw [fixed]
          have newPartition : NormalScannerGrounding.childJobs (NormalScannerGrounding.kind parent.2) =
              (checkedJobs ++ [job]) ++ suffix := by
            simpa only [List.append_assoc, List.singleton_append] using partition
          exact .chain parent copyScope (checkedJobs ++ [job]) suffix parentFrames newPartition root
            (NormalChildViews.advance_prefix built parent.2 checkedJobs job checked
              (NormalScannerStack.job_checked built job selected normal))
            (Fields.extend built fields live) (Stack.extend built D parentStack live)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerPhaseMoves

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerPhaseMoves.chain_move
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerPhaseMoves.normalValue_move
