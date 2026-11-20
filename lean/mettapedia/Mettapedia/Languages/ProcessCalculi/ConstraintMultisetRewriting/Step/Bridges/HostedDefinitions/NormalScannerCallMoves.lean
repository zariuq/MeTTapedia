import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerCertificates
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalReachableProbes

/-!
# Preservation at the scanner's actual source calls

Every live scanner alternative has the native input's constructor and real
field store. Every live probe alternative returns the redex marker. An
unmatched probe earns root normality through the existing fresh-copy law.
Freshness is supplied by the reached source configuration, separately from
the certificate of its typed continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerCallMoves

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration Hosting
open NativeTypesOnTheStep.Computing
open NormalChildViews (Child Job)
open NormalScannerStack (Stack Fields copiedPattern copiedField copiedChain)
open NormalScannerCertificates (Certificate rootFrame)

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)

theorem scan_move {outer current : Child}
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (input : Determines K datum (encodeTm current.2)) (outside : Stack built D outer K frames current)
    {world nextWorld : World (BinderCore.keys built.rules) [] ()}
    {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}
    (storeBelow : StoreBelow world.scope K) (callBelow : DependsBelow world.scope (NormalScanner.scanAt datum))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (.apply (NormalScanner.scanAt datum)), frames, []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D outer child := by
  intro child member live
  cases moved with
  | apply =>
      obtain ⟨clause, included, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
      have same := NormalScannerCoverage.live_clause built D world.scope K datum frames [] included live
        current.2 input
      subst clause
      let ctor := NormalScannerGrounding.kind current.2
      have fields : Fields built (NormalScannerGrounding.matchStore built world.scope K datum ctor)
          current world.scope := by
        intro index used
        exact NormalScannerGrounding.copied_field_determines built world.scope K datum ctor
          (NormalScannerGrounding.values current.2) (encodeTm current.2)
          (NormalScannerGrounding.encode_instance current.2) input live index used
      have continued := NormalScannerStack.Stack.extend built D outside live
      rw [NormalScannerGrounding.callBranch_shape, NormalScannerGrounding.childTests_eq_chain]
      exact .start current world.scope frames fields continued
  | unmatched =>
      have noMatch : ∀ clause ∈ (NormalProgram.program built D).equations,
          ¬ Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) world.scope) clause.lhs,
            NormalScanner.scanAt datum)]) := by assumption
      have liveMatch := NormalScannerGrounding.match_live built world.scope K datum
        (NormalScannerGrounding.kind current.2) (NormalScannerGrounding.values current.2) (encodeTm current.2)
        (NormalScannerGrounding.encode_instance current.2) storeBelow callBelow input
      exact False.elim (noMatch _ (NormalProgramFormation.scanner_mem built D _) liveMatch)

theorem probing_move {outer current : Child}
    (K : List (Constraint (BinderCore.keys built.rules) [] ())) (scope : Nat)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (fields : Fields built K current scope) (outside : Stack built D outer K frames current)
    {world nextWorld : World (BinderCore.keys built.rules) [] ()}
    {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}
    (storeBelow : StoreBelow world.scope K)
    (callBelow : DependsBelow world.scope (NormalScanner.probeAt (copiedPattern built scope current)))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (.apply (NormalScanner.probeAt (copiedPattern built scope current))),
        rootFrame built D scope current :: frames, []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D outer child := by
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
      change Certificate built D outer
        ⟨_, (callBranch D world.scope K (NormalScanner.probeAt (copiedPattern built scope current))
          (rootFrame built D scope current :: frames) [] clause).focus,
          rootFrame built D scope current :: frames, []⟩
      rw [reply]
      exact .redexReturning _ (copiedPattern built scope current)
        (copiedChain built D scope (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2))) frames
  | unmatched =>
      have noMatch : ∀ clause ∈ (NormalProgram.program built D).equations,
          ¬ Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) world.scope) clause.lhs,
            NormalScanner.probeAt (copiedPattern built scope current))]) := by assumption
      rw [Multiset.mem_singleton.mp member] at live ⊢
      have pattern := NormalScannerStack.Fields.pattern built fields live
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
      exact .probed current scope frames noRoot fields outside

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerCallMoves

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerCallMoves.scan_move
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerCallMoves.probing_move
