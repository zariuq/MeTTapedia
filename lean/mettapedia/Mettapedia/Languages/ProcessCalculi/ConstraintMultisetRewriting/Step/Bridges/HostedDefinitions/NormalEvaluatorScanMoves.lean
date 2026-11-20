import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorCertificates

/-!
# Scanner reflection inside the actual evaluator and public bind

Running inner scanner moves retain both enclosing frames. A finished inner
marker certifies the very native term whose payload the evaluator holds;
the real marker bind then produces the held done reply. Constraint growth
preserves that payload through every generated live branch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorScanMoves

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration Hosting
open NativeTypesOnTheStep.Computing
open NormalEvaluatorCertificates (Certificate Reaches publicFrame markerFrame payload envelop)

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)

theorem scanner_finished_shape {outer : NormalChildViews.Child}
    {inside : Branch (BinderCore.keys built.rules) [] () D.Ty}
    (known : NormalScannerCertificates.Certificate built D outer inside)
    (finished : inside.Finished (D := D)) :
    inside = ⟨inside.store, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))), [], []⟩ := by
  cases known with
  | scan | start | probing | chain =>
      obtain ⟨_, value, focus⟩ := finished
      cases focus
  | probed | redexReturning | redexValue => cases finished.1
  | normalValue current frames normal outside =>
      have empty : frames = [] := finished.1
      subst frames
      rfl

theorem scanning_move {initial : Tower.Tm 0} (current : Tower.Tm 0) (scope : Nat)
    (inside : Branch (BinderCore.keys built.rules) [] () D.Ty)
    (reached : Reaches built initial current)
    (input : Determines inside.store (payload built scope) (encodeTm current))
    (scanner : NormalScannerCertificates.Certificate built D ⟨0, current⟩ inside)
    {world nextWorld : World (BinderCore.keys built.rules) [] ()}
    {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}
    (arrow : ArrowBranch (envelop built D scope inside))
    (fresh : NormalScannerReflection.FreshCalls built D world.scope (envelop built D scope inside))
    (moved : Move D (NormalProgram.program built D) supply world (envelop built D scope inside) nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child := by
  by_cases finished : inside.Finished (D := D)
  · have shape := scanner_finished_shape built D scanner finished
    have normal := NormalScannerCertificates.finished_normal built D scanner finished
    have actual : Move D (NormalProgram.program built D) supply world
        ⟨inside.store, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))),
          [markerFrame built D scope, publicFrame built D], []⟩ nextWorld children := by
      have shaped := moved
      rw [shape] at shaped
      simpa only [envelop, ContinuationLift.branch, List.nil_append, List.singleton_append] using shaped
    cases actual with
    | letBind =>
        intro child member live
        have output := NormalEvaluatorStore.determines_child D (NormalProgram.program built D) supply moved
          input member live
        rw [Multiset.mem_singleton.mp member] at output ⊢
        have fixed : instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) world.scope)
            (payload built scope) = payload built scope :=
          NormalScannerGrounding.open_copied_datum built scope world.scope 1 (by decide) 0
        simp only [Comp.inst, Comp.mapData, NormalProgram.doneAt,
          NormalScanner.instantiate_nodeAt, List.map_cons, List.map_nil, fixed]
        exact .returningDone current (payload built scope) reached normal output
  · let middle := ContinuationLift.branch (markerFrame built D scope) inside
    have middleArrow : ArrowBranch middle :=
      NormalScannerEmbedded.arrow_inner built D (publicFrame built D) middle arrow
    have running : ¬ middle.Finished (D := D) := by
      intro done
      have empty := done.1
      simp [middle, ContinuationLift.branch] at empty
    obtain ⟨middleChildren, innerMove, same⟩ := NormalFrameReflection.move D (NormalProgram.program built D)
      supply (publicFrame built D) middleArrow running moved
    intro child member live
    have output := NormalEvaluatorStore.determines_child D (NormalProgram.program built D) supply moved
      input member live
    rw [same] at member
    obtain ⟨mid, included, rfl⟩ := Multiset.mem_map.mp member
    obtain ⟨newInside, sameMiddle, known⟩ := NormalScannerEmbedded.move built D supply
      (markerFrame built D scope) scanner middleArrow finished fresh innerMove mid included live
    subst mid
    exact .scanning current scope newInside reached output known

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorScanMoves

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorScanMoves.scanning_move
