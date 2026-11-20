import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerStack
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProbeExecution

/-!
# Pointwise source certificates for scanner reflection

Certificates retain each actual scanner phase and its typed continuation.
Redex replies are distinguished from successful marker returns. An empty
certified stack identifies the original native goal, rather than any marker
in an unrelated branch. Preservation under source moves is a separate lemma.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerCertificates

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open NormalChildViews (Child Job)
open NormalScannerStack (Stack Fields copiedPattern copiedField copiedChain childFrame)

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())

def rootFrame (scope : Nat) (term : Child) : Frame (BinderCore.keys built.rules) [] () D.Ty :=
  NormalProbeExecution.gateFrame built D (copiedPattern built scope term)
    (copiedChain built D scope (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind term.2)))

inductive Certificate (outer : Child) : Branch (BinderCore.keys built.rules) [] () D.Ty → Prop
  | scan {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (datum : Data (BinderCore.keys built.rules) [] ()) (current : Child)
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (input : Determines K datum (encodeTm current.2)) (outside : Stack built D outer K frames current) :
      Certificate outer ⟨K, .eval (.apply (NormalScanner.scanAt datum)), frames, []⟩
  | start {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Child) (scope : Nat) (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (fields : Fields built K current scope) (outside : Stack built D outer K frames current) :
      Certificate outer ⟨K,
        .eval (NormalScanner.rootTest built (copiedPattern built scope current)
          (copiedChain built D scope (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2)))),
        frames, []⟩
  | probing {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Child) (scope : Nat) (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (fields : Fields built K current scope) (outside : Stack built D outer K frames current) :
      Certificate outer ⟨K, .eval (.apply (NormalScanner.probeAt (copiedPattern built scope current))),
        rootFrame built D scope current :: frames, []⟩
  | probed {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Child) (scope : Nat) (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (root : ¬ NormalRootMatching.Redex built current.2)
      (fields : Fields built K current scope) (outside : Stack built D outer K frames current) :
      Certificate outer ⟨K, .value (NormalScanner.probeAt (copiedPattern built scope current)),
        rootFrame built D scope current :: frames, []⟩
  | redexReturning (K : List (Constraint (BinderCore.keys built.rules) [] ()))
      (datum : Data (BinderCore.keys built.rules) [] ())
      (body : Comp (BinderCore.keys built.rules) [] () D.Ty)
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)) :
      Certificate outer ⟨K, .eval (.ret (NormalProbe.marker (fam (BinderCore.keys built.rules)))),
        NormalProbeExecution.gateFrame built D datum body :: frames, []⟩
  | redexValue (K : List (Constraint (BinderCore.keys built.rules) [] ()))
      (datum : Data (BinderCore.keys built.rules) [] ())
      (body : Comp (BinderCore.keys built.rules) [] () D.Ty)
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)) :
      Certificate outer ⟨K, .value (NormalProbe.marker (fam (BinderCore.keys built.rules))),
        NormalProbeExecution.gateFrame built D datum body :: frames, []⟩
  | chain {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Child) (scope : Nat) (checkedJobs jobs : List Job)
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (partition : NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2) = checkedJobs ++ jobs)
      (root : ¬ NormalRootMatching.Redex built current.2)
      (checked : NormalChildViews.JobsNormal built current.2 checkedJobs)
      (fields : Fields built K current scope) (outside : Stack built D outer K frames current) :
      Certificate outer ⟨K, .eval (copiedChain built D scope jobs), frames, []⟩
  | normalValue {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Child) (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (normal : NormalStructure.Normal built current.2) (outside : Stack built D outer K frames current) :
      Certificate outer ⟨K, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))), frames, []⟩

theorem initial {n : Nat} (term : Tower.Tm n) :
    Certificate built D ⟨n, term⟩
      (⟨[], .eval (NormalScanner.query built (encodeTm term)), [], []⟩ :
        Branch (BinderCore.keys built.rules) [] () D.Ty) := by
  refine .scan _ ⟨n, term⟩ [] ?_ .done
  refine ⟨Hosting.initial_live, ?_⟩
  intro X target assignment _
  exact Rigid.instantiate_include assignment _

theorem finished_normal {outer : Child} {branch : Branch (BinderCore.keys built.rules) [] () D.Ty}
    (known : Certificate built D outer branch) (finished : branch.Finished (D := D)) :
    NormalStructure.Normal built outer.2 := by
  cases known with
  | scan | start | probing | chain =>
      obtain ⟨_, term, focus⟩ := finished
      cases focus
  | probed | redexReturning | redexValue => cases finished.1
  | normalValue current frames normal outside =>
      have empty : frames = [] := finished.1
      subst frames
      have same := NormalScannerStack.Stack.empty built D outside
      cases same
      exact normal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerCertificates

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerCertificates.initial
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerCertificates.finished_normal
