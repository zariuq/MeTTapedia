import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerReflection

/-!
# Finite work annotations for the actual scanner certificates

Annotations index the existing typed parent stack and phase certificates.
They retain native child scopes and actual remaining job lists. These natural
numbers provide well-founded proof evidence; they are not execution costs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerProgressRank

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open NormalChildViews (Child Job)
open NormalScannerStack (Stack Fields copiedPattern copiedField copiedChain childFrame)
open NormalScannerCertificates (Certificate rootFrame)

def scanCost : {n : Nat} → Tower.Tm n → Nat
  | _, .var _ | _, .const _ | _, .head _ => 5
  | _, .pi first second | _, .sigma first second | _, .app first second | _, .pair first second =>
      scanCost first + scanCost second + 9
  | _, .id carrier left right => scanCost carrier + scanCost left + scanCost right + 11
  | _, .lam body | _, .fst body | _, .snd body | _, .refl body => scanCost body + 7

def childCost {n : Nat} (term : Tower.Tm n) (index : Fin 3) : Nat :=
  match NormalChildViews.child term index with
  | some selected => scanCost selected.2
  | none => 0

def chainCost {n : Nat} (term : Tower.Tm n) : List Job → Nat
  | [] => 1
  | job :: jobs => childCost term job.2 + chainCost term jobs + 2

theorem chainCost_positive {n : Nat} (term : Tower.Tm n) (jobs : List Job) :
    0 < chainCost term jobs := by
  cases jobs <;> simp only [chainCost] <;> omega

theorem chainCost_cons {n : Nat} (term : Tower.Tm n) (job : Job) (jobs : List Job) (selected : Child)
    (found : NormalChildViews.child term job.2 = some selected) :
    chainCost term (job :: jobs) = scanCost selected.2 + chainCost term jobs + 2 := by
  simp only [chainCost, childCost, found]

theorem scanCost_eq {n : Nat} (term : Tower.Tm n) :
    scanCost term = 4 + chainCost term (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind term)) := by
  cases term <;>
    simp [scanCost, chainCost, childCost, NormalChildViews.child,
      NormalScannerGrounding.kind, NormalScannerGrounding.childJobs] <;> omega

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())

inductive StackScore {outer : Child} {K : List (Constraint (BinderCore.keys built.rules) [] ())} :
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)} → {current : Child} →
    Stack built D outer K frames current → Nat → Prop
  | done : StackScore (.done : Stack built D outer K [] outer) 0
  | child {parent current : Child} {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
      (scope : Nat) (checkedJobs : List Job) (job : Job) (suffix : List Job)
      (partition : NormalScannerGrounding.childJobs (NormalScannerGrounding.kind parent.2) = checkedJobs ++ job :: suffix)
      (selected : NormalChildViews.child parent.2 job.2 = some current)
      (root : ¬ NormalRootMatching.Redex built parent.2)
      (checked : NormalChildViews.JobsNormal built parent.2 checkedJobs)
      (fields : Fields built K parent scope) (outside : Stack built D outer K frames parent)
      {work : Nat} (scored : StackScore outside work) :
      StackScore (.child scope checkedJobs job suffix partition selected root checked fields outside)
        (1 + chainCost parent.2 suffix + work)

theorem stack_has_score {outer current : Child} {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    (known : Stack built D outer K frames current) : ∃ work, StackScore built D known work := by
  induction known with
  | done => exact ⟨0, .done⟩
  | child scope checkedJobs job suffix partition selected root checked fields outside ih =>
      obtain ⟨work, scored⟩ := ih
      exact ⟨_, .child scope checkedJobs job suffix partition selected root checked fields outside scored⟩

theorem StackScore.extend {outer current : Child}
    {K extra : List (Constraint (BinderCore.keys built.rules) [] ())}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    {known : Stack built D outer K frames current} {work : Nat}
    (scored : StackScore built D known work) (live : Solvable (K ++ extra)) :
    StackScore built D (Stack.extend built D known live) work := by
  induction scored with
  | done => exact .done
  | child scope checkedJobs job suffix partition selected root checked fields outside _ ih =>
      exact .child scope checkedJobs job suffix partition selected root checked
        (Fields.extend built fields live) (Stack.extend built D outside live) ih

inductive Score {outer : Child} : {before : Branch (BinderCore.keys built.rules) [] () D.Ty} →
    Certificate built D outer before → Nat → Prop
  | scan {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (datum : Data (BinderCore.keys built.rules) [] ()) (current : Child)
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (input : Determines K datum (encodeTm current.2)) (outside : Stack built D outer K frames current)
      {work : Nat} (scored : StackScore built D outside work) :
      Score (.scan datum current frames input outside) (scanCost current.2 + work)
  | start {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Child) (scope : Nat) (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (fields : Fields built K current scope) (outside : Stack built D outer K frames current)
      {work : Nat} (scored : StackScore built D outside work) :
      Score (.start current scope frames fields outside)
        (3 + chainCost current.2 (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2)) + work)
  | probing {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Child) (scope : Nat) (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (fields : Fields built K current scope) (outside : Stack built D outer K frames current)
      {work : Nat} (scored : StackScore built D outside work) :
      Score (.probing current scope frames fields outside)
        (2 + chainCost current.2 (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2)) + work)
  | probed {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Child) (scope : Nat) (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (root : ¬ NormalRootMatching.Redex built current.2)
      (fields : Fields built K current scope) (outside : Stack built D outer K frames current)
      {work : Nat} (scored : StackScore built D outside work) :
      Score (.probed current scope frames root fields outside)
        (1 + chainCost current.2 (NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2)) + work)
  | redexReturning (K : List (Constraint (BinderCore.keys built.rules) [] ()))
      (datum : Data (BinderCore.keys built.rules) [] ()) (body : Comp (BinderCore.keys built.rules) [] () D.Ty)
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)) :
      Score (.redexReturning K datum body frames) 2
  | redexValue (K : List (Constraint (BinderCore.keys built.rules) [] ()))
      (datum : Data (BinderCore.keys built.rules) [] ()) (body : Comp (BinderCore.keys built.rules) [] () D.Ty)
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)) :
      Score (.redexValue K datum body frames) 1
  | chain {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Child) (scope : Nat) (checkedJobs jobs : List Job)
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (partition : NormalScannerGrounding.childJobs (NormalScannerGrounding.kind current.2) = checkedJobs ++ jobs)
      (root : ¬ NormalRootMatching.Redex built current.2)
      (checked : NormalChildViews.JobsNormal built current.2 checkedJobs)
      (fields : Fields built K current scope) (outside : Stack built D outer K frames current)
      {work : Nat} (scored : StackScore built D outside work) :
      Score (.chain current scope checkedJobs jobs frames partition root checked fields outside)
        (chainCost current.2 jobs + work)
  | normalValue {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Child) (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (normal : NormalStructure.Normal built current.2) (outside : Stack built D outer K frames current)
      {work : Nat} (scored : StackScore built D outside work) :
      Score (.normalValue current frames normal outside) work

theorem certificate_has_score {outer : Child} {before : Branch (BinderCore.keys built.rules) [] () D.Ty}
    (known : Certificate built D outer before) : ∃ work, Score built D known work := by
  cases known with
  | scan datum current frames input outside =>
      obtain ⟨work, scored⟩ := stack_has_score built D outside
      exact ⟨_, .scan datum current frames input outside scored⟩
  | start current scope frames fields outside =>
      obtain ⟨work, scored⟩ := stack_has_score built D outside
      exact ⟨_, .start current scope frames fields outside scored⟩
  | probing current scope frames fields outside =>
      obtain ⟨work, scored⟩ := stack_has_score built D outside
      exact ⟨_, .probing current scope frames fields outside scored⟩
  | probed current scope frames root fields outside =>
      obtain ⟨work, scored⟩ := stack_has_score built D outside
      exact ⟨_, .probed current scope frames root fields outside scored⟩
  | redexReturning K datum body frames => exact ⟨2, .redexReturning K datum body frames⟩
  | redexValue K datum body frames => exact ⟨1, .redexValue K datum body frames⟩
  | chain current scope checkedJobs jobs frames partition root checked fields outside =>
      obtain ⟨work, scored⟩ := stack_has_score built D outside
      exact ⟨_, .chain current scope checkedJobs jobs frames partition root checked fields outside scored⟩
  | normalValue current frames normal outside =>
      obtain ⟨work, scored⟩ := stack_has_score built D outside
      exact ⟨work, .normalValue current frames normal outside scored⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerProgressRank

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerProgressRank.certificate_has_score
