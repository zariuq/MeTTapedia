import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorDriverReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerEmbedded
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorPublic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorStore

/-!
# Pointwise certificates for the actual normal-profile public evaluator

Original-row episodes retain one directed source boundary. Scanner work is
the already certified scanner beneath the actual marker and public frames.
Held done replies and the public payload return have separate phases.
Preservation under every source move is proved in the following modules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorCertificates

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())

abbrev Reaches (first last : Tower.Tm 0) : Prop :=
  StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) first last

def publicFrame : Frame (BinderCore.keys built.rules) [] () D.Ty :=
  PublicQuery.frame RuntimeSubstitution.rules built.authored

def payload (scope : Nat) : Data (BinderCore.keys built.rules) [] () :=
  NormalScannerStack.copiedField built scope 0

def markerFrame (scope : Nat) : Frame (BinderCore.keys built.rules) [] () D.Ty :=
  .bindTo (NormalScanner.site built 1) (NormalScanner.marker (fam (BinderCore.keys built.rules)))
    (.ret (NormalProgram.doneAt (payload built scope)))

def scanBody (scope : Nat) : Comp (BinderCore.keys built.rules) [] () D.Ty :=
  .let_ (NormalScanner.site built 1) (NormalScanner.marker (fam (BinderCore.keys built.rules)))
    (.apply (NormalScanner.scanAt (payload built scope))) (.ret (NormalProgram.doneAt (payload built scope)))

def envelop (scope : Nat) (inside : Branch (BinderCore.keys built.rules) [] () D.Ty) :
    Branch (BinderCore.keys built.rules) [] () D.Ty :=
  ContinuationLift.branch (publicFrame built D) (ContinuationLift.branch (markerFrame built D scope) inside)

def CorrectOutput (initial : Tower.Tm 0) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) : Prop :=
  ∀ value, Reads K datum value → ∃ normal : Tower.Tm 0,
    value = encodeTm normal ∧ Reaches built initial normal ∧ NormalStructure.Normal built normal

inductive Certificate (initial : Tower.Tm 0) : Branch (BinderCore.keys built.rules) [] () D.Ty → Prop
  | initial : Certificate initial ⟨[], .eval (NormalProgram.query built initial), [], []⟩
  | evaluating {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Tower.Tm 0) (call : Data (BinderCore.keys built.rules) [] ())
      (reached : Reaches built initial current)
      (input : Determines K call (NormalEvaluatorGrounding.callCode .evaluate (encodeTm current))) :
      Certificate initial ⟨K, .eval (.apply call), [publicFrame built D], []⟩
  | choosing {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Tower.Tm 0) (scope : Nat) (reached : Reaches built initial current)
      (input : Determines K (payload built scope) (encodeTm current)) :
      Certificate initial ⟨K, .eval (NormalEvaluatorGrounding.bodyAt built .evaluate (payload built scope)),
        [publicFrame built D], []⟩
  | startingScan {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Tower.Tm 0) (scope : Nat) (reached : Reaches built initial current)
      (input : Determines K (payload built scope) (encodeTm current)) :
      Certificate initial ⟨K, .eval (scanBody built D scope), [publicFrame built D], []⟩
  | machine {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (before : Tower.Tm 0) (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
      (reached : Reaches built initial before) (episode : NormalEvaluatorMachineView.Episode built before code)
      (input : Determines K call code) :
      Certificate initial ⟨K, .eval (.apply call), [publicFrame built D], []⟩
  | machineValue {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
      (head : closedHead code = some activeTag) (input : Determines K call code) :
      Certificate initial ⟨K, .value call, [publicFrame built D], []⟩
  | scanning (current : Tower.Tm 0) (scope : Nat)
      (inside : Branch (BinderCore.keys built.rules) [] () D.Ty)
      (reached : Reaches built initial current)
      (input : Determines inside.store (payload built scope) (encodeTm current))
      (scanner : NormalScannerCertificates.Certificate built D ⟨0, current⟩ inside) :
      Certificate initial (envelop built D scope inside)
  | returningDone {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Tower.Tm 0) (datum : Data (BinderCore.keys built.rules) [] ())
      (reached : Reaches built initial current) (normal : NormalStructure.Normal built current)
      (input : Determines K datum (encodeTm current)) :
      Certificate initial ⟨K, .eval (.ret (NormalProgram.doneAt datum)), [publicFrame built D], []⟩
  | repliedDone {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Tower.Tm 0) (datum : Data (BinderCore.keys built.rules) [] ())
      (reached : Reaches built initial current) (normal : NormalStructure.Normal built current)
      (input : Determines K datum (encodeTm current)) :
      Certificate initial ⟨K, .value (NormalProgram.doneAt datum), [publicFrame built D], []⟩
  | returning {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (datum : Data (BinderCore.keys built.rules) [] ()) (correct : CorrectOutput built initial K datum) :
      Certificate initial ⟨K, .eval (.ret datum), [], []⟩
  | finished {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (datum : Data (BinderCore.keys built.rules) [] ()) (correct : CorrectOutput built initial K datum) :
      Certificate initial ⟨K, .value datum, [], []⟩

theorem determines_done {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()} {value : MClosed}
    (known : Determines K datum value) : Determines K (NormalProgram.doneAt datum) (doneC value) := by
  refine ⟨known.1, ?_⟩
  intro X target assignment solved
  simp only [NormalProgram.doneAt, NormalScanner.instantiate_nodeAt, List.map_cons, List.map_nil,
    known.2 target assignment solved]
  exact (NormalScanner.include_nodeAt target doneTag [value]).symm

theorem finished_read {initial : Tower.Tm 0} {branch : Branch (BinderCore.keys built.rules) [] () D.Ty}
    (known : Certificate built D initial branch) (finished : branch.Finished (D := D))
    {value : MClosed} (read : value ∈ branch.answer (D := D)) :
    ∃ normal : Tower.Tm 0,
      value = encodeTm normal ∧ Reaches built initial normal ∧ NormalStructure.Normal built normal := by
  cases known with
  | initial | evaluating | choosing | startingScan | machine | returningDone | returning =>
      obtain ⟨_, focus, _⟩ := read
      cases focus
  | machineValue | repliedDone => cases finished.1
  | scanning current scope inside reached input scanner =>
      have nonempty : (envelop built D scope inside).frames ≠ [] := by
        simp [envelop, ContinuationLift.branch]
      exact False.elim (nonempty finished.1)
  | finished datum correct =>
      obtain ⟨actual, focus, observed⟩ := read
      have same : datum = actual := Focus.value.inj focus
      subst actual
      exact correct value observed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorCertificates

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorCertificates.finished_read
