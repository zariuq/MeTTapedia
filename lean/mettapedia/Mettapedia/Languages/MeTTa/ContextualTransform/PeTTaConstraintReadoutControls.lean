import Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintReadout
import Mettapedia.Languages.MeTTa.PeTTa.StreamingAnswerTransport
import Lean.Elab.Tactic.Cbv

/-!
# Different actual representatives, one shared observation

The source solves x=y in one orientation; the runtime solves the equivalent
y=x in the other. Their actual readouts differ, while the general MGU bridge
proves equality of joint observations. Caller controls retain both the inverse
basis and branch bindings instead of executing displayed labels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstraintReadoutControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS
open UnifyingConstraintPresentation
open OutputPlan.ConstraintAdmission

def x : Atom := .var "x"
def y : Atom := .var "y"
def z : Atom := .var "z"
def a : Atom := .symbol "a"
def constraints : Destination.Equations := [(x,y)]
def reversed : Subst := [("y",x)]
def sourceModel : Destination.Environment := Mettapedia.Logic.LP.Subst.single "x" (.var "y")

theorem actual_source_orientation : Destination.resolve constraints = some sourceModel := by
  simp [Destination.resolve,Destination.equations,Destination.encode,constraints,x,y,sourceModel,
    Mettapedia.Logic.LP.unifyTotal,Mettapedia.Logic.LP.Subst.applyEqs]
  exact Mettapedia.Logic.LP.Subst.comp_id_left _

theorem reversed_represents_same_equation : Represents constraints reversed := by
  intro model
  change Destination.Solves model [(x,y)] ↔ Destination.Solves model [(y,x)]
  simp only [Destination.Solves,List.mem_singleton,forall_eq]
  exact eq_comm

theorem reversed_is_idempotent : Unifying.Idempotent reversed := by
  have computed : Unifying.unify [] y x = .ok reversed := by decide +kernel
  exact (Unifying.unifyTerms_sound (Unifying.fuelFor [] y x) [] reversed y x
    (by simp [Unifying.Idempotent,Subst.lookup]) computed).1

theorem actual_representatives_differ : Destination.read sourceModel x ≠ Unifying.resolve reversed x := by
  simp [Destination.read,Destination.encode,Destination.decode,sourceModel,x,reversed,
    Mettapedia.Logic.LP.Subst.single,Unifying.resolve,Mettapedia.Languages.ProcessCalculi.MORK.applySubst,Subst.lookup]

theorem actual_joint_observations_agree (observations : List Atom) :
    Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout.joint (observations.map (Destination.read sourceModel)) =
      Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout.joint (observations.map (Unifying.resolve reversed)) :=
  source_runtime_joint_readout constraints reversed sourceModel reversed_represents_same_equation
    reversed_is_idempotent actual_source_orientation observations

def program : SpaceSemantics.Program := {equations := [],declarations := []}
def base : Streaming.State := {world := {state := Effects.empty},agenda := []}
def caller (body : Atom) : List Streaming.Frame := [.source (.bind (OutputPlan.hold (.var "result")) body)]
def answer : Unifying.Answer := ⟨x,[("x",a)]⟩

def returnedValues (answers : List Unifying.Answer) (body : Atom) : Option (List Atom) :=
  match Streaming.run program 40
      {base with agenda := [.execute ⟨.returned answers,caller body⟩]} with
  | .complete state => some (Streaming.values state)
  | _ => none

def displayedOnly : List Unifying.Answer :=
  let packet := AnswerReadout.packAnswers [answer]
  List.zipWith (fun value bindings => ⟨value,bindings⟩) packet.payload.values packet.bindings

theorem displayed_labels_cannot_replace_the_inverse :
    returnedValues [answer] (.var "result") = some [a] ∧
      returnedValues displayedOnly (.var "result") = some [.var "0"] := by
  constructor <;> decide +kernel

theorem dropping_branch_bindings_changes_the_caller :
    returnedValues [⟨Effects.boolean true,[("x",a)]⟩] x = some [a] ∧
      returnedValues [⟨Effects.boolean true,[]⟩] x = some [x] := by
  constructor <;> decide +kernel

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstraintReadoutControls
