import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Actual argument packets from independently delivered operands

Each operand's entry action and annotated read are checked separately. The
existing source argument rules then construct one complete packet, with the
same frame and world, at every live scope. Literal Empty or Error data is not
a newly raised result: the source's stopped predicate also checks change.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.DeliveredArgumentPackets

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed

theorem delivered_exact {Context World : Type} {environment : WorldEnvironment Context World} {policy : Policy}
    {label : Context} {world finalWorld : World} {live scope value expected frame results}
    (entered : Entry.Rel policy.reentry (frame.read policy value).status (frame.read policy value).erase expected .deliver)
    (source : Stateful.AtomRel environment label world live scope value expected frame results finalWorld (policy := policy)) :
    results = [(frame.read policy value, frame)] ∧ finalWorld = world := by
  cases source
  all_goals first
    | exact ⟨rfl, rfl⟩
    | have impossible : (Entry.Action.deliver) = .cast := Entry.functional entered (by assumption)
      cases impossible
    | have impossible : (Entry.Action.deliver) = .interpret := Entry.functional entered (by assumption)
      cases impossible

theorem source {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
    (label : Context) (world : World) (scope : List String) (frame : Frame) (requests : List ArgumentRequest)
    (fixed : ∀ request ∈ requests, frame.read policy request.1 = request.1)
    (entered : ∀ request ∈ requests, Entry.Rel policy.reentry request.1.status request.1.erase request.2 .deliver)
    (live : List Atom) :
    Stateful.ArgumentsRel environment label world live scope requests frame
      [(Entry.Value.argumentPacket (requests.map Prod.fst), frame)] world (policy := policy) := by
  induction requests generalizing live with
  | nil => exact .nil
  | cons request requests ih =>
    have held : Stateful.AtomRel environment label world (argumentScope requests ++ live) scope request.1 request.2 frame
        [(request.1, frame)] world (policy := policy) := by
      simpa only [fixed request List.mem_cons_self] using
        (Stateful.AtomRel.delivered (environment := environment) (policy := policy) (label := label) (world0 := world)
          (live := argumentScope requests ++ live) (scope := scope) (value := request.1) (frame := frame)
          (by simpa only [fixed request List.mem_cons_self] using entered request List.mem_cons_self))
    apply Stateful.ArgumentsRel.cons held
    have remaining := ih (fun value member => fixed value (List.mem_cons_of_mem _ member))
      (fun value member => entered value (List.mem_cons_of_mem _ member)) (request.1.erase :: live)
    simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using
      (Stateful.ArgumentBranchesRel.continuing (head := (request.1, frame))
        (by simp [ArgumentStopped]) remaining Stateful.ArgumentBranchesRel.nil)

end Mettapedia.Languages.MeTTa.HE.DeliveredArgumentPackets
