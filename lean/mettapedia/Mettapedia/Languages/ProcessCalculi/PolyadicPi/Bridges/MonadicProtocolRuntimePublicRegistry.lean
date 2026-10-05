import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimePublicUpdate
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRetirement

/-!
# Source communication and debt at a selected public commitment

The original offered owner and original idle position are selected in the
actual source term. A binary communication replaces that offered output by
its opened guard; the selected persistent source listener remains present.
All other owner and idle occurrences are retained. The same occurrence gains
exactly three pending private communications.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicRegistry

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors ScopedActiveFrontier
open RuntimePublicationArrangement RuntimePublicUpdate

private theorem exchange {Γ : Ctx sig} (a b c : Proc Γ) :
    StructuralEq (par a (par b c)) (par b (par a c)) :=
  (StructuralEq.parAssoc _ _ _).symm.trans
    ((StructuralEq.par (.parComm _ _) (.refl _)).trans (.parAssoc _ _ _))

private theorem shuffle {Γ : Ctx sig} (a b c d : Proc Γ) :
    StructuralEq (par (par a b) (par c d)) (par a (par c (par b d))) :=
  (StructuralEq.parAssoc _ _ _).trans (.par (.refl _) (exchange _ _ _))

def sourceRest {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n)
    (frame : List (Proc Γ)) (input : Fin frame.length) : Proc Γ :=
  par (parallel (((List.finRange n).erase owner).map (fun other => (registry other).source)))
    (parallel (otherFrame frame input))

theorem source_before {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel first second : Name Γ)
    (offered : registry owner = .offered channel first second)
    (frame : List (Proc Γ)) (input : Fin frame.length) :
    StructuralEq (registrySource registry (parallel frame))
      (par (out2 channel first second) (par frame[input.val] (sourceRest registry owner frame input))) := by
  have slots := parallel_perm ((List.perm_cons_erase (List.mem_finRange owner)).map
    (fun other => (registry other).source))
  have framed := parallel_perm ((List.perm_cons_erase (List.mem_finRange input)).map
    (fun position => frame[position.val]))
  have indexed := RuntimeIdleUpdate.indexed_parallel frame id
  change parallel ((List.finRange frame.length).map (fun position => frame[position.val])) =
    parallel (frame.map id) at indexed
  rw [indexed, List.map_id] at framed
  simp only [List.map_cons, parallel, offered, Slot.source] at slots framed
  exact (StructuralEq.par slots framed).trans (shuffle _ _ _ _)

private theorem other_sources {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (call : Call Γ) :
    (((List.finRange n).erase owner).map (fun other => (commit registry owner call other).source)) =
      (((List.finRange n).erase owner).map (fun other => (registry other).source)) := by
  apply List.map_congr_left
  intro other member
  have different := ((List.nodup_finRange n).mem_erase_iff.mp member).1
  rw [commit, Function.update_of_ne different]

theorem source_after {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (call : Call Γ) (frame : List (Proc Γ)) (input : Fin frame.length)
    (persistent : Bool) :
    StructuralEq (registrySource (commit registry owner call) (parallel (updatedFrame persistent frame input)))
      (par (readback call)
        (if persistent then par frame[input.val] (sourceRest registry owner frame input)
         else sourceRest registry owner frame input)) := by
  have slots := parallel_perm ((List.perm_cons_erase (List.mem_finRange owner)).map
    (fun other => (commit registry owner call other).source))
  simp only [List.map_cons, parallel] at slots
  have chosen : commit registry owner call owner = .pending .callback call := Function.update_self _ _ _
  rw [chosen, Slot.source, other_sources] at slots
  cases persistent with
  | false => exact (StructuralEq.par slots (.refl _)).trans (.parAssoc _ _ _)
  | true =>
      change StructuralEq (par _ (par frame[input.val] (parallel (otherFrame frame input)))) _
      exact (StructuralEq.par slots (.refl _)).trans (shuffle _ _ _ _)

theorem primitive_commit {Γ : Ctx sig} (persistent : Bool) (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) (frame : Proc Γ) :
    StepModulo (par (out2 channel first second) (par (binaryReceiver persistent channel body) frame))
      (par (openPair body first second)
        (if persistent then par (rep (inp2 channel body)) frame else frame)) := by
  cases persistent with
  | false =>
      exact ⟨par (par (out2 channel first second) (inp2 channel body)) frame,
        par (openPair body first second) frame, (StructuralEq.parAssoc _ _ _).symm,
        .parL _ (.comm2 _ _ _ _), .refl _⟩
  | true =>
      refine ⟨par (par (out2 channel first second) (inp2 channel body))
          (par (rep (inp2 channel body)) frame),
        par (openPair body first second) (par (rep (inp2 channel body)) frame),
        ?_, .parL _ (.comm2 _ _ _ _), .refl _⟩
      exact (StructuralEq.par (.refl _) (.par (.repUnfold _) (.refl _))).trans
        ((StructuralEq.par (.refl _) (.parAssoc _ _ _)).trans (StructuralEq.parAssoc _ _ _).symm)

theorem source_commit {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel : Name Γ) (call : Call Γ)
    (offered : registry owner = .offered channel call.first call.second)
    (frame : List (Proc Γ)) (input : Fin frame.length) (persistent : Bool)
    (original : frame[input.val] = binaryReceiver persistent channel call.body) :
    StepModulo (registrySource registry (parallel frame))
      (registrySource (commit registry owner call) (parallel (updatedFrame persistent frame input))) := by
  have before := source_before registry owner channel call.first call.second offered frame input
  rw [original] at before
  have after := source_after registry owner call frame input persistent
  rw [original] at after
  have resulting : StructuralEq
      (par (openPair call.body call.first call.second)
        (if persistent then par (rep (inp2 channel call.body)) (sourceRest registry owner frame input)
         else sourceRest registry owner frame input))
      (registrySource (commit registry owner call) (parallel (updatedFrame persistent frame input))) := by
    cases persistent <;> exact after.symm
  exact modulo_target_equation (modulo_source_equation before
    (primitive_commit persistent channel call.first call.second call.body
      (sourceRest registry owner frame input))) resulting

theorem public_debt {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel : Name Γ) (call : Call Γ)
    (offered : registry owner = .offered channel call.first call.second) :
    registryRemaining (commit registry owner call) = registryRemaining registry + 3 := by
  let owners := (List.finRange n).erase owner
  have old := ((List.perm_cons_erase (List.mem_finRange owner)).map
    (fun other => (registry other).remaining)).sum_eq
  have next := ((List.perm_cons_erase (List.mem_finRange owner)).map
    (fun other => (commit registry owner call other).remaining)).sum_eq
  have retained : owners.map (fun other => (commit registry owner call other).remaining) =
      owners.map (fun other => (registry other).remaining) := by
    apply List.map_congr_left
    intro other member
    have different := ((List.nodup_finRange n).mem_erase_iff.mp member).1
    rw [commit, Function.update_of_ne different]
  unfold registryRemaining
  rw [next, old]
  simp only [List.map_cons, List.sum_cons]
  rw [retained]
  simp only [commit, Function.update_self, offered, Slot.remaining, Phase.remaining]
  dsimp only [owners]
  omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicRegistry
