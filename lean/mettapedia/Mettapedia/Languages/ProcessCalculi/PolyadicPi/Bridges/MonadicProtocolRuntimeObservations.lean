import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeWitness
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.ActiveObservationSubjects

/-!
# Public listeners in the mixed tuple runtime

Every public unary listener in a supplied runtime representative comes from
an original source listener, of unary or binary arity. Offered callback waiters
and committed field listeners have private subjects. The two enclosing name
telescopes and all static endpoint equations preserve this observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeObservations

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors RuntimeWitness ScopedActiveFrontier
open ActiveObservation ActiveMarkedNames

universe u

theorem coherent_header_rename {Key : Type u} {Γ Δ : Ctx sig}
    (kind : ActiveHeaderInvariant.Header) (subject fresh : Key) (reindex : Ren sig Γ Δ)
    (sourceKeys : Environment Key Γ) (targetKeys : Environment Key Δ)
    (consistent : ∀ name, targetKeys (reindex .nm name) = sourceKeys name) (process : Proc Γ) :
    HasHeader kind subject fresh targetKeys (rename reindex process) ↔
      HasHeader kind subject fresh sourceKeys process := by
  unfold HasHeader
  rw [← fitted_observe ((ActiveSyntaxMarking.mark_fits () process).rename reindex) fresh]
  rw [observe_rename (fun _ : Unit => fresh) reindex process
    (ActiveSyntaxMarking.mark () process) sourceKeys targetKeys consistent]
  rfl

theorem reindexed_public_header_iff {Γ Δ : Ctx sig} (reindex : Ren sig Γ Δ)
    (faithful : Function.Injective (reindex .nm)) (kind : ActiveHeaderInvariant.Header)
    (channel : Var Γ .nm) (process : Proc Γ) :
    PublicHeader kind (reindex .nm channel) (rename reindex process) ↔
      PublicHeader kind channel process := by
  unfold PublicHeader
  rw [coherent_header_rename kind (Var.succ (reindex .nm channel)) Var.zero reindex
    (fun name => Var.succ (reindex .nm name)) (fun name => Var.succ name) (fun _ => rfl)]
  apply hasHeader_subject_compare
  · constructor <;> intro impossible <;> cases impossible
  · intro name
    simp only [Var.succ.injEq]
    exact ⟨fun same => faithful same, congrArg (reindex .nm)⟩

theorem actor_has_no_public_input {Γ : Ctx sig} {n : Nat}
    (channel : Var Γ .nm) (actor : Actor n Γ) :
    ¬ PublicHeader .input1 (ambient n .nm channel) actor.render := by
  cases actor with
  | publication owner subject =>
      simp only [Actor.render, PublicHeader, hasHeader_out1, reduceCtorEq, false_and, not_false_eq_true]
  | waiter owner first second =>
      simp only [Actor.render, input_header, PublicHeader, hasHeader_inp1,
        keyName, nameKey, true_and, Var.succ.injEq]
      exact fun equal => key_ne_ambient n owner .session channel equal.symm
  | output owner kind call =>
      simp only [Actor.render, output_header, PublicHeader, hasHeader_out1,
        reduceCtorEq, false_and, not_false_eq_true]
  | input owner kind call =>
      simp only [Actor.render, input_header, PublicHeader, hasHeader_inp1,
        keyName, nameKey, true_and, Var.succ.injEq]
      exact fun equal => key_ne_ambient n owner kind.port channel equal.symm

theorem assembly_input_from_frame {Γ : Ctx sig} {n : Nat}
    (registry : Fin n → Slot Γ) (frame : Proc Γ) (channel : Var Γ .nm)
    (observed : PublicHeader .input1 (ambient n .nm channel) (assembly registry frame)) :
    PublicHeader .input1 channel (lower frame) := by
  change HasHeader .input1 _ _ _ (par _ _) at observed
  rcases (hasHeader_par _ _ _ _ _ _).mp observed with actor | framed
  · change PublicHeader .input1 _ (parallel ((entries registry).map Actor.render)) at actor
    obtain ⟨process, member, observed⟩ := (publicHeader_parallel_iff _ _ _).mp actor
    obtain ⟨selected, _, rfl⟩ := List.mem_map.mp member
    exact False.elim (actor_has_no_public_input channel selected observed)
  · have faithful : Function.Injective (ambient (Γ := Γ) n .nm) := by
      rw [← privateScope_inclusion n]
      exact (privateScope n).inclusion_injective .nm
    exact (reindexed_public_header_iff (ambient n) faithful .input1 channel (lower frame)).mp framed

theorem idle_input_reflected {Γ : Ctx sig} {atom : Proc Γ} (head : IdleFrame.Head atom)
    (channel : Var Γ .nm) (observed : PublicHeader .input1 channel (lower atom)) :
    PublicHeader .input1 channel atom ∨ PublicHeader .input2 channel atom := by
  cases head with
  | output subject datum =>
      simp only [lower_out1, PublicHeader, hasHeader_out1, reduceCtorEq, false_and] at observed
  | input1 subject body =>
      exact Or.inl (by simpa only [lower_inp1, PublicHeader, hasHeader_inp1] using observed)
  | input2 subject body =>
      exact Or.inr (by simpa only [lower_inp2, receivePair, PublicHeader, hasHeader_inp1, hasHeader_inp2] using observed)
  | server1 subject body =>
      exact Or.inl (by simpa only [lower_rep, lower_inp1, PublicHeader, hasHeader_rep, hasHeader_inp1] using observed)
  | server2 subject body =>
      exact Or.inr (by simpa only [lower_rep, lower_inp2, receivePair, PublicHeader, hasHeader_rep,
        hasHeader_inp1, hasHeader_inp2] using observed)

theorem frame_input_reflected {Γ : Ctx sig} (frame : List (Proc Γ))
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) (channel : Var Γ .nm)
    (observed : PublicHeader .input1 channel (lower (parallel frame))) :
    PublicHeader .input1 channel (parallel frame) ∨ PublicHeader .input2 channel (parallel frame) := by
  rw [← IdleFrame.parallel_lower] at observed
  obtain ⟨process, member, seen⟩ := (publicHeader_parallel_iff _ _ _).mp observed
  obtain ⟨atom, present, rfl⟩ := List.mem_map.mp member
  rcases idle_input_reflected (heads atom present) channel seen with unary | binary
  · exact Or.inl ((publicHeader_parallel_iff _ _ _).mpr ⟨atom, present, unary⟩)
  · exact Or.inr ((publicHeader_parallel_iff _ _ _).mpr ⟨atom, present, binary⟩)

/-- No primitive schedule or endpoint representation is assumed. The given
runtime witness derives the original public listener and its source arity. -/
theorem public_input_reflected {Γ : Ctx sig} {source target : Proc Γ}
    (witness : Witness source target) (channel : Var Γ .nm)
    (observed : PublicHeader .input1 channel target) :
    PublicHeader .input1 channel source ∨ PublicHeader .input2 channel source := by
  have opened := ((predicate .input1 channel).2 witness.target).mp observed
  change PublicHeader .input1 channel
    (witness.scope.close ((privateScope witness.n).close
      (registryTarget witness.registry (parallel witness.frame)))) at opened
  rw [publicHeader_scope_iff, publicHeader_scope_iff, privateScope_inclusion] at opened
  have actors := (registry_equation witness.registry (parallel witness.frame) witness.live)
  have assembled := ((predicate .input1 _).2 actors).mp opened
  have framed := assembly_input_from_frame witness.registry (parallel witness.frame)
    (witness.scope.inclusion .nm channel) assembled
  rcases frame_input_reflected witness.frame witness.heads _ framed with unary | binary
  · apply Or.inl
    apply ((predicate .input1 channel).2 witness.source).mpr
    apply (publicHeader_scope_iff _ _ _ _).mpr
    change HasHeader .input1 _ _ _ (par _ _)
    exact (hasHeader_par _ _ _ _ _ _).mpr (Or.inr unary)
  · apply Or.inr
    apply ((predicate .input2 channel).2 witness.source).mpr
    apply (publicHeader_scope_iff _ _ _ _).mpr
    change HasHeader .input2 _ _ _ (par _ _)
    exact (hasHeader_par _ _ _ _ _ _).mpr (Or.inr binary)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeObservations
