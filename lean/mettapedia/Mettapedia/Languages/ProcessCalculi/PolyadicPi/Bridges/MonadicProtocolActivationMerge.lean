import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolInitialization
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRegistryReindex
import Mathlib.Data.List.FinRange

/-!
# Combining actual tuple registries after continuation activation

The new offers precede the existing occurrence registry. Each old occurrence
has an injective retained index, and the equations compare actual source and
closed target terms. Closing the allocated scopes before comparing them keeps
the independently allocated private names distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.ActivationMerge

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open MonadicProtocol.Capabilities MonadicProtocol.RuntimeState
open MonadicProtocol.Initialization ScopedActiveFrontier

def append {Γ : Ctx sig} {m n : Nat}
    (first : Fin m → Slot Γ) (second : Fin n → Slot Γ) : Fin (m + n) → Slot Γ :=
  Fin.append first second

theorem append_first {Γ : Ctx sig} {m n : Nat}
    (first : Fin m → Slot Γ) (second : Fin n → Slot Γ) (owner : Fin m) :
    append first second (Fin.castAdd n owner) = first owner :=
  Fin.append_left first second owner

theorem append_old {Γ : Ctx sig} {m n : Nat}
    (first : Fin m → Slot Γ) (second : Fin n → Slot Γ) (owner : Fin n) :
    append first second (Fin.natAdd m owner) = second owner :=
  Fin.append_right first second owner

theorem old_owners_retained (m n : Nat) : Function.Injective (Fin.natAdd m : Fin n → Fin (m + n)) := by
  intro first second equal
  apply Fin.ext
  have positions := congrArg Fin.val equal
  simp only [Fin.val_natAdd] at positions
  omega

theorem append_list {Γ : Ctx sig} {m n : Nat} {α : Type*}
    (first : Fin m → Slot Γ) (second : Fin n → Slot Γ) (observe : Slot Γ → α) :
    (List.finRange (m + n)).map (fun owner => observe (append first second owner)) =
      ((List.finRange m).map (fun owner => observe (first owner))) ++
      ((List.finRange n).map (fun owner => observe (second owner))) := by
  simp only [← List.ofFn_eq_map]
  have pointwise : (fun owner => observe (append first second owner)) =
      Fin.append (fun owner => observe (first owner)) (fun owner => observe (second owner)) := by
    funext owner
    induction owner using Fin.addCases <;> simp only [append, Fin.append_left, Fin.append_right]
  rw [pointwise, List.ofFn_fin_append]

private theorem exchange {Γ : Ctx sig} (a b c : Proc Γ) :
    StructuralEq (par a (par b c)) (par b (par a c)) :=
  (StructuralEq.parAssoc _ _ _).symm.trans
    ((StructuralEq.par (.parComm _ _) (.refl _)).trans (.parAssoc _ _ _))

private theorem regroup {Γ : Ctx sig} (a b c d : Proc Γ) :
    StructuralEq (par (par a b) (par c d)) (par (par a c) (par b d)) :=
  (StructuralEq.parAssoc _ _ _).trans
    ((StructuralEq.par (.refl _) (exchange b c d)).trans (StructuralEq.parAssoc _ _ _).symm)

theorem source_append {Γ : Ctx sig} {m n : Nat}
    (first : Fin m → Slot Γ) (second : Fin n → Slot Γ) (firstFrame secondFrame : Proc Γ) :
    StructuralEq (par (registrySource first firstFrame) (registrySource second secondFrame))
      (registrySource (append first second) (par firstFrame secondFrame)) := by
  rw [registrySource, registrySource, registrySource, append_list]
  exact (regroup _ _ _ _).trans (.par (parallel_append _ _) (.refl _))

theorem target_append {Γ : Ctx sig} {m n : Nat}
    (first : Fin m → Slot Γ) (second : Fin n → Slot Γ) (firstFrame secondFrame : Proc Γ) :
    StructuralEq
      (par ((privateScope m).close (registryTarget first firstFrame))
        ((privateScope n).close (registryTarget second secondFrame)))
      ((privateScope (m + n)).close
        (registryTarget (append first second) (par firstFrame secondFrame))) := by
  have assembled := (StructuralEq.par (registry_closed m first firstFrame)
    (registry_closed n second secondFrame)).trans (regroup _ _ _ _)
  refine assembled.trans ?_
  have joined := registry_closed (m + n) (append first second) (par firstFrame secondFrame)
  rw [append_list, lower_par] at joined
  exact (StructuralEq.par (parallel_append _ _) (.refl _)).trans joined.symm

theorem remaining_append {Γ : Ctx sig} {m n : Nat}
    (first : Fin m → Slot Γ) (second : Fin n → Slot Γ) :
    registryRemaining (append first second) = registryRemaining first + registryRemaining second := by
  simp only [registryRemaining, append_list, List.sum_append]

theorem offered_remaining {Γ : Ctx sig} (entries : List (Offer Γ)) :
    registryRemaining (offeredRegistry entries) = 0 := by
  simp only [registryRemaining, offeredRegistry, Offer.slot, Slot.remaining, List.map_const',
    List.sum_replicate, nsmul_zero]

/-- A registry can be carried through a newly opened source scope without
changing any of its private occurrence identities or communication debt. -/
theorem closed_reindex {Γ Δ : Ctx sig} {n : Nat}
    (registry : Fin n → Slot Γ) (frame : Proc Γ) (environment : Ren sig Γ Δ) :
    StructuralEq
      (rename environment ((privateScope n).close (registryTarget registry frame)))
      ((privateScope n).close (registryTarget
        (fun owner => (registry owner).rename environment) (rename environment frame))) := by
  have carried := (registry_closed n registry frame).rename environment
  rw [rename_par, parallel_rename, List.map_map, lower_rename] at carried
  simp only [Function.comp_def, Slot.closed_rename] at carried
  exact carried.trans (registry_closed n (fun owner => (registry owner).rename environment)
    (rename environment frame)).symm

def expanded {Γ : Ctx sig} {n : Nat} {body : Proc Γ}
    (registry : Fin n → Slot Γ) (entry : Entry body) : Fin (entry.offers.length + n) → Slot entry.world :=
  append (offeredRegistry entry.offers) (fun owner => (registry owner).rename entry.scope.inclusion)

def residual {Γ : Ctx sig} {body : Proc Γ} (entry : Entry body)
    (old : List (Proc Γ)) : List (Proc entry.world) :=
  entry.residual ++ old.map (rename entry.scope.inclusion)

private theorem source_frame {Γ : Ctx sig} {n : Nat}
    (registry : Fin n → Slot Γ) {first second : Proc Γ} (equal : StructuralEq first second) :
    StructuralEq (registrySource registry first) (registrySource registry second) :=
  .par (.refl _) equal

private theorem target_frame {Γ : Ctx sig} {n : Nat}
    (registry : Fin n → Slot Γ) {first second : Proc Γ} (equal : StructuralEq first second) :
    StructuralEq ((privateScope n).close (registryTarget registry first))
      ((privateScope n).close (registryTarget registry second)) :=
  (privateScope n).congr (.par (.refl _) ((lower_structural equal).rename (ambient n)))

/-- The supplied activated source body is replaced by its actual opened
entry. The original occurrence registry is carried intact into that world;
only the entry's exposed binary outputs become new offers. -/
theorem activation_source {Γ : Ctx sig} {n : Nat} {body : Proc Γ}
    (registry : Fin n → Slot Γ) (old : List (Proc Γ)) (entry : Entry body) :
    StructuralEq (par (registrySource registry (parallel old)) body)
      (entry.scope.close (registrySource (expanded registry entry) (parallel (residual entry old)))) := by
  have expose := (StructuralEq.parComm (registrySource registry (parallel old)) body).trans
    (.par entry.source (.refl (registrySource registry (parallel old))))
  have outside := entry.scope.par_left
    (registrySource (offeredRegistry entry.offers) (parallel entry.residual))
    (registrySource registry (parallel old))
  rw [registrySource_rename, parallel_rename] at outside
  have joined := source_append (offeredRegistry entry.offers)
    (fun owner => (registry owner).rename entry.scope.inclusion)
    (parallel entry.residual) (parallel (old.map (rename entry.scope.inclusion)))
  exact expose.trans (outside.trans (entry.scope.congr
    (joined.trans (source_frame (expanded registry entry) (parallel_append _ _)))))

/-- The target comparison assembles the newly activated continuation beside
the real closed states of all previous sessions. Pending source readouts are
not inspected or initialized by this operation. -/
theorem activation_target {Γ : Ctx sig} {n : Nat} {body : Proc Γ}
    (registry : Fin n → Slot Γ) (old : List (Proc Γ)) (entry : Entry body) :
    StructuralEq
      (par ((privateScope n).close (registryTarget registry (parallel old))) (lower body))
      (entry.scope.close ((privateScope (entry.offers.length + n)).close
        (registryTarget (expanded registry entry) (parallel (residual entry old))))) := by
  have expose := (StructuralEq.parComm
    ((privateScope n).close (registryTarget registry (parallel old))) (lower body)).trans
    (.par entry.target (.refl ((privateScope n).close (registryTarget registry (parallel old)))))
  have outside := entry.scope.par_left
    ((privateScope entry.offers.length).close
      (registryTarget (offeredRegistry entry.offers) (parallel entry.residual)))
    ((privateScope n).close (registryTarget registry (parallel old)))
  have oldCarried := closed_reindex registry (parallel old) entry.scope.inclusion
  rw [parallel_rename] at oldCarried
  have joined := target_append (offeredRegistry entry.offers)
    (fun owner => (registry owner).rename entry.scope.inclusion)
    (parallel entry.residual) (parallel (old.map (rename entry.scope.inclusion)))
  exact expose.trans (outside.trans (entry.scope.congr
    ((StructuralEq.par (.refl _) oldCarried).trans
      (joined.trans (target_frame (expanded registry entry) (parallel_append _ _))))))

theorem activation_remaining {Γ : Ctx sig} {n : Nat} {body : Proc Γ}
    (registry : Fin n → Slot Γ) (entry : Entry body) :
    registryRemaining (expanded registry entry) = registryRemaining registry := by
  rw [expanded, remaining_append, offered_remaining, registryRemaining_rename, zero_add]

theorem activation_old {Γ : Ctx sig} {n : Nat} {body : Proc Γ}
    (registry : Fin n → Slot Γ) (entry : Entry body) (owner : Fin n) :
    expanded registry entry (Fin.natAdd entry.offers.length owner) =
      (registry owner).rename entry.scope.inclusion :=
  append_old _ _ owner

private theorem renamed_head_absent {Γ Δ : Ctx sig} {atom : Proc Γ}
    (head : GuardedAtom atom) (absent : selectOffer atom = none) (environment : Ren sig Γ Δ) :
    selectOffer (rename environment atom) = none := by
  cases head with
  | inp1 | inp2 | out1 | server1 | server2 => rfl
  | out2 => cases absent

/-- Every ordinary occurrence in the merged frame retains its actual guard.
The two lists are concatenated, rather than identified by term equality. -/
theorem activation_heads {Γ : Ctx sig} {body : Proc Γ}
    (old : List (Proc Γ)) (entry : Entry body)
    (heads : ∀ atom ∈ old, GuardedAtom atom ∧ selectOffer atom = none) :
    ∀ atom ∈ residual entry old, GuardedAtom atom ∧ selectOffer atom = none := by
  intro atom member
  change atom ∈ entry.residual ++ old.map (rename entry.scope.inclusion) at member
  rcases List.mem_append.mp member with fresh | carried
  · exact entry.heads atom fresh
  · obtain ⟨original, originalMember, same⟩ := List.mem_map.mp carried
    subst atom
    obtain ⟨head, absent⟩ := heads original originalMember
    exact ⟨head.rename entry.scope.inclusion, renamed_head_absent head absent entry.scope.inclusion⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.ActivationMerge
