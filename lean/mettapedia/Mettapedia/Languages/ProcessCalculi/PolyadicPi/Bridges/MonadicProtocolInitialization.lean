import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeState
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolSimulation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolGuarded

/-!
# Source-derived initialization of the tuple-protocol registry

Each active binary output becomes its own offered slot. Its ordered fields
and multiplicity are retained; no receiver is chosen during initialization.
Ordinary source atoms remain in a frame, while the existing restriction
telescope records their actual shared world. The source and lowered target
equations are proved separately against their literal supplied terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Initialization

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open MonadicProtocol.Capabilities MonadicProtocol.RuntimeState ScopedActiveFrontier

private theorem nil_left {Γ : Ctx sig} (p : Proc Γ) : StructuralEq (par nil p) p :=
  (StructuralEq.parComm _ _).trans (.parUnit _)

/-- Closing a whole registry is the parallel composition of its individually
closed slots. Older slots and the ordinary frame see neither newly introduced
private position. This theorem applies to every phase, including offers. -/
theorem registry_closed : ∀ {Γ : Ctx sig} (n : Nat)
    (registry : Fin n → Slot Γ) (frame : Proc Γ),
    StructuralEq ((privateScope n).close (registryTarget registry frame))
      (par (parallel ((List.finRange n).map (fun owner => (registry owner).closed))) (lower frame)) := by
  intro Γ n
  induction n with
  | zero =>
      intro registry frame
      simp only [privateScope, Scope.close, registryTarget, List.finRange_zero,
        List.map_nil, parallel]
      change StructuralEq (par nil (rename (fun _ name => name) (lower frame)))
        (par nil (lower frame))
      rw [rename_id]
      exact .refl _
  | succ n ih =>
      intro registry frame
      let tail : Fin n → Slot Γ := fun owner => registry owner.succ
      let old := registryTarget tail frame
      let shift : Ren sig (World n Γ) (World (n + 1) Γ) := fun _ name => .succ (.succ name)
      have shifted : ∀ p : Proc (World n Γ), rename shift p = weaken (weaken p) := by
        intro p
        simp only [weaken, rename_comp]
        rfl
      have listEq : (List.finRange (n + 1)).map (fun owner => (registry owner).placed (n + 1) owner) =
          (registry ⟨0, Nat.succ_pos n⟩).placed (n + 1) ⟨0, Nat.succ_pos n⟩ ::
            (((List.finRange n).map (fun owner => (tail owner).placed n owner)).map
              (rename shift)) := by
        simp only [List.finRange_succ, List.map_cons, List.map_map]
        congr 1
        apply List.map_congr_left
        intro owner _
        change (registry owner.succ).placed (n + 1) owner.succ =
          rename shift ((tail owner).placed n owner)
        rw [shifted]
        exact placed_extend n owner (registry owner.succ)
      have frameEq : rename (ambient (n + 1)) (lower frame) =
          rename shift (rename (ambient n) (lower frame)) := by
        rw [rename_comp]
        rfl
      have oldParallel : parallel
          (((List.finRange n).map (fun owner => (tail owner).placed n owner)).map
            (rename shift)) =
          rename shift (parallel ((List.finRange n).map (fun owner => (tail owner).placed n owner))) :=
        (parallel_rename shift _).symm
      have arranged : StructuralEq (registryTarget registry frame)
          (par ((registry ⟨0, Nat.succ_pos n⟩).placed (n + 1) ⟨0, Nat.succ_pos n⟩)
            (rename shift old)) := by
        dsimp only [registryTarget]
        rw [listEq, parallel, oldParallel, frameEq]
        have together : par
            (rename shift (parallel ((List.finRange n).map (fun owner => (tail owner).placed n owner))))
            (rename shift (rename (ambient n) (lower frame))) = rename shift old := by
          rw [← rename_par]
          rfl
        exact (StructuralEq.parAssoc _ _ _).trans (together ▸ StructuralEq.refl _)
      have firstClosed : nu (nu ((registry ⟨0, Nat.succ_pos n⟩).placed (n + 1) ⟨0, Nat.succ_pos n⟩)) =
          rename (ambient n) (registry ⟨0, Nat.succ_pos n⟩).closed := by
        simp only [Slot.placed, placement_new, Slot.closed, rename_nu]
        have lift : liftRen (ambient (Γ := Γ) n) [.nm, .nm] =
            liftRen (liftRen (ambient n) [.nm]) [.nm] := by
          funext sort name
          cases name with
          | zero => rfl
          | succ name => cases name <;> rfl
        rw [lift]
        rfl
      have paired := (Scope.par_left (.bind (.bind .nil))
        ((registry ⟨0, Nat.succ_pos n⟩).placed (n + 1) ⟨0, Nat.succ_pos n⟩) old).symm
      change StructuralEq
        (nu (nu (par ((registry ⟨0, Nat.succ_pos n⟩).placed (n + 1) ⟨0, Nat.succ_pos n⟩)
          (rename shift old))))
        (par (nu (nu ((registry ⟨0, Nat.succ_pos n⟩).placed (n + 1) ⟨0, Nat.succ_pos n⟩))) old) at paired
      rw [firstClosed] at paired
      have outside := (privateScope n).par_right old (registry ⟨0, Nat.succ_pos n⟩).closed
      rw [privateScope_inclusion] at outside
      have result := ((privateScope n).congr
        ((StructuralEq.nu (.nu arranged)).trans paired)).trans outside.symm
      have completed := result.trans (.par (.refl _) (ih tail frame))
      rw [privateScope, Scope.close_append]
      refine completed.trans ?_
      simp only [List.finRange_succ, List.map_cons, List.map_map, parallel]
      exact (StructuralEq.parAssoc _ _ _).symm


/-- A source binary output keeps its literal channel and ordered fields. -/
structure Offer (Γ : Ctx sig) where
  channel : Name Γ
  first : Name Γ
  second : Name Γ

def Offer.slot {Γ : Ctx sig} (offer : Offer Γ) : Slot Γ :=
  .offered offer.channel offer.first offer.second

def Offer.source {Γ : Ctx sig} (offer : Offer Γ) : Proc Γ := offer.slot.source

def selectOffer : {Γ : Ctx sig} → Proc Γ → Option (Offer Γ)
  | _, .op .out2 (.cons channel (.cons first (.cons second .nil))) => some ⟨channel, first, second⟩
  | _, _ => none

theorem selected_source : ∀ {Γ : Ctx sig} (process : Proc Γ) (offer : Offer Γ),
    selectOffer process = some offer → process = offer.source
  | _, .var _, _, selected => by cases selected
  | _, .op .nil .nil, _, selected => by cases selected
  | _, .op .par (.cons _ (.cons _ .nil)), _, selected => by cases selected
  | _, .op .inp1 (.cons _ (.cons _ .nil)), _, selected => by cases selected
  | _, .op .inp2 (.cons _ (.cons _ .nil)), _, selected => by cases selected
  | _, .op .out1 (.cons _ (.cons _ .nil)), _, selected => by cases selected
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))), _, selected => by cases selected; rfl
  | _, .op .nu (.cons _ .nil), _, selected => by cases selected
  | _, .op .rep (.cons _ .nil), _, selected => by cases selected

def offers {Γ : Ctx sig} : List (Proc Γ) → List (Offer Γ)
  | [] => []
  | first :: rest => match selectOffer first with
    | none => offers rest
    | some offer => offer :: offers rest

def frameAtoms {Γ : Ctx sig} : List (Proc Γ) → List (Proc Γ)
  | [] => []
  | first :: rest => match selectOffer first with
    | none => first :: frameAtoms rest
    | some _ => frameAtoms rest

private theorem exchange {Γ : Ctx sig} (a b c : Proc Γ) :
    StructuralEq (par a (par b c)) (par b (par a c)) :=
  (StructuralEq.parAssoc _ _ _).symm.trans
    ((StructuralEq.par (.parComm _ _) (.refl _)).trans (.parAssoc _ _ _))

/-- Partitioning is an equation about the original finite occurrence list.
Repeated equal outputs remain repeated offers. -/
theorem source_partition {Γ : Ctx sig} (atoms : List (Proc Γ)) :
    StructuralEq (parallel atoms)
      (par (parallel ((offers atoms).map Offer.source)) (parallel (frameAtoms atoms))) := by
  induction atoms with
  | nil => exact (nil_left nil).symm
  | cons head rest ih =>
      cases selected : selectOffer head with
      | none =>
          simp only [offers, frameAtoms, selected, parallel]
          exact (StructuralEq.par (.refl _) ih).trans (exchange _ _ _)
      | some offer =>
          have same := selected_source head offer selected
          simp only [offers, frameAtoms, selected, List.map_cons, parallel]
          exact (StructuralEq.par (.refl _) ih).trans
            (same ▸ (StructuralEq.parAssoc _ _ _).symm)

def offeredRegistry {Γ : Ctx sig} (entries : List (Offer Γ)) : Fin entries.length → Slot Γ :=
  fun owner => entries[owner.val].slot

theorem offered_sources {Γ : Ctx sig} (entries : List (Offer Γ)) :
    (List.finRange entries.length).map (fun owner => (offeredRegistry entries owner).source) =
      entries.map Offer.source := by
  have original := List.map_getElem_finRange entries
  have mapped := congrArg (fun values => values.map Offer.source) original
  simpa only [List.map_map, Function.comp_def, offeredRegistry, Offer.source] using mapped

theorem offered_closed {Γ : Ctx sig} (entries : List (Offer Γ)) (frame : Proc Γ) :
    StructuralEq ((privateScope entries.length).close
      (registryTarget (offeredRegistry entries) frame))
      (lower (registrySource (offeredRegistry entries) frame)) := by
  have closed := registry_closed entries.length (offeredRegistry entries) frame
  have each : ∀ slot ∈ (List.finRange entries.length).map (offeredRegistry entries),
      StructuralEq slot.closed (lower slot.source) := by
    intro slot member
    obtain ⟨owner, _, same⟩ := List.mem_map.mp member
    subst slot
    change StructuralEq (Slot.offered _ _ _).closed
      (lower (out2 entries[owner.val].channel entries[owner.val].first entries[owner.val].second))
    rw [lower_out2]
    exact offered_entry _ _ _
  have related : StructuralEq
      (parallel ((List.finRange entries.length).map (fun owner => (offeredRegistry entries owner).closed)))
      (parallel ((List.finRange entries.length).map (fun owner => lower (offeredRegistry entries owner).source))) := by
    have general : ∀ selected : List (Slot Γ),
        (∀ slot ∈ selected, StructuralEq slot.closed (lower slot.source)) →
        StructuralEq (parallel (selected.map Slot.closed)) (parallel (selected.map (fun slot => lower slot.source))) := by
      intro selected
      induction selected with
      | nil => intro _; exact .refl _
      | cons first rest ih =>
          intro compared
          exact .par (compared first (List.mem_cons_self))
            (ih (fun slot member => compared slot (List.mem_cons_of_mem _ member)))
    simpa only [List.map_map, Function.comp_def] using general ((List.finRange entries.length).map (offeredRegistry entries)) each
  have lowerParallel : ∀ selected : List (Proc Γ),
      parallel (selected.map lower) = lower (parallel selected) := by
    intro selected
    induction selected with
    | nil => exact lower_nil.symm
    | cons first rest ih => simp only [List.map_cons, parallel, lower_par, ih]
  refine closed.trans ((StructuralEq.par related (.refl _)).trans ?_)
  have mapped : (List.finRange entries.length).map (fun owner => lower (offeredRegistry entries owner).source) =
      ((List.finRange entries.length).map (fun owner => (offeredRegistry entries owner).source)).map lower := by
    rw [List.map_map]
    rfl
  rw [mapped, lowerParallel]
  rw [registrySource, lower_par]
  exact .refl _

theorem lower_scope : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (process : Proc Δ),
    lower (scope.close process) = scope.close (lower process)
  | _, _, .nil, _ => rfl
  | _, _, .bind rest, process => by
      change lower (nu (rest.close process)) = nu (rest.close (lower process))
      rw [lower_nu, lower_scope]

/-- Entry uses the existing source frontier normalizer, then creates one
uncommitted slot for each of its actual binary-output occurrences. -/
theorem entry {Γ : Ctx sig} (process : Proc Γ) :
    ∃ (Δ : Ctx sig) (scope : Scope Γ Δ) (entries : List (Offer Δ)) (frame : Proc Δ),
      StructuralEq process (scope.close (registrySource (offeredRegistry entries) frame)) ∧
      StructuralEq (lower process)
        (scope.close ((privateScope entries.length).close
          (registryTarget (offeredRegistry entries) frame))) := by
  let frontier := normalize process
  let entries := offers frontier.atoms
  let frame := parallel (frameAtoms frontier.atoms)
  have sourceEq : StructuralEq process
      (frontier.scope.close (registrySource (offeredRegistry entries) frame)) := by
    refine (normalization process).trans (frontier.scope.congr ?_)
    dsimp only [registrySource]
    rw [offered_sources]
    exact source_partition frontier.atoms
  have targetEq := lower_structural sourceEq
  rw [lower_scope] at targetEq
  exact ⟨frontier.world, frontier.scope, entries, frame, sourceEq,
    targetEq.trans (frontier.scope.congr (offered_closed entries frame).symm)⟩

/-- Every residual occurrence is an original occurrence, with its actual
selection result. This property is stronger than simply losing binary offers
from the written list. -/
theorem residual_member {Γ : Ctx sig} (atoms : List (Proc Γ))
    {atom : Proc Γ} (member : atom ∈ frameAtoms atoms) :
    atom ∈ atoms ∧ selectOffer atom = none := by
  induction atoms with
  | nil => cases member
  | cons head rest ih =>
      cases selected : selectOffer head with
      | none =>
          simp only [frameAtoms, selected, List.mem_cons] at member
          rcases member with same | member
          · subst atom
            exact ⟨List.mem_cons_self, selected⟩
          · obtain ⟨present, none⟩ := ih member
            exact ⟨List.mem_cons_of_mem _ present, none⟩
      | some offer =>
          simp only [frameAtoms, selected] at member
          obtain ⟨present, none⟩ := ih member
          exact ⟨List.mem_cons_of_mem _ present, none⟩

/-- The ordinary frame is an actual list of guarded source heads. Its
continuations remain opaque, and no active binary output remains in it. -/
theorem guarded_residual {Γ : Ctx sig} {process : Proc Γ} (guarded : Guarded process) :
    ∀ atom ∈ frameAtoms (normalize process).atoms,
      GuardedAtom atom ∧ selectOffer atom = none := by
  intro atom member
  obtain ⟨original, absent⟩ := residual_member (normalize process).atoms member
  exact ⟨guarded.normalized_atoms atom original, absent⟩

/-- A source-derived entry retains the residual list, rather than just its
parallel composition. Later prefix classification can therefore refer to
the actual selected source occurrence, including equal copies. -/
structure Entry {Γ : Ctx sig} (process : Proc Γ) where
  world : Ctx sig
  scope : Scope Γ world
  offers : List (Offer world)
  residual : List (Proc world)
  heads : ∀ atom ∈ residual, GuardedAtom atom ∧ selectOffer atom = none
  source : StructuralEq process
    (scope.close (registrySource (offeredRegistry offers) (parallel residual)))
  target : StructuralEq (lower process)
    (scope.close ((privateScope offers.length).close
      (registryTarget (offeredRegistry offers) (parallel residual))))

/-- The entries and frame are computed from the source's own active syntax;
the proof does not search for a receiver or inspect an eventual execution. -/
def guarded_entry {Γ : Ctx sig} {process : Proc Γ} (guarded : Guarded process) : Entry process := by
  let frontier := normalize process
  let entries := offers frontier.atoms
  let residual := frameAtoms frontier.atoms
  have sourceEq : StructuralEq process
      (frontier.scope.close (registrySource (offeredRegistry entries) (parallel residual))) := by
    refine (normalization process).trans (frontier.scope.congr ?_)
    rw [registrySource, offered_sources]
    exact source_partition frontier.atoms
  have targetEq := lower_structural sourceEq
  rw [lower_scope] at targetEq
  exact ⟨frontier.world, frontier.scope, entries, residual, guarded_residual guarded, sourceEq,
    targetEq.trans (frontier.scope.congr (offered_closed entries (parallel residual)).symm)⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Initialization
