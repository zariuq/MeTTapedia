import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeIdleUpdate
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimePublicSelection

/-!
# Exposing the chosen public occurrence without changing its frame

The original finite owner permutation exposes the offered publication and its
own waiter. The original idle-list position exposes the selected receiver.
Constructor transports carry their existing labels in both directions. All
other occurrences remain in the same computed residual lists, including equal
messages and persistent listeners on the same public channel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicationArrangement

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors ScopedActiveFrontier
open ActiveMarking ActiveOriginErasure

def otherEntries {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n) :
    List (Actor n Γ) :=
  ((List.finRange n).erase owner).flatMap (fun other => slotActors other (registry other))

def otherPositions {Γ : Ctx sig} (frame : List (Proc Γ)) (input : Fin frame.length) :
    List (Fin frame.length) := (List.finRange frame.length).erase input

def otherFrame {Γ : Ctx sig} (frame : List (Proc Γ)) (input : Fin frame.length) : List (Proc Γ) :=
  (otherPositions frame input).map (fun position => frame[position.val])

def idleMark {Γ : Ctx sig} {n : Nat} (frame : List (Proc Γ)) (position : Fin frame.length) :
    ActiveMarking.Tree (Origin n) :=
  ActiveSyntaxMarking.mark (.idle position.val) (lower frame[position.val])

def idleRender {Γ : Ctx sig} {n : Nat} (frame : List (Proc Γ)) (position : Fin frame.length) :
    Proc (World n Γ) := rename (ambient n) (lower frame[position.val])

def rest {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n)
    (first second : Name Γ) (frame : List (Proc Γ)) (input : Fin frame.length) : Proc (World n Γ) :=
  par (Actor.render (.waiter owner first second))
    (par (parallel ((otherEntries registry owner).map Actor.render))
      (parallel ((otherPositions frame input).map (idleRender frame))))

def restMarks {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n)
    (first second : Name Γ) (frame : List (Proc Γ)) (input : Fin frame.length) : ActiveMarking.Tree (Origin n) :=
  .par (Actor.marks (.waiter owner first second))
    (.par (RuntimeActors.parallelMarks (otherEntries registry owner))
      (RuntimeIdleUpdate.parallelMarks (idleMark frame) (otherPositions frame input)))

def exposed {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n)
    (channel first second : Name Γ) (frame : List (Proc Γ)) (input : Fin frame.length) : Proc (World n Γ) :=
  par (Actor.render (.publication owner channel))
    (par (idleRender frame input) (rest registry owner first second frame input))

def exposedMarks {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n)
    (channel first second : Name Γ) (frame : List (Proc Γ)) (input : Fin frame.length) : ActiveMarking.Tree (Origin n) :=
  .par (Actor.marks (.publication owner channel))
    (.par (idleMark frame input) (restMarks registry owner first second frame input))

theorem actor_marks {Γ : Ctx sig} {n : Nat} (actors : List (Actor n Γ)) :
    RuntimeIdleUpdate.parallelMarks Actor.marks actors = RuntimeActors.parallelMarks actors := by
  induction actors with
  | nil => rfl
  | cons first rest ih => simp only [RuntimeIdleUpdate.parallelMarks, RuntimeActors.parallelMarks, ih]

theorem entries_partition {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel first second : Name Γ)
    (offered : registry owner = .offered channel first second) :
    (entries registry).Perm
      (.publication owner channel :: .waiter owner first second :: otherEntries registry owner) := by
  have partition := (List.perm_cons_erase (List.mem_finRange owner)).flatMap_right
    (fun other => slotActors other (registry other))
  simpa only [entries, List.flatMap_cons, offered, slotActors, List.cons_append, List.nil_append,
    otherEntries] using partition

theorem idle_source_marks {Γ : Ctx sig} {n : Nat} (frame : List (Proc Γ)) :
    RuntimeIdleUpdate.parallelMarks (idleMark (n := n) frame) (List.finRange frame.length) =
      IdleFrame.marks Origin.idle 0 frame := by
  change RuntimeIdleUpdate.parallelMarks
    (fun position : Fin frame.length => ActiveSyntaxMarking.mark (Origin.idle (n := n) position.val) (lower frame[position.val]))
    (List.finRange frame.length) = _
  simpa only [Nat.zero_add] using RuntimeIdleUpdate.indexed_marks (Origin.idle (n := n)) frame 0

theorem idle_source_process {Γ : Ctx sig} {n : Nat} (frame : List (Proc Γ)) :
    parallel ((List.finRange frame.length).map (idleRender (n := n) frame)) =
      rename (ambient n) (lower (parallel frame)) := by
  unfold idleRender
  rw [RuntimeIdleUpdate.indexed_parallel frame (fun process => rename (ambient n) (lower process))]
  rw [← IdleFrame.parallel_lower, parallel_rename, List.map_map]
  rfl

private theorem swap_middle {Label : Type} {Γ : Ctx sig} (a b c d : Proc Γ)
    (am bm cm dm : ActiveMarking.Tree Label) :
    Transport (.par (.par am bm) (.par cm dm)) (par (par a b) (par c d))
      (.par am (.par cm (.par bm dm))) (par a (par c (par b d))) :=
  (Transport.parAssoc am bm (.par cm dm) a b (par c d)).trans
    (.par (.refl am a)
      ((Transport.parAssocBack bm cm dm b c d).trans
        ((Transport.par (.parComm bm cm b c) (.refl dm d)).trans (.parAssoc cm bm dm c b d))))

private theorem unswap_middle {Label : Type} {Γ : Ctx sig} (a b c d : Proc Γ)
    (am bm cm dm : ActiveMarking.Tree Label) :
    Transport (.par am (.par cm (.par bm dm))) (par a (par c (par b d)))
      (.par (.par am bm) (.par cm dm)) (par (par a b) (par c d)) :=
  (Transport.par (.refl am a)
    ((Transport.parAssocBack cm bm dm c b d).trans
      ((Transport.par (.parComm cm bm c b) (.refl dm d)).trans (.parAssoc bm cm dm b c d)))).trans
    (.parAssocBack am bm (.par cm dm) a b (par c d))

/-- Reordering consists only of the actual parallel equations. Every prefix
keeps the mark it had before the actual target communication was exposed. -/
theorem arrange {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel first second : Name Γ)
    (offered : registry owner = .offered channel first second)
    (frame : List (Proc Γ)) (input : Fin frame.length) :
    Transport (assemblyMarks registry frame) (assembly registry (parallel frame))
      (exposedMarks registry owner channel first second frame input)
      (exposed registry owner channel first second frame input) := by
  have actors := RuntimeIdleUpdate.permutation_transport Actor.marks Actor.render
    (entries_partition registry owner channel first second offered)
  simp only [actor_marks] at actors
  have idle := RuntimeIdleUpdate.one_position_transport (idleMark (n := n) frame)
    (idleRender (n := n) frame) (List.finRange frame.length) input (List.mem_finRange input)
  rw [idle_source_marks, idle_source_process] at idle
  have arranged := Transport.par actors idle
  simp only [RuntimeActors.parallelMarks, List.map_cons, parallel] at arranged
  refine arranged.trans ?_
  have middle := swap_middle (Actor.render (.publication owner channel))
    (par (Actor.render (.waiter owner first second)) (parallel ((otherEntries registry owner).map Actor.render)))
    (idleRender frame input) (parallel ((otherPositions frame input).map (idleRender frame)))
    (Actor.marks (.publication owner channel))
    (.par (Actor.marks (.waiter owner first second)) (RuntimeActors.parallelMarks (otherEntries registry owner)))
    (idleMark frame input) (RuntimeIdleUpdate.parallelMarks (idleMark frame) (otherPositions frame input))
  exact middle.trans (.par (.refl _ _) (.par (.refl _ _)
    (.parAssoc _ _ _ _ _ _)))

theorem unarrange {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel first second : Name Γ)
    (offered : registry owner = .offered channel first second)
    (frame : List (Proc Γ)) (input : Fin frame.length) :
    Transport (exposedMarks registry owner channel first second frame input)
      (exposed registry owner channel first second frame input)
      (assemblyMarks registry frame) (assembly registry (parallel frame)) := by
  have actors := RuntimeIdleUpdate.permutation_transport Actor.marks Actor.render
    (entries_partition registry owner channel first second offered).symm
  simp only [actor_marks] at actors
  have idle := RuntimeIdleUpdate.permutation_transport (idleMark (n := n) frame) (idleRender (n := n) frame)
    (RuntimeIdleUpdate.one_position_permutation (List.finRange frame.length) input (List.mem_finRange input)).symm
  rw [idle_source_marks, idle_source_process] at idle
  have last := Transport.par actors idle
  simp only [RuntimeActors.parallelMarks, RuntimeIdleUpdate.parallelMarks, List.map_cons, parallel] at last
  refine Transport.trans ?_ last
  have middle := unswap_middle (Actor.render (.publication owner channel))
    (par (Actor.render (.waiter owner first second)) (parallel ((otherEntries registry owner).map Actor.render)))
    (idleRender frame input) (parallel ((otherPositions frame input).map (idleRender frame)))
    (Actor.marks (.publication owner channel))
    (.par (Actor.marks (.waiter owner first second)) (RuntimeActors.parallelMarks (otherEntries registry owner)))
    (idleMark frame input) (RuntimeIdleUpdate.parallelMarks (idleMark frame) (otherPositions frame input))
  exact (Transport.par (.refl _ _) (.par (.refl _ _) (.parAssocBack _ _ _ _ _ _))).trans middle

theorem positions_fits {Γ : Ctx sig} {n : Nat} (frame : List (Proc Γ))
    (positions : List (Fin frame.length)) :
    Fits (RuntimeIdleUpdate.parallelMarks (idleMark (n := n) frame) positions)
      (parallel (positions.map (idleRender (n := n) frame))) := by
  induction positions with
  | nil => exact .nil
  | cons first rest ih => exact .par ((ActiveSyntaxMarking.mark_fits _ _).rename (ambient n)) ih

theorem rest_fits {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n)
    (first second : Name Γ) (frame : List (Proc Γ)) (input : Fin frame.length) :
    Fits (restMarks registry owner first second frame input)
      (rest registry owner first second frame input) :=
  .par (Actor.fits _) (.par (RuntimeActors.parallel_fits _) (positions_fits frame _))

theorem remaining_idle {Γ : Ctx sig} {n : Nat} (frame : List (Proc Γ)) (input : Fin frame.length) :
    parallel ((otherPositions frame input).map (idleRender (n := n) frame)) =
      rename (ambient n) (lower (parallel (otherFrame frame input))) := by
  unfold idleRender
  rw [← IdleFrame.parallel_lower, parallel_rename]
  simp only [otherFrame, List.map_map, Function.comp_def]

theorem other_heads {Γ : Ctx sig} (frame : List (Proc Γ)) (input : Fin frame.length)
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) :
    ∀ atom ∈ otherFrame frame input, IdleFrame.Head atom := by
  intro atom member
  obtain ⟨position, _, same⟩ := List.mem_map.mp member
  subst atom
  exact heads _ (List.getElem_mem position.isLt)

theorem rest_unused {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n)
    (first second : Name Γ) (frame : List (Proc Γ)) (input : Fin frame.length)
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) :
    ScopedOpening.Vacuous (rest registry owner first second frame input) := by
  simp only [rest, par, ScopedOpening.Vacuous]
  rw [remaining_idle, ScopedOpening.vacuous_rename]
  exact ⟨RuntimeIdleUpdate.actor_unused _, RuntimeIdleUpdate.actors_unused _,
    IdleFrame.unused _ (other_heads frame input heads)⟩

theorem rest_single {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n)
    (first second : Name Γ) (frame : List (Proc Γ)) (input : Fin frame.length)
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) :
    SingleBodies (rest registry owner first second frame input) := by
  simp only [rest, par, SingleBodies]
  rw [remaining_idle, singleBodies_rename]
  exact ⟨RuntimeIdleUpdate.actor_single _, RuntimeIdleUpdate.actors_single _,
    IdleFrame.single _ (other_heads frame input heads)⟩

theorem slot_origin_exclusion {Γ : Ctx sig} {n : Nat} (other owner : Fin n)
    (different : other ≠ owner) (slot : Slot Γ) (index : Nat)
    (actor : Actor n Γ) (present : actor ∈ slotActors other slot) :
    actor.origin ≠ .publication owner ∧ actor.origin ≠ .idle index := by
  cases slot with
  | released => exact False.elim (List.not_mem_nil present)
  | offered channel first second =>
      simp only [slotActors, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl
      · exact ⟨fun same => different (Origin.publication.inj same), by intro same; cases same⟩
      · exact ⟨(by intro same; cases same), (by intro same; cases same)⟩
  | pending phase call =>
      obtain ⟨kind, _, same⟩ := List.mem_map.mp present
      subst actor
      cases kind <;> exact ⟨(by intro same; cases same), (by intro same; cases same)⟩

theorem rest_count_zero {Γ : Ctx sig} {n : Nat} [DecidableEq (Origin n)]
    (registry : Fin n → Slot Γ) (owner : Fin n) (first second : Name Γ)
    (frame : List (Proc Γ)) (input : Fin frame.length)
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) :
    originCount (fun origin => decide (origin = .idle input.val ∨ origin = .publication owner))
      (restMarks registry owner first second frame input) = 0 := by
  let selected := fun origin : Origin n => decide (origin = .idle input.val ∨ origin = .publication owner)
  have waiter : originCount selected (Actor.marks (.waiter owner first second)) = 0 :=
    RuntimeIdleUpdate.actor_count_zero selected _ (by simp only [selected, Actor.origin, reduceCtorEq, false_or, decide_false])
  have actors : originCount selected (RuntimeActors.parallelMarks (otherEntries registry owner)) = 0 := by
    apply RuntimeIdleUpdate.actors_count_zero
    intro actor member
    obtain ⟨other, member, present⟩ := List.mem_flatMap.mp member
    have different := ((List.nodup_finRange n).mem_erase_iff.mp member).1
    obtain ⟨notPub, notIdle⟩ := slot_origin_exclusion other owner different (registry other) input.val actor present
    simp only [selected, notPub, notIdle, false_or, decide_false]
  have idle : originCount selected
      (RuntimeIdleUpdate.parallelMarks (idleMark frame) (otherPositions frame input)) = 0 := by
    apply RuntimeIdleUpdate.parallel_count_zero
    intro position member
    apply RuntimeIdleUpdate.idle_count_zero _ _ (heads _ (List.getElem_mem position.isLt))
    have different := ((List.nodup_finRange frame.length).mem_erase_iff.mp member).1
    have values : position.val ≠ input.val := fun same => different (Fin.ext same)
    simp only [selected, Origin.idle.injEq, values, reduceCtorEq, false_or, decide_false]
  change originCount selected _ = 0
  simp only [restMarks, originCount, waiter, actors, idle, Nat.zero_add]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicationArrangement
