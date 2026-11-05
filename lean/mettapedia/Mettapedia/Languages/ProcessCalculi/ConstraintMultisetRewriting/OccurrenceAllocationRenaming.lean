import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ScheduleComposition

/-!
# Fresh bound allocation names for a finite selected private body

Entry occurrences retain their names in the left summand. Each internal
production receives a name indexed by its allocation position in the right
summand. A source number may therefore be reused after consumption without
identifying its old entry occurrence with its new creation.

The existing occurrence step and its freshness rule are unchanged. These
names describe a compiler comparison, not a new source-level observation
or a runtime representation. Guards and conditional row meanings retain
their separate transport obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationRenaming

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {O : Type} [DecidableEq O]

abbrev Name (O : Type) := O ⊕ (Nat × O)

def erase : Name O → O
  | .inl occurrence => occurrence
  | .inr (_, occurrence) => occurrence

def fresh (stage : Nat) (occurrence : O) : Name O := .inr (stage, occurrence)

structure Cursor (O : Type) where
  next : Nat
  current : O → Name O
  projects : ∀ occurrence, erase (current occurrence) = occurrence
  older : ∀ occurrence stage origin, current occurrence = .inr (stage, origin) → stage < next

def Cursor.initial : Cursor O :=
  ⟨0, Sum.inl, (fun _ => rfl), (by intro _ _ _ impossible; cases impossible)⟩

omit [DecidableEq O] in
theorem Cursor.injective (cursor : Cursor O) : Function.Injective cursor.current := by
  intro first second same
  exact (cursor.projects first).symm.trans ((congrArg erase same).trans (cursor.projects second))

def Cursor.rename (cursor : Cursor O) (picked : Selection O) : Selection (Name O) :=
  ⟨picked.taken.map cursor.current, picked.read.map cursor.current, picked.made.map (fresh cursor.next)⟩

def Cursor.advance (cursor : Cursor O) (picked : Selection O) : Cursor O where
  next := cursor.next + 1
  current occurrence := if occurrence ∈ picked.made then fresh cursor.next occurrence else cursor.current occurrence
  projects occurrence := by
    split
    · rfl
    · exact cursor.projects occurrence
  older occurrence stage origin same := by
    split at same
    · have equal := Sum.inr.inj same
      have stages := congrArg Prod.fst equal
      change cursor.next = stage at stages
      omega
    · exact Nat.lt_trans (cursor.older occurrence stage origin same) (Nat.lt_succ_self _)

theorem Cursor.new_disjoint (cursor : Cursor O) (made world : Finset O) :
    Disjoint (made.image (fresh cursor.next)) (world.image cursor.current) := by
  apply Finset.disjoint_left.mpr
  intro name created old
  obtain ⟨origin, _member, rfl⟩ := Finset.mem_image.mp created
  obtain ⟨occurrence, _present, same⟩ := Finset.mem_image.mp old
  have impossible := cursor.older occurrence cursor.next origin same
  omega

def label (_ : O) : Unit := ()

theorem mapped_toFinset {P : Type} [DecidableEq P] (values : List O) (mapping : O → P) :
    (values.map mapping).toFinset = values.toFinset.image mapping := by
  ext name
  simp

theorem Cursor.rename_enabled (cursor : Cursor O) {picked : Selection O} {world : Finset O}
    (enabled : Enabled label world (picked.commit : Commit O Unit)) :
    Enabled label (world.image cursor.current) ((cursor.rename picked).commit : Commit (Name O) Unit) := by
  have taken := Finset.image_subset_image enabled.taken_subset (f := cursor.current)
  have kept := Finset.image_subset_image enabled.kept_subset (f := cursor.current)
  have apart := (Finset.disjoint_image cursor.injective).mpr enabled.apart
  refine ⟨?_, ?_, ?_, ?_, by simp [Selection.commit]⟩
  · simpa only [Cursor.rename, Selection.commit, mapped_toFinset] using taken
  · simpa only [Cursor.rename, Selection.commit, mapped_toFinset] using kept
  · simpa only [Cursor.rename, Selection.commit, mapped_toFinset] using apart
  · simpa only [Cursor.rename, Selection.commit, mapped_toFinset] using cursor.new_disjoint picked.made.toFinset world

/-- Changing the allocation names commutes with the actual physical update. -/
theorem Cursor.fire_image (cursor : Cursor O) (picked : Selection O) (world : Finset O)
    (sourceFresh : Disjoint picked.made.toFinset world) :
    fire (world.image cursor.current) ((cursor.rename picked).commit : Commit (Name O) Unit) =
      (fire world (picked.commit : Commit O Unit)).image (cursor.advance picked).current := by
  change (world.image cursor.current \ (picked.taken.map cursor.current).toFinset) ∪
      (picked.made.map (fresh cursor.next)).toFinset = _
  rw [mapped_toFinset, mapped_toFinset, ← Finset.image_sdiff _ _ cursor.injective]
  change _ = ((world \ picked.taken.toFinset) ∪ picked.made.toFinset).image (cursor.advance picked).current
  rw [Finset.image_union]
  apply congrArg₂ (· ∪ ·)
  · apply Finset.image_congr
    intro occurrence member
    have notMade : occurrence ∉ picked.made := by
      intro made
      exact Finset.disjoint_left.mp sourceFresh (List.mem_toFinset.mpr made) (Finset.mem_sdiff.mp member).1
    exact (if_neg notMade).symm
  · apply Finset.image_congr
    intro occurrence member
    exact (if_pos (List.mem_toFinset.mp member)).symm

def rename (cursor : Cursor O) : List (Selection O) → List (Selection (Name O))
  | [] => []
  | picked :: rest => cursor.rename picked :: rename (cursor.advance picked) rest

def finish (cursor : Cursor O) : List (Selection O) → Cursor O
  | [] => cursor
  | picked :: rest => finish (cursor.advance picked) rest

def commits (code : List (Selection O)) : List (Commit O Unit) := code.map Selection.commit

def project (picked : Selection (Name O)) : Selection O :=
  ⟨picked.taken.map erase, picked.read.map erase, picked.made.map erase⟩

omit [DecidableEq O] in
theorem Cursor.project_rename (cursor : Cursor O) (picked : Selection O) :
    project (cursor.rename picked) = picked := by
  have old : (fun occurrence => erase (cursor.current occurrence)) = id := funext cursor.projects
  have created : (fun occurrence : O => erase (fresh cursor.next occurrence)) = id := rfl
  cases picked
  simp only [project, Cursor.rename, List.map_map, Function.comp_def, old, created, List.map_id]

/-- The comparison preserves the ordered physical choices in all three ports. -/
theorem trace_projection (code : List (Selection O)) (cursor : Cursor O) :
    (rename cursor code).map project = code := by
  induction code generalizing cursor with
  | nil => rfl
  | cons picked rest prior =>
      simp only [rename, List.map_cons, Cursor.project_rename, prior]

/-- Every admitted resource history has a fresh-allocation history with the exact projected store. -/
theorem lifts (code : List (Selection O)) (cursor : Cursor O) (world : Finset O)
    (enabled : Executable label world (commits code)) :
    Executable label (world.image cursor.current) (commits (rename cursor code)) ∧
      fireList (world.image cursor.current) (commits (rename cursor code)) =
        (fireList world (commits code)).image (finish cursor code).current := by
  induction code generalizing cursor world with
  | nil => exact ⟨.nil _, rfl⟩
  | cons picked rest prior =>
      obtain ⟨first, later⟩ := executable_cons_iff.mp enabled
      obtain ⟨tail, same⟩ := prior (cursor.advance picked) (fire world picked.commit) later
      have changed := cursor.fire_image picked world first.fresh
      refine ⟨Executable.cons (cursor.rename_enabled first) ?_, ?_⟩
      · simpa only [commits, changed] using tail
      · change fireList (fire (world.image cursor.current) (cursor.rename picked).commit)
          (commits (rename (cursor.advance picked) rest)) = _
        rw [changed]
        exact same

theorem erase_image (cursor : Cursor O) (world : Finset O) :
    (world.image cursor.current).image erase = world := by
  ext occurrence
  constructor
  · intro member
    obtain ⟨name, inside, same⟩ := Finset.mem_image.mp member
    obtain ⟨source, present, rfl⟩ := Finset.mem_image.mp inside
    rw [cursor.projects] at same
    exact same ▸ present
  · intro member
    exact Finset.mem_image.mpr ⟨cursor.current occurrence, Finset.mem_image.mpr ⟨occurrence, member, rfl⟩,
      cursor.projects occurrence⟩

/-- Erasure forgets only the bound allocation names, preserving every live source occurrence. -/
theorem final_projection (code : List (Selection O)) (cursor : Cursor O) (world : Finset O)
    (enabled : Executable label world (commits code)) :
    (fireList (world.image cursor.current) (commits (rename cursor code))).image erase =
      fireList world (commits code) := by
  rw [(lifts code cursor world enabled).2]
  exact erase_image _ _

/-- The renamed body has one enabled net commit under the existing occurrence rules. -/
theorem one_net_commit (code : List (Selection O)) (world : Finset O)
    (enabled : Executable label world (commits code)) :
    let cursor : Cursor O := .initial
    let compiled := CompiledSchedule.compile label (commits (rename cursor code))
    Enabled label (world.image cursor.current) compiled.effect ∧
      (fire (world.image cursor.current) compiled.effect).image erase = fireList world (commits code) := by
  dsimp only
  have executable := (lifts code Cursor.initial world enabled).1
  obtain ⟨ready, same⟩ := (CompiledSchedule.compile_correct label _ _).2
    ((CompiledSchedule.compile_condition_iff label _ _).mpr executable)
  refine ⟨ready, ?_⟩
  rw [same]
  exact final_projection code Cursor.initial world enabled

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationRenaming
