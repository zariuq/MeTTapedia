import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationRenaming
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ScheduleComposition

/-!
# Entry uses survive allocation renaming exactly

A later use refers to an entry occurrence only if no earlier selection
created that logical identifier. This statement depends on selections and
the allocation cursor, not on source values or solver models.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationRenaming

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {O P : Type}

def initialUse : List (Selection O) → O → Prop
  | [], _ => False
  | picked :: rest, occurrence =>
      (occurrence ∈ picked.taken ∨ occurrence ∈ picked.read) ∨
        (occurrence ∉ picked.made ∧ initialUse rest occurrence)

theorem initialUse_append (first second : List (Selection O)) (occurrence : O) :
    initialUse (first ++ second) occurrence ↔ initialUse first occurrence ∨
      ((∀ picked ∈ first, occurrence ∉ picked.made) ∧ initialUse second occurrence) := by
  induction first with
  | nil => simp only [List.nil_append, initialUse, List.not_mem_nil, false_implies, implies_true, true_and, false_or]
  | cons picked rest prior =>
      simp only [List.cons_append, initialUse, List.forall_mem_cons, prior]
      tauto

def UsesName (code : List (Selection P)) (physical : P) : Prop :=
  ∃ picked ∈ code, physical ∈ picked.taken ∨ physical ∈ picked.read

theorem usesName_cons (picked : Selection P) (rest : List (Selection P)) (physical : P) :
    UsesName (picked :: rest) physical ↔ (physical ∈ picked.taken ∨ physical ∈ picked.read) ∨ UsesName rest physical := by
  constructor
  · rintro ⟨selected, member, used⟩
    rcases List.mem_cons.mp member with rfl | later
    · exact .inl used
    · exact .inr ⟨selected, later, used⟩
  · rintro (used | ⟨selected, member, used⟩)
    · exact ⟨picked, List.mem_cons_self, used⟩
    · exact ⟨selected, List.mem_cons_of_mem _ member, used⟩

theorem renamed_port_iff (cursor : Cursor O) (picked : Selection O) (occurrence : O) :
    (Sum.inl occurrence ∈ (cursor.rename picked).taken ∨ Sum.inl occurrence ∈ (cursor.rename picked).read) ↔
      cursor.current occurrence = Sum.inl occurrence ∧ (occurrence ∈ picked.taken ∨ occurrence ∈ picked.read) := by
  constructor
  · rintro (taken | read)
    · obtain ⟨source, member, same⟩ := List.mem_map.mp taken
      have original : source = occurrence := (cursor.projects source).symm.trans (congrArg erase same)
      subst source
      exact ⟨same, .inl member⟩
    · obtain ⟨source, member, same⟩ := List.mem_map.mp read
      have original : source = occurrence := (cursor.projects source).symm.trans (congrArg erase same)
      subst source
      exact ⟨same, .inr member⟩
  · rintro ⟨same, taken | read⟩
    · exact .inl (List.mem_map.mpr ⟨occurrence, taken, same⟩)
    · exact .inr (List.mem_map.mpr ⟨occurrence, read, same⟩)

variable [DecidableEq O]

theorem Cursor.advance_inl_iff (cursor : Cursor O) (picked : Selection O) (occurrence : O) :
    (cursor.advance picked).current occurrence = Sum.inl occurrence ↔
      cursor.current occurrence = Sum.inl occurrence ∧ occurrence ∉ picked.made := by
  by_cases made : occurrence ∈ picked.made <;> simp only [Cursor.advance, made, if_true, if_false, fresh]
  · simp
  · simp

theorem usesName_rename_iff (cursor : Cursor O) (code : List (Selection O)) (occurrence : O) :
    UsesName (rename cursor code) (Sum.inl occurrence) ↔
      cursor.current occurrence = Sum.inl occurrence ∧ initialUse code occurrence := by
  induction code generalizing cursor with
  | nil => simp only [rename, UsesName, List.not_mem_nil, false_and, exists_false, initialUse, and_false]
  | cons picked rest prior =>
      rw [rename, usesName_cons, renamed_port_iff, prior, Cursor.advance_inl_iff]
      change (_ ∧ _) ∨ ((_ ∧ _) ∧ _) ↔ _ ∧ (_ ∨ (_ ∧ _))
      tauto

theorem usesName_initial_iff (code : List (Selection O)) (occurrence : O) :
    UsesName (rename Cursor.initial code) (Sum.inl occurrence) ↔ initialUse code occurrence := by
  rw [usesName_rename_iff]
  simp only [Cursor.initial, true_and]

/-- A compiled net input must occur in an authored input port. -/
theorem compiled_input_has_port (label : O → Unit)
    (code : List (Commit O Unit)) (physical : O)
    (used : physical ∈ (CompiledSchedule.compile label code).effect.taken ∪
      (CompiledSchedule.compile label code).effect.kept) :
    ∃ commit ∈ code, physical ∈ commit.taken ∨ physical ∈ commit.kept := by
  induction code with
  | nil =>
      simp only [CompiledSchedule.compile, CompiledSchedule.empty, Finset.union_self,
        Finset.notMem_empty] at used
  | cons first rest prior =>
      have source : physical ∈ first.taken ∨ physical ∈ first.kept ∨
          physical ∈ (CompiledSchedule.compile label rest).effect.taken ∪
            (CompiledSchedule.compile label rest).effect.kept := by
        simp only [CompiledSchedule.compile, CompiledSchedule.prepend, Commit.compose,
          Commit.sequentialInput, Commit.sequentialTaken, Commit.sequentialMade,
          Finset.mem_union, Finset.mem_sdiff] at used ⊢
        grind
      rcases source with taken | kept | later
      · exact ⟨first, List.mem_cons_self, .inl taken⟩
      · exact ⟨first, List.mem_cons_self, .inr kept⟩
      · obtain ⟨commit, member, port⟩ := prior later
        exact ⟨commit, List.mem_cons_of_mem _ member, port⟩


/-- Every net production comes from an authored creation port. -/
theorem compiled_made_has_creation (label : O → Unit)
    (code : List (Commit O Unit)) (name : O) :
    name ∈ (CompiledSchedule.compile label code).effect.made → ∃ commit ∈ code, name ∈ commit.made := by
  induction code with
  | nil => simp [CompiledSchedule.compile, CompiledSchedule.empty]
  | cons first rest prior =>
      intro member
      change name ∈ first.sequentialMade (CompiledSchedule.compile label rest).effect \
        first.sequentialTaken (CompiledSchedule.compile label rest).effect at member
      have choices := Finset.mem_union.mp (Finset.mem_sdiff.mp member).1
      rcases choices with initial | later
      · exact ⟨first, List.mem_cons_self, (Finset.mem_sdiff.mp initial).1⟩
      · obtain ⟨commit, inside, created⟩ := prior later
        exact ⟨commit, List.mem_cons_of_mem _ inside, created⟩


/-- An invocation control is consumed together with the data update. -/
theorem enabled_with_control {N : Type} [DecidableEq N] {world : Finset N} {effect : Commit N Unit}
    (enabled : Enabled (fun _ => ()) world effect) :
    Enabled (fun _ : Option N => ()) (insert none (world.image some))
      ⟨insert none (effect.taken.image some), effect.kept.image some, effect.made.image some, []⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro physical member
    rcases Finset.mem_insert.mp member with same | kept
    · subst physical
      exact Finset.mem_insert_self _ _
    · obtain ⟨original, used, rfl⟩ := Finset.mem_image.mp kept
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (enabled.taken_subset used))
  · intro physical member
    obtain ⟨original, used, rfl⟩ := Finset.mem_image.mp member
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (enabled.kept_subset used))
  · apply Finset.disjoint_left.mpr
    intro physical taken kept
    obtain ⟨original, read, rfl⟩ := Finset.mem_image.mp kept
    rcases Finset.mem_insert.mp taken with impossible | taken
    · cases impossible
    · obtain ⟨other, used, same⟩ := Finset.mem_image.mp taken
      have equal : other = original := Option.some.inj same
      subst other
      exact Finset.disjoint_left.mp enabled.apart used read
  · apply Finset.disjoint_left.mpr
    intro physical made present
    obtain ⟨original, created, rfl⟩ := Finset.mem_image.mp made
    rcases Finset.mem_insert.mp present with impossible | present
    · cases impossible
    · obtain ⟨other, visible, same⟩ := Finset.mem_image.mp present
      have equal : other = original := Option.some.inj same
      subst other
      exact Finset.disjoint_left.mp enabled.fresh created visible
  · intro query member
    cases member


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationRenaming
