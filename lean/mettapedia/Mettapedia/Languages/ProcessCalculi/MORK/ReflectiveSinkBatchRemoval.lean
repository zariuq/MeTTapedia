import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution

/-!
# Removal and absence frames for reflective sink batches

These lemmas isolate the support algebra needed by consume/emit MM2 rules.
A matched remove sink eliminates its instantiated atom.  A later sequence of
remove sinks and add sinks that cannot instantiate that atom preserves the
absence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open WQComputable

/-- Substitution preserves a literal expression head, so templates headed by
different symbols can never instantiate to the same atom. -/
theorem instantiateTemplateAtom?_expression_symbol_head_ne
    (substitution : Subst) (authoredHead candidateHead : String)
    (authoredTail candidateTail : List Atom)
    (different : authoredHead ≠ candidateHead) :
    instantiateTemplateAtom? substitution
        (.expression (.symbol authoredHead :: authoredTail)) ≠
      some (.expression (.symbol candidateHead :: candidateTail)) := by
  unfold instantiateTemplateAtom?
  split
  · simp [applySubst, applySubst.applySubstList, different]
  · simp_all

@[simp] theorem mem_cSubtractSupport_iff (candidate : Atom)
    (space staged : List Atom) :
    candidate ∈ cSubtractSupport space staged ↔
      candidate ∈ space ∧ candidate ∉ staged := by
  simp [cSubtractSupport]

/-- A remove sink eliminates an atom instantiated by any matcher row,
independently of whether that atom was present before the sink. -/
theorem not_mem_cFinalizeSupportSink_remove_of_row
    (rows : List Subst) (space : List Atom) (authored candidate : Atom)
    (substitution : Subst)
    (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateTemplateAtom? substitution authored = some candidate) :
    candidate ∉ cFinalizeSupportSink (.remove authored)
      (rows.foldl (stageReflectiveSupportSink (.remove authored)) []) space := by
  rw [cFinalizeSupportSink, mem_cSubtractSupport_iff]
  intro member
  exact member.2 ((mem_foldl_stageReflectiveSupportSink_iff
    (.remove authored) rows [] candidate).2
      (Or.inr ⟨substitution, rowMember, instantiates⟩))

/-- A suffix containing only remove sinks and add sinks that cannot produce
`candidate` preserves its absence. -/
theorem not_mem_cApplyReflectiveSinkBatch_of_remove_or_nonproducing_add
    (rows : List Subst) {space : List Atom} {sinks : List Sink}
    {candidate : Atom}
    (safe : ∀ sink ∈ sinks,
      (∃ authored, sink = .remove authored) ∨
        ∃ authored, sink = .add authored ∧
          ∀ substitution ∈ rows,
            instantiateTemplateAtom? substitution authored ≠ some candidate)
    (absent : candidate ∉ space) :
    candidate ∉ cApplyReflectiveSinkBatch rows space sinks := by
  induction sinks generalizing space with
  | nil => exact absent
  | cons sink rest induction =>
      have restSafe : ∀ later ∈ rest,
          (∃ authored, later = .remove authored) ∨
            ∃ authored, later = .add authored ∧
              ∀ substitution ∈ rows,
                instantiateTemplateAtom? substitution authored ≠
                  some candidate := by
        intro later laterMember
        exact safe later (by simp [laterMember])
      rcases safe sink (by simp) with remove | add
      · obtain ⟨authored, rfl⟩ := remove
        simp only [cApplyReflectiveSinkBatch]
        apply induction restSafe
        rw [cFinalizeSupportSink, mem_cSubtractSupport_iff]
        exact fun member => absent member.1
      · obtain ⟨authored, rfl, nonproducing⟩ := add
        simp only [cApplyReflectiveSinkBatch]
        apply induction restSafe
        rw [cFinalizeSupportSink, mem_cUnionSupport_iff]
        rintro (member | staged)
        · exact absent member
        · rw [mem_foldl_stageReflectiveSupportSink_iff] at staged
          rcases staged with impossible | ⟨substitution, rowMember,
              instantiates⟩
          · simp at impossible
          · exact nonproducing substitution rowMember instantiates

/-- A sink batch preserves an existing atom when every sink is either an add
or a remove whose template cannot instantiate that atom on any matcher row.
This is the positive frame dual of absence preservation above. -/
theorem mem_cApplyReflectiveSinkBatch_of_add_or_nonremoving_remove
    (rows : List Subst) {space : List Atom} {sinks : List Sink}
    {candidate : Atom}
    (safe : ∀ sink ∈ sinks,
      (∃ authored, sink = .add authored) ∨
        ∃ authored, sink = .remove authored ∧
          ∀ substitution ∈ rows,
            instantiateTemplateAtom? substitution authored ≠ some candidate)
    (present : candidate ∈ space) :
    candidate ∈ cApplyReflectiveSinkBatch rows space sinks := by
  induction sinks generalizing space with
  | nil => exact present
  | cons sink rest induction =>
      have restSafe : ∀ later ∈ rest,
          (∃ authored, later = .add authored) ∨
            ∃ authored, later = .remove authored ∧
              ∀ substitution ∈ rows,
                instantiateTemplateAtom? substitution authored ≠
                  some candidate := by
        intro later laterMember
        exact safe later (by simp [laterMember])
      rcases safe sink (by simp) with add | remove
      · obtain ⟨authored, rfl⟩ := add
        simp only [cApplyReflectiveSinkBatch]
        apply induction restSafe
        rw [cFinalizeSupportSink, mem_cUnionSupport_iff]
        exact Or.inl present
      · obtain ⟨authored, rfl, nonremoving⟩ := remove
        simp only [cApplyReflectiveSinkBatch]
        apply induction restSafe
        rw [cFinalizeSupportSink, mem_cSubtractSupport_iff]
        refine ⟨present, ?_⟩
        intro staged
        rw [mem_foldl_stageReflectiveSupportSink_iff] at staged
        rcases staged with impossible | ⟨substitution, rowMember,
            instantiates⟩
        · simp at impossible
        · exact nonremoving substitution rowMember instantiates

/-- After a matched leading remove, a safe suffix cannot recreate the removed
atom. -/
theorem not_mem_cApplyReflectiveSinkBatch_remove_cons_of_row
    (rows : List Subst) (space : List Atom) (authored candidate : Atom)
    (rest : List Sink) (substitution : Subst)
    (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateTemplateAtom? substitution authored = some candidate)
    (restSafe : ∀ sink ∈ rest,
      (∃ later, sink = .remove later) ∨
        ∃ later, sink = .add later ∧
          ∀ laterSubstitution ∈ rows,
            instantiateTemplateAtom? laterSubstitution later ≠
              some candidate) :
    candidate ∉ cApplyReflectiveSinkBatch rows space
      (.remove authored :: rest) := by
  simp only [cApplyReflectiveSinkBatch]
  exact not_mem_cApplyReflectiveSinkBatch_of_remove_or_nonproducing_add
    rows restSafe
      (not_mem_cFinalizeSupportSink_remove_of_row rows space authored candidate
        substitution rowMember instantiates)

/-- A matched remove at any position eliminates its instantiated atom when
the remaining suffix cannot recreate that atom.  The preceding sinks are
irrelevant because the remove establishes absence at its own boundary. -/
theorem not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    (rows : List Subst) (space : List Atom) (before : List Sink)
    (authored candidate : Atom) (rest : List Sink) (substitution : Subst)
    (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateTemplateAtom? substitution authored = some candidate)
    (restSafe : ∀ sink ∈ rest,
      (∃ later, sink = .remove later) ∨
        ∃ later, sink = .add later ∧
          ∀ laterSubstitution ∈ rows,
            instantiateTemplateAtom? laterSubstitution later ≠
              some candidate) :
    candidate ∉ cApplyReflectiveSinkBatch rows space
      (before ++ .remove authored :: rest) := by
  induction before generalizing space with
  | nil =>
      exact not_mem_cApplyReflectiveSinkBatch_remove_cons_of_row
        rows space authored candidate rest substitution rowMember instantiates
          restSafe
  | cons sink before induction =>
      simp only [List.cons_append, cApplyReflectiveSinkBatch]
      exact induction _

#print axioms mem_cSubtractSupport_iff
#print axioms instantiateTemplateAtom?_expression_symbol_head_ne
#print axioms not_mem_cFinalizeSupportSink_remove_of_row
#print axioms not_mem_cApplyReflectiveSinkBatch_of_remove_or_nonproducing_add
#print axioms mem_cApplyReflectiveSinkBatch_of_add_or_nonremoving_remove
#print axioms not_mem_cApplyReflectiveSinkBatch_remove_cons_of_row
#print axioms not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row

end Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
