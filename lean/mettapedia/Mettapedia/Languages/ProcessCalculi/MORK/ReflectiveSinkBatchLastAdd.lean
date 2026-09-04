import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution

/-!
# A terminal reflective add survives an arbitrary sink prefix

This small frame lemma avoids reducing a complete reflective state when the
last sink of a directive publishes the observation of interest.  Earlier
sinks may add or remove unrelated atoms; the final add still inserts every
successful instantiation into the resulting finite support.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- If the final sink is an add and one matching row instantiates its
template, the instantiated atom belongs to the result after any preceding
sink batch. -/
theorem mem_cApplyReflectiveSinkBatch_append_add_of_row
    (rows : List Subst) (space : List Atom) (before : List Sink)
    (authored candidate : Atom) (substitution : Subst)
    (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateTemplateAtom? substitution authored = some candidate) :
    candidate ∈ cApplyReflectiveSinkBatch rows space
      (before ++ [.add authored]) := by
  induction before generalizing space with
  | nil =>
      exact mem_cApplyReflectiveSinkBatch_add_cons_of_row
        rows space authored candidate [] substitution rowMember instantiates
        (by simp)
  | cons sink rest induction =>
      simp only [List.cons_append, cApplyReflectiveSinkBatch]
      apply induction

/-- A successful add at an arbitrary sink position survives when every later
sink is also an add.  The prefix may contain any supported sink operations. -/
theorem mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
    (rows : List Subst) (space : List Atom) (before : List Sink)
    (authored candidate : Atom) (rest : List Sink) (substitution : Subst)
    (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateTemplateAtom? substitution authored = some candidate)
    (restAdd : ∀ sink ∈ rest, ∃ later, sink = .add later) :
    candidate ∈ cApplyReflectiveSinkBatch rows space
      (before ++ .add authored :: rest) := by
  induction before generalizing space with
  | nil =>
      exact mem_cApplyReflectiveSinkBatch_add_cons_of_row
        rows space authored candidate rest substitution rowMember instantiates
          restAdd
  | cons sink before induction =>
      simp only [List.cons_append, cApplyReflectiveSinkBatch]
      exact induction _

/-- An add-only batch publishes every authored add that one successful matcher
row instantiates.  The selected add need not be first or last. -/
theorem mem_cApplyReflectiveSinkBatch_of_add_only_member
    (rows : List Subst) (space : List Atom) (sinks : List Sink)
    (authored candidate : Atom) (substitution : Subst)
    (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateTemplateAtom? substitution authored = some candidate)
    (allAdd : ∀ sink ∈ sinks, ∃ atom, sink = .add atom)
    (authoredMember : .add authored ∈ sinks) :
    candidate ∈ cApplyReflectiveSinkBatch rows space sinks := by
  induction sinks generalizing space with
  | nil => simp at authoredMember
  | cons sink rest induction =>
      obtain ⟨current, rfl⟩ := allAdd sink (by simp)
      have restAdd : ∀ later ∈ rest, ∃ atom, later = .add atom := by
        intro later member
        exact allAdd later (by simp [member])
      simp only [List.mem_cons] at authoredMember
      rcases authoredMember with equal | member
      · have currentEqual : current = authored := Sink.add.inj equal.symm
        subst current
        exact mem_cApplyReflectiveSinkBatch_add_cons_of_row
          rows space authored candidate rest substitution rowMember
            instantiates restAdd
      · simp only [cApplyReflectiveSinkBatch]
        exact induction _ restAdd member

/-- An arbitrary sink prefix followed by an add-only suffix still publishes
every selected add from that suffix. -/
theorem mem_cApplyReflectiveSinkBatch_append_add_only_member
    (rows : List Subst) (space : List Atom) (before adds : List Sink)
    (authored candidate : Atom) (substitution : Subst)
    (rowMember : substitution ∈ rows)
    (instantiates :
      instantiateTemplateAtom? substitution authored = some candidate)
    (allAdd : ∀ sink ∈ adds, ∃ atom, sink = .add atom)
    (authoredMember : .add authored ∈ adds) :
    candidate ∈ cApplyReflectiveSinkBatch rows space (before ++ adds) := by
  induction before generalizing space with
  | nil =>
      exact mem_cApplyReflectiveSinkBatch_of_add_only_member rows space adds
        authored candidate substitution rowMember instantiates allAdd
          authoredMember
  | cons sink before induction =>
      simp only [List.cons_append, cApplyReflectiveSinkBatch]
      exact induction _

#print axioms mem_cApplyReflectiveSinkBatch_append_add_of_row
#print axioms mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
#print axioms mem_cApplyReflectiveSinkBatch_of_add_only_member
#print axioms mem_cApplyReflectiveSinkBatch_append_add_only_member

end Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
