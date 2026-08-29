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

#print axioms mem_cApplyReflectiveSinkBatch_append_add_of_row
#print axioms mem_cApplyReflectiveSinkBatch_append_add_cons_of_row

end Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
