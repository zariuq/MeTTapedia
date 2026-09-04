import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchLastAdd

/-!
# Positive outputs of one reflective source directive

A target-specific proof may identify one successful matcher row and one add
sink without unfolding the reflective executor.  Later add-only sinks preserve
the emitted atom.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

theorem mem_cFireReflectiveSourceExecFact_of_add_sink
    (space : List Atom) (directive : SourceExecFact)
    (before : List Sink) (authored candidate : Atom) (rest : List Sink)
    (sinksExact : directive.rule.tmpl.sinks =
      before ++ .add authored :: rest)
    (substitution : Subst)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (directive.atom :: space.erase directive.atom)
        directive.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution authored = some candidate)
    (restAdd : ∀ sink ∈ rest, ∃ later, sink = .add later) :
    candidate ∈ cFireReflectiveSourceExecFact space directive := by
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [sinksExact]
  exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
    substitution rowMember instantiates restAdd

theorem mem_cFireReflectiveSourceExecFact_of_last_add
    (space : List Atom) (directive : SourceExecFact)
    (before : List Sink) (authored candidate : Atom)
    (sinksExact : directive.rule.tmpl.sinks = before ++ [.add authored])
    (substitution : Subst)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (directive.atom :: space.erase directive.atom)
        directive.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution authored = some candidate) :
    candidate ∈ cFireReflectiveSourceExecFact space directive := by
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [sinksExact]
  exact mem_cApplyReflectiveSinkBatch_append_add_of_row _ _ before authored
    candidate substitution rowMember instantiates

/-- A successful row publishes any selected member of an add-only suffix of
the authored sink batch.  Earlier sinks may add or remove unrelated atoms. -/
theorem mem_cFireReflectiveSourceExecFact_of_add_only_suffix_member
    (space : List Atom) (directive : SourceExecFact)
    (before adds : List Sink) (authored candidate : Atom)
    (sinksExact : directive.rule.tmpl.sinks = before ++ adds)
    (substitution : Subst)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (directive.atom :: space.erase directive.atom)
        directive.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution authored = some candidate)
    (allAdd : ∀ sink ∈ adds, ∃ atom, sink = .add atom)
    (authoredMember : .add authored ∈ adds) :
    candidate ∈ cFireReflectiveSourceExecFact space directive := by
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [sinksExact]
  exact mem_cApplyReflectiveSinkBatch_append_add_only_member _ _ before adds
    authored candidate substitution rowMember instantiates allAdd
      authoredMember

#print axioms mem_cFireReflectiveSourceExecFact_of_add_sink
#print axioms mem_cFireReflectiveSourceExecFact_of_last_add
#print axioms mem_cFireReflectiveSourceExecFact_of_add_only_suffix_member

end Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
