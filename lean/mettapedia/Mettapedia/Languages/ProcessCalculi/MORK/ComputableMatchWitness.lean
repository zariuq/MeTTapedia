import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSourceExecAdd

/-!
# Symbolic witnesses for computable compatible matching

Concrete evaluation of an unordered multi-factor match explores every
candidate ordering in the list presentation.  A proof that already knows one
exact witness per factor should instead follow that witness path directly.
This module records such paths and proves that they occur in the computable
matcher without enumerating unrelated alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-- One explicit left-to-right witness path through a compatible pattern. -/
inductive MatchWitnessPath (space : CSpace) :
    List Atom → Subst → List Atom → Subst → List Atom → Prop
  | nil (substitution witnesses) :
      MatchWitnessPath space [] substitution witnesses substitution witnesses
  | cons {pattern : Atom} {patterns : List Atom}
      {before after : Subst} {witness : Atom}
      {witnesses finalWitnesses : List Atom} {final : Subst}
      (witness_mem : witness ∈ space)
      (match_eq : cmatchAtom before pattern witness = some after)
      (rest : MatchWitnessPath space patterns after (witness :: witnesses)
        final finalWitnesses) :
      MatchWitnessPath space (pattern :: patterns) before witnesses final
        finalWitnesses

private theorem matchWitnessPath_mem_go
    {space : CSpace} {patterns : List Atom} {before final : Subst}
    {witnesses finalWitnesses : List Atom}
    (path : MatchWitnessPath space patterns before witnesses final
      finalWitnesses) :
    (final, finalWitnesses) ∈
      cmatchPattern.go space patterns before witnesses := by
  induction path with
  | nil => simp [cmatchPattern.go]
  | @cons pattern patterns before after witness witnesses finalWitnesses final
      witness_mem match_eq rest induction =>
      simp only [cmatchPattern.go, List.mem_flatMap]
      refine ⟨(after, witness), ?_, induction⟩
      exact List.mem_filterMap.mpr
        ⟨witness, witness_mem, by simp [match_eq]⟩

theorem matchWitnessPath_mem_cmatchPattern
    {space : CSpace} {patterns : List Atom} {before final : Subst}
    {finalWitnesses : List Atom}
    (path : MatchWitnessPath space patterns before [] final
      finalWitnesses) :
    (final, finalWitnesses) ∈
      cmatchPattern before space { atoms := patterns } := by
  exact matchWitnessPath_mem_go path

theorem matchWitnessPath_mem_cmatchInputSpec
    {space : CSpace} {patterns : List Atom} {before final : Subst}
    {finalWitnesses : List Atom}
    (path : MatchWitnessPath space patterns before [] final
      finalWitnesses) :
    final ∈
      (cmatchInputSpec before space (.compat { atoms := patterns })).map
        Prod.fst := by
  rw [List.mem_map]
  exact ⟨(final, finalWitnesses), by
    exact matchWitnessPath_mem_cmatchPattern path, rfl⟩

#print axioms matchWitnessPath_mem_cmatchPattern
#print axioms matchWitnessPath_mem_cmatchInputSpec

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
