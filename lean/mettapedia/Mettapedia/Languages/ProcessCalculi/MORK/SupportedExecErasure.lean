import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec

/-!
# Supported directive erasure

These lemmas expose the small list law used by remove-before-interpret
schedulers: consuming one supported directive erases exactly its decoded
candidate and leaves every other candidate in presentation order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open WQComputable

theorem extractSupportedSourceExecFact_atom {atom : Atom}
    {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact atom = some directive) :
    directive.atom = atom := by
  unfold extractSupportedSourceExecFact at decoded
  cases rawEq : extractRawExecFact atom with
  | none => simp [rawEq] at decoded
  | some raw =>
      have rawAtom : raw.atom = atom := by
        unfold extractRawExecFact at rawEq
        split at rawEq
        · exact (congrArg RawExecFact.atom (Option.some.inj rawEq)).symm
        · simp at rawEq
      simp only [rawEq] at decoded
      unfold decodeSupportedSourceExec at decoded
      cases inputEq : parseSupportedInput raw.inputExpr <;>
        simp [inputEq] at decoded
      cases templateEq : parseSupportedTemplate raw.templateExpr <;>
        simp [templateEq] at decoded
      subst directive
      exact rawAtom

/-- Membership in the decoded scheduler inventory retains the exact executable
atom that supplied the candidate. -/
theorem sourceExecFact_atom_mem_of_mem_supported
    {space : List Atom} {directive : SourceExecFact}
    (member : directive ∈ cSupportedSourceExecFacts space) :
    directive.atom ∈ space := by
  rcases List.mem_filterMap.mp member with
    ⟨atom, atomMember, decoded⟩
  have exactAtom := extractSupportedSourceExecFact_atom decoded
  simpa [exactAtom] using atomMember

/-- Exact executable-atom membership and successful decoding give membership
in the scheduler inventory.  This is the converse direction used when a
source transformation publishes a particular executable row. -/
theorem sourceExecFact_mem_supported_of_atom_mem
    {space : List Atom} {directive : SourceExecFact}
    (member : directive.atom ∈ space)
    (decoded : extractSupportedSourceExecFact directive.atom =
      some directive) :
    directive ∈ cSupportedSourceExecFacts space := by
  exact List.mem_filterMap.mpr ⟨directive.atom, member, decoded⟩

/-- Strict supported-directive decoding can succeed only on the ordinary
four-field executable syntax shell.  The parsed rule body remains opaque. -/
theorem extractSupportedSourceExecFact_exec_shape {atom : Atom}
    {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact atom = some directive) :
    ∃ location input output,
      atom = .expression [.symbol "exec", location, input, output] := by
  unfold extractSupportedSourceExecFact at decoded
  cases rawEq : extractRawExecFact atom with
  | none => simp [rawEq] at decoded
  | some raw =>
      have rawShape : ∃ location input output,
          atom = .expression [.symbol "exec", location, input, output] := by
        unfold extractRawExecFact at rawEq
        split at rawEq
        · exact ⟨_, _, _, rfl⟩
        · simp at rawEq
      exact rawShape

/-- A successfully decoded executable cannot have a different fixed syntax
head.  The directive payload remains completely opaque. -/
theorem supportedExecAtom_ne_expression_head
    {atom : Atom} {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact atom = some directive)
    (head : String) (tail : List Atom) (different : head ≠ "exec") :
    atom ≠ .expression (.symbol head :: tail) := by
  obtain ⟨location, input, output, shape⟩ :=
    extractSupportedSourceExecFact_exec_shape decoded
  rw [shape]
  intro equal
  injection equal with atomsEqual
  have headEqual : "exec" = head := by
    simpa using congrArg List.head? atomsEqual
  exact different headEqual.symm

/-- If supported-directive extraction preserves the full presentation length,
then every presented atom has a supported decoder witness.  This avoids
case-splitting on large concrete rule payloads when only their executable
syntax shell matters. -/
theorem exists_extractSupportedSourceExecFact_of_mem_of_full_length
    (space : List Atom)
    (full : (cSupportedSourceExecFacts space).length = space.length)
    {atom : Atom} (member : atom ∈ space) :
    ∃ directive, extractSupportedSourceExecFact atom = some directive := by
  unfold cSupportedSourceExecFacts at full
  induction space with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      cases decoded : extractSupportedSourceExecFact head with
      | none =>
          simp only [List.filterMap_cons, decoded, List.length_cons] at full
          have bound := List.length_filterMap_le
            extractSupportedSourceExecFact tail
          omega
      | some directive =>
          rcases member with rfl | tailMember
          · exact ⟨directive, decoded⟩
          · apply induction
            · simp only [List.filterMap_cons, decoded, List.length_cons] at full
              omega
            · exact tailMember

/-- Decoding commutes with consuming one successfully decoded directive.
This is independent of the directive's rule body and scheduler key. -/
theorem cSupportedSourceExecFacts_erase (space : List Atom)
    (directive : SourceExecFact)
    (decoded : extractSupportedSourceExecFact directive.atom =
      some directive) :
    cSupportedSourceExecFacts (space.erase directive.atom) =
      (cSupportedSourceExecFacts space).erase directive := by
  unfold cSupportedSourceExecFacts
  induction space with
  | nil => rfl
  | cons head tail induction =>
      by_cases headEq : head = directive.atom
      · subst head
        simp [decoded]
      · have headBeq : ¬(head == directive.atom) := by
          simpa using headEq
        rw [List.erase_cons_tail headBeq]
        simp only [List.filterMap_cons]
        cases headDecoded : extractSupportedSourceExecFact head with
        | none => simp [induction]
        | some headDirective =>
            have directiveNe : headDirective ≠ directive := by
              intro equal
              subst headDirective
              exact headEq
                (extractSupportedSourceExecFact_atom headDecoded).symm
            simp [directiveNe, induction]

/-- Supported-directive extraction preserves duplicate freedom whenever the
underlying exact atom presentation is duplicate-free. -/
theorem cSupportedSourceExecFacts_nodup_of_space_nodup
    {space : List Atom} (nodup : space.Nodup) :
    (cSupportedSourceExecFacts space).Nodup := by
  unfold cSupportedSourceExecFacts
  induction space with
  | nil => simp
  | cons atom tail induction =>
      have atomFresh : atom ∉ tail := nodup.notMem
      have tailNodup : tail.Nodup := nodup.of_cons
      simp only [List.filterMap_cons]
      cases decoded : extractSupportedSourceExecFact atom with
      | none => exact induction tailNodup
      | some directive =>
          apply List.nodup_cons.mpr
          constructor
          · intro member
            rcases List.mem_filterMap.mp member with
              ⟨candidate, candidateMember, candidateDecoded⟩
            have atomEq := extractSupportedSourceExecFact_atom decoded
            have candidateEq :=
              extractSupportedSourceExecFact_atom candidateDecoded
            exact atomFresh (candidateEq.symm.trans atomEq ▸ candidateMember)
          · exact induction tailNodup

#print axioms extractSupportedSourceExecFact_atom
#print axioms sourceExecFact_atom_mem_of_mem_supported
#print axioms extractSupportedSourceExecFact_exec_shape
#print axioms supportedExecAtom_ne_expression_head
#print axioms exists_extractSupportedSourceExecFact_of_mem_of_full_length
#print axioms cSupportedSourceExecFacts_erase
#print axioms sourceExecFact_mem_supported_of_atom_mem
#print axioms cSupportedSourceExecFacts_nodup_of_space_nodup

end Mettapedia.Languages.ProcessCalculi.MORK
