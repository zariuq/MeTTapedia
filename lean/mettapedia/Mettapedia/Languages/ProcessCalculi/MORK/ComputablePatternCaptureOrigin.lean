import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity

/-!
# Proof-relevant origin at an arbitrary positive-pattern premise

A compatible matcher processes its premises from left to right.  A value
captured by any selected premise remains present in the final substitution,
because the remaining matcher only extends existing bindings.  This is the
generic provenance seam for rules that republish an opaque payload captured
after ordinary data premises.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-- A value captured at one designated premise of a successful positive
matcher originates in an actual carrier row and survives in the final
substitution.  Prefix premises may establish other bindings first. -/
theorem cmatchPattern_go_capture_origin
    (captures : Atom → Atom → Prop) (variableName : String)
    (space : CSpace) (before : List Atom) (capturePattern : Atom)
    (after : List Atom) (initial : Subst) (witnesses : List Atom)
    {final : Subst} {finalWitnesses : List Atom}
    (member : (final, finalWitnesses) ∈
      cmatchPattern.go space (before ++ capturePattern :: after) initial
        witnesses)
    (capture : ∀ {beforeCapture afterCapture carrier},
      cmatchAtom beforeCapture capturePattern carrier = some afterCapture →
        ∃ value,
          Subst.lookup afterCapture variableName = some value ∧
            captures carrier value) :
    ∃ carrier value,
      carrier ∈ space ∧
        Subst.lookup final variableName = some value ∧
        captures carrier value := by
  induction before generalizing initial witnesses with
  | nil =>
      simp only [List.nil_append, cmatchPattern.go, List.mem_flatMap] at member
      obtain ⟨⟨afterCapture, carrier⟩, matchedMember, tailMember⟩ := member
      rw [List.mem_filterMap] at matchedMember
      obtain ⟨candidate, candidateMember, mapped⟩ := matchedMember
      simp only [Option.map_eq_some_iff] at mapped
      obtain ⟨matchedSubstitution, matched, equal⟩ := mapped
      cases equal
      obtain ⟨value, lookup, captured⟩ := capture matched
      have lookupExtension := cmatchPattern_go_lookupExtends tailMember
      exact ⟨carrier, value, candidateMember,
        lookupExtension variableName value lookup, captured⟩
  | cons head tail ih =>
      simp only [List.cons_append, cmatchPattern.go,
        List.mem_flatMap] at member
      obtain ⟨⟨afterPrefix, carrier⟩, _prefixMatch, tailMember⟩ := member
      exact ih afterPrefix (carrier :: witnesses) tailMember

/-- Input-spec specialization of `cmatchPattern_go_capture_origin`.  The
returned carrier is a concrete member of the matched space, not an auxiliary
witness supplied by the caller. -/
theorem cmatchInputSpec_capture_origin
    (captures : Atom → Atom → Prop) (variableName : String)
    (space : CSpace) (before : List Atom) (capturePattern : Atom)
    (after : List Atom) {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec [] space
        (.compat (mkPattern (before ++ capturePattern :: after)))).map
          Prod.fst)
    (capture : ∀ {beforeCapture afterCapture carrier},
      cmatchAtom beforeCapture capturePattern carrier = some afterCapture →
        ∃ value,
          Subst.lookup afterCapture variableName = some value ∧
            captures carrier value) :
    ∃ carrier value,
      carrier ∈ space ∧
        Subst.lookup substitution variableName = some value ∧
        captures carrier value := by
  rw [List.mem_map] at member
  obtain ⟨⟨final, finalWitnesses⟩, matched, rfl⟩ := member
  exact cmatchPattern_go_capture_origin captures variableName space before
    capturePattern after [] [] matched capture

#print axioms cmatchPattern_go_capture_origin
#print axioms cmatchInputSpec_capture_origin

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
