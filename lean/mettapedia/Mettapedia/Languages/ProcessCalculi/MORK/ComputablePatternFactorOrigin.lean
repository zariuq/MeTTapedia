import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity

/-!
# Proof-relevant origin at an arbitrary positive-pattern premise

A successful compatible match must obtain a carrier row for every authored
premise.  The theorems below expose the carrier selected at one designated
premise, even when earlier premises have already extended the substitution.
This permits absence proofs for later premises without evaluating a complete
closed matcher.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Expressions with distinct fixed symbol heads cannot match, regardless of
their tails or the incoming substitution. -/
theorem cmatchAtom_expression_symbol_head_ne
    (substitution : Subst) (patternHead concreteHead : String)
    (patternTail concreteTail : List Atom)
    (distinct : patternHead ≠ concreteHead) :
    cmatchAtom substitution
        (.expression (.symbol patternHead :: patternTail))
        (.expression (.symbol concreteHead :: concreteTail)) = none := by
  simp [cmatchAtom, cmatchAtomList, distinct]

/-- A successful positive matcher obtains the designated premise from an
actual row of the input carrier. -/
theorem cmatchPattern_go_factor_origin
    (space : CSpace) (before : List Atom) (factor : Atom)
    (after : List Atom) (initial : Subst) (witnesses : List Atom)
    {final : Subst} {finalWitnesses : List Atom}
    (member : (final, finalWitnesses) ∈
      cmatchPattern.go space (before ++ factor :: after) initial witnesses) :
    ∃ beforeFactor afterFactor carrier,
      carrier ∈ space ∧
        cmatchAtom beforeFactor factor carrier = some afterFactor := by
  induction before generalizing initial witnesses with
  | nil =>
      simp only [List.nil_append, cmatchPattern.go, List.mem_flatMap] at member
      obtain ⟨⟨afterFactor, carrier⟩, matchedMember, _tailMember⟩ := member
      rw [List.mem_filterMap] at matchedMember
      obtain ⟨candidate, candidateMember, mapped⟩ := matchedMember
      simp only [Option.map_eq_some_iff] at mapped
      obtain ⟨matchedSubstitution, matched, equal⟩ := mapped
      cases equal
      exact ⟨initial, afterFactor, carrier, candidateMember, matched⟩
  | cons head tail induction =>
      simp only [List.cons_append, cmatchPattern.go,
        List.mem_flatMap] at member
      obtain ⟨⟨afterPrefix, carrier⟩, _prefixMatch, tailMember⟩ := member
      exact induction afterPrefix (carrier :: witnesses) tailMember

/-- If one designated premise cannot match any carrier row under any
substitution, the complete positive matcher has no result. -/
theorem cmatchPattern_go_eq_nil_of_factor_never_matches
    (space : CSpace) (before : List Atom) (factor : Atom)
    (after : List Atom) (initial : Subst) (witnesses : List Atom)
    (neverMatches : ∀ beforeFactor carrier, carrier ∈ space →
      cmatchAtom beforeFactor factor carrier = none) :
    cmatchPattern.go space (before ++ factor :: after) initial witnesses = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro result member
  obtain ⟨beforeFactor, afterFactor, carrier, carrierMember, matched⟩ :=
    cmatchPattern_go_factor_origin space before factor after initial witnesses member
  rw [neverMatches beforeFactor carrier carrierMember] at matched
  contradiction

/-- Input-spec specialization of designated-premise impossibility. -/
theorem cmatchInputSpec_compat_eq_nil_of_factor_never_matches
    (space : CSpace) (before : List Atom) (factor : Atom)
    (after : List Atom) (initial : Subst)
    (neverMatches : ∀ beforeFactor carrier, carrier ∈ space →
      cmatchAtom beforeFactor factor carrier = none) :
    cmatchInputSpec initial space
        (.compat (mkPattern (before ++ factor :: after))) = [] := by
  simpa only [cmatchInputSpec, mkPattern, cmatchPattern] using
    cmatchPattern_go_eq_nil_of_factor_never_matches space before factor after
      initial [] neverMatches

/-- Input-spec specialization of `cmatchPattern_go_factor_origin`. -/
theorem cmatchInputSpec_factor_origin
    (space : CSpace) (before : List Atom) (factor : Atom)
    (after : List Atom) {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec [] space
        (.compat (mkPattern (before ++ factor :: after)))).map Prod.fst) :
    ∃ beforeFactor afterFactor carrier,
      carrier ∈ space ∧
        cmatchAtom beforeFactor factor carrier = some afterFactor := by
  rw [List.mem_map] at member
  obtain ⟨⟨final, finalWitnesses⟩, matched, rfl⟩ := member
  exact cmatchPattern_go_factor_origin space before factor after [] [] matched

#print axioms cmatchAtom_expression_symbol_head_ne
#print axioms cmatchPattern_go_factor_origin
#print axioms cmatchPattern_go_eq_nil_of_factor_never_matches
#print axioms cmatchInputSpec_compat_eq_nil_of_factor_never_matches
#print axioms cmatchInputSpec_factor_origin

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
