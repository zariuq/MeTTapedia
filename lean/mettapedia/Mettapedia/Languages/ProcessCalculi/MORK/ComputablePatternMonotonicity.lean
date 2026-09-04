import Mettapedia.Languages.ProcessCalculi.MORK.Conformance
import Mettapedia.Languages.ProcessCalculi.MORK.InvertibleHead

/-!
# Monotonicity of computable positive pattern matching

Adding atoms to a finite list presentation cannot destroy a positive
simultaneous match.  The theorem is intentionally scoped to `Pattern`, whose
factors are all positive; negative source factors require a different law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Every row produced over a smaller positive-pattern space is also produced
over a larger space containing all of its atoms. -/
theorem cmatchPattern_mono
    (σ₀ : Subst) (small large : CSpace) (p : Pattern)
    (included : ∀ atom ∈ small, atom ∈ large)
    (σ : Subst) (consumed : List Atom)
    (matched : (σ, consumed) ∈ cmatchPattern σ₀ small p) :
    (σ, consumed) ∈ cmatchPattern σ₀ large p := by
  simp only [cmatchPattern] at matched ⊢
  suffices h : ∀ (patterns : List Atom) (σIn : Subst)
      (consumedIn : List Atom) (σOut : Subst) (consumedOut : List Atom),
      (σOut, consumedOut) ∈
          cmatchPattern.go small patterns σIn consumedIn →
        (σOut, consumedOut) ∈
          cmatchPattern.go large patterns σIn consumedIn by
    exact h p.atoms σ₀ [] σ consumed matched
  intro patterns
  induction patterns with
  | nil =>
      intro σIn consumedIn σOut consumedOut member
      simpa only [cmatchPattern.go] using member
  | cons pattern rest induction =>
      intro σIn consumedIn σOut consumedOut member
      simp only [cmatchPattern.go] at member ⊢
      rw [List.mem_flatMap] at member ⊢
      obtain ⟨⟨σMid, atom⟩, foundSmall, continued⟩ := member
      refine ⟨(σMid, atom), ?_, induction σMid (atom :: consumedIn)
        σOut consumedOut continued⟩
      rw [List.mem_filterMap] at foundSmall ⊢
      obtain ⟨concrete, concreteSmall, matchedAtom⟩ := foundSmall
      exact ⟨concrete, included concrete concreteSmall, matchedAtom⟩

/-- Appending rows that cannot match any premise of a positive pattern leaves
the complete matcher result unchanged.  The hypothesis is substitution-aware:
it rules out a late row becoming relevant only after earlier premises extend
the current substitution. -/
theorem cmatchPattern_append_of_right_never_matches
    (σ₀ : Subst) (base extra : CSpace) (p : Pattern)
    (irrelevant : ∀ (σ : Subst) (pattern : Atom), pattern ∈ p.atoms →
      ∀ atom ∈ extra, cmatchAtom σ pattern atom = none) :
    cmatchPattern σ₀ (base ++ extra) p = cmatchPattern σ₀ base p := by
  simp only [cmatchPattern]
  suffices h : ∀ (patterns : List Atom),
      (∀ pattern ∈ patterns, pattern ∈ p.atoms) →
      ∀ (σ : Subst) (consumed : List Atom),
        cmatchPattern.go (base ++ extra) patterns σ consumed =
          cmatchPattern.go base patterns σ consumed by
    exact h p.atoms (fun _ member => member) σ₀ []
  intro patterns subset
  induction patterns with
  | nil =>
      intro σ consumed
      rfl
  | cons pattern rest induction =>
      intro σ consumed
      simp only [cmatchPattern.go, List.filterMap_append]
      have extraEmpty :
          extra.filterMap (fun atom => (cmatchAtom σ pattern atom).map (·, atom)) =
            [] := by
        rw [List.filterMap_eq_nil_iff]
        intro atom atomMember
        rw [irrelevant σ pattern (subset pattern (by simp)) atom atomMember]
        rfl
      rw [extraEmpty, List.append_nil]
      apply List.flatMap_congr
      intro pair pairMember
      rcases pair with ⟨σ', atom⟩
      exact induction (fun candidate member =>
        subset candidate (List.mem_cons_of_mem pattern member)) σ' (atom :: consumed)

/-! ## Proof-relevant matcher origin -/

/-- A successful computable positive-pattern suffix only extends the
substitution with which that suffix began.  In particular, bindings selected
by an earlier premise cannot be silently replaced by later premises. -/
theorem cmatchPattern_go_lookupExtends
    {space : CSpace} {patterns : List Atom} {initial : Subst}
    {witnesses : List Atom} {final : Subst} {finalWitnesses : List Atom}
    (member : (final, finalWitnesses) ∈
      cmatchPattern.go space patterns initial witnesses) :
    final.lookupExtends initial := by
  induction patterns generalizing initial witnesses with
  | nil =>
      simp only [cmatchPattern.go, List.mem_singleton, Prod.mk.injEq] at member
      rcases member with ⟨rfl, _⟩
      exact fun _ _ lookup => lookup
  | cons pattern rest induction =>
      simp only [cmatchPattern.go, List.mem_flatMap] at member
      obtain ⟨⟨afterHead, atom⟩, matchedMember, tailMember⟩ := member
      rw [List.mem_filterMap] at matchedMember
      obtain ⟨candidate, _candidateMember, mapped⟩ := matchedMember
      simp only [Option.map_eq_some_iff] at mapped
      obtain ⟨matchedSubstitution, matched, equal⟩ := mapped
      cases equal
      rw [cmatchAtom_eq_matchAtom] at matched
      exact Subst.lookupExtends_trans (matchAtom_lookupExtends matched)
        (induction tailMember)

/-- Every successful nonempty compatible match retains an actual first
witness from the input carrier, together with the substitution produced by
that witness and the fact that the final substitution extends it.  This is
the generic provenance seam for rules that later republish an opaque value
captured by their first premise. -/
theorem cmatchInputSpec_first_match_origin
    {space : CSpace} {first : Atom} {rest : List Atom}
    {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec [] space
        (.compat (mkPattern (first :: rest)))).map Prod.fst) :
    ∃ afterFirst firstAtom,
      firstAtom ∈ space ∧
        cmatchAtom [] first firstAtom = some afterFirst ∧
        substitution.lookupExtends afterFirst := by
  rw [List.mem_map] at member
  obtain ⟨⟨found, foundWitnesses⟩, foundMember, foundEq⟩ := member
  change found = substitution at foundEq
  subst substitution
  simp only [cmatchInputSpec, mkPattern, cmatchPattern,
    cmatchPattern.go, List.mem_flatMap] at foundMember
  obtain ⟨⟨afterFirst, firstAtom⟩, firstMatch, tailMember⟩ := foundMember
  rw [List.mem_filterMap] at firstMatch
  obtain ⟨candidate, firstMember, mapped⟩ := firstMatch
  simp only [Option.map_eq_some_iff] at mapped
  obtain ⟨matchedSubstitution, firstMatched, equal⟩ := mapped
  cases equal
  exact ⟨afterFirst, firstAtom, firstMember, firstMatched,
    cmatchPattern_go_lookupExtends tailMember⟩

/-- A relation witnessed by a value captured from the first matched atom is
still witnessed by the final substitution returned after all later premises.
The matcher may refine the environment, but it cannot mint or replace the
captured value. -/
theorem cmatchInputSpec_first_capture_origin
    (captures : Atom → Atom → Prop) (variableName : String)
    {space : CSpace} {first : Atom} {rest : List Atom}
    {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec [] space
        (.compat (mkPattern (first :: rest)))).map Prod.fst)
    (firstCapture : ∀ {afterFirst firstAtom},
      cmatchAtom [] first firstAtom = some afterFirst →
        ∃ value, Subst.lookup afterFirst variableName = some value ∧
          captures firstAtom value) :
    ∃ firstAtom value,
      firstAtom ∈ space ∧
        Subst.lookup substitution variableName = some value ∧
        captures firstAtom value := by
  obtain ⟨afterFirst, firstAtom, firstMember, firstMatched, extendsSubst⟩ :=
    cmatchInputSpec_first_match_origin member
  obtain ⟨value, lookup, captured⟩ := firstCapture firstMatched
  exact ⟨firstAtom, value, firstMember,
    extendsSubst variableName value lookup,
    captured⟩

/-! ## Canonical generated matcher rows -/

/-- A list of authored patterns matches the pointwise image of one compatible
ground substitution when those concrete rows are present in the carrier.
This avoids rebuilding a long, target-specific matcher derivation for every
generated finite rule surface. -/
theorem cmatchPattern_go_appliedSubst
    (targetSubstitution : Subst) {space : CSpace}
    (patterns : List Atom) (initial : Subst) (witnesses : List Atom)
    (compatible : initial.compatWith targetSubstitution)
    (ground : ∀ pattern ∈ patterns,
      isGroundAtom (applySubst targetSubstitution pattern) = true)
    (present : ∀ pattern ∈ patterns,
      applySubst targetSubstitution pattern ∈ space) :
    ∃ final finalWitnesses,
      (final, finalWitnesses) ∈
          cmatchPattern.go space patterns initial witnesses ∧
        final.compatWith targetSubstitution := by
  induction patterns generalizing initial witnesses with
  | nil =>
      exact ⟨initial, witnesses, by simp [cmatchPattern.go], compatible⟩
  | cons pattern rest induction =>
      have patternGround := ground pattern (by simp)
      obtain ⟨afterPattern, relational, afterCompatible,
          _appliedExact⟩ :=
        matchAtomRel_self_compat initial pattern targetSubstitution compatible
          patternGround
      obtain ⟨final, finalWitnesses, tailMember, finalCompatible⟩ :=
        induction afterPattern (applySubst targetSubstitution pattern :: witnesses)
          afterCompatible
          (fun candidate member => ground candidate (by simp [member]))
          (fun candidate member => present candidate (by simp [member]))
      refine ⟨final, finalWitnesses, ?_, finalCompatible⟩
      simp only [cmatchPattern.go, List.mem_flatMap]
      refine ⟨(afterPattern, applySubst targetSubstitution pattern), ?_,
        tailMember⟩
      rw [List.mem_filterMap]
      refine ⟨applySubst targetSubstitution pattern,
        present pattern (by simp), ?_⟩
      rw [cmatchAtom_eq_matchAtom, matchAtom_complete relational]
      rfl

/-- Empty-environment specialization for an ordinary compatible input. -/
theorem cmatchInputSpec_appliedSubst_nonempty
    (targetSubstitution : Subst) (space : CSpace) (patterns : List Atom)
    (ground : ∀ pattern ∈ patterns,
      isGroundAtom (applySubst targetSubstitution pattern) = true)
    (present : ∀ pattern ∈ patterns,
      applySubst targetSubstitution pattern ∈ space) :
    ∃ final finalWitnesses,
      (final, finalWitnesses) ∈
          cmatchInputSpec [] space (.compat (mkPattern patterns)) ∧
        final.compatWith targetSubstitution := by
  have emptyCompatible : Subst.compatWith [] targetSubstitution := by
    intro variableName atom lookup
    simp [Subst.lookup] at lookup
  simpa [cmatchInputSpec, mkPattern, cmatchPattern] using
    cmatchPattern_go_appliedSubst targetSubstitution patterns [] []
      emptyCompatible ground present

#print axioms cmatchPattern_mono
#print axioms cmatchPattern_append_of_right_never_matches
#print axioms cmatchPattern_go_lookupExtends
#print axioms cmatchInputSpec_first_match_origin
#print axioms cmatchInputSpec_first_capture_origin
#print axioms cmatchPattern_go_appliedSubst
#print axioms cmatchInputSpec_appliedSubst_nonempty

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
