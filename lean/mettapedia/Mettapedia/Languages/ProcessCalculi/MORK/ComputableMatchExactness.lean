import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternFactorOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution

/-!
# Exact replay for computable MM2 matching

The computable positive matcher preserves the concrete atom selected for each
pattern factor, even when that atom contains expression-local variables.  The
result is stronger than the ground-only inverse used by arithmetic
specialization: a rule may safely reissue an exact input directive without
reclassifying its inner variables as outer binders.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-! ## Covered substitutions are stable under extension -/

mutual
  theorem templateCovered_of_lookupExtends
      {before after : Subst} (hExt : after.lookupExtends before) :
      ∀ template,
        templateCovered before template = true →
          templateCovered after template = true
    | .var name, covered => by
        cases found : before.lookup name with
        | none => simp [templateCovered, found] at covered
        | some value => simp [templateCovered, hExt name value found]
    | .symbol _, _ => rfl
    | .grounded _, _ => rfl
    | .expression templates, covered =>
        templatesCovered_of_lookupExtends hExt templates covered

  theorem templatesCovered_of_lookupExtends
      {before after : Subst} (hExt : after.lookupExtends before) :
      ∀ templates,
        templatesCovered before templates = true →
          templatesCovered after templates = true
    | [], _ => rfl
    | template :: templates, covered => by
        simp only [templatesCovered, Bool.and_eq_true] at covered ⊢
        exact ⟨templateCovered_of_lookupExtends hExt template covered.1,
          templatesCovered_of_lookupExtends hExt templates covered.2⟩
end

mutual
  theorem applySubst_eq_of_lookupExtends_covered
      {before after : Subst} (hExt : after.lookupExtends before) :
      ∀ template,
        templateCovered before template = true →
          applySubst after template = applySubst before template
    | .var name, covered => by
        cases found : before.lookup name with
        | none => simp [templateCovered, found] at covered
        | some value => simp [applySubst, found, hExt name value found]
    | .symbol _, _ => rfl
    | .grounded _, _ => rfl
    | .expression templates, covered => by
        exact congrArg Atom.expression
          (applySubstList_eq_of_lookupExtends_covered hExt templates covered)

  theorem applySubstList_eq_of_lookupExtends_covered
      {before after : Subst} (hExt : after.lookupExtends before) :
      ∀ templates,
        templatesCovered before templates = true →
          applySubst.applySubstList after templates =
            applySubst.applySubstList before templates
    | [], _ => rfl
    | template :: templates, covered => by
        simp only [templatesCovered, Bool.and_eq_true] at covered
        simp only [applySubst.applySubstList]
        rw [applySubst_eq_of_lookupExtends_covered hExt template covered.1,
          applySubstList_eq_of_lookupExtends_covered hExt templates
            covered.2]
end

/-! ## Match coverage and exactness -/

mutual
  theorem cmatchAtom_templateCovered :
      ∀ (before : Subst) (pattern concrete : Atom) (after : Subst),
        cmatchAtom before pattern concrete = some after →
          templateCovered after pattern = true
    | before, .var name, concrete, after, matched => by
        cases found : before.lookup name with
        | none =>
            simp only [cmatchAtom, found] at matched
            cases matched
            simp [templateCovered, Subst.lookup, List.find?]
        | some value =>
            simp only [cmatchAtom, found] at matched
            split at matched
            · cases matched
              simp [templateCovered, found]
            · contradiction
    | before, .symbol left, .symbol right, after, matched => by
        simp only [cmatchAtom] at matched
        split at matched
        · cases matched
          rfl
        · contradiction
    | before, .grounded left, .grounded right, after, matched => by
        simp only [cmatchAtom] at matched
        split at matched
        · cases matched
          rfl
        · contradiction
    | before, .expression patterns, .expression concretes, after, matched => by
        exact cmatchAtomList_templateCovered before patterns concretes after
          matched
    | before, .symbol _, .var _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .symbol _, .grounded _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .symbol _, .expression _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .grounded _, .var _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .grounded _, .symbol _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .grounded _, .expression _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .expression _, .var _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .expression _, .symbol _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .expression _, .grounded _, after, matched => by
        simp [cmatchAtom] at matched

  theorem cmatchAtomList_templateCovered :
      ∀ (before : Subst) (patterns concretes : List Atom) (after : Subst),
        cmatchAtomList before patterns concretes = some after →
          templatesCovered after patterns = true
    | before, [], [], after, matched => by
        simp only [cmatchAtomList] at matched
        cases matched
        rfl
    | before, [], _ :: _, after, matched => by
        simp [cmatchAtomList] at matched
    | before, _ :: _, [], after, matched => by
        simp [cmatchAtomList] at matched
    | before, pattern :: patterns, concrete :: concretes, after, matched => by
        simp only [cmatchAtomList] at matched
        cases headMatch : cmatchAtom before pattern concrete with
        | none => simp [headMatch] at matched
        | some middle =>
            simp [headMatch] at matched
            have tailExtends : after.lookupExtends middle := by
              rw [_root_.Mettapedia.Languages.ProcessCalculi.MORK.Conformance.cmatchAtomList_eq_matchAtomList] at matched
              exact matchAtom_lookupExtends.matchAtomList_lookupExtends matched
            simp only [templatesCovered, Bool.and_eq_true]
            exact
              ⟨templateCovered_of_lookupExtends tailExtends pattern
                  (cmatchAtom_templateCovered before pattern concrete middle
                    headMatch),
                cmatchAtomList_templateCovered middle patterns concretes after
                  matched⟩
end

mutual
  theorem cmatchAtom_applySubst :
      ∀ (before : Subst) (pattern concrete : Atom) (after : Subst),
        cmatchAtom before pattern concrete = some after →
          applySubst after pattern = concrete
    | before, .var name, concrete, after, matched => by
        cases found : before.lookup name with
        | none =>
            simp only [cmatchAtom, found] at matched
            cases matched
            simp [applySubst, Subst.lookup, List.find?]
        | some value =>
            simp only [cmatchAtom, found] at matched
            split at matched
            · cases matched
              have equal : concrete = value := by
                exact eq_of_beq (by assumption)
              simp [applySubst, found, equal]
            · contradiction
    | before, .symbol left, .symbol right, after, matched => by
        simp only [cmatchAtom] at matched
        split at matched
        · cases matched
          simpa using eq_of_beq (by assumption)
        · contradiction
    | before, .grounded left, .grounded right, after, matched => by
        simp only [cmatchAtom] at matched
        split at matched
        · cases matched
          simpa using eq_of_beq (by assumption)
        · contradiction
    | before, .expression patterns, .expression concretes, after, matched => by
        simp only [cmatchAtom] at matched
        exact congrArg Atom.expression
          (cmatchAtomList_applySubst before patterns concretes after matched)
    | before, .symbol _, .var _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .symbol _, .grounded _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .symbol _, .expression _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .grounded _, .var _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .grounded _, .symbol _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .grounded _, .expression _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .expression _, .var _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .expression _, .symbol _, after, matched => by
        simp [cmatchAtom] at matched
    | before, .expression _, .grounded _, after, matched => by
        simp [cmatchAtom] at matched

  theorem cmatchAtomList_applySubst :
      ∀ (before : Subst) (patterns concretes : List Atom) (after : Subst),
        cmatchAtomList before patterns concretes = some after →
          applySubst.applySubstList after patterns = concretes
    | before, [], [], after, matched => by
        simp only [cmatchAtomList] at matched
        cases matched
        rfl
    | before, [], _ :: _, after, matched => by
        simp [cmatchAtomList] at matched
    | before, _ :: _, [], after, matched => by
        simp [cmatchAtomList] at matched
    | before, pattern :: patterns, concrete :: concretes, after, matched => by
        simp only [cmatchAtomList] at matched
        cases headMatch : cmatchAtom before pattern concrete with
        | none => simp [headMatch] at matched
        | some middle =>
            simp [headMatch] at matched
            have tailExtends : after.lookupExtends middle := by
              rw [_root_.Mettapedia.Languages.ProcessCalculi.MORK.Conformance.cmatchAtomList_eq_matchAtomList] at matched
              exact matchAtom_lookupExtends.matchAtomList_lookupExtends matched
            simp only [applySubst.applySubstList]
            rw [applySubst_eq_of_lookupExtends_covered tailExtends pattern
                  (cmatchAtom_templateCovered before pattern concrete middle
                    headMatch),
                cmatchAtom_applySubst before pattern concrete middle headMatch,
                cmatchAtomList_applySubst middle patterns concretes after
                  matched]
end

/-! ## Exact factor origin -/

theorem cmatchPattern_go_factor_replay_origin
    (space : CSpace) : ∀ before factor after initial witnesses final
      finalWitnesses,
      (final, finalWitnesses) ∈
        cmatchPattern.go space (before ++ factor :: after) initial witnesses →
      ∃ beforeFactor afterFactor carrier,
        carrier ∈ space ∧
          cmatchAtom beforeFactor factor carrier = some afterFactor ∧
          final.lookupExtends afterFactor ∧
          applySubst final factor = carrier
  | [], factor, after, initial, witnesses, final, finalWitnesses, member => by
      simp only [List.nil_append, cmatchPattern.go, List.mem_flatMap] at member
      obtain ⟨⟨afterFactor, carrier⟩, matchedMember, tailMember⟩ := member
      rw [List.mem_filterMap] at matchedMember
      obtain ⟨concrete, carrierMember, mapped⟩ := matchedMember
      simp only [Option.map_eq_some_iff] at mapped
      obtain ⟨matchedSubstitution, matched, equal⟩ := mapped
      cases equal
      have tailExtends := cmatchPattern_go_lookupExtends tailMember
      exact ⟨initial, afterFactor, carrier, carrierMember, matched,
        tailExtends,
        (applySubst_eq_of_lookupExtends_covered tailExtends factor
          (cmatchAtom_templateCovered initial factor carrier afterFactor
            matched)).trans
          (cmatchAtom_applySubst initial factor carrier afterFactor matched)⟩
  | beforeHead :: beforeTail, factor, after, initial, witnesses, final,
      finalWitnesses, member => by
      simp only [List.cons_append, cmatchPattern.go, List.mem_flatMap] at member
      obtain ⟨⟨afterHead, carrier⟩, _matchedHead, tailMember⟩ := member
      exact cmatchPattern_go_factor_replay_origin space beforeTail factor after
        afterHead (carrier :: witnesses) final finalWitnesses tailMember

/-- Any designated compatible-input factor is reissued exactly as one input
carrier under the final matcher substitution. -/
theorem cmatchInputSpec_factor_replay_origin
    (space : CSpace) (before after : List Atom) (factor : Atom)
    {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec [] space
        (.compat (mkPattern (before ++ factor :: after)))).map Prod.fst) :
    ∃ carrier ∈ space, applySubst substitution factor = carrier := by
  rw [List.mem_map] at member
  obtain ⟨⟨final, finalWitnesses⟩, matched, rfl⟩ := member
  obtain ⟨beforeFactor, afterFactor, carrier, carrierMember, factorMatched,
      finalExtends, replay⟩ :=
    cmatchPattern_go_factor_replay_origin space before factor after [] []
      final finalWitnesses (by
        simpa only [cmatchInputSpec, mkPattern, cmatchPattern] using matched)
  exact ⟨carrier, carrierMember, replay⟩

/-- A designated compatible-input factor retains its actual local matching
witness as well as its final replay.  This is the inversion form needed when
the carrier's source table, rather than the final substitution alone,
determines the unique represented row. -/
theorem cmatchInputSpec_factor_match_origin
    (space : CSpace) (before after : List Atom) (factor : Atom)
    {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec [] space
        (.compat (mkPattern (before ++ factor :: after)))).map Prod.fst) :
    ∃ beforeFactor afterFactor carrier,
      carrier ∈ space ∧
        cmatchAtom beforeFactor factor carrier = some afterFactor ∧
        substitution.lookupExtends afterFactor ∧
        applySubst substitution factor = carrier := by
  rw [List.mem_map] at member
  obtain ⟨⟨final, finalWitnesses⟩, matched, rfl⟩ := member
  exact cmatchPattern_go_factor_replay_origin space before factor after [] []
    final finalWitnesses (by
      simpa only [cmatchInputSpec, mkPattern, cmatchPattern] using matched)

/-- A member of a finite pattern list has an exact before/factor/after
decomposition. -/
theorem list_split_at_factor (factor : Atom) : ∀ patterns : List Atom,
    factor ∈ patterns → ∃ before after, patterns = before ++ factor :: after
  | [], member => by simp at member
  | head :: tail, member => by
      rcases List.mem_cons.mp member with equal | member
      · subst factor
        exact ⟨[], tail, rfl⟩
      · obtain ⟨before, after, split⟩ := list_split_at_factor factor tail member
        exact ⟨head :: before, after, by simp [split]⟩

/-- Any factor appearing in a compatible input pattern is replayed exactly
from one carrier selected by the complete matcher. -/
theorem cmatchInputSpec_compat_factor_replay_origin
    (space : CSpace) (pattern : Pattern) (factor : Atom)
    {substitution : Subst} (factorMember : factor ∈ pattern.atoms)
    (member : substitution ∈
      (cmatchInputSpec [] space (.compat pattern)).map Prod.fst) :
    ∃ carrier ∈ space, applySubst substitution factor = carrier := by
  cases pattern with
  | mk patterns =>
      obtain ⟨before, after, split⟩ :=
        list_split_at_factor factor patterns factorMember
      rw [split] at member
      exact cmatchInputSpec_factor_replay_origin space before after factor
        member

/-- Pattern-level form of `cmatchInputSpec_factor_match_origin`. -/
theorem cmatchInputSpec_compat_factor_match_origin
    (space : CSpace) (pattern : Pattern) (factor : Atom)
    {substitution : Subst} (factorMember : factor ∈ pattern.atoms)
    (member : substitution ∈
      (cmatchInputSpec [] space (.compat pattern)).map Prod.fst) :
    ∃ beforeFactor afterFactor carrier,
      carrier ∈ space ∧
        cmatchAtom beforeFactor factor carrier = some afterFactor ∧
        substitution.lookupExtends afterFactor ∧
        applySubst substitution factor = carrier := by
  cases pattern with
  | mk patterns =>
      obtain ⟨before, after, split⟩ :=
        list_split_at_factor factor patterns factorMember
      rw [split] at member
      exact cmatchInputSpec_factor_match_origin space before after factor member

section AxiomAudit

#print axioms templateCovered_of_lookupExtends
#print axioms templatesCovered_of_lookupExtends
#print axioms applySubst_eq_of_lookupExtends_covered
#print axioms applySubstList_eq_of_lookupExtends_covered
#print axioms cmatchAtom_templateCovered
#print axioms cmatchAtomList_templateCovered
#print axioms cmatchAtom_applySubst
#print axioms cmatchAtomList_applySubst
#print axioms cmatchPattern_go_factor_replay_origin
#print axioms cmatchInputSpec_factor_replay_origin
#print axioms cmatchInputSpec_factor_match_origin
#print axioms list_split_at_factor
#print axioms cmatchInputSpec_compat_factor_replay_origin
#print axioms cmatchInputSpec_compat_factor_match_origin

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
