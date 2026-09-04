import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchSafety
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution

/-!
# Hereditary safety for rule-scoped MM2 matching

Rule-scoped execution has two matcher forms: ordinary compatible patterns and
explicit source factors.  This module proves that both can only bind values
already present below hereditary-safe workspace atoms.  The result is stated
without committing to any particular invariant, so it can carry executable
origin, typing, provenance, or representation information.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

private theorem morkSupportFind_mem
    {space : List Atom} {target representative : Atom}
    (found : morkSupportFind? space target = some representative) :
    representative ∈ space := by
  exact List.mem_of_find?_eq_some found

/-- One explicit source factor cannot introduce an unsafe substitution value.
The equality and inequality forms select a representative from the existing
physical support; inequality first removes a key, which can only reduce the
available source atoms. -/
theorem cMatchSourceFactorMork_substitutionValuesWithin
    (property : Atom → Prop)
    (hereditary : AtomPropertyHereditary property)
    (space : List Atom) (spaceWithin : AtomsWithin property space)
    (substitution : Subst)
    (_before : SubstitutionValuesWithin property substitution)
    (factor : SourceFactor) {result : Subst} {witness : Atom}
    (member : (result, witness) ∈
      cMatchSourceFactorMork substitution space factor) :
    SubstitutionValuesWithin property result := by
  cases factor with
  | btm pattern =>
      simp only [cMatchSourceFactorMork] at member
      rw [List.mem_filterMap] at member
      obtain ⟨candidate, candidateMember, mapped⟩ := member
      simp only [Option.map_eq_some_iff] at mapped
      obtain ⟨matchedResult, matched, equal⟩ := mapped
      have resultEqual : matchedResult = result := congrArg Prod.fst equal
      rw [← resultEqual]
      exact cmatchAtom_substitutionValuesWithin property hereditary
        substitution pattern candidate matchedResult _before
        (spaceWithin candidate candidateMember) matched
  | eqConstraint pattern witness =>
      cases found :
          morkSupportFind? space (applySubst substitution pattern) with
      | none => simp [cMatchSourceFactorMork, found] at member
      | some representative =>
          simp only [cMatchSourceFactorMork, found] at member
          cases matched : cmatchAtom substitution witness representative with
          | none => simp [matched] at member
          | some next =>
              simp [matched] at member
              rcases member with ⟨resultEqual, _⟩
              subst result
              exact cmatchAtom_substitutionValuesWithin property hereditary
                substitution witness representative next _before
                (spaceWithin representative (morkSupportFind_mem found))
                matched
  | neqConstraint pattern witness =>
      simp only [cMatchSourceFactorMork] at member
      rw [List.mem_filterMap] at member
      obtain ⟨candidate, candidateMember, mapped⟩ := member
      simp only [Option.map_eq_some_iff] at mapped
      obtain ⟨matchedResult, matched, equal⟩ := mapped
      have resultEqual : matchedResult = result := congrArg Prod.fst equal
      rw [← resultEqual]
      exact cmatchAtom_substitutionValuesWithin property hereditary
        substitution witness candidate matchedResult _before
        (morkEraseSupport_atomsWithin property space
          (applySubst substitution pattern) spaceWithin candidate candidateMember)
        matched

/-- A complete explicit-source factor sequence preserves the pointwise
substitution invariant from its initial environment to every successful row. -/
theorem cMatchSourceFactorsMork_substitutionValuesWithin
    (property : Atom → Prop)
    (hereditary : AtomPropertyHereditary property)
    (space : List Atom) (spaceWithin : AtomsWithin property space) :
    ∀ (factors : List SourceFactor) (substitution : Subst)
      (_before : SubstitutionValuesWithin property substitution)
      {result : Subst} {witnesses : List Atom},
      (result, witnesses) ∈
        cMatchSourceFactorsMork substitution space factors →
      SubstitutionValuesWithin property result := by
  intro factors
  induction factors with
  | nil =>
      intro substitution before result witnesses member
      simp only [cMatchSourceFactorsMork, List.mem_singleton,
        Prod.mk.injEq] at member
      exact member.1 ▸ before
  | cons factor factors induction =>
      intro substitution before result witnesses member
      simp only [cMatchSourceFactorsMork, List.mem_flatMap] at member
      obtain ⟨⟨middle, witness⟩, headMember, tailMember⟩ := member
      rw [List.mem_map] at tailMember
      obtain ⟨⟨final, tailWitnesses⟩, finalMember, equal⟩ := tailMember
      have resultEqual : final = result := congrArg Prod.fst equal
      rw [← resultEqual]
      exact induction middle
        (cMatchSourceFactorMork_substitutionValuesWithin property hereditary
          space spaceWithin substitution before factor headMember)
        finalMember

/-- Every row produced by the rule-scoped matcher inherits the pointwise
invariant from the workspace, for both compatible and explicit inputs. -/
theorem cMatchInputSpecMork_substitutionValuesWithin
    (property : Atom → Prop)
    (hereditary : AtomPropertyHereditary property)
    (space : List Atom) (spaceWithin : AtomsWithin property space)
    (input : InputSpec) {substitution : Subst}
    (member : substitution ∈
      (cMatchInputSpecMork [] space input).map Prod.fst) :
    SubstitutionValuesWithin property substitution := by
  cases input with
  | compat pattern =>
      exact cmatchInputSpec_compat_substitutionValuesWithin property
        hereditary space spaceWithin pattern member
  | explicit factors =>
      rw [List.mem_map] at member
      obtain ⟨⟨result, witnesses⟩, resultMember, equal⟩ := member
      subst substitution
      exact cMatchSourceFactorsMork_substitutionValuesWithin property
        hereditary space spaceWithin factors []
        (substitutionValuesWithin_nil property) resultMember

/-- The matcher rows consumed by one rule-scoped firing inherit an atom-local
invariant from the live state.  Re-inserting the selected directive is safe
when that directive itself satisfies the invariant; guard filtering can only
remove candidate rows. -/
theorem cFireRuleScopedSourceExecFact_matchValuesWithin
    (property : Atom → Prop)
    (hereditary : AtomPropertyHereditary property)
    (space : List Atom) (directive : SourceExecFact)
    (spaceWithin : AtomsWithin property space)
    (directiveWithin : property directive.atom) :
    let live := morkEraseSupport space directive.atom
    let read := morkInsertSupport live directive.atom
    let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
      (substitution, _) => matchSourceGuards substitution directive.rule.guards
    ∀ substitution ∈ rows.map Prod.fst,
      SubstitutionValuesWithin property substitution := by
  dsimp
  intro substitution member
  rw [List.mem_map] at member
  obtain ⟨pair, pairMember, equal⟩ := member
  subst substitution
  rw [List.mem_filter] at pairMember
  apply cMatchInputSpecMork_substitutionValuesWithin property hereditary
    (morkInsertSupport (morkEraseSupport space directive.atom) directive.atom)
    ?_ directive.rule.input
  · rw [List.mem_map]
    exact ⟨pair, pairMember.1, rfl⟩
  · exact morkInsertSupport_atomsWithin property
      (morkEraseSupport space directive.atom) directive.atom
      (morkEraseSupport_atomsWithin property space directive.atom spaceWithin)
      directiveWithin

section AxiomAudit

#print axioms cMatchSourceFactorMork_substitutionValuesWithin
#print axioms cMatchSourceFactorsMork_substitutionValuesWithin
#print axioms cMatchInputSpecMork_substitutionValuesWithin
#print axioms cFireRuleScopedSourceExecFact_matchValuesWithin

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
