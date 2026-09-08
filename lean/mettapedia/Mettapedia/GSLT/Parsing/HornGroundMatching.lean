import Mettapedia.GSLT.Parsing.HornSideAdmission

/-!
# Exactness of the existing first-order ground matcher

The matcher and term carriers are those already used by Horn specialization.
These proofs relate successful matching to the independent substitution
operation used by certificate replay. Matching may extend an environment but
must preserve its existing bindings and unique variable identifiers.

This is not a native evaluator correctness theorem. It supplies the matching
obligation needed when equation execution is connected to authored rules.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.HornGroundMatching

open HornCertificate HornSideAdmission

theorem lookupGround_eq_instantiate (identifier : Nat)
    (substitution : Substitution) :
    lookupGround identifier substitution =
      instantiateTerm substitution (.var identifier) := by
  induction substitution with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨candidate, value⟩
      simp only [lookupGround, instantiateTerm_var_cons, ih]

/-- Every binding visible before matching remains visible afterwards. -/
def Extends (before after : Substitution) : Prop :=
  ∀ identifier value, lookupGround identifier before = some value →
    lookupGround identifier after = some value

theorem Extends.refl (substitution : Substitution) :
    Extends substitution substitution := by
  intro _ _ found
  exact found

theorem Extends.trans {first middle last : Substitution}
    (left : Extends first middle) (right : Extends middle last) :
    Extends first last := by
  intro identifier value found
  exact right identifier value (left identifier value found)

theorem lookupGround_none_iff (identifier : Nat)
    (substitution : Substitution) :
    lookupGround identifier substitution = none ↔
      identifier ∉ substitution.unzip.1 := by
  induction substitution with
  | nil => simp [lookupGround]
  | cons binding rest ih =>
      rcases binding with ⟨candidate, value⟩
      by_cases equal : identifier = candidate
      · simp [lookupGround, equal]
      · simp [lookupGround, equal, ih]

theorem bindGround_correct {identifier : Nat} {value : GroundTerm}
    {before after : Substitution}
    (bound : bindGround identifier value before = some after) :
    lookupGround identifier after = some value ∧
      Extends before after ∧
      (substitutionValid before = true → substitutionValid after = true) := by
  cases found : lookupGround identifier before with
  | none =>
      simp only [bindGround, found] at bound
      cases bound
      refine ⟨by simp [lookupGround], ?_, ?_⟩
      · intro other previous existing
        have different : other ≠ identifier := by
          intro equal
          subst other
          simp [found] at existing
        simp [lookupGround, different, existing]
      · intro valid
        have absent := (lookupGround_none_iff identifier before).mp found
        simp only [substitutionValid, decide_eq_true_eq] at valid ⊢
        exact List.nodup_cons.mpr ⟨absent, valid⟩
  | some previous =>
      by_cases equal : previous = value
      · simp only [bindGround, found, if_pos equal, Option.some.injEq] at bound
        subst after
        exact ⟨by simpa [equal] using found, .refl _, fun valid => valid⟩
      · simp [bindGround, found, equal] at bound

mutual
  theorem instantiateTerm_of_extends {before after : Substitution}
      (preserved : Extends before after) (term : Term) (value : GroundTerm)
      (instantiated : instantiateTerm before term = some value) :
      instantiateTerm after term = some value := by
    cases term with
    | var identifier =>
        rw [← lookupGround_eq_instantiate] at instantiated ⊢
        exact preserved identifier value instantiated
    | atom name => exact instantiated
    | integer integer => exact instantiated
    | app constructor arguments =>
        cases found : instantiateTerms before arguments with
        | none => simp [instantiateTerm, found] at instantiated
        | some values =>
            have transported := instantiateTerms_of_extends preserved arguments values found
            simpa [instantiateTerm, found, transported] using instantiated
  termination_by sizeOf term

  theorem instantiateTerms_of_extends {before after : Substitution}
      (preserved : Extends before after) (terms : Terms) (values : GroundTerms)
      (instantiated : instantiateTerms before terms = some values) :
      instantiateTerms after terms = some values := by
    cases terms with
    | nil => exact instantiated
    | cons head tail =>
        cases foundHead : instantiateTerm before head with
        | none => simp [instantiateTerms, foundHead] at instantiated
        | some headValue =>
            cases foundTail : instantiateTerms before tail with
            | none => simp [instantiateTerms, foundHead, foundTail] at instantiated
            | some tailValues =>
                have headTransported :=
                  instantiateTerm_of_extends preserved head headValue foundHead
                have tailTransported :=
                  instantiateTerms_of_extends preserved tail tailValues foundTail
                simpa [instantiateTerms, foundHead, foundTail,
                  headTransported, tailTransported] using instantiated
  termination_by sizeOf terms
end

mutual
  /-- A successful term match is an exact instance, preserves all existing
  bindings, and cannot introduce a duplicate variable identifier. -/
  theorem matchGroundTerm_correct (pattern : Term) (target : GroundTerm)
      {before after : Substitution}
      (matched : matchGroundTerm pattern target before = some after) :
      instantiateTerm after pattern = some target ∧
        Extends before after ∧
        (substitutionValid before = true → substitutionValid after = true) := by
    cases pattern with
    | var identifier =>
        obtain ⟨bound, preserved, valid⟩ := bindGround_correct matched
        exact ⟨by simpa [lookupGround_eq_instantiate] using bound, preserved, valid⟩
    | atom name =>
        cases target <;> simp_all [matchGroundTerm, instantiateTerm, Extends]
    | integer value =>
        cases target <;> simp_all [matchGroundTerm, instantiateTerm, Extends]
    | app constructor arguments =>
        cases target with
        | atom _ => simp [matchGroundTerm] at matched
        | integer _ => simp [matchGroundTerm] at matched
        | app targetConstructor targets =>
            by_cases equal : constructor = targetConstructor
            · subst targetConstructor
              simp only [matchGroundTerm, bne_self_eq_false, Bool.false_eq_true,
                ↓reduceIte] at matched
              obtain ⟨instantiated, preserved, valid⟩ :=
                matchGroundTerms_correct arguments targets matched
              exact ⟨by simp [instantiateTerm, instantiated], preserved, valid⟩
            · simp [matchGroundTerm, equal] at matched
  termination_by sizeOf pattern

  theorem matchGroundTerms_correct (patterns : Terms) (targets : GroundTerms)
      {before after : Substitution}
      (matched : matchGroundTerms patterns targets before = some after) :
      instantiateTerms after patterns = some targets ∧
        Extends before after ∧
        (substitutionValid before = true → substitutionValid after = true) := by
    cases patterns with
    | nil =>
        cases targets <;> simp_all [matchGroundTerms, instantiateTerms, Extends]
    | cons head tail =>
        cases targets with
        | nil => simp [matchGroundTerms] at matched
        | cons targetHead targetTail =>
            cases matchedHead : matchGroundTerm head targetHead before with
            | none => simp [matchGroundTerms, matchedHead] at matched
            | some middle =>
                have matchedTail : matchGroundTerms tail targetTail middle = some after := by
                  simpa [matchGroundTerms, matchedHead] using matched
                obtain ⟨headInstance, firstPreserved, firstValid⟩ :=
                  matchGroundTerm_correct head targetHead matchedHead
                obtain ⟨tailInstance, lastPreserved, lastValid⟩ :=
                  matchGroundTerms_correct tail targetTail matchedTail
                have headTransported :=
                  instantiateTerm_of_extends lastPreserved head targetHead headInstance
                exact ⟨by simp [instantiateTerms, headTransported, tailInstance],
                  firstPreserved.trans lastPreserved, fun valid => lastValid (firstValid valid)⟩
  termination_by sizeOf patterns
end

theorem matchGroundAtom_correct (pattern : Atom) (target : GroundAtom)
    {substitution : Substitution}
    (matched : matchGroundAtom pattern target = some substitution) :
    instantiateAtom substitution pattern = some target ∧
      substitutionValid substitution = true := by
  by_cases equal : pattern.relation = target.relation
  · have matchedTerms :
        matchGroundTerms pattern.arguments target.arguments [] = some substitution := by
      simpa [matchGroundAtom, equal] using matched
    obtain ⟨instantiated, _, valid⟩ :=
      matchGroundTerms_correct pattern.arguments target.arguments matchedTerms
    refine ⟨?_, valid (by decide)⟩
    cases pattern
    cases target
    simp_all [instantiateAtom]
  · simp [matchGroundAtom, equal] at matched

theorem Extends.nil (substitution : Substitution) : Extends [] substitution := by
  intro identifier value found
  simp [lookupGround] at found

theorem Extends.cons {before witness : Substitution}
    (preserved : Extends before witness) (identifier : Nat) (value : GroundTerm)
    (found : lookupGround identifier witness = some value) :
    Extends ((identifier, value) :: before) witness := by
  intro other previous existing
  by_cases equal : other = identifier
  · subst other
    have valuesEqual : value = previous := by simpa [lookupGround] using existing
    simpa [valuesEqual] using found
  · exact preserved other previous (by simpa [lookupGround, equal] using existing)

theorem bindGround_complete {before witness : Substitution}
    (preserved : Extends before witness) (identifier : Nat) (value : GroundTerm)
    (found : lookupGround identifier witness = some value) :
    ∃ after, bindGround identifier value before = some after ∧ Extends after witness := by
  cases current : lookupGround identifier before with
  | none =>
      exact ⟨(identifier, value) :: before, by simp [bindGround, current],
        preserved.cons identifier value found⟩
  | some previous =>
      have valuesEqual : previous = value :=
        Option.some.inj ((preserved identifier previous current).symm.trans found)
      exact ⟨before, by simp [bindGround, current, valuesEqual], preserved⟩

mutual
  /-- Every ground instance consistent with the initial bindings can be
  matched. The resulting bindings still agree with the supplied witness. -/
  theorem matchGroundTerm_complete {before witness : Substitution}
      (preserved : Extends before witness) (pattern : Term) (target : GroundTerm)
      (instantiated : instantiateTerm witness pattern = some target) :
      ∃ after, matchGroundTerm pattern target before = some after ∧
        Extends after witness := by
    cases pattern with
    | var identifier =>
        exact bindGround_complete preserved identifier target
          (by simpa [lookupGround_eq_instantiate] using instantiated)
    | atom name =>
        have equal : GroundTerm.atom name = target := by
          simpa [instantiateTerm] using instantiated
        subst target
        exact ⟨before, by simp [matchGroundTerm], preserved⟩
    | integer value =>
        have equal : GroundTerm.integer value = target := by
          simpa [instantiateTerm] using instantiated
        subst target
        exact ⟨before, by simp [matchGroundTerm], preserved⟩
    | app constructor arguments =>
        cases found : instantiateTerms witness arguments with
        | none => simp [instantiateTerm, found] at instantiated
        | some values =>
            have equal : GroundTerm.app constructor values = target := by
              simpa [instantiateTerm, found] using instantiated
            subst target
            obtain ⟨after, matched, lastPreserved⟩ :=
              matchGroundTerms_complete preserved arguments values found
            exact ⟨after, by simpa [matchGroundTerm] using matched, lastPreserved⟩
  termination_by sizeOf pattern

  theorem matchGroundTerms_complete {before witness : Substitution}
      (preserved : Extends before witness) (patterns : Terms) (targets : GroundTerms)
      (instantiated : instantiateTerms witness patterns = some targets) :
      ∃ after, matchGroundTerms patterns targets before = some after ∧
        Extends after witness := by
    cases patterns with
    | nil =>
        have equal : GroundTerms.nil = targets := by
          simpa [instantiateTerms] using instantiated
        subst targets
        exact ⟨before, rfl, preserved⟩
    | cons head tail =>
        cases foundHead : instantiateTerm witness head with
        | none => simp [instantiateTerms, foundHead] at instantiated
        | some headValue =>
            cases foundTail : instantiateTerms witness tail with
            | none => simp [instantiateTerms, foundHead, foundTail] at instantiated
            | some tailValues =>
                have equal : GroundTerms.cons headValue tailValues = targets := by
                  simpa [instantiateTerms, foundHead, foundTail] using instantiated
                subst targets
                obtain ⟨middle, matchedHead, middlePreserved⟩ :=
                  matchGroundTerm_complete preserved head headValue foundHead
                obtain ⟨after, matchedTail, lastPreserved⟩ :=
                  matchGroundTerms_complete middlePreserved tail tailValues foundTail
                exact ⟨after, by simp [matchGroundTerms, matchedHead, matchedTail],
                  lastPreserved⟩
  termination_by sizeOf patterns
end

/-- No search bound or uniqueness assumption is required for first-order
ground matching: success is exactly existence of a ground instance. -/
theorem matchGroundTerm_iff_instance (pattern : Term) (target : GroundTerm) :
    (∃ substitution, matchGroundTerm pattern target [] = some substitution) ↔
      ∃ substitution, substitutionValid substitution = true ∧
        instantiateTerm substitution pattern = some target := by
  constructor
  · rintro ⟨substitution, matched⟩
    obtain ⟨instantiated, _, valid⟩ := matchGroundTerm_correct pattern target matched
    exact ⟨substitution, valid (by decide), instantiated⟩
  · rintro ⟨witness, _, instantiated⟩
    obtain ⟨substitution, matched, _⟩ :=
      matchGroundTerm_complete (.nil witness) pattern target instantiated
    exact ⟨substitution, matched⟩

/-- Ground atom matching is exact for the independently stated substitution
semantics, including shared variables across different arguments. -/
theorem matchGroundAtom_iff_instance (pattern : Atom) (target : GroundAtom) :
    (∃ substitution, matchGroundAtom pattern target = some substitution) ↔
      ∃ substitution, substitutionValid substitution = true ∧
        instantiateAtom substitution pattern = some target := by
  constructor
  · rintro ⟨substitution, matched⟩
    obtain ⟨instantiated, valid⟩ := matchGroundAtom_correct pattern target matched
    exact ⟨substitution, valid, instantiated⟩
  · rintro ⟨witness, _, instantiated⟩
    rcases pattern with ⟨relation, arguments⟩
    rcases target with ⟨targetRelation, targetArguments⟩
    cases found : instantiateTerms witness arguments with
    | none => simp [instantiateAtom, found] at instantiated
    | some values =>
        have equal : GroundAtom.mk relation values = ⟨targetRelation, targetArguments⟩ := by
          simpa [instantiateAtom, found] using instantiated
        cases equal
        obtain ⟨substitution, matched, _⟩ :=
          matchGroundTerms_complete (.nil witness) arguments _ found
        exact ⟨substitution, by simpa [matchGroundAtom] using matched⟩

mutual
  theorem instantiateTerm_isSome_iff (substitution : Substitution) (term : Term) :
      (instantiateTerm substitution term).isSome = true ↔
        ∀ identifier ∈ HornSpecialization.termVariables term,
          (lookupGround identifier substitution).isSome = true := by
    cases term with
    | var identifier =>
        simp [HornSpecialization.termVariables, lookupGround_eq_instantiate]
    | atom name => simp [instantiateTerm, HornSpecialization.termVariables]
    | integer value => simp [instantiateTerm, HornSpecialization.termVariables]
    | app constructor arguments =>
        rw [HornSpecialization.termVariables, ← instantiateTerms_isSome_iff substitution arguments]
        cases found : instantiateTerms substitution arguments <;> simp [instantiateTerm, found]
  termination_by sizeOf term

  theorem instantiateTerms_isSome_iff (substitution : Substitution) (terms : Terms) :
      (instantiateTerms substitution terms).isSome = true ↔
        ∀ identifier ∈ HornSpecialization.termsVariables terms,
          (lookupGround identifier substitution).isSome = true := by
    cases terms with
    | nil => simp [instantiateTerms, HornSpecialization.termsVariables]
    | cons head tail =>
        simp only [HornSpecialization.termsVariables, List.mem_append, or_imp, forall_and]
        rw [← instantiateTerm_isSome_iff substitution head,
          ← instantiateTerms_isSome_iff substitution tail]
        cases foundHead : instantiateTerm substitution head <;>
          cases foundTail : instantiateTerms substitution tail <;>
          simp [instantiateTerms, foundHead, foundTail]
  termination_by sizeOf terms
end

private def repeatedVariable : Term :=
  .app "pair" (.cons (.var 0) (.cons (.var 0) .nil))

theorem repeated_variable_matches_equal_values :
    matchGroundTerm repeatedVariable
      (.app "pair" (.cons (.atom "a") (.cons (.atom "a") .nil))) [] =
        some [(0, .atom "a")] := by decide

theorem repeated_variable_refuses_unequal_values :
    matchGroundTerm repeatedVariable
      (.app "pair" (.cons (.atom "a") (.cons (.atom "b") .nil))) [] = none := by decide

theorem existing_binding_is_not_overwritten :
    matchGroundTerm (.var 0) (.atom "new") [(0, .atom "old")] = none := by decide

theorem atom_and_nullary_application_do_not_match (name : String) :
    matchGroundTerm (.atom name) (.app name .nil) [] = none ∧
      matchGroundTerm (.app name .nil) (.atom name) [] = none := by
  exact ⟨rfl, rfl⟩

#print axioms matchGroundTerm_correct
#print axioms matchGroundTerms_correct
#print axioms matchGroundAtom_correct
#print axioms matchGroundTerm_iff_instance
#print axioms matchGroundAtom_iff_instance

end Mettapedia.GSLT.Parsing.HornGroundMatching
