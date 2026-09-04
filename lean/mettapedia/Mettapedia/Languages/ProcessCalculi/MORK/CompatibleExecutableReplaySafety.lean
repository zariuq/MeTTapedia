import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutableTemplateSafety
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutableSubtermSafety

/-!
# Compatible-input executable replay safety

A compatible MM2 rule may reissue a directive selected as one complete input
carrier.  That is distinct from constructing a new directive from unrelated
matched fields.  This module makes the distinction structural and proves that
the former preserves a fixed recursive executable inventory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

mutual
  /-- A template is compatible-replay-safe when each executable directive is
  either fixed and inventory-authorized, or occurs as one complete compatible
  input factor. -/
  def compatibleExecutableTemplateSafe
      (allowed : List RawExecFact) (pattern : Pattern) : Atom → Bool
    | .var _ | .symbol _ | .grounded _ => true
    | atom@(.expression children) =>
        match children with
        | .var _ :: _ => false
        | .symbol head :: _ =>
            if head == "exec" then
              match extractRawExecFact atom with
              | none => compatibleExecutableTemplatesSafe allowed pattern children
              | some raw =>
                  ((atomFreeVars atom == []) && raw ∈ allowed) ||
                    raw.atom ∈ pattern.atoms
            else compatibleExecutableTemplatesSafe allowed pattern children
        | _ => compatibleExecutableTemplatesSafe allowed pattern children

  /-- List companion of `compatibleExecutableTemplateSafe`. -/
  def compatibleExecutableTemplatesSafe
      (allowed : List RawExecFact) (pattern : Pattern) : List Atom → Bool
    | [] => true
    | atom :: atoms =>
        compatibleExecutableTemplateSafe allowed pattern atom &&
          compatibleExecutableTemplatesSafe allowed pattern atoms
end

private theorem rawExecFact_atom_eq_of_extract
    {atom : Atom} {raw : RawExecFact}
    (extracted : extractRawExecFact atom = some raw) :
    raw.atom = atom := by
  unfold extractRawExecFact at extracted
  split at extracted <;> try contradiction
  next equal =>
    injection extracted with rawEqual
    exact congrArg RawExecFact.atom rawEqual.symm

private theorem executableSubtermsWithin_expression
    {allowed : List RawExecFact} {children : List Atom}
    (root : ∀ raw, extractRawExecFact (.expression children) = some raw →
      raw ∈ allowed)
    (below : ExecutableSubtermListWithin allowed children) :
    ExecutableSubtermsWithin allowed (.expression children) := by
  intro raw member
  simp only [rawExecSubterms, List.mem_append, Option.mem_toList] at member
  rcases member with rootMember | childMember
  · exact root raw rootMember
  · exact below raw childMember

private theorem extractRawExecFact_applySubst_execHead_none
    (substitution : Subst) (tail : List Atom)
    (absent : extractRawExecFact (.expression (.symbol "exec" :: tail)) =
      none) :
    extractRawExecFact
      (applySubst substitution (.expression (.symbol "exec" :: tail))) =
        none := by
  cases tail with
  | nil => rfl
  | cons first tail =>
      cases tail with
      | nil => rfl
      | cons second tail =>
          cases tail with
          | nil => rfl
          | cons third tail =>
              cases tail with
              | nil => simp [extractRawExecFact] at absent
              | cons fourth tail => rfl

/-! ## Replay transport -/

mutual
  /-- Instantiating a compatible-replay-safe template preserves recursive
  executable authority.  A dynamic directive is admitted only through an
  exact input-carrier replay witness. -/
  theorem compatibleExecutableTemplateSafe_applySubst
      (allowed : List RawExecFact) (pattern : Pattern) (space : CSpace)
      (substitution : Subst)
      (fixed : ∀ raw ∈ allowed,
        ExecutableSubtermsWithin allowed raw.atom)
      (spaceWithin : AtomsWithin (ExecutableSubtermsWithin allowed) space)
      (values : SubstitutionValuesWithin
        (ExecutableSubtermsWithin allowed) substitution)
      (replay : ∀ factor ∈ pattern.atoms,
        ∃ carrier ∈ space, applySubst substitution factor = carrier) : ∀ template,
      compatibleExecutableTemplateSafe allowed pattern template = true →
        ExecutableSubtermsWithin allowed (applySubst substitution template)
    | .var name, _ => by
        cases found : substitution.lookup name with
        | none =>
            intro raw member
            simp only [applySubst, found] at member
            cases member
        | some value =>
            simpa [applySubst, found] using values.lookup found
    | .symbol _, _ => by
        intro raw member
        simp only [applySubst, rawExecSubterms, Option.mem_toList] at member
        cases member
    | .grounded _, _ => by
        intro raw member
        simp only [applySubst, rawExecSubterms, Option.mem_toList] at member
        cases member
    | .expression children, safe => by
        cases children with
        | nil =>
            apply executableSubtermsWithin_expression
            · intro raw extracted
              simp only [extractRawExecFact] at extracted
              cases extracted
            · exact executableSubtermListWithin_nil allowed
        | cons head tail =>
            cases head with
            | var name =>
                simp [compatibleExecutableTemplateSafe] at safe
            | symbol name =>
                cases headEq : name == "exec" with
                | false =>
                    have listSafe :
                        compatibleExecutableTemplatesSafe allowed pattern
                          (.symbol name :: tail) = true := by
                      simpa [compatibleExecutableTemplateSafe, headEq] using safe
                    have notName : name ≠ "exec" := by
                      intro equal
                      subst name
                      simp at headEq
                    have rootNone :
                        extractRawExecFact
                          (applySubst substitution
                            (.expression (.symbol name :: tail))) = none := by
                      simp [applySubst, applySubst.applySubstList,
                        extractRawExecFact, notName]
                    have rootNone' :
                        extractRawExecFact (.expression
                          (applySubst.applySubstList substitution
                            (.symbol name :: tail))) = none := by
                      simpa only [applySubst] using rootNone
                    apply executableSubtermsWithin_expression
                    · intro raw root
                      rw [rootNone'] at root
                      cases root
                    · exact compatibleExecutableTemplatesSafe_applySubst
                        allowed pattern space substitution fixed spaceWithin values
                        replay (.symbol name :: tail) listSafe
                | true =>
                    have nameEq : name = "exec" := by simpa using headEq
                    subst name
                    cases extracted :
                        extractRawExecFact
                          (.expression (.symbol "exec" :: tail)) with
                    | none =>
                        have listSafe :
                            compatibleExecutableTemplatesSafe allowed pattern
                              (.symbol "exec" :: tail) = true := by
                          simpa [compatibleExecutableTemplateSafe, extracted]
                            using safe
                        have rootNone :
                            extractRawExecFact
                              (applySubst substitution
                                (.expression (.symbol "exec" :: tail))) =
                                  none :=
                          extractRawExecFact_applySubst_execHead_none
                            substitution tail extracted
                        have rootNone' :
                            extractRawExecFact (.expression
                              (applySubst.applySubstList substitution
                                (.symbol "exec" :: tail))) = none := by
                          simpa only [applySubst] using rootNone
                        apply executableSubtermsWithin_expression
                        · intro raw root
                          rw [rootNone'] at root
                          cases root
                        · exact compatibleExecutableTemplatesSafe_applySubst
                            allowed pattern space substitution fixed spaceWithin
                            values replay (.symbol "exec" :: tail) listSafe
                    | some raw =>
                        have authorizedOrReplay :
                            (((atomFreeVars
                                (.expression (.symbol "exec" :: tail)) = []) &&
                              raw ∈ allowed) ||
                              (raw.atom ∈ pattern.atoms)) = true := by
                          simpa [compatibleExecutableTemplateSafe, extracted]
                            using safe
                        rw [Bool.or_eq_true] at authorizedOrReplay
                        rcases authorizedOrReplay with fixedBranch | replayBranch
                        · have fixedParts :
                              atomFreeVars
                                  (.expression (.symbol "exec" :: tail)) = [] ∧
                                raw ∈ allowed := by
                              simpa [Bool.and_eq_true] using fixedBranch
                          change ExecutableSubtermsWithin allowed
                            (applySubst substitution
                              (.expression (.symbol "exec" :: tail)))
                          rw [applySubst_eq_self_of_atomFreeVars_nil
                            substitution (.expression (.symbol "exec" :: tail))
                            fixedParts.1]
                          have rawAtom := rawExecFact_atom_eq_of_extract extracted
                          rw [← rawAtom]
                          exact fixed raw fixedParts.2
                        · have factorMember : raw.atom ∈ pattern.atoms := by
                            simpa [List.contains_iff_mem] using replayBranch
                          obtain ⟨carrier, carrierMember, replayEqual⟩ :=
                            replay raw.atom factorMember
                          have rawAtom := rawExecFact_atom_eq_of_extract extracted
                          change ExecutableSubtermsWithin allowed
                            (applySubst substitution
                              (.expression (.symbol "exec" :: tail)))
                          rw [← rawAtom, replayEqual]
                          exact spaceWithin carrier carrierMember
            | grounded value =>
                have rootNone :
                    extractRawExecFact
                      (applySubst substitution
                        (.expression (.grounded value :: tail))) = none := by
                  simp [applySubst, applySubst.applySubstList,
                    extractRawExecFact]
                have rootNone' :
                    extractRawExecFact (.expression
                      (applySubst.applySubstList substitution
                        (.grounded value :: tail))) = none := by
                  simpa only [applySubst] using rootNone
                apply executableSubtermsWithin_expression
                · intro raw root
                  rw [rootNone'] at root
                  cases root
                · exact compatibleExecutableTemplatesSafe_applySubst
                    allowed pattern space substitution fixed spaceWithin values
                    replay (.grounded value :: tail) safe
            | expression inner =>
                have rootNone :
                    extractRawExecFact
                      (applySubst substitution
                        (.expression (.expression inner :: tail))) = none := by
                  simp [applySubst, applySubst.applySubstList,
                    extractRawExecFact]
                have rootNone' :
                    extractRawExecFact (.expression
                      (applySubst.applySubstList substitution
                        (.expression inner :: tail))) = none := by
                  simpa only [applySubst] using rootNone
                apply executableSubtermsWithin_expression
                · intro raw root
                  rw [rootNone'] at root
                  cases root
                · exact compatibleExecutableTemplatesSafe_applySubst
                    allowed pattern space substitution fixed spaceWithin values
                    replay (.expression inner :: tail) safe

  /-- List companion of
  `compatibleExecutableTemplateSafe_applySubst`. -/
  theorem compatibleExecutableTemplatesSafe_applySubst
      (allowed : List RawExecFact) (pattern : Pattern) (space : CSpace)
      (substitution : Subst)
      (fixed : ∀ raw ∈ allowed,
        ExecutableSubtermsWithin allowed raw.atom)
      (spaceWithin : AtomsWithin (ExecutableSubtermsWithin allowed) space)
      (values : SubstitutionValuesWithin
        (ExecutableSubtermsWithin allowed) substitution)
      (replay : ∀ factor ∈ pattern.atoms,
        ∃ carrier ∈ space, applySubst substitution factor = carrier) : ∀ templates,
      compatibleExecutableTemplatesSafe allowed pattern templates = true →
        ExecutableSubtermListWithin allowed
          (applySubst.applySubstList substitution templates)
    | [], _ => by exact executableSubtermListWithin_nil allowed
    | template :: templates, safe => by
        simp only [compatibleExecutableTemplatesSafe, Bool.and_eq_true] at safe
        simp only [applySubst.applySubstList]
        apply executableSubtermListWithin_cons.mpr
        constructor
        · exact compatibleExecutableTemplateSafe_applySubst
            allowed pattern space substitution fixed spaceWithin values replay
            template safe.1
        · exact compatibleExecutableTemplatesSafe_applySubst
            allowed pattern space substitution fixed spaceWithin values replay
            templates safe.2
end

/-- A complete compatible match supplies both the inherited substitution
authority and the exact replay witnesses required by the transport theorem. -/
theorem cmatchInputSpec_compat_compatibleExecutableTemplateSafe_applySubst
    (allowed : List RawExecFact) (pattern : Pattern) (space : CSpace)
    {substitution : Subst}
    (fixed : ∀ raw ∈ allowed,
      ExecutableSubtermsWithin allowed raw.atom)
    (spaceWithin : AtomsWithin (ExecutableSubtermsWithin allowed) space)
    (matchMember : substitution ∈
      (cmatchInputSpec [] space (.compat pattern)).map Prod.fst) :
    ∀ template,
      compatibleExecutableTemplateSafe allowed pattern template = true →
        ExecutableSubtermsWithin allowed (applySubst substitution template) := by
  intro template safe
  apply compatibleExecutableTemplateSafe_applySubst
    allowed pattern space substitution fixed spaceWithin
  · exact cmatchInputSpec_compat_substitutionValuesWithin
      (ExecutableSubtermsWithin allowed)
      (executableSubtermsWithin_hereditary allowed)
      space spaceWithin pattern matchMember
  · intro factor factorMember
    exact cmatchInputSpec_compat_factor_replay_origin
      space pattern factor factorMember matchMember
  · exact safe

/-! ## Controls -/

private def controlDirective : Atom :=
  .expression [.symbol "exec", .symbol "location",
    .expression [.symbol "I"], .expression [.symbol "O"]]

private def controlRawDirective : RawExecFact :=
  ⟨controlDirective, .symbol "location",
    .expression [.symbol "I"], .expression [.symbol "O"]⟩

/-- A compiler-fixed directive is accepted when it belongs to the fixed
inventory. -/
theorem fixed_authorized_directive_is_compatible_replay_safe :
    compatibleExecutableTemplateSafe [controlRawDirective]
      (mkPattern []) controlDirective = true := by
  decide

/-- A whole directive listed as an input factor is accepted for exact replay
even when the fixed inventory is empty. -/
theorem input_directive_is_compatible_replay_safe :
    compatibleExecutableTemplateSafe []
      (mkPattern [controlDirective]) controlDirective = true := by
  decide

/-- An executable shell assembled from a variable payload is not an exact
input-factor replay and remains rejected. -/
theorem assembled_directive_is_not_compatible_replay_safe :
    compatibleExecutableTemplateSafe []
      (mkPattern [.var "payload"])
      (.expression [.symbol "exec", .symbol "location",
        .expression [.symbol "I", .var "payload"],
        .expression [.symbol "O"]]) = false := by
  decide

section AxiomAudit

#print axioms compatibleExecutableTemplateSafe_applySubst
#print axioms compatibleExecutableTemplatesSafe_applySubst
#print axioms cmatchInputSpec_compat_compatibleExecutableTemplateSafe_applySubst
#print axioms fixed_authorized_directive_is_compatible_replay_safe
#print axioms input_directive_is_compatible_replay_safe
#print axioms assembled_directive_is_not_compatible_replay_safe

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
