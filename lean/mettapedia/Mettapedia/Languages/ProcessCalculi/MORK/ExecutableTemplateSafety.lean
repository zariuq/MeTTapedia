import Mettapedia.Languages.ProcessCalculi.MORK.ExecutableSubtermSafety

/-!
# Static executable-template safety

Matching may transport a previously authorized executable value, but an
output template must not assemble a fresh `(exec ...)` shell from independent
matched pieces.  This module defines the static condition that separates
those cases.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

mutual
  /-- A template is executable-safe when a substitution can only transport
authorized directives or retain compiler-fixed ones.  A variable at an
expression head is rejected because it could become the `exec` head. -/
  def executableTemplateSafe (allowed : List RawExecFact) : Atom → Bool
    | .var _ | .symbol _ | .grounded _ => true
    | atom@(.expression children) =>
        match children with
        | .var _ :: _ => false
        | .symbol head :: _ =>
            if head == "exec" then
              match extractRawExecFact atom with
              | none => executableTemplatesSafe allowed children
              | some raw =>
                  (atomFreeVars atom == []) && raw ∈ allowed &&
                    executableTemplatesSafe allowed children
            else executableTemplatesSafe allowed children
        | _ => executableTemplatesSafe allowed children

  /-- List companion of `executableTemplateSafe`. -/
  def executableTemplatesSafe (allowed : List RawExecFact) : List Atom → Bool
    | [] => true
    | atom :: atoms =>
        executableTemplateSafe allowed atom &&
          executableTemplatesSafe allowed atoms
end

/- An atom containing no free variables is unchanged by any substitution. -/
mutual
  theorem applySubst_eq_self_of_atomFreeVars_nil
      (substitution : Subst) : ∀ atom,
      atomFreeVars atom = [] → applySubst substitution atom = atom
    | .var name, free => by simp [atomFreeVars] at free
    | .symbol _, _ => rfl
    | .grounded _, _ => rfl
    | .expression atoms, free => by
        simp only [atomFreeVars] at free
        rw [show applySubst substitution (.expression atoms) =
          .expression (applySubst.applySubstList substitution atoms) by rfl]
        congr
        exact applySubstList_eq_self_of_atomFreeVarsList_nil
          substitution atoms free

  theorem applySubstList_eq_self_of_atomFreeVarsList_nil
      (substitution : Subst) : ∀ atoms,
      atomFreeVars.atomFreeVarsList atoms = [] →
        applySubst.applySubstList substitution atoms = atoms
    | [], _ => rfl
    | atom :: atoms, free => by
        simp only [atomFreeVars.atomFreeVarsList,
          List.append_eq_nil_iff] at free
        simp only [applySubst.applySubstList]
        rw [applySubst_eq_self_of_atomFreeVars_nil substitution atom free.1,
          applySubstList_eq_self_of_atomFreeVarsList_nil
            substitution atoms free.2]
end

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

/-- A fixed `exec` head with a non-directive arity cannot become a directive
after substitution, because substitution preserves expression arity. -/
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

/-! ## Static authority -/

mutual
  /-- Static executable-template safety means every directive already written
  by the template belongs to the declared inventory. -/
  theorem executableTemplateSafe_static
      (allowed : List RawExecFact) : ∀ template,
      executableTemplateSafe allowed template = true →
        ExecutableSubtermsWithin allowed template
    | .var _, _ => by
        intro raw member
        simp only [rawExecSubterms, Option.mem_toList] at member
        cases member
    | .symbol _, _ => by
        intro raw member
        simp only [rawExecSubterms, Option.mem_toList] at member
        cases member
    | .grounded _, _ => by
        intro raw member
        simp only [rawExecSubterms, Option.mem_toList] at member
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
            | var name => simp [executableTemplateSafe] at safe
            | symbol name =>
                cases headEq : name == "exec" with
                | false =>
                    have listSafe :
                        executableTemplatesSafe allowed
                          (.symbol name :: tail) = true := by
                      simpa [executableTemplateSafe, headEq] using safe
                    have notName : name ≠ "exec" := by
                      intro equal
                      subst name
                      simp at headEq
                    apply executableSubtermsWithin_expression
                    · intro raw extracted
                      unfold extractRawExecFact at extracted
                      simp [notName] at extracted
                    · exact executableTemplatesSafe_static allowed
                        (.symbol name :: tail) listSafe
                | true =>
                    have nameEq : name = "exec" := by simpa using headEq
                    subst name
                    cases extracted :
                        extractRawExecFact
                          (.expression (.symbol "exec" :: tail)) with
                    | none =>
                        have listSafe :
                            executableTemplatesSafe allowed
                              (.symbol "exec" :: tail) = true := by
                          simpa [executableTemplateSafe, extracted] using safe
                        apply executableSubtermsWithin_expression
                        · intro raw root
                          rw [extracted] at root
                          cases root
                        · exact executableTemplatesSafe_static allowed
                            (.symbol "exec" :: tail) listSafe
                    | some raw =>
                        have splitSafe :
                            (atomFreeVars
                                (.expression (.symbol "exec" :: tail)) = [] ∧
                              raw ∈ allowed) ∧
                              executableTemplatesSafe allowed
                                (.symbol "exec" :: tail) = true := by
                          simpa [executableTemplateSafe, extracted,
                            Bool.and_eq_true] using safe
                        apply executableSubtermsWithin_expression
                        · intro candidate candidateExtract
                          have equal := Option.some.inj
                            (extracted.symm.trans candidateExtract)
                          cases equal
                          exact splitSafe.1.2
                        · exact executableTemplatesSafe_static allowed
                            (.symbol "exec" :: tail) splitSafe.2
            | grounded value =>
                apply executableSubtermsWithin_expression
                · intro raw extracted
                  simp only [extractRawExecFact] at extracted
                  cases extracted
                · exact executableTemplatesSafe_static allowed
                    (.grounded value :: tail) safe
            | expression inner =>
                apply executableSubtermsWithin_expression
                · intro raw extracted
                  simp only [extractRawExecFact] at extracted
                  cases extracted
                · exact executableTemplatesSafe_static allowed
                    (.expression inner :: tail) safe

  /-- List companion of `executableTemplateSafe_static`. -/
  theorem executableTemplatesSafe_static
      (allowed : List RawExecFact) : ∀ templates,
      executableTemplatesSafe allowed templates = true →
        ExecutableSubtermListWithin allowed templates
    | [], _ => by exact executableSubtermListWithin_nil allowed
    | template :: templates, safe => by
        simp only [executableTemplatesSafe, Bool.and_eq_true] at safe
        apply executableSubtermListWithin_cons.mpr
        constructor
        · exact executableTemplateSafe_static allowed template safe.1
        · exact executableTemplatesSafe_static allowed templates safe.2
end

/-! ## Substitution transport -/

mutual
  /-- Instantiating a static executable-safe template preserves recursive
  executable authority whenever every substitution value has that authority.
  The only executable shell a template may retain is a variable-free,
  compiler-authorized one. -/
  theorem executableTemplateSafe_applySubst
      (allowed : List RawExecFact) (substitution : Subst)
      (values : SubstitutionValuesWithin
        (ExecutableSubtermsWithin allowed) substitution) : ∀ template,
      executableTemplateSafe allowed template = true →
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
            | var name => simp [executableTemplateSafe] at safe
            | symbol name =>
                cases headEq : name == "exec" with
                | false =>
                    have listSafe :
                        executableTemplatesSafe allowed
                          (.symbol name :: tail) = true := by
                      simpa [executableTemplateSafe, headEq] using safe
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
                    · exact executableTemplatesSafe_applySubst allowed
                        substitution values (.symbol name :: tail) listSafe
                | true =>
                    have nameEq : name = "exec" := by simpa using headEq
                    subst name
                    cases extracted :
                        extractRawExecFact
                          (.expression (.symbol "exec" :: tail)) with
                    | none =>
                        have listSafe :
                            executableTemplatesSafe allowed
                              (.symbol "exec" :: tail) = true := by
                          simpa [executableTemplateSafe, extracted] using safe
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
                        · exact executableTemplatesSafe_applySubst allowed
                            substitution values (.symbol "exec" :: tail)
                            listSafe
                    | some raw =>
                        have splitSafe :
                            (atomFreeVars
                                (.expression (.symbol "exec" :: tail)) = [] ∧
                              raw ∈ allowed) ∧
                              executableTemplatesSafe allowed
                                (.symbol "exec" :: tail) = true := by
                          simpa [executableTemplateSafe, extracted,
                            Bool.and_eq_true] using safe
                        change ExecutableSubtermsWithin allowed
                          (applySubst substitution
                            (.expression (.symbol "exec" :: tail)))
                        rw [applySubst_eq_self_of_atomFreeVars_nil
                          substitution (.expression (.symbol "exec" :: tail))
                          splitSafe.1.1]
                        exact executableTemplateSafe_static allowed
                          (.expression (.symbol "exec" :: tail)) safe
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
                · exact executableTemplatesSafe_applySubst allowed
                    substitution values (.grounded value :: tail) safe
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
                · exact executableTemplatesSafe_applySubst allowed
                    substitution values (.expression inner :: tail) safe

  /-- List companion of `executableTemplateSafe_applySubst`. -/
  theorem executableTemplatesSafe_applySubst
      (allowed : List RawExecFact) (substitution : Subst)
      (values : SubstitutionValuesWithin
        (ExecutableSubtermsWithin allowed) substitution) : ∀ templates,
      executableTemplatesSafe allowed templates = true →
        ExecutableSubtermListWithin allowed
          (applySubst.applySubstList substitution templates)
    | [], _ => by exact executableSubtermListWithin_nil allowed
    | template :: templates, safe => by
        simp only [executableTemplatesSafe, Bool.and_eq_true] at safe
        simp only [applySubst.applySubstList]
        apply executableSubtermListWithin_cons.mpr
        constructor
        · exact executableTemplateSafe_applySubst allowed substitution
            values template safe.1
        · exact executableTemplatesSafe_applySubst allowed substitution
            values templates safe.2
end

/-! ## Controls -/

private def controlDirective : Atom :=
  .expression [.symbol "exec", .symbol "location",
    .expression [.symbol "I"], .expression [.symbol "O"]]

private def controlRawDirective : RawExecFact :=
  ⟨controlDirective, .symbol "location",
    .expression [.symbol "I"], .expression [.symbol "O"]⟩

/-- A fixed directive already present in the declared inventory is accepted. -/
theorem fixed_authorized_directive_template_is_safe :
    executableTemplateSafe [controlRawDirective] controlDirective = true := by
  decide

/-- A variable in directive-head position is rejected: it could synthesize
new scheduler authority from otherwise harmless matched data. -/
theorem variable_head_template_is_rejected :
    executableTemplateSafe []
      (.expression [.var "head", .symbol "location",
        .expression [.symbol "I"], .expression [.symbol "O"]]) = false := by
  decide

/-- A fixed directive with an input variable is rejected because substituting
that variable changes the exact directive identity. -/
theorem parameterized_directive_template_is_rejected :
    executableTemplateSafe [controlRawDirective]
      (.expression [.symbol "exec", .symbol "location",
        .expression [.symbol "I", .var "payload"],
        .expression [.symbol "O"]]) = false := by
  decide

section AxiomAudit

#print axioms applySubst_eq_self_of_atomFreeVars_nil
#print axioms applySubstList_eq_self_of_atomFreeVarsList_nil
#print axioms executableTemplateSafe_static
#print axioms executableTemplatesSafe_static
#print axioms executableTemplateSafe_applySubst
#print axioms executableTemplatesSafe_applySubst
#print axioms fixed_authorized_directive_template_is_safe
#print axioms variable_head_template_is_rejected
#print axioms parameterized_directive_template_is_rejected

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
