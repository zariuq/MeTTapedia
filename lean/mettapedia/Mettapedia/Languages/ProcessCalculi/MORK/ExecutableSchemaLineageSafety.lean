import Mettapedia.Languages.ProcessCalculi.MORK.ExecutableSchemaSafety

/-!
# Lineage-safe executable schemas

The fixed executable-schema inventory must remain meaningful after a directive
is copied through source-derived substitutions.  This module records both the
recursive fixed-head discipline and the finite schema lineage of every
executable shell.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

mutual
  /-- A syntax tree is lineage-authorized when every executable shell has a
fixed symbolic head, recursively authorized children, and a derivation from a
fixed executable schema. -/
  def ExecutableSchemaAtomAuthorized (schemas : List RawExecFact) : Atom → Prop
    | .var _ | .symbol _ | .grounded _ => True
    | atom@(.expression children) =>
        ExecutableSchemaAtomsAuthorized schemas children ∧
          match children with
          | .var _ :: _ => False
          | .symbol name :: _ =>
              if name = "exec" then
                match extractRawExecFact atom with
                | none => True
                | some raw => RawExecFactFromSchemas schemas raw
              else True
          | _ => True

  /-- List companion of `ExecutableSchemaAtomAuthorized`. -/
  def ExecutableSchemaAtomsAuthorized (schemas : List RawExecFact) :
      List Atom → Prop
    | [] => True
    | atom :: atoms =>
        ExecutableSchemaAtomAuthorized schemas atom ∧
          ExecutableSchemaAtomsAuthorized schemas atoms
end

/-- A valid fixed-head executable shell remains an executable shell after a
substitution.  Its lineage is extended by precisely that substitution. -/
private theorem rawExecFactFromSchemas_applySubst_execHead
    (schemas : List RawExecFact) (substitution : Subst)
    (tail : List Atom) (raw : RawExecFact)
    (extracted : extractRawExecFact (.expression (.symbol "exec" :: tail)) =
      some raw)
    (authorized : RawExecFactFromSchemas schemas raw) :
    ∃ output : RawExecFact,
      extractRawExecFact
        (applySubst substitution (.expression (.symbol "exec" :: tail))) =
          some output ∧
        RawExecFactFromSchemas schemas output := by
  cases tail with
  | nil => simp [extractRawExecFact] at extracted
  | cons location tail =>
      cases tail with
      | nil => simp [extractRawExecFact] at extracted
      | cons input tail =>
          cases tail with
          | nil => simp [extractRawExecFact] at extracted
          | cons template tail =>
              cases tail with
              | nil =>
                  simp only [extractRawExecFact] at extracted
                  injection extracted with rawEqual
                  subst raw
                  let output : RawExecFact :=
                    ⟨applySubst substitution
                        (.expression [.symbol "exec", location, input, template]),
                      applySubst substitution location,
                      applySubst substitution input,
                      applySubst substitution template⟩
                  refine ⟨output, ?_, ?_⟩
                  · simp [output, applySubst, applySubst.applySubstList,
                      extractRawExecFact]
                  · rcases authorized with ⟨schema, schemaMember, lineage,
                      lineageEqual⟩
                    refine ⟨schema, schemaMember, lineage ++ [substitution], ?_⟩
                    calc
                      applySubstChain (lineage ++ [substitution]) schema.atom =
                          applySubstChain [substitution]
                            (applySubstChain lineage schema.atom) :=
                        applySubstChain_append lineage [substitution] schema.atom
                      _ = applySubst substitution
                            (applySubstChain lineage schema.atom) := rfl
                      _ = applySubst substitution
                            (.expression [.symbol "exec", location, input,
                              template]) := by rw [lineageEqual]
                      _ = output.atom := rfl
              | cons extra tail => simp [extractRawExecFact] at extracted

/-- A malformed fixed-head shell remains malformed under substitution because
the `exec` head and its arity are syntax, not matched data. -/
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

mutual
  /-- Substituting lineage-authorized values preserves both fixed expression
heads and every fixed-schema lineage. -/
  theorem executableSchemaAtomAuthorized_applySubst
      (schemas : List RawExecFact) (substitution : Subst)
      (values : SubstitutionValuesWithin
        (ExecutableSchemaAtomAuthorized schemas) substitution) : ∀ atom,
      ExecutableSchemaAtomAuthorized schemas atom →
        ExecutableSchemaAtomAuthorized schemas (applySubst substitution atom)
    | .var name, _ => by
        cases found : substitution.lookup name with
        | none => simp [applySubst, found, ExecutableSchemaAtomAuthorized]
        | some value =>
            simpa [applySubst, found] using values.lookup found
    | .symbol _, _ => trivial
    | .grounded _, _ => trivial
    | .expression children, authorized => by
        cases children with
        | nil => exact ⟨trivial, trivial⟩
        | cons head tail =>
            rcases authorized with ⟨childrenAuthorized, rootAuthorized⟩
            have childrenResult :=
              executableSchemaAtomsAuthorized_applySubst schemas substitution
                values (head :: tail) childrenAuthorized
            cases head with
            | var name =>
                simp at rootAuthorized
            | symbol name =>
                by_cases exec : name = "exec"
                · subst name
                  cases extracted :
                      extractRawExecFact
                        (.expression (.symbol "exec" :: tail)) with
                  | none =>
                      refine ⟨childrenResult, ?_⟩
                      have targetNone :=
                        extractRawExecFact_applySubst_execHead_none
                          substitution tail extracted
                      change (match extractRawExecFact
                        (applySubst substitution
                          (.expression (.symbol "exec" :: tail))) with
                        | none => True
                        | some raw => RawExecFactFromSchemas schemas raw)
                      rw [targetNone]
                      trivial
                  | some raw =>
                      have rawAuthorized : RawExecFactFromSchemas schemas raw := by
                        simpa [ExecutableSchemaAtomAuthorized, extracted]
                          using rootAuthorized
                      obtain ⟨output, targetExtract, outputAuthorized⟩ :=
                        rawExecFactFromSchemas_applySubst_execHead schemas
                          substitution tail raw extracted rawAuthorized
                      refine ⟨childrenResult, ?_⟩
                      change (match extractRawExecFact
                        (applySubst substitution
                          (.expression (.symbol "exec" :: tail))) with
                        | none => True
                        | some raw => RawExecFactFromSchemas schemas raw)
                      rw [targetExtract]
                      exact outputAuthorized
                · refine ⟨childrenResult, ?_⟩
                  change (if name = "exec" then
                    match extractRawExecFact
                      (.expression (.symbol name ::
                        applySubst.applySubstList substitution tail)) with
                    | none => True
                    | some raw => RawExecFactFromSchemas schemas raw
                    else True)
                  rw [if_neg exec]
                  trivial
            | grounded value =>
                exact ⟨childrenResult, trivial⟩
            | expression inner =>
                exact ⟨childrenResult, trivial⟩

  /-- List companion of
`executableSchemaAtomAuthorized_applySubst`. -/
  theorem executableSchemaAtomsAuthorized_applySubst
      (schemas : List RawExecFact) (substitution : Subst)
      (values : SubstitutionValuesWithin
        (ExecutableSchemaAtomAuthorized schemas) substitution) : ∀ atoms,
      ExecutableSchemaAtomsAuthorized schemas atoms →
        ExecutableSchemaAtomsAuthorized schemas
          (applySubst.applySubstList substitution atoms)
    | [], _ => trivial
    | atom :: atoms, authorized => by
        rcases authorized with ⟨atomAuthorized, atomsAuthorized⟩
        exact ⟨executableSchemaAtomAuthorized_applySubst schemas substitution
          values atom atomAuthorized,
          executableSchemaAtomsAuthorized_applySubst schemas substitution
            values atoms atomsAuthorized⟩
end

/-- A list authorization witnesses each listed atom. -/
theorem executableSchemaAtomsAuthorized_mem
    (schemas : List RawExecFact) {atoms : List Atom} {atom : Atom}
    (authorized : ExecutableSchemaAtomsAuthorized schemas atoms)
    (member : atom ∈ atoms) :
    ExecutableSchemaAtomAuthorized schemas atom := by
  induction atoms with
  | nil => simp at member
  | cons head tail induction =>
      rcases authorized with ⟨headAuthorized, tailAuthorized⟩
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst atom
        exact headAuthorized
      · exact induction tailAuthorized member

/-- Lineage authorization descends to every expression child, so it is a
valid invariant for the generic matching safety theorem. -/
theorem executableSchemaAtomAuthorized_hereditary
    (schemas : List RawExecFact) :
    AtomPropertyHereditary (ExecutableSchemaAtomAuthorized schemas) := by
  intro children authorized child member
  exact executableSchemaAtomsAuthorized_mem schemas authorized.1 member

/-- The template field of a scheduler-visible executable shell is one of its
authorized syntax children.  This is the exact bridge from whole directive
authorization to the syntax consumed by the strict directive decoder. -/
theorem executableSchemaAtomAuthorized_rawTemplate
    (schemas : List RawExecFact) {atom : Atom} {raw : RawExecFact}
    (extracted : extractRawExecFact atom = some raw)
    (authorized : ExecutableSchemaAtomAuthorized schemas atom) :
    ExecutableSchemaAtomAuthorized schemas raw.templateExpr := by
  unfold extractRawExecFact at extracted
  split at extracted <;> try contradiction
  next equal =>
    injection extracted with rawEqual
    subst raw
    exact executableSchemaAtomsAuthorized_mem schemas authorized.1 (by simp)

mutual
  /-- The fixed syntactic schema checker establishes the semantic lineage
authorization predicate at the initial compiler boundary. -/
  theorem executableSchemaTemplateSafe_authorized
      (schemas : List RawExecFact) : ∀ atom,
      executableSchemaTemplateSafe schemas atom = true →
        ExecutableSchemaAtomAuthorized schemas atom
    | .var _, _ => trivial
    | .symbol _, _ => trivial
    | .grounded _, _ => trivial
    | .expression children, safe => by
        cases children with
        | nil => exact ⟨trivial, trivial⟩
        | cons head tail =>
            cases head with
            | var name =>
                simp [executableSchemaTemplateSafe] at safe
            | symbol name =>
                by_cases exec : name = "exec"
                · subst name
                  cases extracted :
                      extractRawExecFact (.expression (.symbol "exec" :: tail)) with
                  | none =>
                      have childrenSafe :
                          executableSchemaTemplatesSafe schemas
                            (.symbol "exec" :: tail) = true := by
                        simpa [executableSchemaTemplateSafe, extracted]
                          using safe
                      refine ⟨executableSchemaTemplatesSafe_authorized schemas
                        (.symbol "exec" :: tail) childrenSafe, ?_⟩
                      simp [extracted]
                  | some raw =>
                      have parts : raw ∈ schemas ∧
                          executableSchemaTemplatesSafe schemas
                            (.symbol "exec" :: tail) = true := by
                        simpa [executableSchemaTemplateSafe, extracted,
                          Bool.and_eq_true] using safe
                      refine ⟨executableSchemaTemplatesSafe_authorized schemas
                        (.symbol "exec" :: tail) parts.2, ?_⟩
                      simpa [ExecutableSchemaAtomAuthorized, extracted] using
                        (show RawExecFactFromSchemas schemas raw from
                          ⟨raw, parts.1, [], rfl⟩)
                · have childrenSafe :
                    executableSchemaTemplatesSafe schemas
                      (.symbol name :: tail) = true := by
                    simp [executableSchemaTemplateSafe, exec] at safe
                    exact safe
                  refine ⟨executableSchemaTemplatesSafe_authorized schemas
                    (.symbol name :: tail) childrenSafe, ?_⟩
                  simp [exec]
            | grounded value =>
                exact ⟨executableSchemaTemplatesSafe_authorized schemas
                  (.grounded value :: tail) safe, trivial⟩
            | expression inner =>
                exact ⟨executableSchemaTemplatesSafe_authorized schemas
                  (.expression inner :: tail) safe, trivial⟩

  /-- List companion of `executableSchemaTemplateSafe_authorized`. -/
  theorem executableSchemaTemplatesSafe_authorized
      (schemas : List RawExecFact) : ∀ atoms,
      executableSchemaTemplatesSafe schemas atoms = true →
        ExecutableSchemaAtomsAuthorized schemas atoms
    | [], _ => trivial
    | atom :: atoms, safe => by
        have parts : executableSchemaTemplateSafe schemas atom = true ∧
            executableSchemaTemplatesSafe schemas atoms = true := by
          simpa [executableSchemaTemplatesSafe, Bool.and_eq_true] using safe
        exact ⟨executableSchemaTemplateSafe_authorized schemas atom parts.1,
          executableSchemaTemplatesSafe_authorized schemas atoms parts.2⟩
end

/-- Every sink that can place an atom into support carries an authorized
syntax tree.  Removal sinks cannot introduce executable authority. -/
def ExecutableSchemaAuthorizedTemplate (schemas : List RawExecFact)
    (template : Template) : Prop :=
  ∀ sink ∈ template.sinks,
    match sink with
    | .add atom | .head _ atom | .tail _ atom =>
        ExecutableSchemaAtomAuthorized schemas atom
    | .remove _ => True

/-- The fixed Boolean template check establishes the semantic lineage
authorization of every support-producing sink. -/
theorem executableSchemaSafeTemplate_authorized
    (schemas : List RawExecFact) (template : Template)
    (safe : ExecutableSchemaSafeTemplate schemas template) :
    ExecutableSchemaAuthorizedTemplate schemas template := by
  intro sink member
  cases sink with
  | add atom =>
      have sinkSafe := (List.all_eq_true.mp safe) (.add atom) member
      apply executableSchemaTemplateSafe_authorized schemas atom
      simpa [executableSchemaSafeSink] using sinkSafe
  | remove atom => trivial
  | head count atom =>
      have sinkSafe := (List.all_eq_true.mp safe) (.head count atom) member
      apply executableSchemaTemplateSafe_authorized schemas atom
      simpa [executableSchemaSafeSink] using sinkSafe
  | tail count atom =>
      have sinkSafe := (List.all_eq_true.mp safe) (.tail count atom) member
      apply executableSchemaTemplateSafe_authorized schemas atom
      simpa [executableSchemaSafeSink] using sinkSafe

private theorem instantiateRuleTemplateAtom_eq_applySubst
    {input : InputSpec} {substitution : Subst} {authored atom : Atom}
    (instantiated : instantiateRuleTemplateAtom? input substitution authored =
      some atom) :
    applySubst substitution authored = atom := by
  unfold instantiateRuleTemplateAtom? at instantiated
  split at instantiated
  · exact Option.some.inj instantiated
  · contradiction

/-- A lineage-authorized template meets the support-addition obligation of
rule-scoped execution.  Inherited data is reauthorized by the substitution
closure theorem; no matcher result can synthesize a variable-headed shell. -/
theorem executableSchemaAuthorizedTemplate_ruleScopedAdditions
    (schemas : List RawExecFact) (input : InputSpec) (rows : List Subst)
    (template : Template)
    (authorized : ExecutableSchemaAuthorizedTemplate schemas template)
    (values : ∀ substitution ∈ rows,
      SubstitutionValuesWithin
        (ExecutableSchemaAtomAuthorized schemas) substitution) :
    RuleScopedTemplateAdditionsWithin
      (ExecutableSchemaAtomAuthorized schemas) input rows template := by
  intro sink sinkMember
  cases sink with
  | remove atom => trivial
  | add authored =>
      intro substitution rowMember atom instantiated
      have authoredAuthorized := authorized (.add authored) sinkMember
      have instantiatedEqual :=
        instantiateRuleTemplateAtom_eq_applySubst instantiated
      rw [← instantiatedEqual]
      exact executableSchemaAtomAuthorized_applySubst schemas substitution
        (values substitution rowMember) authored authoredAuthorized
  | head count authored =>
      intro substitution rowMember atom instantiated
      have authoredAuthorized := authorized (.head count authored) sinkMember
      have instantiatedEqual :=
        instantiateRuleTemplateAtom_eq_applySubst instantiated
      rw [← instantiatedEqual]
      exact executableSchemaAtomAuthorized_applySubst schemas substitution
        (values substitution rowMember) authored authoredAuthorized
  | tail count authored =>
      intro substitution rowMember atom instantiated
      have authoredAuthorized := authorized (.tail count authored) sinkMember
      have instantiatedEqual :=
        instantiateRuleTemplateAtom_eq_applySubst instantiated
      rw [← instantiatedEqual]
      exact executableSchemaAtomAuthorized_applySubst schemas substitution
        (values substitution rowMember) authored authoredAuthorized

/-- One rule-scoped scheduler firing preserves finite schema lineage when the
selected directive and its parsed template carry the same authorization. -/
theorem cFireRuleScopedSourceExecFact_lineageAuthorized
    (schemas : List RawExecFact) (space : List Atom)
    (directive : SourceExecFact)
    (spaceWithin : AtomsWithin (ExecutableSchemaAtomAuthorized schemas) space)
    (directiveWithin : ExecutableSchemaAtomAuthorized schemas directive.atom)
    (templateAuthorized :
      ExecutableSchemaAuthorizedTemplate schemas directive.rule.tmpl) :
    AtomsWithin (ExecutableSchemaAtomAuthorized schemas)
      (cFireRuleScopedSourceExecFact space directive) := by
  apply cFireRuleScopedSourceExecFact_atomsWithin_of_additions
  · exact spaceWithin
  · dsimp
    apply executableSchemaAuthorizedTemplate_ruleScopedAdditions schemas
      directive.rule.input _ directive.rule.tmpl templateAuthorized
    exact cFireRuleScopedSourceExecFact_matchValuesWithin
      (ExecutableSchemaAtomAuthorized schemas)
      (executableSchemaAtomAuthorized_hereditary schemas)
      space directive spaceWithin directiveWithin

section AxiomAudit

#print axioms executableSchemaAtomsAuthorized_mem
#print axioms executableSchemaAtomAuthorized_hereditary
#print axioms executableSchemaAtomAuthorized_rawTemplate
#print axioms executableSchemaTemplateSafe_authorized
#print axioms executableSchemaTemplatesSafe_authorized
#print axioms rawExecFactFromSchemas_applySubst_execHead
#print axioms executableSchemaAtomAuthorized_applySubst
#print axioms executableSchemaAtomsAuthorized_applySubst
#print axioms executableSchemaSafeTemplate_authorized
#print axioms executableSchemaAuthorizedTemplate_ruleScopedAdditions
#print axioms cFireRuleScopedSourceExecFact_lineageAuthorized

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
