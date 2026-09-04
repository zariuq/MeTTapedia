import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchSafety
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutableSubtermSafety
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution
import Mettapedia.Languages.ProcessCalculi.MORK.RuleScopedMatchSafety

/-!
# Schema-derived executable authority

A verifier may install an executable directive whose data fields have been
instantiated from a successful match.  Literal membership in a finite rule
inventory is then too strong: the directive's schema is fixed, while its data
is deliberately dynamic.  This module separates fixed executable structure
from values inherited through a substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Apply a finite source-derived sequence of substitutions.  A directive may
be copied through more than one scheduler step before it becomes active, so
authority records that finite lineage rather than only the latest rewrite. -/
def applySubstChain : List Subst → Atom → Atom
  | [], atom => atom
  | substitution :: substitutions, atom =>
      applySubstChain substitutions (applySubst substitution atom)

@[simp] theorem applySubstChain_nil (atom : Atom) :
    applySubstChain [] atom = atom := rfl

@[simp] theorem applySubstChain_singleton (substitution : Subst) (atom : Atom) :
    applySubstChain [substitution] atom = applySubst substitution atom := rfl

/-- A substitution lineage respects concatenation: the right-hand lineage
continues exactly where the left-hand lineage leaves off. -/
theorem applySubstChain_append : ∀ (before after : List Subst) (atom : Atom),
    applySubstChain (before ++ after) atom =
      applySubstChain after (applySubstChain before atom)
  | [], after, atom => rfl
  | substitution :: before, after, atom => by
      simpa [applySubstChain] using
        applySubstChain_append before after (applySubst substitution atom)

/-- One concrete executable shell is authorized when it descends through a
finite source-derived substitution lineage from a fixed executable schema. -/
def RawExecFactSchemaInstance (schema concrete : RawExecFact) : Prop :=
  ∃ substitutions : List Subst,
    applySubstChain substitutions schema.atom = concrete.atom

/-- An executable shell comes from one member of a fixed schema inventory. -/
def RawExecFactFromSchemas (schemas : List RawExecFact)
    (concrete : RawExecFact) : Prop :=
  ∃ schema ∈ schemas, RawExecFactSchemaInstance schema concrete

/-- Every executable shell nested in an atom comes from the fixed schemas. -/
def ExecutableSubtermsFromSchemas (schemas : List RawExecFact)
    (atom : Atom) : Prop :=
  ∀ raw ∈ rawExecSubterms atom, RawExecFactFromSchemas schemas raw

/-- List form of schema-derived executable authority. -/
def ExecutableSubtermListFromSchemas (schemas : List RawExecFact)
    (atoms : List Atom) : Prop :=
  ∀ raw ∈ rawExecSubtermsList atoms, RawExecFactFromSchemas schemas raw

mutual
  /-- A template is safe to instantiate when every executable shell it authors
  has a fixed symbolic head and belongs to the schema inventory.  Subterms are
  checked recursively so a variable cannot become the head of a freshly
  assembled nested directive. -/
  def executableSchemaTemplateSafe (schemas : List RawExecFact) : Atom → Bool
    | .var _ | .symbol _ | .grounded _ => true
    | atom@(.expression children) =>
        match children with
        | .var _ :: _ => false
        | .symbol head :: _ =>
            let childrenSafe := executableSchemaTemplatesSafe schemas children
            if head == "exec" then
              match extractRawExecFact atom with
              | none => childrenSafe
              | some raw => (raw ∈ schemas) && childrenSafe
            else childrenSafe
        | _ => executableSchemaTemplatesSafe schemas children

  def executableSchemaTemplatesSafe (schemas : List RawExecFact) :
      List Atom → Bool
    | [] => true
    | atom :: atoms =>
        executableSchemaTemplateSafe schemas atom &&
          executableSchemaTemplatesSafe schemas atoms
end

/-- The schema check concerns sinks that can add rows.  Removes cannot
introduce executable authority; `head` and `tail` select staged rows that are
then unioned into the live support, so their authored atoms require the same
structural check as ordinary additions. -/
def executableSchemaSafeSink (schemas : List RawExecFact) : Sink → Bool
  | .add atom => executableSchemaTemplateSafe schemas atom
  | .remove _ => true
  | .head _ atom | .tail _ atom => executableSchemaTemplateSafe schemas atom

/-- Every authored addition in the template has fixed executable structure. -/
def ExecutableSchemaSafeTemplate (schemas : List RawExecFact)
    (template : Template) : Prop :=
  template.sinks.all (executableSchemaSafeSink schemas) = true

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

private theorem applySubst_nil : ∀ atom : Atom, applySubst [] atom = atom
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression atoms => by
      simp only [applySubst]
      rw [applySubstList_nil atoms]
where
  applySubstList_nil : ∀ atoms : List Atom,
      applySubst.applySubstList [] atoms = atoms
    | [] => rfl
    | atom :: atoms => by
        simp only [applySubst.applySubstList]
        rw [applySubst_nil atom, applySubstList_nil atoms]

/-! ## Structural transport -/

mutual
  /-- Instantiating a schema-safe template preserves recursively tracked
  executable authority.  Every dynamic value must already be authorized by
  the substitution; every fresh executable root retains a fixed schema. -/
  theorem executableSchemaTemplateSafe_applySubst
      (schemas : List RawExecFact) (substitution : Subst)
      (values : SubstitutionValuesWithin
        (ExecutableSubtermsFromSchemas schemas) substitution) : ∀ template,
      executableSchemaTemplateSafe schemas template = true →
        ExecutableSubtermsFromSchemas schemas
          (applySubst substitution template)
    | .var name, _ => by
        cases found : substitution.lookup name with
        | none =>
            intro raw member
            simp [applySubst, found, rawExecSubterms, extractRawExecFact]
              at member
        | some value =>
            simpa [applySubst, found] using values.lookup found
    | .symbol _, _ => by
        intro raw member
        simp [applySubst, rawExecSubterms, extractRawExecFact] at member
    | .grounded _, _ => by
        intro raw member
        simp [applySubst, rawExecSubterms, extractRawExecFact] at member
    | .expression children, safe => by
        cases children with
        | nil =>
            intro raw member
            simp [applySubst, applySubst.applySubstList, rawExecSubterms,
              rawExecSubtermsList, extractRawExecFact] at member
        | cons head tail =>
            cases head with
            | var name =>
                simp [executableSchemaTemplateSafe] at safe
            | symbol name =>
                cases headEq : name == "exec" with
                | false =>
                    have listSafe :
                        executableSchemaTemplatesSafe schemas
                          (.symbol name :: tail) = true := by
                      simpa [executableSchemaTemplateSafe, headEq] using safe
                    have notExec : name ≠ "exec" := by
                      intro equal
                      subst name
                      simp at headEq
                    have rootNone :
                        extractRawExecFact
                          (applySubst substitution
                            (.expression (.symbol name :: tail))) = none := by
                      simp [applySubst, applySubst.applySubstList,
                        extractRawExecFact, notExec]
                    have rootNone' :
                        extractRawExecFact (.expression
                          (applySubst.applySubstList substitution
                            (.symbol name :: tail))) = none := by
                      simpa only [applySubst] using rootNone
                    intro raw member
                    simp only [applySubst, rawExecSubterms, List.mem_append,
                      Option.mem_toList] at member
                    rcases member with root | nested
                    · rw [rootNone'] at root
                      cases root
                    · exact executableSchemaTemplatesSafe_applySubst schemas
                        substitution values (.symbol name :: tail) listSafe raw
                        nested
                | true =>
                    have nameEq : name = "exec" := by simpa using headEq
                    subst name
                    cases extracted :
                        extractRawExecFact
                          (.expression (.symbol "exec" :: tail)) with
                    | none =>
                        have listSafe :
                            executableSchemaTemplatesSafe schemas
                              (.symbol "exec" :: tail) = true := by
                          simpa [executableSchemaTemplateSafe, extracted]
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
                        intro raw member
                        simp only [applySubst, rawExecSubterms,
                          List.mem_append, Option.mem_toList] at member
                        rcases member with root | nested
                        · rw [rootNone'] at root
                          cases root
                        · exact executableSchemaTemplatesSafe_applySubst schemas
                            substitution values (.symbol "exec" :: tail)
                            listSafe raw nested
                    | some schema =>
                        have allowedAndListSafe :
                            schema ∈ schemas ∧
                              executableSchemaTemplatesSafe schemas
                                (.symbol "exec" :: tail) = true := by
                          simpa [executableSchemaTemplateSafe, extracted,
                            Bool.and_eq_true] using safe
                        intro raw member
                        simp only [applySubst, rawExecSubterms,
                          List.mem_append, Option.mem_toList] at member
                        rcases member with root | nested
                        · have outputExtract :
                            extractRawExecFact (.expression
                              (applySubst.applySubstList substitution
                                (.symbol "exec" :: tail))) = some raw := by
                            simpa using root
                          refine ⟨schema, allowedAndListSafe.1,
                            [substitution], ?_⟩
                          calc
                            applySubstChain [substitution] schema.atom =
                                applySubst substitution schema.atom := rfl
                            _ =
                                applySubst substitution
                                  (.expression (.symbol "exec" :: tail)) := by
                              rw [extractRawExecFact_atom_eq extracted]
                            _ = raw.atom :=
                              (extractRawExecFact_atom_eq outputExtract).symm
                        · exact executableSchemaTemplatesSafe_applySubst schemas
                            substitution values (.symbol "exec" :: tail)
                            allowedAndListSafe.2 raw nested
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
                intro raw member
                simp only [applySubst, rawExecSubterms, List.mem_append,
                  Option.mem_toList] at member
                rcases member with root | nested
                · rw [rootNone'] at root
                  cases root
                · exact executableSchemaTemplatesSafe_applySubst schemas
                    substitution values (.grounded value :: tail) safe raw
                    nested
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
                intro raw member
                simp only [applySubst, rawExecSubterms, List.mem_append,
                  Option.mem_toList] at member
                rcases member with root | nested
                · rw [rootNone'] at root
                  cases root
                · exact executableSchemaTemplatesSafe_applySubst schemas
                    substitution values (.expression inner :: tail) safe raw
                    nested

  /-- List companion of
  `executableSchemaTemplateSafe_applySubst`. -/
  theorem executableSchemaTemplatesSafe_applySubst
      (schemas : List RawExecFact) (substitution : Subst)
      (values : SubstitutionValuesWithin
        (ExecutableSubtermsFromSchemas schemas) substitution) : ∀ templates,
      executableSchemaTemplatesSafe schemas templates = true →
        ExecutableSubtermListFromSchemas schemas
          (applySubst.applySubstList substitution templates)
    | [], _ => by
        intro raw member
        simp [applySubst.applySubstList, rawExecSubtermsList] at member
    | template :: templates, safe => by
        have parts :
            executableSchemaTemplateSafe schemas template = true ∧
              executableSchemaTemplatesSafe schemas templates = true := by
          simpa [executableSchemaTemplatesSafe, Bool.and_eq_true] using safe
        intro raw member
        simp only [applySubst.applySubstList, rawExecSubtermsList,
          List.mem_append] at member
        rcases member with head | tail
        · exact executableSchemaTemplateSafe_applySubst schemas substitution
            values template parts.1 raw head
        · exact executableSchemaTemplatesSafe_applySubst schemas substitution
            values templates parts.2 raw tail
end

/-- A schema-safe template can add only schema-authorized atoms whenever its
matcher substitution already carries schema-authorized values. -/
theorem executableSchemaSafeTemplate_added
    (schemas : List RawExecFact) (rows : List Subst) (template : Template)
    (safe : ExecutableSchemaSafeTemplate schemas template)
    (values : ∀ substitution ∈ rows,
      SubstitutionValuesWithin
        (ExecutableSubtermsFromSchemas schemas) substitution) :
    ReflectiveAddedAtomsWithin (ExecutableSubtermsFromSchemas schemas)
      rows template := by
  intro atom added
  rcases added with
    ⟨sink, sinkMember, authored, sinkEqual,
      substitution, rowMember, instantiated⟩
  subst sink
  have sinkSafe := (List.all_eq_true.mp safe)
    (.add authored) sinkMember
  have authoredSafe :
      executableSchemaTemplateSafe schemas authored = true := by
    simpa [executableSchemaSafeSink] using sinkSafe
  have instantiatedEqual : applySubst substitution authored = atom := by
    unfold instantiateTemplateAtom? at instantiated
    split at instantiated
    · exact Option.some.inj instantiated
    · contradiction
  rw [← instantiatedEqual]
  exact executableSchemaTemplateSafe_applySubst schemas substitution
    (values substitution rowMember) authored authoredSafe

private theorem executableSchemaTemplateSafe_ruleScopedInstantiation
    (schemas : List RawExecFact) (input : InputSpec)
    (substitution : Subst) (authored atom : Atom)
    (values : SubstitutionValuesWithin
      (ExecutableSubtermsFromSchemas schemas) substitution)
    (authoredSafe : executableSchemaTemplateSafe schemas authored = true)
    (instantiated : instantiateRuleTemplateAtom? input substitution authored =
      some atom) :
    ExecutableSubtermsFromSchemas schemas atom := by
  have instantiatedEqual : applySubst substitution authored = atom := by
    unfold instantiateRuleTemplateAtom? at instantiated
    split at instantiated
    · exact Option.some.inj instantiated
    · contradiction
  rw [← instantiatedEqual]
  exact executableSchemaTemplateSafe_applySubst schemas substitution values
    authored authoredSafe

/-- A schema-safe template meets the addition obligation of rule-scoped
execution.  Output-local variables remain harmless: they stay variables under
substitution, whereas every inherited replacement value is already tracked. -/
theorem executableSchemaSafeTemplate_ruleScopedAdditions
    (schemas : List RawExecFact) (input : InputSpec)
    (rows : List Subst) (template : Template)
    (safe : ExecutableSchemaSafeTemplate schemas template)
    (values : ∀ substitution ∈ rows,
      SubstitutionValuesWithin
        (ExecutableSubtermsFromSchemas schemas) substitution) :
    RuleScopedTemplateAdditionsWithin
      (ExecutableSubtermsFromSchemas schemas) input rows template := by
  intro sink sinkMember
  cases sink with
  | remove _ => trivial
  | add authored =>
      intro substitution rowMember atom instantiated
      have sinkSafe := (List.all_eq_true.mp safe)
        (.add authored) sinkMember
      have authoredSafe :
          executableSchemaTemplateSafe schemas authored = true := by
        simpa [executableSchemaSafeSink] using sinkSafe
      exact executableSchemaTemplateSafe_ruleScopedInstantiation schemas input
        substitution authored atom (values substitution rowMember) authoredSafe
        instantiated
  | head count authored =>
      intro substitution rowMember atom instantiated
      have sinkSafe := (List.all_eq_true.mp safe)
        (.head count authored) sinkMember
      have authoredSafe :
          executableSchemaTemplateSafe schemas authored = true := by
        simpa [executableSchemaSafeSink] using sinkSafe
      exact executableSchemaTemplateSafe_ruleScopedInstantiation schemas input
        substitution authored atom (values substitution rowMember) authoredSafe
        instantiated
  | tail count authored =>
      intro substitution rowMember atom instantiated
      have sinkSafe := (List.all_eq_true.mp safe)
        (.tail count authored) sinkMember
      have authoredSafe :
          executableSchemaTemplateSafe schemas authored = true := by
        simpa [executableSchemaSafeSink] using sinkSafe
      exact executableSchemaTemplateSafe_ruleScopedInstantiation schemas input
        substitution authored atom (values substitution rowMember) authoredSafe
        instantiated

/-- Schema-derived authority is hereditary through every expression edge. -/
theorem executableSubtermsFromSchemas_hereditary
    (schemas : List RawExecFact) :
    AtomPropertyHereditary (ExecutableSubtermsFromSchemas schemas) := by
  intro children parent child childMember raw rawMember
  apply parent raw
  simp only [rawExecSubterms, rawExecSubtermsList_eq_flatMap,
    List.mem_append, Option.mem_toList, List.mem_flatMap]
  exact Or.inr ⟨child, childMember, rawMember⟩

/-- A selected rule-scoped directive preserves schema-derived executable
authority when its source state and its authored output template satisfy the
same schema relation. -/
theorem cFireRuleScopedSourceExecFact_schemaAuthorized
    (schemas : List RawExecFact) (space : List Atom)
    (directive : SourceExecFact)
    (spaceWithin : AtomsWithin (ExecutableSubtermsFromSchemas schemas) space)
    (directiveWithin : ExecutableSubtermsFromSchemas schemas directive.atom)
    (templateSafe : ExecutableSchemaSafeTemplate schemas directive.rule.tmpl) :
    AtomsWithin (ExecutableSubtermsFromSchemas schemas)
      (cFireRuleScopedSourceExecFact space directive) := by
  apply cFireRuleScopedSourceExecFact_atomsWithin_of_additions
  · exact spaceWithin
  · dsimp
    apply executableSchemaSafeTemplate_ruleScopedAdditions schemas
      directive.rule.input _ directive.rule.tmpl templateSafe
    exact cFireRuleScopedSourceExecFact_matchValuesWithin
      (ExecutableSubtermsFromSchemas schemas)
      (executableSubtermsFromSchemas_hereditary schemas)
      space directive spaceWithin directiveWithin

/-- A fixed directive is one of its own authorized schema instances. -/
theorem rawExecFact_member_is_schema_instance
    {schemas : List RawExecFact} {raw : RawExecFact}
    (member : raw ∈ schemas) :
    RawExecFactFromSchemas schemas raw :=
  ⟨raw, member, [], rfl⟩

/-- Every fixed inventory member has recursively schema-derived authority. -/
theorem rawExecFact_executableSubtermsFromSchemas
    {schemas : List RawExecFact} {raw : RawExecFact}
    (closed : ∀ nested ∈ rawExecSubterms raw.atom, nested ∈ schemas) :
    ExecutableSubtermsFromSchemas schemas raw.atom := by
  intro nested nestedMember
  exact rawExecFact_member_is_schema_instance (closed nested nestedMember)

/-! ## Controls -/

private def schemaControlDirective : Atom :=
  .expression [.symbol "exec", .symbol "fixed-location",
    .expression [.symbol ",", .var "payload"],
    .expression [.symbol "O", .expression [.symbol "+", .var "payload"]]]

private def schemaControlRaw : RawExecFact :=
  ⟨schemaControlDirective, .symbol "fixed-location",
    .expression [.symbol ",", .var "payload"],
    .expression [.symbol "O", .expression [.symbol "+", .var "payload"]]⟩

/-- Positive control: an executable schema may carry ordinary dynamic data. -/
example : executableSchemaTemplateSafe [schemaControlRaw]
    schemaControlDirective = true := by
  decide

/-- Negative control: a variable in executable head position cannot assemble
a fresh directive by substitution. -/
example : executableSchemaTemplateSafe [schemaControlRaw]
    (.expression [.var "head", .symbol "location", .symbol "input",
      .symbol "output"]) = false := by
  decide

section AxiomAudit

#print axioms executableSchemaTemplateSafe_applySubst
#print axioms executableSchemaTemplatesSafe_applySubst
#print axioms applySubstChain_append
#print axioms executableSchemaSafeTemplate_added
#print axioms executableSchemaSafeTemplate_ruleScopedAdditions
#print axioms cFireRuleScopedSourceExecFact_schemaAuthorized
#print axioms executableSubtermsFromSchemas_hereditary
#print axioms rawExecFact_member_is_schema_instance
#print axioms rawExecFact_executableSubtermsFromSchemas

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
