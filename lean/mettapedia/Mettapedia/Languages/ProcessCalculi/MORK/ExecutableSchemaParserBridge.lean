import Mettapedia.Languages.ProcessCalculi.MORK.ExecutableSchemaLineageSafety

/-!
# Syntax-to-schema executable authority

The strict MM2 directive parser preserves the executable-schema discipline of
the rule-scoped scheduler.  This is the syntax-to-execution seam: a parsed
sink cannot introduce an executable shell whose authored syntax was not
already structurally authorized.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- A strict parsed sink preserves the structural executable-schema check on
its authored syntax. -/
theorem parseSupportedSink_schemaSafe
    (schemas : List RawExecFact) {source : Atom} {sink : Sink}
    (parsed : parseSupportedSink source = some sink)
    (safe : executableSchemaTemplateSafe schemas source = true) :
    executableSchemaSafeSink schemas sink = true := by
  unfold parseSupportedSink at parsed
  split at parsed
  · injection parsed with equal
    subst sink
    simpa [executableSchemaSafeSink, executableSchemaTemplateSafe,
      executableSchemaTemplatesSafe] using safe
  · injection parsed with equal
    subst sink
    simp [executableSchemaSafeSink]
  · have atomEqual := parseExtremaSink_atom_eq_body true _ _ sink parsed
    cases sink with
    | add atom =>
        simp only [Sink.atom] at atomEqual
        change executableSchemaTemplateSafe schemas atom = true
        rw [atomEqual]
        simp [executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
          Bool.and_eq_true] at safe
        exact safe.2
    | remove atom =>
        simp [executableSchemaSafeSink]
    | head count atom =>
        simp only [Sink.atom] at atomEqual
        change executableSchemaTemplateSafe schemas atom = true
        rw [atomEqual]
        simp [executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
          Bool.and_eq_true] at safe
        exact safe.2
    | tail count atom =>
        simp only [Sink.atom] at atomEqual
        change executableSchemaTemplateSafe schemas atom = true
        rw [atomEqual]
        simp [executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
          Bool.and_eq_true] at safe
        exact safe.2
  · have atomEqual := parseExtremaSink_atom_eq_body false _ _ sink parsed
    cases sink with
    | add atom =>
        simp only [Sink.atom] at atomEqual
        change executableSchemaTemplateSafe schemas atom = true
        rw [atomEqual]
        simp [executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
          Bool.and_eq_true] at safe
        exact safe.2
    | remove atom =>
        simp [executableSchemaSafeSink]
    | head count atom =>
        simp only [Sink.atom] at atomEqual
        change executableSchemaTemplateSafe schemas atom = true
        rw [atomEqual]
        simp [executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
          Bool.and_eq_true] at safe
        exact safe.2
    | tail count atom =>
        simp only [Sink.atom] at atomEqual
        change executableSchemaTemplateSafe schemas atom = true
        rw [atomEqual]
        simp [executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
          Bool.and_eq_true] at safe
        exact safe.2
  · contradiction

/-- A structurally safe syntax list certifies each of its members. -/
theorem executableSchemaTemplatesSafe_mem
    (schemas : List RawExecFact) {atoms : List Atom} {atom : Atom}
    (safe : executableSchemaTemplatesSafe schemas atoms = true)
    (member : atom ∈ atoms) :
    executableSchemaTemplateSafe schemas atom = true := by
  induction atoms with
  | nil => simp at member
  | cons head tail induction =>
      have parts : executableSchemaTemplateSafe schemas head = true ∧
          executableSchemaTemplatesSafe schemas tail = true := by
        simpa [executableSchemaTemplatesSafe, Bool.and_eq_true] using safe
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst atom
        exact parts.1
      · exact induction parts.2 member

/-- The strict list parser preserves schema safety for every decoded sink. -/
theorem parseSupportedSinkList_schemaSafe
    (schemas : List RawExecFact) :
    ∀ {sources : List Atom} {sinks : List Sink},
      parseSupportedSinkList sources = some sinks →
      executableSchemaTemplatesSafe schemas sources = true →
      sinks.all (executableSchemaSafeSink schemas) = true
  | [], sinks, parsed, _ => by
      simp [parseSupportedSinkList] at parsed
      subst sinks
      rfl
  | source :: sources, sinks, parsed, safe => by
      unfold parseSupportedSinkList at parsed
      cases sourceParsed : parseSupportedSink source with
      | none => simp [sourceParsed] at parsed
      | some first =>
          cases restParsed : parseSupportedSinkList sources with
          | none => simp [sourceParsed, restParsed] at parsed
          | some rest =>
              simp [sourceParsed, restParsed] at parsed
              subst sinks
              have parts : executableSchemaTemplateSafe schemas source = true ∧
                  executableSchemaTemplatesSafe schemas sources = true := by
                simpa [executableSchemaTemplatesSafe, Bool.and_eq_true]
                  using safe
              have firstSafe : executableSchemaSafeSink schemas first = true :=
                parseSupportedSink_schemaSafe schemas sourceParsed parts.1
              have restSafe : rest.all (executableSchemaSafeSink schemas) = true :=
                parseSupportedSinkList_schemaSafe schemas restParsed parts.2
              simpa [Bool.and_eq_true] using And.intro firstSafe restSafe

/-- Strict template parsing preserves the schema safety of every sink that the
rule-scoped engine can materialize. -/
theorem parseSupportedTemplate_schemaSafe
    (schemas : List RawExecFact) {source : Atom} {template : Template}
    (parsed : parseSupportedTemplate source = some template)
    (safe : executableSchemaTemplateSafe schemas source = true) :
    ExecutableSchemaSafeTemplate schemas template := by
  cases source with
  | var name => simp [parseSupportedTemplate] at parsed
  | symbol name => simp [parseSupportedTemplate] at parsed
  | grounded value => simp [parseSupportedTemplate] at parsed
  | expression children =>
      cases children with
      | nil => simp [parseSupportedTemplate] at parsed
      | cons head tail =>
          cases head with
          | var name => simp [parseSupportedTemplate] at parsed
          | grounded value => simp [parseSupportedTemplate] at parsed
          | expression inner => simp [parseSupportedTemplate] at parsed
          | symbol name =>
              by_cases comma : name = ","
              · subst name
                change some (mkTemplate (tail.map Sink.add)) = some template
                  at parsed
                injection parsed with equal
                subst template
                have tailSafe :
                    executableSchemaTemplatesSafe schemas tail = true := by
                  simpa [executableSchemaTemplateSafe,
                    executableSchemaTemplatesSafe, Bool.and_eq_true] using safe
                change (tail.map Sink.add).all
                  (executableSchemaSafeSink schemas) = true
                apply List.all_eq_true.mpr
                intro sink member
                simp only [List.mem_map] at member
                rcases member with ⟨atom, atomMember, equal⟩
                subst sink
                simpa [executableSchemaSafeSink] using
                  executableSchemaTemplatesSafe_mem schemas tailSafe atomMember
              · by_cases output : name = "O"
                · subst name
                  unfold parseSupportedTemplate at parsed
                  cases sinksParsed : parseSupportedSinkList tail with
                  | none => simp [sinksParsed] at parsed
                  | some sinks =>
                      simp [sinksParsed] at parsed
                      subst template
                      have tailSafe :
                          executableSchemaTemplatesSafe schemas tail = true := by
                        simpa [executableSchemaTemplateSafe,
                          executableSchemaTemplatesSafe, Bool.and_eq_true]
                          using safe
                      simpa [ExecutableSchemaSafeTemplate, mkTemplate] using
                        parseSupportedSinkList_schemaSafe schemas sinksParsed
                          tailSafe
                · simp [parseSupportedTemplate, comma, output] at parsed

/-- Decoding a supported directive carries syntax-proved schema safety into the
structured rule consumed by rule-scoped execution. -/
theorem decodeSupportedSourceExec_schemaSafe
    (schemas : List RawExecFact) {raw : RawExecFact}
    {directive : SourceExecFact}
    (decoded : decodeSupportedSourceExec raw = some directive)
    (safe : executableSchemaTemplateSafe schemas raw.templateExpr = true) :
    ExecutableSchemaSafeTemplate schemas directive.rule.tmpl := by
  unfold decodeSupportedSourceExec at decoded
  cases inputParsed : parseSupportedInput raw.inputExpr with
  | none => simp [inputParsed] at decoded
  | some input =>
      simp only [inputParsed] at decoded
      cases templateParsed : parseSupportedTemplate raw.templateExpr with
      | none => simp [templateParsed] at decoded
      | some template =>
          simp [templateParsed] at decoded
          subst directive
          exact parseSupportedTemplate_schemaSafe schemas templateParsed safe

/-- Strict sink parsing preserves semantic schema lineage for each
support-producing body. -/
theorem parseSupportedSink_lineageAuthorized
    (schemas : List RawExecFact) {source : Atom} {sink : Sink}
    (parsed : parseSupportedSink source = some sink)
    (authorized : ExecutableSchemaAtomAuthorized schemas source) :
    match sink with
    | .add atom | .head _ atom | .tail _ atom =>
        ExecutableSchemaAtomAuthorized schemas atom
    | .remove _ => True := by
  cases source with
  | var name => simp [parseSupportedSink] at parsed
  | symbol name => simp [parseSupportedSink] at parsed
  | grounded value => simp [parseSupportedSink] at parsed
  | expression children =>
      cases children with
      | nil => simp [parseSupportedSink] at parsed
      | cons head tail =>
          cases head with
          | var name => simp [parseSupportedSink] at parsed
          | grounded value => simp [parseSupportedSink] at parsed
          | expression inner => simp [parseSupportedSink] at parsed
          | symbol name =>
              cases tail with
              | nil => simp [parseSupportedSink] at parsed
              | cons first tail =>
                  cases tail with
                  | nil =>
                      by_cases plus : name = "+"
                      · subst name
                        change some (.add first) = some sink at parsed
                        injection parsed with equal
                        subst sink
                        exact executableSchemaAtomAuthorized_hereditary schemas
                          [.symbol "+", first] authorized first (by simp)
                      · by_cases minus : name = "-"
                        · subst name
                          change some (.remove first) = some sink at parsed
                          injection parsed with equal
                          subst sink
                          trivial
                        · simp [parseSupportedSink, plus, minus] at parsed
                  | cons second tail =>
                      cases tail with
                      | nil =>
                          by_cases headName : name = "head"
                          · subst name
                            change parseExtremaSink true first second = some sink
                              at parsed
                            have secondAuthorized :=
                              executableSchemaAtomAuthorized_hereditary schemas
                                [.symbol "head", first, second] authorized second
                                (by simp)
                            cases sink with
                            | add atom =>
                                change ExecutableSchemaAtomAuthorized schemas atom
                                have atomEqual :=
                                  parseExtremaSink_atom_eq_body true first second
                                    (.add atom) parsed
                                simp only [Sink.atom] at atomEqual
                                rw [atomEqual]
                                exact secondAuthorized
                            | remove atom => trivial
                            | head count atom =>
                                change ExecutableSchemaAtomAuthorized schemas atom
                                have atomEqual :=
                                  parseExtremaSink_atom_eq_body true first second
                                    (.head count atom) parsed
                                simp only [Sink.atom] at atomEqual
                                rw [atomEqual]
                                exact secondAuthorized
                            | tail count atom =>
                                change ExecutableSchemaAtomAuthorized schemas atom
                                have atomEqual :=
                                  parseExtremaSink_atom_eq_body true first second
                                    (.tail count atom) parsed
                                simp only [Sink.atom] at atomEqual
                                rw [atomEqual]
                                exact secondAuthorized
                          · by_cases tailName : name = "tail"
                            · subst name
                              change parseExtremaSink false first second = some sink
                                at parsed
                              have secondAuthorized :=
                                executableSchemaAtomAuthorized_hereditary schemas
                                  [.symbol "tail", first, second] authorized second
                                  (by simp)
                              cases sink with
                              | add atom =>
                                  change ExecutableSchemaAtomAuthorized schemas atom
                                  have atomEqual :=
                                    parseExtremaSink_atom_eq_body false first second
                                      (.add atom) parsed
                                  simp only [Sink.atom] at atomEqual
                                  rw [atomEqual]
                                  exact secondAuthorized
                              | remove atom => trivial
                              | head count atom =>
                                  change ExecutableSchemaAtomAuthorized schemas atom
                                  have atomEqual :=
                                    parseExtremaSink_atom_eq_body false first second
                                      (.head count atom) parsed
                                  simp only [Sink.atom] at atomEqual
                                  rw [atomEqual]
                                  exact secondAuthorized
                              | tail count atom =>
                                  change ExecutableSchemaAtomAuthorized schemas atom
                                  have atomEqual :=
                                    parseExtremaSink_atom_eq_body false first second
                                      (.tail count atom) parsed
                                  simp only [Sink.atom] at atomEqual
                                  rw [atomEqual]
                                  exact secondAuthorized
                            · simp [parseSupportedSink, headName, tailName]
                                at parsed
                      | cons third tail =>
                          simp [parseSupportedSink] at parsed

/-- The strict sink-list parser preserves lineage authorization for every
decoded sink. -/
theorem parseSupportedSinkList_lineageAuthorized
    (schemas : List RawExecFact) :
    ∀ {sources : List Atom} {sinks : List Sink},
      parseSupportedSinkList sources = some sinks →
      ExecutableSchemaAtomsAuthorized schemas sources →
      ∀ sink ∈ sinks,
        match sink with
        | .add atom | .head _ atom | .tail _ atom =>
            ExecutableSchemaAtomAuthorized schemas atom
        | .remove _ => True
  | [], sinks, parsed, _, sink, member => by
      simp [parseSupportedSinkList] at parsed
      subst sinks
      simp at member
  | source :: sources, sinks, parsed, authorized, sink, member => by
      rcases authorized with ⟨sourceAuthorized, sourcesAuthorized⟩
      unfold parseSupportedSinkList at parsed
      cases sourceParsed : parseSupportedSink source with
      | none => simp [sourceParsed] at parsed
      | some first =>
          cases restParsed : parseSupportedSinkList sources with
          | none => simp [sourceParsed, restParsed] at parsed
          | some rest =>
              simp [sourceParsed, restParsed] at parsed
              subst sinks
              simp only [List.mem_cons] at member
              rcases member with equal | member
              · subst sink
                cases first with
                | add atom =>
                    change ExecutableSchemaAtomAuthorized schemas atom
                    exact parseSupportedSink_lineageAuthorized schemas sourceParsed
                      sourceAuthorized
                | remove atom => trivial
                | head count atom =>
                    change ExecutableSchemaAtomAuthorized schemas atom
                    exact parseSupportedSink_lineageAuthorized schemas sourceParsed
                      sourceAuthorized
                | tail count atom =>
                    change ExecutableSchemaAtomAuthorized schemas atom
                    exact parseSupportedSink_lineageAuthorized schemas sourceParsed
                      sourceAuthorized
              · exact parseSupportedSinkList_lineageAuthorized schemas
                  restParsed sourcesAuthorized sink member

/-- Strict template parsing carries semantic schema lineage from syntax into
the structured rule consumed by rule-scoped execution. -/
theorem parseSupportedTemplate_lineageAuthorized
    (schemas : List RawExecFact) {source : Atom} {template : Template}
    (parsed : parseSupportedTemplate source = some template)
    (authorized : ExecutableSchemaAtomAuthorized schemas source) :
    ExecutableSchemaAuthorizedTemplate schemas template := by
  cases source with
  | var name => simp [parseSupportedTemplate] at parsed
  | symbol name => simp [parseSupportedTemplate] at parsed
  | grounded value => simp [parseSupportedTemplate] at parsed
  | expression children =>
      cases children with
      | nil => simp [parseSupportedTemplate] at parsed
      | cons head tail =>
          cases head with
          | var name => simp [parseSupportedTemplate] at parsed
          | grounded value => simp [parseSupportedTemplate] at parsed
          | expression inner => simp [parseSupportedTemplate] at parsed
          | symbol name =>
              by_cases comma : name = ","
              · subst name
                change some (mkTemplate (tail.map Sink.add)) = some template
                  at parsed
                injection parsed with equal
                subst template
                rcases authorized with ⟨childrenAuthorized, _⟩
                rcases childrenAuthorized with ⟨_, tailAuthorized⟩
                intro sink member
                rcases List.mem_map.mp member with ⟨atom, atomMember, equal⟩
                subst sink
                exact executableSchemaAtomsAuthorized_mem schemas
                  tailAuthorized atomMember
              · by_cases output : name = "O"
                · subst name
                  unfold parseSupportedTemplate at parsed
                  cases sinksParsed : parseSupportedSinkList tail with
                  | none => simp [sinksParsed] at parsed
                  | some sinks =>
                      simp [sinksParsed] at parsed
                      subst template
                      rcases authorized with ⟨childrenAuthorized, _⟩
                      rcases childrenAuthorized with ⟨_, tailAuthorized⟩
                      exact parseSupportedSinkList_lineageAuthorized schemas
                        sinksParsed tailAuthorized
                · simp [parseSupportedTemplate, comma, output] at parsed

/-- Decoding a supported directive transfers lineage authorization of its
template syntax into the parsed scheduler template. -/
theorem decodeSupportedSourceExec_lineageAuthorized
    (schemas : List RawExecFact) {raw : RawExecFact}
    {directive : SourceExecFact}
    (decoded : decodeSupportedSourceExec raw = some directive)
    (templateAuthorized :
      ExecutableSchemaAtomAuthorized schemas raw.templateExpr) :
    ExecutableSchemaAuthorizedTemplate schemas directive.rule.tmpl := by
  unfold decodeSupportedSourceExec at decoded
  cases inputParsed : parseSupportedInput raw.inputExpr with
  | none => simp [inputParsed] at decoded
  | some input =>
      simp only [inputParsed] at decoded
      cases parsedTemplate : parseSupportedTemplate raw.templateExpr with
      | none => simp [parsedTemplate] at decoded
      | some template =>
          simp [parsedTemplate] at decoded
          subst directive
          exact parseSupportedTemplate_lineageAuthorized schemas parsedTemplate
            templateAuthorized

private theorem decodeSupportedSourceExec_atom_eq_raw
    {raw : RawExecFact} {directive : SourceExecFact}
    (decoded : decodeSupportedSourceExec raw = some directive) :
    directive.atom = raw.atom := by
  unfold decodeSupportedSourceExec at decoded
  cases inputParsed : parseSupportedInput raw.inputExpr with
  | none => simp [inputParsed] at decoded
  | some input =>
      simp only [inputParsed] at decoded
      cases parsedTemplate : parseSupportedTemplate raw.templateExpr with
      | none => simp [parsedTemplate] at decoded
      | some template =>
          simp [parsedTemplate] at decoded
          subst directive
          rfl

/-- Strict supported-directive decoding preserves the exact atom selected by
the scheduler shell. -/
theorem extractSupportedSourceExecFact_atom_eq
    {atom : Atom} {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact atom = some directive) :
    directive.atom = atom := by
  unfold extractSupportedSourceExecFact at decoded
  cases rawExtract : extractRawExecFact atom with
  | none => simp [rawExtract] at decoded
  | some raw =>
      simp only [rawExtract] at decoded
      calc
        directive.atom = raw.atom :=
          decodeSupportedSourceExec_atom_eq_raw decoded
        _ = atom := extractRawExecFact_atom_eq rawExtract

/-- A strictly decoded scheduler directive inherits lineage authorization from
its exact executable syntax shell. -/
theorem extractSupportedSourceExecFact_lineageAuthorized
    (schemas : List RawExecFact) {atom : Atom} {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact atom = some directive)
    (authorized : ExecutableSchemaAtomAuthorized schemas atom) :
    ExecutableSchemaAuthorizedTemplate schemas directive.rule.tmpl := by
  unfold extractSupportedSourceExecFact at decoded
  cases rawExtract : extractRawExecFact atom with
  | none => simp [rawExtract] at decoded
  | some raw =>
      simp only [rawExtract] at decoded
      exact decodeSupportedSourceExec_lineageAuthorized schemas decoded
        (executableSchemaAtomAuthorized_rawTemplate schemas rawExtract authorized)

/-- Parsing and scheduling compose at the executable-authority boundary: a
strictly decoded, lineage-authorized shell cannot introduce an unauthorized
executable subtree in one rule-scoped firing. -/
theorem cFireRuleScopedSourceExecFact_lineageAuthorized_of_extract
    (schemas : List RawExecFact) (space : List Atom) (atom : Atom)
    (directive : SourceExecFact)
    (decoded : extractSupportedSourceExecFact atom = some directive)
    (spaceWithin : AtomsWithin (ExecutableSchemaAtomAuthorized schemas) space)
    (atomAuthorized : ExecutableSchemaAtomAuthorized schemas atom) :
    AtomsWithin (ExecutableSchemaAtomAuthorized schemas)
      (cFireRuleScopedSourceExecFact space directive) := by
  apply cFireRuleScopedSourceExecFact_lineageAuthorized schemas space directive
    spaceWithin
  · rw [extractSupportedSourceExecFact_atom_eq decoded]
    exact atomAuthorized
  · exact extractSupportedSourceExecFact_lineageAuthorized schemas decoded
      atomAuthorized

/-- Every strict scheduler candidate inherits both the selected atom's
lineage and its parsed-template authorization from a member of the live
support. -/
theorem cSupportedSourceExecFacts_lineageAuthorized
    (schemas : List RawExecFact) (space : List Atom)
    (spaceWithin : AtomsWithin (ExecutableSchemaAtomAuthorized schemas) space)
    {directive : SourceExecFact}
    (member : directive ∈ cSupportedSourceExecFacts space) :
    ExecutableSchemaAtomAuthorized schemas directive.atom ∧
      ExecutableSchemaAuthorizedTemplate schemas directive.rule.tmpl := by
  unfold cSupportedSourceExecFacts at member
  rcases List.mem_filterMap.mp member with ⟨atom, atomMember, decoded⟩
  have atomAuthorized := spaceWithin atom atomMember
  exact ⟨by
    rw [extractSupportedSourceExecFact_atom_eq decoded]
    exact atomAuthorized,
    extractSupportedSourceExecFact_lineageAuthorized schemas decoded
      atomAuthorized⟩

/-- One actual rule-scoped queue transition preserves finite executable
schema lineage under either unsupported-directive policy.  The consuming
policy either fires a strictly decoded directive or removes an unsupported
shell; neither case can mint executable authority. -/
theorem cRuleScopedSourceWorkQueueStep_lineageAuthorized
    (schemas : List RawExecFact) (policy : UnsupportedExecPolicy)
    (space next : List Atom)
    (spaceWithin : AtomsWithin (ExecutableSchemaAtomAuthorized schemas) space)
    (moved : cRuleScopedSourceWorkQueueStep policy space = some next) :
    AtomsWithin (ExecutableSchemaAtomAuthorized schemas) next := by
  cases policy with
  | leaveInert =>
      unfold cRuleScopedSourceWorkQueueStep at moved
      cases selected : selectNextScheduled (cSupportedSourceExecFacts space) with
      | none => simp [selected] at moved
      | some directive =>
          simp only [selected] at moved
          injection moved with nextEqual
          subst next
          have directiveAuthorized :=
            cSupportedSourceExecFacts_lineageAuthorized schemas space spaceWithin
              (selectNextScheduled_mem selected)
          exact cFireRuleScopedSourceExecFact_lineageAuthorized schemas space
            directive spaceWithin directiveAuthorized.1 directiveAuthorized.2
  | consume =>
      unfold cRuleScopedSourceWorkQueueStep at moved
      cases selected : selectNextScheduled (cRawExecFacts space) with
      | none => simp [selected] at moved
      | some raw =>
          have rawMember : raw ∈ cRawExecFacts space :=
            selectNextScheduled_mem selected
          unfold cRawExecFacts at rawMember
          rcases List.mem_filterMap.mp rawMember with
            ⟨atom, atomMember, rawExtract⟩
          have atomAuthorized := spaceWithin atom atomMember
          have rawAuthorized : ExecutableSchemaAtomAuthorized schemas raw.atom := by
            rw [extractRawExecFact_atom_eq rawExtract]
            exact atomAuthorized
          cases decoded : decodeSupportedSourceExec raw with
          | none =>
              simp only [selected, decoded] at moved
              injection moved with nextEqual
              subst next
              exact morkEraseSupport_atomsWithin
                (ExecutableSchemaAtomAuthorized schemas) space raw.atom
                spaceWithin
          | some directive =>
              simp only [selected, decoded] at moved
              injection moved with nextEqual
              subst next
              have templateAuthorized :=
                decodeSupportedSourceExec_lineageAuthorized schemas decoded
                  (executableSchemaAtomAuthorized_rawTemplate schemas rawExtract
                    atomAuthorized)
              have directiveAuthorized :
                  ExecutableSchemaAtomAuthorized schemas directive.atom := by
                rw [decodeSupportedSourceExec_atom_eq_raw decoded,
                  extractRawExecFact_atom_eq rawExtract]
                exact atomAuthorized
              exact cFireRuleScopedSourceExecFact_lineageAuthorized schemas space
                directive spaceWithin directiveAuthorized templateAuthorized

/-- Exact-fuel rule-scoped execution preserves finite executable-schema
lineage at every reachable state. -/
theorem cRuleScopedSourceWorkQueueRunN_lineageAuthorized
    (schemas : List RawExecFact) (policy : UnsupportedExecPolicy) :
    ∀ (fuel : Nat) (space : List Atom),
      AtomsWithin (ExecutableSchemaAtomAuthorized schemas) space →
      AtomsWithin (ExecutableSchemaAtomAuthorized schemas)
        (cRuleScopedSourceWorkQueueRunN policy fuel space).1
  | 0, space, spaceWithin => by
      simp [cRuleScopedSourceWorkQueueRunN]
      exact spaceWithin
  | fuel + 1, space, spaceWithin => by
      simp only [cRuleScopedSourceWorkQueueRunN]
      cases moved : cRuleScopedSourceWorkQueueStep policy space with
      | none => simpa [moved] using spaceWithin
      | some next =>
          have nextWithin := cRuleScopedSourceWorkQueueStep_lineageAuthorized
            schemas policy space next spaceWithin moved
          simpa [moved] using
            cRuleScopedSourceWorkQueueRunN_lineageAuthorized schemas policy fuel
              next nextWithin

section AxiomAudit

#print axioms parseSupportedSink_schemaSafe
#print axioms executableSchemaTemplatesSafe_mem
#print axioms parseSupportedSinkList_schemaSafe
#print axioms parseSupportedTemplate_schemaSafe
#print axioms decodeSupportedSourceExec_schemaSafe
#print axioms parseSupportedSink_lineageAuthorized
#print axioms parseSupportedSinkList_lineageAuthorized
#print axioms parseSupportedTemplate_lineageAuthorized
#print axioms decodeSupportedSourceExec_lineageAuthorized
#print axioms extractSupportedSourceExecFact_atom_eq
#print axioms extractSupportedSourceExecFact_lineageAuthorized
#print axioms cFireRuleScopedSourceExecFact_lineageAuthorized_of_extract
#print axioms cSupportedSourceExecFacts_lineageAuthorized
#print axioms cRuleScopedSourceWorkQueueStep_lineageAuthorized
#print axioms cRuleScopedSourceWorkQueueRunN_lineageAuthorized

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
