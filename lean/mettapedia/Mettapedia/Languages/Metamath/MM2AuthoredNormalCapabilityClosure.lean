import Mettapedia.Languages.Metamath.MM2NormalProofCapabilityClosure
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness

/-!
# Capability closure for the complete authored normal verifier

The normal proof machine is one phase of the authored verifier.  Ordered
source-event directives remain resident while that phase runs, so the live
physical workspace requires an outer executable inventory containing both
families.  This module establishes that outer boundary without weakening the
normal-only closure theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2AuthoredNormalCapabilityClosure

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.MM2NormalProofOwnedClosure
open Mettapedia.Languages.Metamath.MM2NormalProofCapabilityClosure
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## The outer physical boundary -/

/-- Atom-local authority for the complete authored normal verifier. -/
def AuthoredNormalCapabilityAtom (atom : Atom) : Prop :=
  RawExecAtomWithin authoredNormalVerifierRawFacts atom ∧
    NormalVerifierInternalRowIntact atom ∧
      NormalBodyCarrierAuthorized atom

/-- The physical induction boundary retains both ordinary multiplicity and
compact MORK-key uniqueness. -/
def AuthoredNormalCapabilityState (space : List Atom) : Prop :=
  space.Nodup ∧ MorkSupportNodup space ∧
    AtomsWithin AuthoredNormalCapabilityAtom space

/-- Canonical physical support used to launch the admitted authored verifier. -/
def admittedNormalInitialSupport (target : MM2Target) {owner : Atom}
    (input : AdmittedSourceEventInput owner) : List Atom :=
  morkUnionSupport []
    (composeAdmittedNormalProgram authoredMetamathVerifierGSLT target input)

theorem normalProofMachineRawFacts_subset_authored
    {raw : RawExecFact} (member : raw ∈ normalProofMachineRawFacts) :
    raw ∈ authoredNormalVerifierRawFacts := by
  rw [authoredNormalVerifierRawFacts, authoredNormalVerifierRules,
    List.filterMap_append, List.mem_append]
  exact Or.inr member

theorem AuthoredNormalCapabilityState.rawWithin
    {space : List Atom} (state : AuthoredNormalCapabilityState space) :
    RawExecFactsWithin authoredNormalVerifierRawFacts space := by
  intro raw member
  unfold cRawExecFacts at member
  rw [List.mem_filterMap] at member
  obtain ⟨atom, atomMember, extracted⟩ := member
  exact (state.2.2 atom atomMember).1 raw extracted

theorem AuthoredNormalCapabilityState.internalRowsIntact
    {space : List Atom} (state : AuthoredNormalCapabilityState space) :
    NormalVerifierInternalRowsIntact space := by
  intro atom member
  exact (state.2.2 atom member).2.1

theorem AuthoredNormalCapabilityState.bodyCarrierAuthorized
    {space : List Atom} (state : AuthoredNormalCapabilityState space) :
    AtomsWithin NormalBodyCarrierAuthorized space := by
  intro atom member
  exact (state.2.2 atom member).2.2

theorem AuthoredNormalCapabilityState.executionContext
    {space : List Atom} (state : AuthoredNormalCapabilityState space) :
    NormalProofMachineExecutionContext space :=
  ⟨state.rawWithin, state.internalRowsIntact⟩

theorem AuthoredNormalCapabilityState.reflectiveInvariant
    {space : List Atom} (state : AuthoredNormalCapabilityState space) :
    ReflectiveWorkQueueInvariant space :=
  authoredNormalVerifier_reflective_invariant space state.1 state.rawWithin

theorem normalVerifierInternalRows_no_executable_atom :
    normalVerifierInternalRows.all (fun atom =>
      (extractRawExecFact atom).isNone) = true := by
  decide +kernel

theorem authoredNormalVerifierRule_atom_authorized
    {atom : Atom} (member : atom ∈ authoredNormalVerifierRules) :
    AuthoredNormalCapabilityAtom atom := by
  refine ⟨?_, ?_, ?_⟩
  · intro raw extracted
    rw [authoredNormalVerifierRawFacts, List.mem_filterMap]
    exact ⟨atom, member, extracted⟩
  · unfold NormalVerifierInternalRowIntact
    intro internalShape
    have safeAll : authoredNormalVerifierRules.all (fun candidate =>
        !(isVerifierOwnedInternalRowShape candidate)) = true := by
      rw [authoredNormalVerifierRules, List.all_append, Bool.and_eq_true]
      exact ⟨orderedSourceEventPreludeRules_no_internal_row_shape,
        normalProofMachineRules_no_internal_row_shape⟩
    have safe := (List.all_eq_true.mp safeAll) atom member
    have absent : isVerifierOwnedInternalRowShape atom = false := by
      simpa only [Bool.not_eq_true'] using safe
    rw [absent] at internalShape
    contradiction
  · apply normalBodyCarrierAuthorized_of_shape_false
    have safe := (List.all_eq_true.mp
      authoredNormalVerifierRules_no_normal_body_carrier) atom member
    simpa only [Bool.not_eq_true'] using safe

theorem composeAdmittedNormalProgram_rawWithin
    (target : MM2Target) {owner : Atom}
    (input : AdmittedSourceEventInput owner) :
    RawExecFactsWithin authoredNormalVerifierRawFacts
      (composeAdmittedNormalProgram authoredMetamathVerifierGSLT target
        input) := by
  intro raw rawMember
  unfold cRawExecFacts at rawMember
  rw [List.mem_filterMap] at rawMember
  obtain ⟨atom, atomMember, extracted⟩ := rawMember
  rw [composeAdmittedNormalProgram, List.mem_append] at atomMember
  rcases atomMember with verifier | source
  · have verifierMember :
        atom ∈ normalVerifierInternalRows ++ authoredNormalVerifierRules := by
      rw [List.mem_append]
      rw [GenericVerifierSliceArtifact.program, List.mem_append] at verifier
      rcases verifier with internal | rule
      · left
        simpa using internal
      · right
        rw [authoredNormalVerifierRules_eq_transform target]
        exact rule
    rw [List.mem_append] at verifierMember
    rcases verifierMember with internal | rule
    · have none := (List.all_eq_true.mp
        normalVerifierInternalRows_no_executable_atom) atom internal
      rw [Option.isNone_iff_eq_none, extracted] at none
      contradiction
    · exact (authoredNormalVerifierRule_atom_authorized rule).1 raw
        extracted
  · have none := (input.initialRows_no_exec_or_terminal atom source).1
    rw [extracted] at none
    contradiction

theorem composeAdmittedNormalProgram_atomsWithin
    (target : MM2Target) {owner : Atom}
    (input : AdmittedSourceEventInput owner) :
    AtomsWithin AuthoredNormalCapabilityAtom
      (composeAdmittedNormalProgram authoredMetamathVerifierGSLT target
        input) := by
  intro atom member
  exact ⟨(composeAdmittedNormalProgram_rawWithin target input).atom member,
    composeAdmittedNormalProgram_internal_rows_intact
      authoredMetamathVerifierGSLT target input atom member,
    composeAdmittedNormalProgram_body_carrier_authorized target input atom
      member⟩

/-- Admission plus physical support coalescing establishes the exact outer
state used by the real MORK executor. -/
theorem admittedNormalInitialSupport_state
    (target : MM2Target) {owner : Atom}
    (input : AdmittedSourceEventInput owner) :
    AuthoredNormalCapabilityState
      (admittedNormalInitialSupport target input) := by
  refine ⟨?_, ?_, ?_⟩
  · exact morkUnionSupport_list_nodup []
      (composeAdmittedNormalProgram authoredMetamathVerifierGSLT target input)
      (by simp)
  · exact morkUnionSupport_nodup []
      (composeAdmittedNormalProgram authoredMetamathVerifierGSLT target input)
      (by simp [MorkSupportNodup])
  · exact morkUnionSupport_atomsWithin AuthoredNormalCapabilityAtom []
      (composeAdmittedNormalProgram authoredMetamathVerifierGSLT target input)
      (by simp [AtomsWithin])
      (composeAdmittedNormalProgram_atomsWithin target input)

/-! ## Ordered-event output classification -/

/-- One ordered-event output either reinstalls the exact matched first factor
or is structurally unable to carry executable or body-continuation authority. -/
@[simp] def authoredPreludeSafeSink (first : Atom) : Sink → Bool
  | .add atom =>
      (atom == first) ||
        (normalOwnedSafeTemplateAtom atom &&
          normalContinuationSafeTemplateAtom atom)
  | .remove _ => true
  | .head _ _ | .tail _ _ => false

def AuthoredPreludeSafeTemplate (first : Atom) (template : Template) : Prop :=
  template.sinks.all (authoredPreludeSafeSink first) = true

private theorem cmatchPattern_go_lookupExtends
    {space patterns initial witnesses final finalWitnesses}
    (member : (final, finalWitnesses) ∈
      Conformance.Computable.cmatchPattern.go space patterns initial
        witnesses) :
    final.lookupExtends initial := by
  induction patterns generalizing initial witnesses with
  | nil =>
      simp only [Conformance.Computable.cmatchPattern.go,
        List.mem_singleton, Prod.mk.injEq] at member
      rcases member with ⟨rfl, _⟩
      exact fun _ _ lookup => lookup
  | cons pattern rest induction =>
      simp only [Conformance.Computable.cmatchPattern.go,
        List.mem_flatMap] at member
      obtain ⟨⟨afterHead, atom⟩, matchedMember, tailMember⟩ := member
      rw [List.mem_filterMap] at matchedMember
      obtain ⟨candidate, _candidateMember, mapped⟩ := matchedMember
      simp only [Option.map_eq_some_iff] at mapped
      obtain ⟨matchedSubstitution, matched, equal⟩ := mapped
      cases equal
      rw [Conformance.cmatchAtom_eq_matchAtom] at matched
      exact Subst.lookupExtends_trans (matchAtom_lookupExtends matched)
        (induction tailMember)

/-- The final substitution of a nonempty compatible match retains the first
concrete witness and all bindings established while matching it. -/
private theorem cMatchInputSpecMork_first_match_chain
    {space : List Atom} {first : Atom} {rest : List Atom}
    {substitution : Subst}
    (member : substitution ∈
      (cMatchInputSpecMork [] space
        (.compat (mkPattern (first :: rest)))).map Prod.fst) :
    ∃ afterFirst firstAtom,
      firstAtom ∈ space ∧
        Conformance.Computable.cmatchAtom [] first firstAtom =
          some afterFirst ∧
        substitution.lookupExtends afterFirst := by
  rw [List.mem_map] at member
  obtain ⟨⟨found, foundWitnesses⟩, foundMember, foundEq⟩ := member
  change found = substitution at foundEq
  subst substitution
  simp only [cMatchInputSpecMork, mkPattern,
    Conformance.Computable.cmatchPattern,
    Conformance.Computable.cmatchPattern.go,
    List.mem_flatMap] at foundMember
  obtain ⟨⟨afterFirst, firstAtom⟩, firstMatch, tailMember⟩ := foundMember
  rw [List.mem_filterMap] at firstMatch
  obtain ⟨candidate, firstMember, mapped⟩ := firstMatch
  simp only [Option.map_eq_some_iff] at mapped
  obtain ⟨matchedSubstitution, firstMatched, equal⟩ := mapped
  cases equal
  exact ⟨afterFirst, firstAtom, firstMember, firstMatched,
    cmatchPattern_go_lookupExtends tailMember⟩

private theorem instantiated_first_factor_inherits
    (property : Atom → Prop) {space : List Atom}
    {first : Atom} {rest : List Atom} {substitution : Subst} {atom : Atom}
    (spaceWithin : AtomsWithin property space)
    (member : substitution ∈
      (cMatchInputSpecMork [] space
        (.compat (mkPattern (first :: rest)))).map Prod.fst)
    (instantiated :
      instantiateRuleTemplateAtom?
        (.compat (mkPattern (first :: rest))) substitution first = some atom) :
    property atom := by
  obtain ⟨afterFirst, firstAtom, firstMember, firstMatched, extension⟩ :=
    cMatchInputSpecMork_first_match_chain member
  have firstCovered : templateCovered afterFirst first = true :=
    Conformance.Computable.cmatchAtom_templateCovered [] first firstAtom
      afterFirst firstMatched
  have appliedAfter : applySubst afterFirst first = firstAtom :=
    Conformance.Computable.cmatchAtom_applySubst [] first firstAtom afterFirst
      firstMatched
  have appliedFinal : applySubst substitution first = firstAtom := by
    rw [Conformance.Computable.applySubst_eq_of_lookupExtends_covered
      extension first firstCovered]
    exact appliedAfter
  have instantiatedEq : applySubst substitution first = atom := by
    unfold instantiateRuleTemplateAtom? at instantiated
    split at instantiated
    · exact Option.some.inj instantiated
    · contradiction
  exact instantiatedEq ▸ appliedFinal ▸ spaceWithin firstAtom firstMember

private theorem authored_data_template_authorized
    (input : InputSpec) (substitution : Subst) (template atom : Atom)
    (ownedSafe : normalOwnedSafeTemplateAtom template = true)
    (bodySafe : normalContinuationSafeTemplateAtom template = true)
    (instantiated :
      instantiateRuleTemplateAtom? input substitution template = some atom) :
    AuthoredNormalCapabilityAtom atom := by
  have owned := normalOwnedSafeTemplateAtom_ruleScoped_authorized input
    substitution template atom ownedSafe instantiated
  exact ⟨fun raw extracted =>
      normalProofMachineRawFacts_subset_authored (owned.1 raw extracted),
    owned.2,
    normalContinuationSafeTemplateAtom_ruleScoped_authorized input
      substitution template atom bodySafe instantiated⟩

/-- A checked ordered-event template preserves the complete atom-local
authority property for every actual physical matcher row. -/
theorem authoredPreludeSafeTemplate_additions
    {space : List Atom} (first : Atom) (rest : List Atom)
    (spaceWithin : AtomsWithin AuthoredNormalCapabilityAtom space)
    (rows : List Subst)
    (rowsWithin : ∀ substitution ∈ rows,
      substitution ∈
        (cMatchInputSpecMork [] space
          (.compat (mkPattern (first :: rest)))).map Prod.fst)
    (template : Template)
    (safe : AuthoredPreludeSafeTemplate first template) :
    RuleScopedTemplateAdditionsWithin AuthoredNormalCapabilityAtom
      (.compat (mkPattern (first :: rest))) rows template := by
  intro sink sinkMember
  have sinkSafe := (List.all_eq_true.mp safe) sink sinkMember
  cases sink with
  | add authored =>
      simp only [authoredPreludeSafeSink, Bool.or_eq_true,
        Bool.and_eq_true] at sinkSafe
      intro substitution rowMember atom instantiated
      rcases sinkSafe with self | data
      · have equal : authored = first := beq_iff_eq.mp self
        subst authored
        exact instantiated_first_factor_inherits
          AuthoredNormalCapabilityAtom spaceWithin
          (rowsWithin substitution rowMember) instantiated
      · exact authored_data_template_authorized _ _ _ _ data.1 data.2
          instantiated
  | remove authored => trivial
  | head count authored => contradiction
  | tail count authored => contradiction

/-! ## The five ordered-event directives -/

def orderedSourceEventPreludeDirectives : List SourceExecFact :=
  [sourceEventBootstrapDirective, sourceEventDispatchDirective,
    sourceTheoremStartDirective, sourceTheoremSuccessDirective,
    sourceTheoremCommitDirective]

theorem authoredNormalVerifierDirectives_eq_prelude_append_normal :
    authoredNormalVerifierDirectives =
      orderedSourceEventPreludeDirectives ++ normalProofMachineDirectives := by
  decide +kernel

private def bootstrapFirst : Atom :=
  .expression
    [.symbol "exec", sourceEventBootstrapDirective.loc,
      .var "bootstrap-input", .var "bootstrap-output"]

private def dispatchFirst : Atom :=
  .expression
    [.symbol "exec", sourceEventDispatchDirective.loc,
      .var "dispatch-input", .var "dispatch-output"]

private def theoremStartFirst : Atom :=
  .expression
    [.symbol "exec", sourceTheoremStartDirective.loc,
      .var "theorem-start-input", .var "theorem-start-output"]

private def theoremSuccessFirst : Atom :=
  .expression
    [.symbol "exec", sourceTheoremSuccessDirective.loc,
      .var "theorem-success-input", .var "theorem-success-output"]

private def theoremCommitFirst : Atom :=
  .expression
    [.symbol "exec", sourceTheoremCommitDirective.loc,
      .var "theorem-commit-input", .var "theorem-commit-output"]

theorem orderedSourceEventPreludeDirective_classified
    {directive : SourceExecFact}
    (member : directive ∈ orderedSourceEventPreludeDirectives) :
    ∃ first rest,
      directive.rule.input = .compat (mkPattern (first :: rest)) ∧
        AuthoredPreludeSafeTemplate first directive.rule.tmpl := by
  simp only [orderedSourceEventPreludeDirectives, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨bootstrapFirst, _, rfl, ?_⟩
    unfold AuthoredPreludeSafeTemplate
    decide +kernel
  · refine ⟨dispatchFirst, _, rfl, ?_⟩
    unfold AuthoredPreludeSafeTemplate
    decide +kernel
  · refine ⟨theoremStartFirst, _, rfl, ?_⟩
    unfold AuthoredPreludeSafeTemplate
    decide +kernel
  · refine ⟨theoremSuccessFirst, _, rfl, ?_⟩
    unfold AuthoredPreludeSafeTemplate
    decide +kernel
  · refine ⟨theoremCommitFirst, _, rfl, ?_⟩
    unfold AuthoredPreludeSafeTemplate
    decide +kernel

theorem orderedSourceEventPreludeDirective_atom_authorized
    {directive : SourceExecFact}
    (member : directive ∈ orderedSourceEventPreludeDirectives) :
    AuthoredNormalCapabilityAtom directive.atom := by
  apply authoredNormalVerifierRule_atom_authorized
  simp only [orderedSourceEventPreludeDirectives, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [authoredNormalVerifierRules, orderedSourceEventPreludeRules,
      sourceEventBootstrapDirective, sourceEventDispatchDirective,
      sourceTheoremStartDirective, sourceTheoremSuccessDirective,
      sourceTheoremCommitDirective]

theorem orderedSourceEventPreludeDirective_additions_closed
    {space : List Atom}
    (state : AuthoredNormalCapabilityState space)
    {directive : SourceExecFact}
    (member : directive ∈ orderedSourceEventPreludeDirectives) :
    let live := morkEraseSupport space directive.atom
    let read := morkInsertSupport live directive.atom
    let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
      (substitution, _) => matchSourceGuards substitution directive.rule.guards
    RuleScopedTemplateAdditionsWithin AuthoredNormalCapabilityAtom
      directive.rule.input (rows.map Prod.fst) directive.rule.tmpl := by
  obtain ⟨first, rest, inputEq, safe⟩ :=
    orderedSourceEventPreludeDirective_classified member
  dsimp only
  rw [inputEq]
  apply authoredPreludeSafeTemplate_additions first rest
  · exact morkInsertSupport_atomsWithin AuthoredNormalCapabilityAtom
      (morkEraseSupport space directive.atom) directive.atom
      (morkEraseSupport_atomsWithin AuthoredNormalCapabilityAtom space
        directive.atom state.2.2)
      (orderedSourceEventPreludeDirective_atom_authorized member)
  · intro substitution rowMember
    rw [List.mem_map] at rowMember
    obtain ⟨pair, pairMember, equal⟩ := rowMember
    subst substitution
    exact List.mem_map.mpr ⟨pair, (List.mem_filter.mp pairMember).1, rfl⟩
  · exact safe

/-- One actual MORK rule-scoped ordered-event step preserves the complete
authored normal-verifier boundary. -/
theorem AuthoredNormalCapabilityState.firePrelude
    {space : List Atom} (state : AuthoredNormalCapabilityState space)
    {directive : SourceExecFact}
    (member : directive ∈ orderedSourceEventPreludeDirectives) :
    AuthoredNormalCapabilityState
      (cFireRuleScopedSourceExecFact space directive) := by
  exact ⟨cFireRuleScopedSourceExecFact_list_nodup space directive state.1,
    cFireRuleScopedSourceExecFact_mork_nodup space directive state.2.1,
    cFireRuleScopedSourceExecFact_atomsWithin_of_additions
      AuthoredNormalCapabilityAtom space directive state.2.2
      (orderedSourceEventPreludeDirective_additions_closed state member)⟩

/-- A scheduler-selected ordered-event transition is the same physical MORK
step and preserves the outer authored-verifier boundary. -/
theorem AuthoredNormalCapabilityState.ruleScopedStep_of_prelude
    {space target : List Atom}
    (state : AuthoredNormalCapabilityState space)
    (selectedPrelude : ∀ directive,
      selectNextScheduled (cSupportedSourceExecFacts space) = some directive →
        directive ∈ orderedSourceEventPreludeDirectives)
    (moved :
      cRuleScopedSourceWorkQueueStep .leaveInert space = some target) :
    AuthoredNormalCapabilityState target := by
  unfold cRuleScopedSourceWorkQueueStep at moved
  cases selected : selectNextScheduled (cSupportedSourceExecFacts space) with
  | none => simp [selected] at moved
  | some directive =>
      simp only [selected] at moved
      have targetEq : cFireRuleScopedSourceExecFact space directive = target :=
        Option.some.inj moved
      subst target
      exact state.firePrelude (selectedPrelude directive selected)

/-! ## Complete normal-machine transitions in the authored ambient state -/

private theorem ruleScopedAdditionsWithin_authored_of_normal_and_body
    (input : InputSpec) (rows : List Subst) (template : Template)
    (owned : RuleScopedTemplateAdditionsWithin NormalRuleScopedOwnedAtom
      input rows template)
    (body : RuleScopedTemplateAdditionsWithin NormalBodyCarrierAuthorized
      input rows template) :
    RuleScopedTemplateAdditionsWithin AuthoredNormalCapabilityAtom
      input rows template := by
  intro sink member
  cases sink with
  | remove atom => trivial
  | add atom =>
      intro substitution rowMember result instantiated
      have normal := owned (.add atom) member substitution rowMember result
        instantiated
      exact ⟨fun raw extracted =>
          normalProofMachineRawFacts_subset_authored (normal.1 raw extracted),
        normal.2,
        body (.add atom) member substitution rowMember result instantiated⟩
  | head count atom =>
      intro substitution rowMember result instantiated
      have normal := owned (.head count atom) member substitution rowMember
        result instantiated
      exact ⟨fun raw extracted =>
          normalProofMachineRawFacts_subset_authored (normal.1 raw extracted),
        normal.2,
        body (.head count atom) member substitution rowMember result
          instantiated⟩
  | tail count atom =>
      intro substitution rowMember result instantiated
      have normal := owned (.tail count atom) member substitution rowMember
        result instantiated
      exact ⟨fun raw extracted =>
          normalProofMachineRawFacts_subset_authored (normal.1 raw extracted),
        normal.2,
        body (.tail count atom) member substitution rowMember result
          instantiated⟩

private theorem dispatchReflectiveAdditionsClosed
    {space : List Atom} (state : AuthoredNormalCapabilityState space) :
    let live := morkEraseSupport space normalDispatchReloadDirective.atom
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDispatchReloadDirective.atom ::
        live.erase normalDispatchReloadDirective.atom)
      normalDispatchReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin AuthoredNormalCapabilityAtom rows
      normalDispatchReloadDirective.rule.tmpl := by
  dsimp only
  let live := morkEraseSupport space normalDispatchReloadDirective.atom
  have context : NormalProofMachineExecutionContext live :=
    NormalProofMachineExecutionContext.morkEraseSupport
      (AuthoredNormalCapabilityState.executionContext state)
      normalDispatchReloadDirective.atom
  have rawWithin : ReflectiveAddedRawWithin authoredNormalVerifierRawFacts
      ((Conformance.Computable.cmatchInputSpec []
        (normalDispatchReloadDirective.atom ::
          live.erase normalDispatchReloadDirective.atom)
        normalDispatchReloadDirective.rule.input).map Prod.fst)
      normalDispatchReloadDirective.rule.tmpl :=
    normalDispatchReload_additions_raw_within
      authoredNormalVerifierRawFacts context.1 context.2
      (fun selectedRaw selectedExtract =>
        normalProofMachineRawFacts_subset_authored
          (List.mem_filterMap.mpr
            ⟨normalDispatchReloadDirective.atom,
              by simp [normalProofMachineRules,
                normalDispatchReloadDirective],
              selectedExtract⟩))
      (fun normalRaw normalMember =>
        normalProofMachineRawFacts_subset_authored normalMember)
  have internalWithin : ReflectiveAddedAtomsWithin
      NormalVerifierInternalRowIntact
      ((Conformance.Computable.cmatchInputSpec []
        (normalDispatchReloadDirective.atom ::
          live.erase normalDispatchReloadDirective.atom)
        normalDispatchReloadDirective.rule.input).map Prod.fst)
      normalDispatchReloadDirective.rule.tmpl :=
    normalDispatchReload_additions_internal_closed context.2
  have noCarrier := normalDispatchReload_additions_no_carrier context.2
  intro atom added
  exact ⟨rawWithin atom added, internalWithin atom added,
    fun continuation captured =>
      False.elim (noCarrier atom added continuation captured)⟩

theorem normalDispatchReload_ruleScoped_additions_closed
    {space : List Atom} (state : AuthoredNormalCapabilityState space) :
    let live := morkEraseSupport space normalDispatchReloadDirective.atom
    let read := morkInsertSupport live normalDispatchReloadDirective.atom
    let rows := (cMatchInputSpecMork [] read
      normalDispatchReloadDirective.rule.input).filter fun
        (substitution, _) =>
          matchSourceGuards substitution normalDispatchReloadDirective.rule.guards
    RuleScopedTemplateAdditionsWithin AuthoredNormalCapabilityAtom
      normalDispatchReloadDirective.rule.input (rows.map Prod.fst)
      normalDispatchReloadDirective.rule.tmpl := by
  dsimp only
  apply ruleScopedInheritedTemplate_additions_of_reflective
    AuthoredNormalCapabilityAtom normalDispatchReloadDirective.rule.input _
    normalDispatchReloadDirective.rule.tmpl
  · exact normalProofMachineDirective_support_set
      (List.mem_filterMap.mpr
        ⟨normalDispatchReloadRule,
          by simp [normalProofMachineRules],
          extract_normalDispatchReloadRule_exact⟩)
  · unfold RuleScopedInheritedTemplate
    decide +kernel
  · apply reflectiveAddedAtomsWithin_of_rows_subset
      AuthoredNormalCapabilityAtom _ _
      normalDispatchReloadDirective.rule.tmpl
    · intro substitution member
      exact ruleScopedCompatRow_mem_reflectiveRead space
        normalDispatchReloadDirective _ rfl member
    · exact dispatchReflectiveAdditionsClosed state

theorem normalProofMachineDirective_authored_additions_closed
    {space : List Atom} (state : AuthoredNormalCapabilityState space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    let live := morkEraseSupport space directive.atom
    let read := morkInsertSupport live directive.atom
    let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
      (substitution, _) => matchSourceGuards substitution directive.rule.guards
    RuleScopedTemplateAdditionsWithin AuthoredNormalCapabilityAtom
      directive.rule.input (rows.map Prod.fst) directive.rule.tmpl := by
  by_cases dispatch : directive = normalDispatchReloadDirective
  · subst directive
    exact normalDispatchReload_ruleScoped_additions_closed state
  · exact ruleScopedAdditionsWithin_authored_of_normal_and_body
      directive.rule.input _ directive.rule.tmpl
      (normalProofMachineDirective_ruleScoped_owned_additions_closed_of_ne_dispatch
        state.executionContext state.bodyCarrierAuthorized member dispatch)
      (normalProofMachineDirective_ruleScoped_capability_additions_closed_of_ne_dispatch
        state.executionContext state.bodyCarrierAuthorized member dispatch)

/-- Every actual physical normal-machine transition preserves the complete
authored verifier boundary, even while ordered-event directives remain
resident. -/
theorem AuthoredNormalCapabilityState.fireNormal
    {space : List Atom} (state : AuthoredNormalCapabilityState space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    AuthoredNormalCapabilityState
      (cFireRuleScopedSourceExecFact space directive) := by
  exact ⟨cFireRuleScopedSourceExecFact_list_nodup space directive state.1,
    cFireRuleScopedSourceExecFact_mork_nodup space directive state.2.1,
    cFireRuleScopedSourceExecFact_atomsWithin_of_additions
      AuthoredNormalCapabilityAtom space directive state.2.2
      (normalProofMachineDirective_authored_additions_closed state member)⟩

theorem AuthoredNormalCapabilityState.fire
    {space : List Atom} (state : AuthoredNormalCapabilityState space)
    {directive : SourceExecFact}
    (member : directive ∈ authoredNormalVerifierDirectives) :
    AuthoredNormalCapabilityState
      (cFireRuleScopedSourceExecFact space directive) := by
  rw [authoredNormalVerifierDirectives_eq_prelude_append_normal,
    List.mem_append] at member
  rcases member with prelude | normal
  · exact state.firePrelude prelude
  · exact state.fireNormal normal

theorem AuthoredNormalCapabilityState.supportedWithin
    {space : List Atom} (state : AuthoredNormalCapabilityState space) :
    ∀ directive ∈ cSupportedSourceExecFacts space,
      directive ∈ authoredNormalVerifierDirectives := by
  intro directive member
  rcases List.mem_filterMap.mp member with
    ⟨atom, atomMember, extracted⟩
  unfold extractSupportedSourceExecFact at extracted
  cases rawEq : extractRawExecFact atom with
  | none => simp [rawEq] at extracted
  | some raw =>
      simp [rawEq] at extracted
      exact authoredNormalVerifierRawFact_decodes
        (state.rawWithin raw
          (List.mem_filterMap.mpr ⟨atom, atomMember, rawEq⟩))
        extracted

/-- The actual least-key MORK scheduler preserves the complete authored
normal-verifier capability state for every selected prelude or normal rule. -/
theorem AuthoredNormalCapabilityState.ruleScopedStep
    {space target : List Atom}
    (state : AuthoredNormalCapabilityState space)
    (moved :
      cRuleScopedSourceWorkQueueStep .leaveInert space = some target) :
    AuthoredNormalCapabilityState target := by
  unfold cRuleScopedSourceWorkQueueStep at moved
  cases selected : selectNextScheduled (cSupportedSourceExecFacts space) with
  | none => simp [selected] at moved
  | some directive =>
      simp only [selected] at moved
      have targetEq : cFireRuleScopedSourceExecFact space directive = target :=
        Option.some.inj moved
      subst target
      exact state.fire (state.supportedWithin directive
        (selectNextScheduled_mem selected))

theorem AuthoredNormalCapabilityState.of_ruleScopedNativeTypeTrace
    {policy : UnsupportedExecPolicy} (policyEq : policy = .leaveInert)
    {fuel : Nat} {source target : List Atom}
    (initial : AuthoredNormalCapabilityState source)
    (trace : RuleScopedNativeTypeTrace policy fuel source target) :
    AuthoredNormalCapabilityState target := by
  subst policy
  induction trace with
  | refl => exact initial
  | step native tail induction =>
      apply induction
      exact initial.ruleScopedStep
        ((satisfies_ruleScopedNativeListExactTargetNativeType_iff_step
          .leaveInert _ _).1 native)

/-- The complete admitted authored verifier remains capability-closed at the
boundary returned by every finite physical MORK run. -/
theorem AuthoredNormalCapabilityState.ruleScopedRunN
    (fuel : Nat) {source : List Atom}
    (initial : AuthoredNormalCapabilityState source) :
    AuthoredNormalCapabilityState
      (cRuleScopedSourceWorkQueueRunN .leaveInert fuel source).1 := by
  exact initial.of_ruleScopedNativeTypeTrace rfl
    (cRuleScopedSourceWorkQueueRunN_nativeTypeTrace .leaveInert fuel source)

section AxiomAudit

#print axioms normalProofMachineRawFacts_subset_authored
#print axioms AuthoredNormalCapabilityState.executionContext
#print axioms AuthoredNormalCapabilityState.reflectiveInvariant
#print axioms normalVerifierInternalRows_no_executable_atom
#print axioms authoredNormalVerifierRule_atom_authorized
#print axioms composeAdmittedNormalProgram_rawWithin
#print axioms composeAdmittedNormalProgram_atomsWithin
#print axioms admittedNormalInitialSupport_state
#print axioms authoredNormalVerifierDirectives_eq_prelude_append_normal
#print axioms orderedSourceEventPreludeDirective_classified
#print axioms orderedSourceEventPreludeDirective_atom_authorized
#print axioms orderedSourceEventPreludeDirective_additions_closed
#print axioms AuthoredNormalCapabilityState.firePrelude
#print axioms AuthoredNormalCapabilityState.ruleScopedStep_of_prelude
#print axioms normalDispatchReload_ruleScoped_additions_closed
#print axioms normalProofMachineDirective_authored_additions_closed
#print axioms AuthoredNormalCapabilityState.fireNormal
#print axioms AuthoredNormalCapabilityState.fire
#print axioms AuthoredNormalCapabilityState.supportedWithin
#print axioms AuthoredNormalCapabilityState.ruleScopedStep
#print axioms AuthoredNormalCapabilityState.of_ruleScopedNativeTypeTrace
#print axioms AuthoredNormalCapabilityState.ruleScopedRunN

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2AuthoredNormalCapabilityClosure
