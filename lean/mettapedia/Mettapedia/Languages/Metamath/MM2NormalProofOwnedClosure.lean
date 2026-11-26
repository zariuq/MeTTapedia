import Mettapedia.Languages.Metamath.MM2Transformation
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity

/-!
# Owned-code closure for assembled normal-proof execution

The normal verifier stores variable-bearing MM2 rules in inert, verifier-owned
rows and reinstalls them through scheduled reload transitions.  The base
transformation proves that the dispatch reloader can only recover executable
rules from that owned inventory.  This module packages the corresponding
two-part closure result: the reloader preserves both the executable whitelist
and the protected-row invariant in every source-relative owned state.
-/

namespace Mettapedia.Languages.Metamath.MM2NormalProofOwnedClosure

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-! ## Source-derived executable capabilities -/

/-- The exact ambient assumptions consumed by normal-rule matcher inversion.
The complete authored verifier may keep ordered-event directives resident, so
the ambient executable inventory is intentionally wider than the normal-only
output inventory. -/
def NormalProofMachineExecutionContext (space : List Atom) : Prop :=
  RawExecFactsWithin authoredNormalVerifierRawFacts space ∧
    NormalVerifierInternalRowsIntact space

theorem normalProofMachineRawFacts_subset_authoredNormalVerifier
    {raw : RawExecFact} (member : raw ∈ normalProofMachineRawFacts) :
    raw ∈ authoredNormalVerifierRawFacts := by
  rw [authoredNormalVerifierRawFacts, authoredNormalVerifierRules,
    List.filterMap_append, List.mem_append]
  exact Or.inr member

theorem authoredNormalVerifierRawFacts_loc_injective :
    ∀ left right,
      left ∈ authoredNormalVerifierRawFacts →
      right ∈ authoredNormalVerifierRawFacts →
      left.loc = right.loc → left = right := by
  intro left right leftMember rightMember locationsEqual
  exact List.inj_on_of_nodup_map
    (l := authoredNormalVerifierRawFacts)
    (f := RawExecFact.loc)
    (by decide +kernel) leftMember rightMember locationsEqual

theorem authoredNormalVerifierRawFact_mem_normal_of_loc_mem
    {raw : RawExecFact}
    (member : raw ∈ authoredNormalVerifierRawFacts)
    (locationMember : raw.loc ∈
      normalProofMachineRawFacts.map RawExecFact.loc) :
    raw ∈ normalProofMachineRawFacts := by
  rw [List.mem_map] at locationMember
  obtain ⟨normalRaw, normalMember, locationEqual⟩ := locationMember
  have normalAuthored :=
    normalProofMachineRawFacts_subset_authoredNormalVerifier normalMember
  have equal := authoredNormalVerifierRawFacts_loc_injective raw normalRaw
    member normalAuthored locationEqual.symm
  simpa [equal] using normalMember

/-- A reissued shell uses an actual input carrier at a normal scheduler location. -/
private theorem normal_shell_readback_authorized
    {space : List Atom} {selected captured : Atom} {substitution : Subst}
    {priority label inputName outputName : String} {pattern : Pattern} {raw : RawExecFact}
    (state : NormalProofMachineExecutionContext space)
    (selectedNormal : selected ∈ normalProofMachineRules)
    (locNormal : (.expression [.symbol priority, .symbol label] : Atom) ∈
      normalProofMachineRawFacts.map RawExecFact.loc)
    (authored : (.expression [.symbol "exec", .expression [.symbol priority, .symbol label],
      .var inputName, .var outputName] : Atom) ∈ pattern.atoms)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec [] (selected :: space.erase selected)
        (.compat pattern)).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution
      (.expression [.symbol "exec", .expression [.symbol priority, .symbol label],
        .var inputName, .var outputName]) = some captured)
    (extracts : extractRawExecFact captured = some raw) : raw ∈ normalProofMachineRawFacts := by
  have carrier := compat_factor_instantiated_mem (selected :: space.erase selected) pattern
    authored rowMember instantiates
  rcases List.mem_cons.mp carrier with same | prior
  · exact List.mem_filterMap.mpr ⟨selected, selectedNormal, by rwa [← same]⟩
  · apply authoredNormalVerifierRawFact_mem_normal_of_loc_mem
    · exact state.1 raw (List.mem_filterMap.mpr ⟨captured, List.mem_of_mem_erase prior, extracts⟩)
    · rw [← instantiateTemplateAtom?_materializes instantiates] at extracts
      simp only [applySubst, applySubst.applySubstList, extractRawExecFact] at extracts
      have location := congrArg RawExecFact.loc (Option.some.inj extracts).symm
      simpa only [location] using locNormal

private def bundleHasTag (tag : String) : Atom → Bool
  | .expression (.symbol head :: _) => head == tag
  | _ => false

/-- A protected bundle is reconstructed exactly when its tag singles out a
row of the owned inventory and the selected rule is outside that inventory. -/
private theorem normal_bundle_readback
    {space : List Atom} {selected bundle : Atom} {substitution : Subst}
    {tag : String} {fields : List Atom} {pattern : Pattern}
    (intact : NormalVerifierInternalRowsIntact space)
    (reserved : isVerifierOwnedInternalNamespace tag = true)
    (selectedOutside : isVerifierOwnedInternalRowShape selected = false)
    (unique : normalVerifierInternalRows.filter (bundleHasTag tag) = [bundle])
    (authored : (.expression (.symbol tag :: fields) : Atom) ∈ pattern.atoms)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec [] (selected :: space.erase selected)
        (.compat pattern)).map Prod.fst) :
    applySubst substitution (.expression (.symbol tag :: fields)) = bundle := by
  obtain ⟨carrier, present, replay⟩ :=
    Conformance.Computable.cmatchInputSpec_compat_factor_replay_origin
      (selected :: space.erase selected) pattern _ authored rowMember
  have shape : isVerifierOwnedInternalRowShape carrier = true := by
    rw [← replay]
    simp only [applySubst, applySubst.applySubstList, isVerifierOwnedInternalRowShape,
      reserved, Bool.true_or]
  have inSpace : carrier ∈ space := by
    rcases List.mem_cons.mp present with same | prior
    · rw [same, selectedOutside] at shape
      contradiction
    · exact List.mem_of_mem_erase prior
  have tagAgrees : bundleHasTag tag carrier = true := by
    rw [← replay]
    simp [bundleHasTag, applySubst, applySubst.applySubstList]
  have filtered : carrier ∈ normalVerifierInternalRows.filter (bundleHasTag tag) :=
    List.mem_filter.mpr ⟨intact carrier inSpace shape, tagAgrees⟩
  rw [unique] at filtered
  exact replay.trans (List.mem_singleton.mp filtered)

theorem NormalProofMachineOwnedState.executionContext
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    NormalProofMachineExecutionContext space := by
  exact ⟨fun raw member =>
      normalProofMachineRawFacts_subset_authoredNormalVerifier
        (state.1.2 raw member),
    state.2⟩

/-- The two normal body-matcher carriers preserve an opaque continuation.
This relation exposes precisely that payload without constraining the formula
data around it. -/
inductive NormalBodyContinuationCapture : Atom → Atom → Prop where
  | bodyMatch (proof position sourceBody actualBody continuation : Atom) :
      NormalBodyContinuationCapture
        (.expression
          [.symbol "mm-body-match", proof, position, sourceBody, actualBody,
            continuation])
        continuation
  | bodyPrefix
      (proof position replacementBody actualBody sourceTail continuation : Atom) :
      NormalBodyContinuationCapture
        (.expression
          [.symbol "mm-body-prefix", proof, position, replacementBody,
            actualBody, sourceTail, continuation])
        continuation

/-- Source-relative authority carried by one body-machine continuation.  A
non-executable value satisfies the executable clause vacuously, while any
actual executable shell must come from the generated verifier inventory. -/
def NormalBodyContinuationAuthorized (continuation : Atom) : Prop :=
  RawExecAtomWithin normalProofMachineRawFacts continuation ∧
    NormalVerifierInternalRowIntact continuation

/-- Every continuation stored in a live body-matcher carrier has executable
authority only when it already belongs to the generated normal verifier.
Ordinary data continuations satisfy this without being treated as code. -/
def NormalBodyContinuationCapabilities (space : List Atom) : Prop :=
  CapturedAtomsWithin
    NormalBodyContinuationAuthorized
    NormalBodyContinuationCapture space

/-- Strong source-relative state for the one rule that republishes a captured
continuation.  The extra field is an entry-boundary invariant, not a claim
about arbitrary hand-authored MM2 spaces. -/
def NormalProofMachineCapabilityState (space : List Atom) : Prop :=
  NormalProofMachineOwnedState space ∧
    NormalBodyContinuationCapabilities space

/-! ## Data-only sink classification -/

/-- A template atom whose outer constructor and head cannot become either an
executable shell or a protected verifier-owned carrier under substitution.
Variables below the outer head remain unrestricted data. -/
@[simp] def normalOwnedSafeTemplateAtom : Atom → Bool
  | .var _ => false
  | .symbol _ | .grounded _ => true
  | .expression [] => true
  | .expression (.symbol tag :: _) =>
      tag != "exec" &&
        !(isVerifierOwnedInternalNamespace tag ||
          tag == "mm-normal-final-formula-candidate")
  | .expression (.var _ :: _) => false
  | .expression (.grounded _ :: _) => true
  | .expression (.expression _ :: _) => true

/-- Only additions can introduce atoms.  Removals and support extrema are
irrelevant to the addition-origin obligations. -/
@[simp] def normalOwnedSafeSink : Sink → Bool
  | .add atom => normalOwnedSafeTemplateAtom atom
  | .remove _ | .head _ _ | .tail _ _ => true

def NormalOwnedSafeTemplate (template : Template) : Prop :=
  template.sinks.all normalOwnedSafeSink = true

theorem normalOwnedSafeTemplateAtom_raw_none
    (substitution : Subst) (template : Atom)
    (safe : normalOwnedSafeTemplateAtom template = true) :
    extractRawExecFact (applySubst substitution template) = none := by
  cases template with
  | var name => simp at safe
  | symbol name => simp [applySubst, extractRawExecFact]
  | grounded value => simp [applySubst, extractRawExecFact]
  | expression children =>
      cases children with
      | nil =>
          simp [applySubst, applySubst.applySubstList,
            extractRawExecFact]
      | cons head tail =>
          cases head with
          | var name => simp at safe
          | symbol tag =>
              simp only [normalOwnedSafeTemplateAtom, Bool.and_eq_true,
                bne_iff_ne] at safe
              simp [applySubst, applySubst.applySubstList,
                extractRawExecFact, safe.1]
          | grounded value =>
              simp [applySubst, applySubst.applySubstList,
                extractRawExecFact]
          | expression nested =>
              simp [applySubst, applySubst.applySubstList,
                extractRawExecFact]

theorem normalOwnedSafeTemplateAtom_internal_false
    (substitution : Subst) (template : Atom)
    (safe : normalOwnedSafeTemplateAtom template = true) :
    isVerifierOwnedInternalRowShape (applySubst substitution template) =
      false := by
  cases template with
  | var name => simp at safe
  | symbol name => simp [applySubst, isVerifierOwnedInternalRowShape]
  | grounded value => simp [applySubst, isVerifierOwnedInternalRowShape]
  | expression children =>
      cases children with
      | nil =>
          simp [applySubst, applySubst.applySubstList,
            isVerifierOwnedInternalRowShape]
      | cons head tail =>
          cases head with
          | var name => simp at safe
          | symbol tag =>
              simp only [normalOwnedSafeTemplateAtom, Bool.and_eq_true,
                bne_iff_ne] at safe
              have reservedFalse :
                  (isVerifierOwnedInternalNamespace tag ||
                    tag == "mm-normal-final-formula-candidate") = false :=
                by
                  cases reserved :
                      (isVerifierOwnedInternalNamespace tag ||
                        tag == "mm-normal-final-formula-candidate") with
                  | false => rfl
                  | true =>
                      have impossible := safe.2
                      rw [reserved] at impossible
                      simp at impossible
              change
                (isVerifierOwnedInternalNamespace tag ||
                  tag == "mm-normal-final-formula-candidate") = false
              exact reservedFalse
          | grounded value =>
              simp [applySubst, applySubst.applySubstList,
                isVerifierOwnedInternalRowShape]
          | expression nested =>
              simp [applySubst, applySubst.applySubstList,
                isVerifierOwnedInternalRowShape]

private theorem normalOwnedSafeInstantiation_raw_impossible
    {substitution : Subst} {template atom : Atom} {raw : RawExecFact}
    (safe : normalOwnedSafeTemplateAtom template = true)
    (instantiates : instantiateTemplateAtom? substitution template =
      some atom)
    (extracts : extractRawExecFact atom = some raw) : False := by
  have instantiated : applySubst substitution template = atom := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · exact Option.some.inj instantiates
    · simp at instantiates
  rw [← instantiated] at extracts
  rw [normalOwnedSafeTemplateAtom_raw_none substitution template safe]
    at extracts
  contradiction

private theorem normalOwnedSafeInstantiation_internal_impossible
    {substitution : Subst} {template atom : Atom}
    (safe : normalOwnedSafeTemplateAtom template = true)
    (instantiates : instantiateTemplateAtom? substitution template =
      some atom)
    (internalShape : isVerifierOwnedInternalRowShape atom = true) : False := by
  have instantiated : applySubst substitution template = atom := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · exact Option.some.inj instantiates
    · simp at instantiates
  rw [← instantiated] at internalShape
  rw [normalOwnedSafeTemplateAtom_internal_false substitution template safe]
    at internalShape
  contradiction

/-- Check the authored add sinks against data-only shapes and an admitted
class whose meaning is established using the actual matcher row. -/
private def normalOwnedAdmissionSink (recognizes : Atom → Bool) : Sink → Bool
  | .add authored => normalOwnedSafeTemplateAtom authored || recognizes authored
  | .remove _ | .head _ _ | .tail _ _ => true

private theorem normal_owned_additions_of_sink_admission
    {rows : List Subst} {template : Template} (recognizes : Atom → Bool)
    (checked : template.sinks.all (normalOwnedAdmissionSink recognizes) = true)
    (admitted : ∀ {authored atom : Atom} {substitution : Subst},
      recognizes authored = true →
      substitution ∈ rows →
      instantiateTemplateAtom? substitution authored = some atom →
      RawExecAtomWithin normalProofMachineRawFacts atom ∧ NormalVerifierInternalRowIntact atom) :
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows template ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows template := by
  have preserved : ReflectiveAddedAtomsWithin
      (fun atom => RawExecAtomWithin normalProofMachineRawFacts atom ∧
        NormalVerifierInternalRowIntact atom) rows template := by
    intro atom added
    obtain ⟨_, inTemplate, authored, rfl, row, produced, materialized⟩ := added
    have allowed := List.all_eq_true.mp checked (.add authored) inTemplate
    change (normalOwnedSafeTemplateAtom authored || recognizes authored) = true at allowed
    have valid : normalOwnedSafeTemplateAtom authored = true ∨ recognizes authored = true := by
      simpa using allowed
    rcases valid with data | accepted
    · exact ⟨fun _ raw => False.elim
        (normalOwnedSafeInstantiation_raw_impossible data materialized raw),
        fun shape => False.elim
          (normalOwnedSafeInstantiation_internal_impossible data materialized shape)⟩
    · exact admitted accepted produced materialized
  exact ⟨fun atom added => (preserved atom added).1, fun atom added => (preserved atom added).2⟩

private def reloadSelfTemplate (priority name input output : String) : Atom :=
  .expression [.symbol "exec", .expression [.symbol priority, .symbol name],
    .var input, .var output]

private theorem reloadShell_intact {priority name input output : String} {row : Subst} {atom : Atom}
    (instantiates : instantiateTemplateAtom? row (reloadSelfTemplate priority name input output) =
      some atom) : NormalVerifierInternalRowIntact atom := by
  intro shape
  rw [← instantiateTemplateAtom?_materializes instantiates] at shape
  simp [reloadSelfTemplate, applySubst, applySubst.applySubstList,
    isVerifierOwnedInternalRowShape, isVerifierOwnedInternalNamespace] at shape

/-- A reloader can republish its matched self shell and the exact rule
values captured from its owned carrier. -/
private theorem normal_owned_additions_of_reload
    {rows : List Subst} {template : Template}
    (priority name input output : String) (fields : List Atom)
    (checked : template.sinks.all (normalOwnedAdmissionSink
      (fun atom => atom == reloadSelfTemplate priority name input output ||
        fields.contains atom)) = true)
    (shell : ∀ {atom : Atom} {row : Subst}, row ∈ rows →
      instantiateTemplateAtom? row (reloadSelfTemplate priority name input output) = some atom →
      RawExecAtomWithin normalProofMachineRawFacts atom)
    (field : ∀ {authored atom : Atom} {row : Subst},
      authored ∈ fields → row ∈ rows →
      instantiateTemplateAtom? row authored = some atom → atom ∈ normalProofMachineRules) :
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows template ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows template := by
  apply normal_owned_additions_of_sink_admission _ checked
  intro authored atom row allowed produced instantiates
  have classified : authored = reloadSelfTemplate priority name input output ∨ authored ∈ fields := by
    simpa using allowed
  rcases classified with same | payload
  · subst authored
    exact ⟨shell produced instantiates, reloadShell_intact instantiates⟩
  · have member := field payload produced instantiates
    refine ⟨fun raw extracts => List.mem_filterMap.mpr ⟨atom, member, extracts⟩, ?_⟩
    intro shape
    have inert := List.all_eq_true.mp normalProofMachineRules_no_internal_row_shape atom member
    simp [shape] at inert

private theorem normal_owned_data_additions (rows : List Subst) (template : Template)
    (safe : NormalOwnedSafeTemplate template) :
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows template ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows template := by
  apply normal_owned_additions_of_sink_admission (fun _ => false)
  · apply List.all_eq_true.mpr
    intro sink member
    have classified := List.all_eq_true.mp safe sink member
    cases sink with
    | add _ => simpa [normalOwnedAdmissionSink] using classified
    | remove _ => rfl
    | head _ _ => rfl
    | tail _ _ => rfl
  · intro _ _ _ impossible
    cases impossible

/-- A syntactically data-only target template preserves the executable whitelist. -/
theorem normalOwnedSafeTemplate_raw_closed
    (rows : List Subst) (template : Template)
    (safe : NormalOwnedSafeTemplate template) :
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows template :=
  (normal_owned_data_additions rows template safe).1

/-- The same data-only template preserves the protected inert-row invariant. -/
theorem normalOwnedSafeTemplate_internal_closed
    (rows : List Subst) (template : Template)
    (safe : NormalOwnedSafeTemplate template) :
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows template :=
  (normal_owned_data_additions rows template safe).2

/-! ## Generic matcher provenance used by opaque reload bundles -/

/-- A successful suffix of the computable compatible matcher extends the
substitution with which that suffix began. -/
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

/-- The corresponding two-factor matcher decomposition used by reloaders
whose payload rules are authored directly in the sink batch. -/
private theorem cmatchInputSpec_two_match_chain
    {space : List Atom} {first second : Atom} {substitution : Subst}
    (member : substitution ∈
      (Conformance.Computable.cmatchInputSpec [] space
        (.compat (mkPattern [first, second]))).map Prod.fst) :
    ∃ afterFirst firstAtom secondAtom,
      firstAtom ∈ space ∧ secondAtom ∈ space ∧
        Conformance.Computable.cmatchAtom [] first firstAtom =
          some afterFirst ∧
        Conformance.Computable.cmatchAtom afterFirst second secondAtom =
          some substitution := by
  rw [List.mem_map] at member
  obtain ⟨⟨found, witnesses⟩, foundMember, foundEq⟩ := member
  change found = substitution at foundEq
  subst substitution
  simp only [Conformance.Computable.cmatchInputSpec, mkPattern,
    Conformance.Computable.cmatchPattern,
    Conformance.Computable.cmatchPattern.go, List.mem_flatMap] at foundMember
  obtain ⟨⟨afterFirst, firstAtom⟩, firstMatch,
    afterFirstMember⟩ := foundMember
  obtain ⟨⟨afterSecond, secondAtom⟩, secondMatch,
    finished⟩ := afterFirstMember
  simp only [List.mem_singleton, Prod.mk.injEq] at finished
  rcases finished with ⟨substEq, _witnessEq⟩
  subst afterSecond
  rw [List.mem_filterMap] at firstMatch secondMatch
  obtain ⟨firstCandidate, firstMember, firstResult⟩ := firstMatch
  obtain ⟨secondCandidate, secondMember, secondResult⟩ := secondMatch
  simp only [Option.map_eq_some_iff] at firstResult secondResult
  obtain ⟨firstSubst, firstMatched, firstEq⟩ := firstResult
  obtain ⟨secondSubst, secondMatched, secondEq⟩ := secondResult
  cases firstEq
  cases secondEq
  exact ⟨afterFirst, firstAtom, secondAtom, firstMember, secondMember,
    firstMatched, secondMatched⟩

/-- In an owned machine state, the body reloader's third matcher witness is
the one exact generated body-rule bundle.  A same-shaped row with altered
payloads is not authorized merely by its head symbol. -/
private theorem normalBodyReload_bundle_readback
    {space : List Atom} (state : NormalProofMachineExecutionContext space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        normalBodyReloadDirective.rule.input).map Prod.fst) :
    applySubst substitution
      (.expression [.symbol "mm-internal-body-match-rules",
         .var "body-rule-const", .var "body-rule-variable",
         .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
         .var "body-rule-nil"]) = normalBodyMatchRuleBundle := by
  refine normal_bundle_readback state.2 ?_ ?_ ?_ ?_ rowMember
  · rfl
  · rfl
  · rfl
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The body reloader's self shell is recovered from an executable witness
already present in the owned state (or from the selected directive prepended
to the read space).  It therefore cannot synthesize foreign executable code. -/
private theorem normalBodyReload_captured_self_raw_authorized
    {space : List Atom} {substitution : Subst} {captured : Atom}
    {raw : RawExecFact}
    (state : NormalProofMachineExecutionContext space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        normalBodyReloadDirective.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution
        (.expression
          [.symbol "exec",
            .expression [.symbol "11", .symbol "mm-normal-body-reload"],
            .var "body-reload-self-input",
            .var "body-reload-self-output"]) = some captured)
    (extracts : extractRawExecFact captured = some raw) :
    raw ∈ normalProofMachineRawFacts := by
  refine normal_shell_readback_authorized state ?_ ?_ ?_ rowMember instantiates extracts
  · simp [normalBodyReloadDirective, normalProofMachineRules]
  · decide +kernel
  · exact List.mem_cons_self

/-- Every variable-valued body-rule add sink is fixed by the exact owned
bundle and therefore selects one of the five generated matcher rules. -/
theorem normalBodyReload_captured_rule_authorized
    {space : List Atom} {substitution : Subst} {authored captured : Atom}
    (state : NormalProofMachineExecutionContext space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        normalBodyReloadDirective.rule.input).map Prod.fst)
    (authoredMember : authored ∈
      [(.var "body-rule-const" : Atom), .var "body-rule-variable",
        .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
        .var "body-rule-nil"])
    (instantiates :
      instantiateTemplateAtom? substitution authored = some captured) :
    captured ∈
      [normalBodyMatchConstRule, normalBodyMatchVariableRule,
        normalBodyPrefixNilRule, normalBodyPrefixConsRule,
        normalBodyMatchNilRule] := by
  exact materialized_field_instantiation_mem (normalBodyReload_bundle_readback state rowMember) authoredMember instantiates

theorem normalBodyReload_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyReloadDirective.atom ::
        space.erase normalBodyReloadDirective.atom)
      normalBodyReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalBodyReloadDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalBodyReloadDirective.rule.tmpl := by
  apply normal_owned_additions_of_reload "11" "mm-normal-body-reload"
    "body-reload-self-input" "body-reload-self-output"
    [(.var "body-rule-const" : Atom), .var "body-rule-variable",
      .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
      .var "body-rule-nil"] (by decide +kernel)
  · intro atom row produced materialized raw extracts
    exact normalBodyReload_captured_self_raw_authorized state produced materialized extracts
  · intro authored atom row member produced materialized
    have read := normalBodyReload_captured_rule_authorized state produced member materialized
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at read
    rcases read with rfl | rfl | rfl | rfl | rfl <;> simp [normalProofMachineRules]

/-- Every executable atom introduced by the body-matcher reloader is either
its already-authorized self shell or one of the five rules reconstructed from
the exact owned bundle. -/
theorem normalBodyReload_additions_raw_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyReloadDirective.atom ::
        space.erase normalBodyReloadDirective.atom)
      normalBodyReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalBodyReloadDirective.rule.tmpl :=
  (normalBodyReload_owned_additions_closed state).1

theorem normalBodyReload_additions_internal_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyReloadDirective.atom ::
        space.erase normalBodyReloadDirective.atom)
      normalBodyReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalBodyReloadDirective.rule.tmpl :=
  (normalBodyReload_owned_additions_closed state).2

theorem NormalProofMachineOwnedState.fire_bodyReload
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space normalBodyReloadDirective) := by
  rcases normalBodyReload_owned_additions_closed
      (NormalProofMachineOwnedState.executionContext state) with
    ⟨rawClosed, internalClosed⟩
  exact state.fire normalBodyReloadDirective
    (by
      change normalBodyReloadDirective ∈
        normalProofMachineRules.filterMap extractSupportedSourceExecFact
      exact List.mem_filterMap.mpr
        ⟨normalBodyReloadRule,
          by simp [normalProofMachineRules],
          extract_normalBodyReloadRule_exact⟩)
    rawClosed internalClosed

/-! ## Result-body builder reloader -/

/-- In an owned state, a body-builder reload match can use only the canonical
seven-rule carrier. -/
private theorem normalBodyBuildReload_bundle_readback
    {space : List Atom} (state : NormalProofMachineExecutionContext space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyBuildReloadDirective.atom ::
          space.erase normalBodyBuildReloadDirective.atom)
        normalBodyBuildReloadDirective.rule.input).map Prod.fst) :
    applySubst substitution
      (.expression [.symbol "mm-internal-body-build-rules",
         .var "build-rule-const", .var "build-rule-variable",
         .var "build-rule-prefix-nil", .var "build-rule-prefix-cons",
         .var "build-rule-nil", .var "build-rule-reverse-cons",
         .var "build-rule-reverse-nil"]) = normalBodyBuildRuleBundle := by
  refine normal_bundle_readback state.2 ?_ ?_ ?_ ?_ rowMember
  · rfl
  · rfl
  · rfl
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The reloader's self shell is recovered from an executable witness already
authorized by the source-relative state. -/
private theorem normalBodyBuildReload_captured_self_raw_authorized
    {space : List Atom} {substitution : Subst} {captured : Atom}
    {raw : RawExecFact}
    (state : NormalProofMachineExecutionContext space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyBuildReloadDirective.atom ::
          space.erase normalBodyBuildReloadDirective.atom)
        normalBodyBuildReloadDirective.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution
        (.expression
          [.symbol "exec",
            .expression
              [.symbol "30", .symbol "mm-normal-body-build-reload"],
            .var "build-reload-self-input",
            .var "build-reload-self-output"]) = some captured)
    (extracts : extractRawExecFact captured = some raw) :
    raw ∈ normalProofMachineRawFacts := by
  refine normal_shell_readback_authorized state ?_ ?_ ?_ rowMember instantiates extracts
  · simp [normalBodyBuildReloadDirective, normalProofMachineRules]
  · decide +kernel
  · exact List.mem_cons_self

/-- A variable-valued body-builder add sink is one of the seven rules in the
exact owned carrier. -/
theorem normalBodyBuildReload_captured_rule_authorized
    {space : List Atom} {substitution : Subst} {authored captured : Atom}
    (state : NormalProofMachineExecutionContext space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyBuildReloadDirective.atom ::
          space.erase normalBodyBuildReloadDirective.atom)
        normalBodyBuildReloadDirective.rule.input).map Prod.fst)
    (authoredMember : authored ∈
      [(.var "build-rule-const" : Atom), .var "build-rule-variable",
        .var "build-rule-prefix-nil", .var "build-rule-prefix-cons",
        .var "build-rule-nil", .var "build-rule-reverse-cons",
        .var "build-rule-reverse-nil"])
    (instantiates :
      instantiateTemplateAtom? substitution authored = some captured) :
    captured ∈
      [normalBodyBuildConstRule, normalBodyBuildVariableRule,
        normalBodyBuildPrefixNilRule, normalBodyBuildPrefixConsRule,
        normalBodyBuildNilRule, normalBodyReverseConsRule,
        normalBodyReverseNilRule] := by
  exact materialized_field_instantiation_mem (normalBodyBuildReload_bundle_readback state rowMember) authoredMember instantiates

theorem normalBodyBuildReload_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyBuildReloadDirective.atom ::
        space.erase normalBodyBuildReloadDirective.atom)
      normalBodyBuildReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalBodyBuildReloadDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalBodyBuildReloadDirective.rule.tmpl := by
  apply normal_owned_additions_of_reload "30" "mm-normal-body-build-reload"
    "build-reload-self-input" "build-reload-self-output"
    [(.var "build-rule-const" : Atom), .var "build-rule-variable",
      .var "build-rule-prefix-nil", .var "build-rule-prefix-cons",
      .var "build-rule-nil", .var "build-rule-reverse-cons",
      .var "build-rule-reverse-nil"] (by decide +kernel)
  · intro atom row produced materialized raw extracts
    exact normalBodyBuildReload_captured_self_raw_authorized state produced materialized extracts
  · intro authored atom row member produced materialized
    have read := normalBodyBuildReload_captured_rule_authorized state produced member materialized
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at read
    rcases read with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [normalProofMachineRules]

/-- Every executable addition made by the result-body reloader comes from its
authorized self shell or the exact seven-rule carrier. -/
theorem normalBodyBuildReload_additions_raw_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyBuildReloadDirective.atom ::
        space.erase normalBodyBuildReloadDirective.atom)
      normalBodyBuildReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalBodyBuildReloadDirective.rule.tmpl :=
  (normalBodyBuildReload_owned_additions_closed state).1

theorem normalBodyBuildReload_additions_internal_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyBuildReloadDirective.atom ::
        space.erase normalBodyBuildReloadDirective.atom)
      normalBodyBuildReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalBodyBuildReloadDirective.rule.tmpl :=
  (normalBodyBuildReload_owned_additions_closed state).2

theorem NormalProofMachineOwnedState.fire_bodyBuildReload
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space
        normalBodyBuildReloadDirective) := by
  rcases normalBodyBuildReload_owned_additions_closed
      (NormalProofMachineOwnedState.executionContext state) with
    ⟨rawClosed, internalClosed⟩
  exact state.fire normalBodyBuildReloadDirective
    (by
      change normalBodyBuildReloadDirective ∈
        normalProofMachineRules.filterMap extractSupportedSourceExecFact
      exact List.mem_filterMap.mpr
        ⟨normalBodyBuildReloadRule,
          by simp [normalProofMachineRules],
          extract_normalBodyBuildReloadRule_exact⟩)
    rawClosed internalClosed

/-! ## DV-machine reloader -/

/-- Public proof surface for the otherwise private authored DV matcher list. -/
private theorem normalDVReload_input_exact :
    normalDVReloadDirective.rule.input =
      .compat (mkPattern
        [(.expression
            [.symbol "exec",
              .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
              .var "dv-reload-self-input",
              .var "dv-reload-self-output"] : Atom),
         .expression
            [.symbol "mm-reload-dv", .var "dv-reload-proof",
              .var "dv-reload-pc"],
         .expression
            [.symbol "mm-internal-dv-rules",
              .var "dv-rule-pair-begin", .var "dv-rule-left-const",
              .var "dv-rule-left-variable", .var "dv-rule-right-const",
              .var "dv-rule-right-variable", .var "dv-rule-right-nil",
              .var "dv-rule-left-nil", .var "dv-rule-complete"]]) := by
  rfl

/-- Public proof surface for the otherwise private authored DV sink list. -/
private theorem normalDVReload_sinks_exact :
    normalDVReloadDirective.rule.tmpl.sinks =
      [Sink.add
        (.expression
          [.symbol "exec",
            .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
            .var "dv-reload-self-input", .var "dv-reload-self-output"]),
       Sink.remove
        (.expression
          [.symbol "mm-reload-dv", .var "dv-reload-proof",
            .var "dv-reload-pc"]),
       Sink.add (.var "dv-rule-pair-begin"),
       Sink.add (.var "dv-rule-left-const"),
       Sink.add (.var "dv-rule-left-variable"),
       Sink.add (.var "dv-rule-right-const"),
       Sink.add (.var "dv-rule-right-variable"),
       Sink.add (.var "dv-rule-right-nil"),
       Sink.add (.var "dv-rule-left-nil"),
       Sink.add (.var "dv-rule-complete")] := by
  rfl

/-- In an owned state the third DV-reload witness is the one exact carrier
emitted by the generic verifier, never a same-headed row with altered code. -/
private theorem normalDVReload_bundle_readback
    {space : List Atom} (state : NormalProofMachineExecutionContext space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDVReloadDirective.atom ::
          space.erase normalDVReloadDirective.atom)
        normalDVReloadDirective.rule.input).map Prod.fst) :
    applySubst substitution
      (.expression [.symbol "mm-internal-dv-rules",
         .var "dv-rule-pair-begin", .var "dv-rule-left-const",
         .var "dv-rule-left-variable", .var "dv-rule-right-const",
         .var "dv-rule-right-variable", .var "dv-rule-right-nil",
         .var "dv-rule-left-nil", .var "dv-rule-complete"]) = normalDVRuleBundle := by
  refine normal_bundle_readback state.2 ?_ ?_ ?_ ?_ rowMember
  · rfl
  · rfl
  · rfl
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The captured DV-reloader self shell is an executable atom already present
in the owned state (or the selected directive itself). -/
private theorem normalDVReload_captured_self_raw_authorized
    {space : List Atom} {substitution : Subst} {captured : Atom}
    {raw : RawExecFact}
    (state : NormalProofMachineExecutionContext space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDVReloadDirective.atom ::
          space.erase normalDVReloadDirective.atom)
        normalDVReloadDirective.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution
        (.expression
          [.symbol "exec",
            .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
            .var "dv-reload-self-input", .var "dv-reload-self-output"]) =
          some captured)
    (extracts : extractRawExecFact captured = some raw) :
    raw ∈ normalProofMachineRawFacts := by
  refine normal_shell_readback_authorized state ?_ ?_ ?_ rowMember instantiates extracts
  · simp [normalDVReloadDirective, normalProofMachineRules]
  · decide +kernel
  · exact List.mem_cons_self

/-- A variable-valued DV add sink is fixed by the exact owned carrier and
therefore selects one of the eight authored DV rules. -/
theorem normalDVReload_captured_rule_authorized
    {space : List Atom} {substitution : Subst} {authored captured : Atom}
    (state : NormalProofMachineExecutionContext space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDVReloadDirective.atom ::
          space.erase normalDVReloadDirective.atom)
        normalDVReloadDirective.rule.input).map Prod.fst)
    (authoredMember : authored ∈
      [(.var "dv-rule-pair-begin" : Atom), .var "dv-rule-left-const",
        .var "dv-rule-left-variable", .var "dv-rule-right-const",
        .var "dv-rule-right-variable", .var "dv-rule-right-nil",
        .var "dv-rule-left-nil", .var "dv-rule-complete"])
    (instantiates :
      instantiateTemplateAtom? substitution authored = some captured) :
    captured ∈
      [normalDVPairBeginRule, normalDVLeftConstRule,
        normalDVLeftVariableRule, normalDVRightConstRule,
        normalDVRightVariableRule, normalDVRightNilRule,
        normalDVLeftNilRule, normalDVCompleteRule] := by
  exact materialized_field_instantiation_mem (normalDVReload_bundle_readback state rowMember) authoredMember instantiates

theorem normalDVReload_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDVReloadDirective.atom ::
        space.erase normalDVReloadDirective.atom)
      normalDVReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalDVReloadDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalDVReloadDirective.rule.tmpl := by
  apply normal_owned_additions_of_reload "22" "mm-normal-dv-reload"
    "dv-reload-self-input" "dv-reload-self-output"
    [(.var "dv-rule-pair-begin" : Atom), .var "dv-rule-left-const",
      .var "dv-rule-left-variable", .var "dv-rule-right-const",
      .var "dv-rule-right-variable", .var "dv-rule-right-nil",
      .var "dv-rule-left-nil", .var "dv-rule-complete"] (by rw [normalDVReload_sinks_exact]; decide +kernel)
  · intro atom row produced materialized raw extracts
    exact normalDVReload_captured_self_raw_authorized state produced materialized extracts
  · intro authored atom row member produced materialized
    have read := normalDVReload_captured_rule_authorized state produced member materialized
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at read
    rcases read with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [normalProofMachineRules]

/-- Every executable addition made by the DV reloader is either its authorized
self shell or one of the eight rules recovered from the exact owned carrier. -/
theorem normalDVReload_additions_raw_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDVReloadDirective.atom ::
        space.erase normalDVReloadDirective.atom)
      normalDVReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalDVReloadDirective.rule.tmpl :=
  (normalDVReload_owned_additions_closed state).1

theorem normalDVReload_additions_internal_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDVReloadDirective.atom ::
        space.erase normalDVReloadDirective.atom)
      normalDVReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalDVReloadDirective.rule.tmpl :=
  (normalDVReload_owned_additions_closed state).2

theorem NormalProofMachineOwnedState.fire_dvReload
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space normalDVReloadDirective) := by
  rcases normalDVReload_owned_additions_closed
      (NormalProofMachineOwnedState.executionContext state) with
    ⟨rawClosed, internalClosed⟩
  exact state.fire normalDVReloadDirective
    (by
      change normalDVReloadDirective ∈
        normalProofMachineRules.filterMap extractSupportedSourceExecFact
      exact List.mem_filterMap.mpr
        ⟨normalDVReloadRule,
          by simp [normalProofMachineRules],
          extract_normalDVReloadRule_exact⟩)
    rawClosed internalClosed



/-- The dispatch reloader cannot introduce a protected inert row.  Its two
add sinks produce either its executable self shell or a rule recovered from
the exact verifier-owned dispatch relation; both have ordinary `exec` shape,
not a reserved inert-row head. -/
theorem normalDispatchReload_additions_internal_closed
    {space : List Atom} (state : NormalVerifierInternalRowsIntact space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDispatchReloadDirective.atom ::
        space.erase normalDispatchReloadDirective.atom)
      normalDispatchReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalDispatchReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression [.symbol "32", .symbol "mm-normal-dispatch-reload"],
          .var "reload-self-input", .var "reload-self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-reload-normal-dispatch", .var "reload-proof"]),
     Sink.add (.var "reload-rule")] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression [.symbol "32", .symbol "mm-normal-dispatch-reload"],
              .var "reload-self-input", .var "reload-self-output"] : Atom) ∨
        authored = .var "reload-rule" := by
    simpa [normalDispatchReloadDirective] using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · rw [selfSink] at instantiates
    have atomShape :
        ∃ input output,
          atom =
            .expression
              [.symbol "exec",
                .expression
                  [.symbol "32", .symbol "mm-normal-dispatch-reload"],
                input, output] := by
      unfold instantiateTemplateAtom? at instantiates
      split at instantiates
      · have applied := Option.some.inj instantiates
        refine ⟨_, _, applied.symm⟩
      · simp at instantiates
    rcases atomShape with ⟨input, output, rfl⟩
    simp [isVerifierOwnedInternalRowShape,
      isVerifierOwnedInternalNamespace] at internalShape
  · rw [ruleSink] at instantiates
    have authorized : atom ∈ normalProofMachineRules :=
      normalDispatchReload_captured_rule_authorized_of_internal state rowMember
        instantiates
    have safe :=
      (List.all_eq_true.mp normalProofMachineRules_no_internal_row_shape)
        atom authorized
    have notInternal : isVerifierOwnedInternalRowShape atom = false := by
      simpa only [Bool.not_eq_true'] using safe
    rw [notInternal] at internalShape
    contradiction

/-- The selected dispatch-reload transition satisfies the complete local
owned-addition obligation, with no separately supplied authorization witness. -/
theorem normalDispatchReload_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDispatchReloadDirective.atom ::
        space.erase normalDispatchReloadDirective.atom)
      normalDispatchReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalDispatchReloadDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalDispatchReloadDirective.rule.tmpl := by
  exact ⟨normalDispatchReload_additions_raw_closed state,
    normalDispatchReload_additions_internal_closed state.2⟩

/-- Firing the actual dispatch reloader preserves the full owned normal-proof
machine invariant for an arbitrary represented space. -/
theorem NormalProofMachineOwnedState.fire_dispatchReload
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space normalDispatchReloadDirective) := by
  rcases normalDispatchReload_owned_additions_closed state with
    ⟨rawClosed, internalClosed⟩
  exact state.fire normalDispatchReloadDirective
    (by
      change normalDispatchReloadDirective ∈
        normalProofMachineRules.filterMap extractSupportedSourceExecFact
      exact List.mem_filterMap.mpr
        ⟨normalDispatchReloadRule,
          by simp [normalProofMachineRules],
          extract_normalDispatchReloadRule_exact⟩)
    rawClosed internalClosed

/-! ## Persistent self-reinstalling rule shells -/

/-- Every persistent normal-machine shell has the same outer representation.
The priority and rule name are literals; only the parsed input and output bytes
are captured and re-emitted. -/
private def normalPersistentSelfTemplate (priority name : String) : Atom :=
  reloadSelfTemplate priority name "self-input" "self-output"

/-- The executable result of a persistent self template is the concrete shell
that supplied the first matcher witness.  Thus it is either the selected
authored directive itself or executable code already authorized in the prior
owned state. -/
private theorem normalPersistent_captured_self_raw_authorized
    {space : List Atom} {substitution : Subst} {captured : Atom}
    {raw : RawExecFact} {priority name : String}
    {directive : SourceExecFact} {rest : List Atom}
    (state : NormalProofMachineExecutionContext space)
    (locationMember :
      (.expression [.symbol priority, .symbol name] : Atom) ∈
        normalProofMachineRawFacts.map RawExecFact.loc)
    (directiveMember : directive.atom ∈ normalProofMachineRules)
    (inputExact : directive.rule.input =
      .compat (mkPattern
        (normalPersistentSelfTemplate priority name :: rest)))
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (directive.atom :: space.erase directive.atom)
        directive.rule.input).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution
      (normalPersistentSelfTemplate priority name) = some captured)
    (extracts : extractRawExecFact captured = some raw) :
    raw ∈ normalProofMachineRawFacts := by
  rw [inputExact] at rowMember
  exact normal_shell_readback_authorized state directiveMember locationMember
    List.mem_cons_self rowMember instantiates extracts

/-! ## Persistent hypothesis-step self shell -/

/-- A persistent rule may republish its own checked input shell. All
other addition templates must preserve both ownership observations as data. -/
private theorem normal_persistent_owned_additions
    {space : List Atom} {priority name : String} {directive : SourceExecFact}
    (state : NormalProofMachineExecutionContext space)
    (locationMember : (.expression [.symbol priority, .symbol name] : Atom) ∈
      normalProofMachineRawFacts.map RawExecFact.loc)
    (directiveMember : directive.atom ∈ normalProofMachineRules)
    (firstFactor : ∃ rest, directive.rule.input =
      .compat (mkPattern (normalPersistentSelfTemplate priority name :: rest)))
    (checked : directive.rule.tmpl.sinks.all
      (normalOwnedAdmissionSink (· == normalPersistentSelfTemplate priority name)) = true) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (directive.atom :: space.erase directive.atom) directive.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows directive.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows directive.rule.tmpl := by
  obtain ⟨_, inputExact⟩ := firstFactor
  apply normal_owned_additions_of_sink_admission _ checked
  intro authored atom row accepted produced materialized
  have equal := beq_iff_eq.mp accepted
  subst authored
  exact ⟨fun _ extracts => normalPersistent_captured_self_raw_authorized state locationMember directiveMember
    inputExact produced materialized extracts,
    reloadShell_intact materialized⟩

example : normalOwnedAdmissionSink
    (· == normalPersistentSelfTemplate "00" "mm-normal-hypothesis-step")
    (.add (.var "unclassified")) = false := by decide +kernel

example : normalOwnedAdmissionSink
    (· == normalPersistentSelfTemplate "00" "mm-normal-hypothesis-step")
    (.add (normalPersistentSelfTemplate "00" "mm-normal-hypothesis-step")) = true :=
  by decide +kernel

theorem normalHypothesis_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalHypothesisDirective.atom ::
        space.erase normalHypothesisDirective.atom)
      normalHypothesisDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalHypothesisDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalHypothesisDirective.rule.tmpl :=
  normal_persistent_owned_additions (priority := "00") (name := "mm-normal-hypothesis-step")
    state (by decide +kernel)
    (by
      simp [normalHypothesisDirective, normalProofMachineRules])
    ⟨_, rfl⟩ (by decide +kernel)

/-- Hypothesis-step additions preserve the executable whitelist: its only
executable output is the exact persistent self shell. -/
theorem normalHypothesis_additions_raw_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalHypothesisDirective.atom ::
        space.erase normalHypothesisDirective.atom)
      normalHypothesisDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalHypothesisDirective.rule.tmpl :=
  (normalHypothesis_owned_additions_closed state).1

theorem normalHypothesis_additions_internal_closed
    {space : List Atom} (_state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalHypothesisDirective.atom ::
        space.erase normalHypothesisDirective.atom)
      normalHypothesisDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalHypothesisDirective.rule.tmpl :=
  (normalHypothesis_owned_additions_closed _state).2

theorem NormalProofMachineOwnedState.fire_hypothesis
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space normalHypothesisDirective) := by
  rcases normalHypothesis_owned_additions_closed
      (NormalProofMachineOwnedState.executionContext state) with
    ⟨rawClosed, internalClosed⟩
  exact state.fire normalHypothesisDirective
    (by
      change normalHypothesisDirective ∈
        normalProofMachineRules.filterMap extractSupportedSourceExecFact
      exact List.mem_filterMap.mpr
        ⟨normalHypothesisStepRule,
          by simp [normalProofMachineRules],
          extract_normalHypothesisStepRule_exact⟩)
    rawClosed internalClosed

/-! ## Persistent assertion-pop self shell -/

theorem normalAssertionPop_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalAssertionPopDirective.atom ::
        space.erase normalAssertionPopDirective.atom)
      normalAssertionPopDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalAssertionPopDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalAssertionPopDirective.rule.tmpl :=
  normal_persistent_owned_additions (priority := "02") (name := "mm-normal-assertion-pop")
    state (by decide +kernel)
    (by
      change normalAssertionPopRule ∈ normalProofMachineRules
      simp [normalProofMachineRules])
    ⟨_, rfl⟩ (by decide +kernel)

/-- Assertion-pop additions preserve the executable whitelist.  The only
executable addition is reconstructed from the exact first self-shell witness;
the updated pop cursor is data. -/
theorem normalAssertionPop_additions_raw_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalAssertionPopDirective.atom ::
        space.erase normalAssertionPopDirective.atom)
      normalAssertionPopDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalAssertionPopDirective.rule.tmpl :=
  (normalAssertionPop_owned_additions_closed state).1

theorem normalAssertionPop_additions_internal_closed
    {space : List Atom} (_state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalAssertionPopDirective.atom ::
        space.erase normalAssertionPopDirective.atom)
      normalAssertionPopDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalAssertionPopDirective.rule.tmpl :=
  (normalAssertionPop_owned_additions_closed _state).2

theorem NormalProofMachineOwnedState.fire_assertionPop
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space normalAssertionPopDirective) := by
  rcases normalAssertionPop_owned_additions_closed
      (NormalProofMachineOwnedState.executionContext state) with
    ⟨rawClosed, internalClosed⟩
  exact state.fire normalAssertionPopDirective
    (by
      change normalAssertionPopDirective ∈
        normalProofMachineRules.filterMap extractSupportedSourceExecFact
      exact List.mem_filterMap.mpr
        ⟨normalAssertionPopRule,
          by simp [normalProofMachineRules],
          extract_normalAssertionPopRule_exact⟩)
    rawClosed internalClosed

/-! ## Persistent floating-hypothesis self shell -/

theorem normalAssertionFloating_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalAssertionFloatingDirective.atom ::
        space.erase normalAssertionFloatingDirective.atom)
      normalAssertionFloatingDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalAssertionFloatingDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalAssertionFloatingDirective.rule.tmpl :=
  normal_persistent_owned_additions (priority := "04") (name := "mm-normal-assertion-floating")
    state (by decide +kernel)
    (by
      change normalAssertionFloatingRule ∈ normalProofMachineRules
      simp [normalProofMachineRules])
    ⟨_, rfl⟩ (by decide +kernel)

/-- Floating-hypothesis additions preserve the executable whitelist.  Its
substitution and child rows are data; the self shell is reconstructed from the
exact first matcher witness. -/
theorem normalAssertionFloating_additions_raw_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalAssertionFloatingDirective.atom ::
        space.erase normalAssertionFloatingDirective.atom)
      normalAssertionFloatingDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalAssertionFloatingDirective.rule.tmpl :=
  (normalAssertionFloating_owned_additions_closed state).1

theorem normalAssertionFloating_additions_internal_closed
    {space : List Atom} (_state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalAssertionFloatingDirective.atom ::
        space.erase normalAssertionFloatingDirective.atom)
      normalAssertionFloatingDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalAssertionFloatingDirective.rule.tmpl :=
  (normalAssertionFloating_owned_additions_closed _state).2

theorem NormalProofMachineOwnedState.fire_assertionFloating
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space
        normalAssertionFloatingDirective) := by
  rcases normalAssertionFloating_owned_additions_closed
      (NormalProofMachineOwnedState.executionContext state) with
    ⟨rawClosed, internalClosed⟩
  exact state.fire normalAssertionFloatingDirective
    (by
      change normalAssertionFloatingDirective ∈
        normalProofMachineRules.filterMap extractSupportedSourceExecFact
      exact List.mem_filterMap.mpr
        ⟨normalAssertionFloatingRule,
          by simp [normalProofMachineRules],
          extract_normalAssertionFloatingRule_exact⟩)
    rawClosed internalClosed

/-! ## Captured continuation publication -/

private def normalBodyMatchNilCarrierPattern : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .expression [.symbol "mm-nil"], .expression [.symbol "mm-nil"],
      .var "continuation"]

/-- Matching the final body cell exposes the continuation as a value selected
from the concrete carrier.  The theorem neither trusts nor classifies that
value; its authority is supplied separately by the source-relative state. -/
private theorem matchAtom_normalBodyMatchNil_captures_continuation
    {result : Subst} {atom : Atom}
    (matched : Conformance.Computable.cmatchAtom []
      normalBodyMatchNilCarrierPattern atom = some result) :
    ∃ continuation,
      Subst.lookup result "continuation" = some continuation ∧
        NormalBodyContinuationCapture atom continuation := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tail1 =>
      cases headMatched
      cases tail1 with
      | expr_cons proofMatched tail2 =>
          cases tail2 with
          | expr_cons positionMatched tail3 =>
              cases tail3 with
              | expr_cons sourceMatched tail4 =>
                  cases sourceMatched with
                  | expr_cons sourceHead sourceTail =>
                      cases sourceHead
                      cases sourceTail
                      cases tail4 with
                      | expr_cons actualMatched tail5 =>
                          cases actualMatched with
                          | expr_cons actualHead actualTail =>
                              cases actualHead
                              cases actualTail
                              cases tail5 with
                              | expr_cons continuationMatched finalTail =>
                                  cases finalTail
                                  cases continuationMatched with
                                  | var_fresh lookup =>
                                      refine ⟨_, ?_, .bodyMatch _ _ _ _ _⟩
                                      simp [Subst.lookup]
                                  | var_bound lookup =>
                                      exact ⟨_, lookup,
                                        .bodyMatch _ _ _ _ _⟩

/-- The value instantiated by the continuation sink comes from a concrete
body-match carrier in the pre-state, never from the sink template itself. -/
private theorem normalBodyMatchNil_continuation_origin
    {space : List Atom} {substitution : Subst} {continuation : Atom}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyMatchNilDirective.atom ::
          space.erase normalBodyMatchNilDirective.atom)
        normalBodyMatchNilDirective.rule.input).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution
      (.var "continuation") = some continuation) :
    ∃ carrier ∈ space,
      NormalBodyContinuationCapture carrier continuation := by
  have rowMember' : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyMatchNilDirective.atom ::
          space.erase normalBodyMatchNilDirective.atom)
        (.compat (mkPattern [normalBodyMatchNilCarrierPattern]))).map
          Prod.fst := by
    change substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyMatchNilDirective.atom ::
          space.erase normalBodyMatchNilDirective.atom)
        (.compat (mkPattern [normalBodyMatchNilCarrierPattern]))).map
          Prod.fst at rowMember
    exact rowMember
  obtain ⟨carrier, captured, carrierMember, capturedLookup,
      capture⟩ :=
    Conformance.Computable.cmatchInputSpec_first_capture_origin
      NormalBodyContinuationCapture "continuation" rowMember'
      matchAtom_normalBodyMatchNil_captures_continuation
  have continuationLookup :
      Subst.lookup substitution "continuation" = some continuation :=
    (instantiateTemplateAtom?_var_eq_some_iff substitution "continuation"
      continuation).1 instantiates
  have capturedEq : captured = continuation :=
    Option.some.inj (capturedLookup.symm.trans continuationLookup)
  subst captured
  rcases List.mem_cons.mp carrierMember with selected | prior
  · cases capture with
    | bodyMatch proof position sourceBody actualBody continuation =>
        simp [normalBodyMatchNilDirective, normalBodyMatchNilRule] at selected
    | bodyPrefix proof position replacementBody actualBody sourceTail
        continuation =>
        simp [normalBodyMatchNilDirective, normalBodyMatchNilRule] at selected
  · exact ⟨carrier, List.mem_of_mem_erase prior, capture⟩

private theorem normalBodyMatchNil_owned_additions_closed
    {space : List Atom} (state : NormalBodyContinuationCapabilities space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyMatchNilDirective.atom :: space.erase normalBodyMatchNilDirective.atom)
      normalBodyMatchNilDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows normalBodyMatchNilDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalBodyMatchNilDirective.rule.tmpl := by
  apply normal_owned_additions_of_sink_admission (· == (.var "continuation" : Atom))
  · decide +kernel
  · intro authored atom row allowed produced instantiates
    have same := beq_iff_eq.mp allowed
    subst authored
    obtain ⟨carrier, member, capture⟩ := normalBodyMatchNil_continuation_origin produced instantiates
    exact state carrier member atom capture

theorem normalBodyMatchNil_additions_raw_closed
    {space : List Atom}
    (state : NormalBodyContinuationCapabilities space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyMatchNilDirective.atom ::
        space.erase normalBodyMatchNilDirective.atom)
      normalBodyMatchNilDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalBodyMatchNilDirective.rule.tmpl :=
  (normalBodyMatchNil_owned_additions_closed state).1

theorem normalBodyMatchNil_additions_internal_closed
    {space : List Atom}
    (state : NormalBodyContinuationCapabilities space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyMatchNilDirective.atom ::
        space.erase normalBodyMatchNilDirective.atom)
      normalBodyMatchNilDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalBodyMatchNilDirective.rule.tmpl :=
  (normalBodyMatchNil_owned_additions_closed state).2

theorem NormalProofMachineCapabilityState.fire_bodyMatchNil_owned
    {space : List Atom} (state : NormalProofMachineCapabilityState space) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space normalBodyMatchNilDirective) := by
  exact state.1.fire normalBodyMatchNilDirective
    (by
      exact List.mem_filterMap.mpr
        ⟨normalBodyMatchNilRule, by simp [normalProofMachineRules],
          extract_normalBodyMatchNilRule_exact⟩)
    (normalBodyMatchNil_additions_raw_closed state.2)
    (normalBodyMatchNil_additions_internal_closed state.2)

/-! ## Complete normal-machine ownership classification -/

/-- Every authored normal-machine directive is either one of the explicitly
audited executable-output cases or has a syntactically data-only output
template.  This finite classification is computed from the parsed target
artifact. -/
private def normalProofMachineDirectiveOwnedClassified
    (directive : SourceExecFact) : Bool :=
  decide (directive = normalBodyReloadDirective) ||
    decide (directive = normalDVReloadDirective) ||
    decide (directive = normalBodyBuildReloadDirective) ||
    decide (directive = normalDispatchReloadDirective) ||
    decide (directive = normalHypothesisDirective) ||
    decide (directive = normalAssertionPopDirective) ||
    decide (directive = normalAssertionFloatingDirective) ||
    decide (directive = normalBodyMatchNilDirective) ||
    directive.rule.tmpl.sinks.all normalOwnedSafeSink

private theorem normalProofMachineDirectives_all_ownedClassified :
    normalProofMachineDirectives.all
      normalProofMachineDirectiveOwnedClassified = true := by
  decide +kernel

theorem normalProofMachineDirective_owned_classification
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    directive = normalBodyReloadDirective ∨
      directive = normalDVReloadDirective ∨
      directive = normalBodyBuildReloadDirective ∨
      directive = normalDispatchReloadDirective ∨
      directive = normalHypothesisDirective ∨
      directive = normalAssertionPopDirective ∨
      directive = normalAssertionFloatingDirective ∨
      directive = normalBodyMatchNilDirective ∨
      NormalOwnedSafeTemplate directive.rule.tmpl := by
  have checked :=
    (List.all_eq_true.mp normalProofMachineDirectives_all_ownedClassified)
      directive member
  simp only [normalProofMachineDirectiveOwnedClassified,
    Bool.or_eq_true, decide_eq_true_eq] at checked
  unfold NormalOwnedSafeTemplate
  aesop

/-- Every normal-machine directive except the continuation-publishing
body-match completion preserves source-relative verifier ownership.  This
theorem turns the finite parser-level classification into the global closure
boundary; no per-fixture scheduler state is involved. -/
theorem NormalProofMachineOwnedState.fire_of_ne_bodyMatchNil
    {space : List Atom} (state : NormalProofMachineOwnedState space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives)
    (notBodyMatchNil : directive ≠ normalBodyMatchNilDirective) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space directive) := by
  rcases normalProofMachineDirective_owned_classification member with
    bodyReload | dvReload | bodyBuildReload | dispatchReload | hypothesis |
      assertionPop | assertionFloating | bodyMatchNil | safe
  · subst directive
    exact NormalProofMachineOwnedState.fire_bodyReload state
  · subst directive
    exact NormalProofMachineOwnedState.fire_dvReload state
  · subst directive
    exact NormalProofMachineOwnedState.fire_bodyBuildReload state
  · subst directive
    exact NormalProofMachineOwnedState.fire_dispatchReload state
  · subst directive
    exact NormalProofMachineOwnedState.fire_hypothesis state
  · subst directive
    exact NormalProofMachineOwnedState.fire_assertionPop state
  · subst directive
    exact NormalProofMachineOwnedState.fire_assertionFloating state
  · exact False.elim (notBodyMatchNil bodyMatchNil)
  · exact state.fire directive member
      (normalOwnedSafeTemplate_raw_closed _ _ safe)
      (normalOwnedSafeTemplate_internal_closed _ _ safe)

/-- Every parsed normal verifier directive preserves ownership from the
strong source-relative capability state.  This closes the formerly excluded
body-match completion without claiming arbitrary hostile carriers are safe. -/
theorem NormalProofMachineCapabilityState.fire_owned
    {space : List Atom} (state : NormalProofMachineCapabilityState space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space directive) := by
  by_cases bodyMatchNil : directive = normalBodyMatchNilDirective
  · subst directive
    exact state.fire_bodyMatchNil_owned
  · exact NormalProofMachineOwnedState.fire_of_ne_bodyMatchNil
      state.1 member bodyMatchNil

/-! ## Negative control -/

private def protectedCarrier : Atom :=
  .expression
    [.symbol "mm-internal-normal-dispatch-rule", .symbol "forged"]

/-- The protected-row conclusion is substantive: the reserved inert carrier
shape is recognized and therefore cannot be discharged by the executable-head
argument used for legitimate reload additions. -/
theorem protectedCarrier_is_internal :
    isVerifierOwnedInternalRowShape protectedCarrier = true := by
  rfl

private def forgedContinuationExec : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "999", .symbol "forged-continuation"],
      .expression [.symbol ","], .expression [.symbol "O"]]

private def forgedContinuationRaw : RawExecFact where
  atom := forgedContinuationExec
  loc := .expression [.symbol "999", .symbol "forged-continuation"]
  inputExpr := .expression [.symbol ","]
  templateExpr := .expression [.symbol "O"]

private def forgedContinuationCarrier : Atom :=
  .expression
    [.symbol "mm-body-match", .symbol "proof", .symbol "pc",
      .expression [.symbol "mm-nil"], .expression [.symbol "mm-nil"],
      forgedContinuationExec]

/-- Merely placing executable text in a syntactically valid body carrier does
not establish the source-relative capability state. -/
theorem forged_body_match_continuation_rejected :
    ¬ NormalBodyContinuationCapabilities [forgedContinuationCarrier] := by
  intro within
  have authorized := within forgedContinuationCarrier (by simp)
    forgedContinuationExec
    (NormalBodyContinuationCapture.bodyMatch _ _ _ _ _)
  have extracted : extractRawExecFact forgedContinuationExec =
      some forgedContinuationRaw := by
    rfl
  have notAuthorized : forgedContinuationRaw ∉ normalProofMachineRawFacts := by
    decide +kernel
  exact notAuthorized (authorized.1 forgedContinuationRaw extracted)

#print axioms normalDispatchReload_additions_internal_closed
#print axioms normalProofMachineRawFacts_subset_authoredNormalVerifier
#print axioms authoredNormalVerifierRawFacts_loc_injective
#print axioms authoredNormalVerifierRawFact_mem_normal_of_loc_mem
#print axioms NormalProofMachineOwnedState.executionContext
#print axioms normalDispatchReload_owned_additions_closed
#print axioms NormalProofMachineOwnedState.fire_dispatchReload
#print axioms normalOwnedSafeTemplate_raw_closed
#print axioms normalOwnedSafeTemplate_internal_closed
#print axioms normalHypothesis_additions_raw_closed
#print axioms normalHypothesis_additions_internal_closed
#print axioms normalHypothesis_owned_additions_closed
#print axioms NormalProofMachineOwnedState.fire_hypothesis
#print axioms normalAssertionPop_owned_additions_closed
#print axioms NormalProofMachineOwnedState.fire_assertionPop
#print axioms normalAssertionFloating_owned_additions_closed
#print axioms NormalProofMachineOwnedState.fire_assertionFloating
#print axioms normalBodyReload_additions_raw_closed
#print axioms normalBodyReload_captured_rule_authorized
#print axioms normalBodyReload_additions_internal_closed
#print axioms normalBodyReload_owned_additions_closed
#print axioms NormalProofMachineOwnedState.fire_bodyReload
#print axioms normalBodyBuildReload_additions_raw_closed
#print axioms normalBodyBuildReload_captured_rule_authorized
#print axioms normalBodyBuildReload_additions_internal_closed
#print axioms normalBodyBuildReload_owned_additions_closed
#print axioms NormalProofMachineOwnedState.fire_bodyBuildReload
#print axioms normalDVReload_additions_raw_closed
#print axioms normalDVReload_captured_rule_authorized
#print axioms normalDVReload_additions_internal_closed
#print axioms normalDVReload_owned_additions_closed
#print axioms NormalProofMachineOwnedState.fire_dvReload
#print axioms normalProofMachineDirective_owned_classification
#print axioms NormalProofMachineOwnedState.fire_of_ne_bodyMatchNil
#print axioms normalBodyMatchNil_additions_raw_closed
#print axioms normalBodyMatchNil_additions_internal_closed
#print axioms NormalProofMachineCapabilityState.fire_bodyMatchNil_owned
#print axioms NormalProofMachineCapabilityState.fire_owned
#print axioms forged_body_match_continuation_rejected
#print axioms protectedCarrier_is_internal

end Mettapedia.Languages.Metamath.MM2NormalProofOwnedClosure
