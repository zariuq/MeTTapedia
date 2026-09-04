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

/-- A syntactically data-only target template cannot introduce executable
code, independently of which matcher substitutions were produced. -/
theorem normalOwnedSafeTemplate_raw_closed
    (rows : List Subst) (template : Template)
    (safe : NormalOwnedSafeTemplate template) :
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows template := by
  intro atom added raw extracts
  rcases added with
    ⟨sink, sinkMember, authored, rfl,
      substitution, _rowMember, instantiates⟩
  have safeSink := (List.all_eq_true.mp safe) (.add authored) sinkMember
  have safeAuthored : normalOwnedSafeTemplateAtom authored = true := by
    simpa using safeSink
  have instantiated : applySubst substitution authored = atom := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · exact Option.some.inj instantiates
    · simp at instantiates
  rw [← instantiated] at extracts
  rw [normalOwnedSafeTemplateAtom_raw_none substitution authored safeAuthored]
    at extracts
  contradiction

/-- The same data-only template cannot introduce a protected inert carrier. -/
theorem normalOwnedSafeTemplate_internal_closed
    (rows : List Subst) (template : Template)
    (safe : NormalOwnedSafeTemplate template) :
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      template := by
  intro atom added
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rcases added with
    ⟨sink, sinkMember, authored, rfl,
      substitution, _rowMember, instantiates⟩
  have safeSink := (List.all_eq_true.mp safe) (.add authored) sinkMember
  have safeAuthored : normalOwnedSafeTemplateAtom authored = true := by
    simpa using safeSink
  have instantiated : applySubst substitution authored = atom := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · exact Option.some.inj instantiates
    · simp at instantiates
  rw [← instantiated] at internalShape
  rw [normalOwnedSafeTemplateAtom_internal_false substitution authored
    safeAuthored] at internalShape
  contradiction

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

/-- The final row of an arbitrary nonempty compatible matcher retains the
first concrete witness and extends the substitution produced by matching it.
This is the reusable origin lemma for persistent self-reinstalling rules. -/
private theorem cmatchInputSpec_first_match_chain
    {space : List Atom} {first : Atom} {rest : List Atom}
    {substitution : Subst}
    (member : substitution ∈
      (Conformance.Computable.cmatchInputSpec [] space
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
  simp only [Conformance.Computable.cmatchInputSpec, mkPattern,
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

/-- A successful three-factor compatible match retains the three concrete
witness atoms and the exact substitution chain that produced the final row. -/
private theorem cmatchInputSpec_three_match_chain
    {space : List Atom} {first second third : Atom}
    {substitution : Subst}
    (member : substitution ∈
      (Conformance.Computable.cmatchInputSpec [] space
        (.compat (mkPattern [first, second, third]))).map Prod.fst) :
    ∃ afterFirst afterSecond firstAtom secondAtom thirdAtom,
      firstAtom ∈ space ∧ secondAtom ∈ space ∧ thirdAtom ∈ space ∧
        Conformance.Computable.cmatchAtom [] first firstAtom =
          some afterFirst ∧
        Conformance.Computable.cmatchAtom afterFirst second secondAtom =
          some afterSecond ∧
        Conformance.Computable.cmatchAtom afterSecond third thirdAtom =
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
    afterSecondMember⟩ := afterFirstMember
  obtain ⟨⟨afterThird, thirdAtom⟩, thirdMatch,
    finished⟩ := afterSecondMember
  simp only [List.mem_singleton, Prod.mk.injEq] at finished
  rcases finished with ⟨substEq, _witnessEq⟩
  subst afterThird
  rw [List.mem_filterMap] at firstMatch secondMatch thirdMatch
  obtain ⟨firstCandidate, firstMember, firstResult⟩ := firstMatch
  obtain ⟨secondCandidate, secondMember, secondResult⟩ := secondMatch
  obtain ⟨thirdCandidate, thirdMember, thirdResult⟩ := thirdMatch
  simp only [Option.map_eq_some_iff] at firstResult secondResult thirdResult
  obtain ⟨firstSubst, firstMatched, firstEq⟩ := firstResult
  obtain ⟨secondSubst, secondMatched, secondEq⟩ := secondResult
  obtain ⟨thirdSubst, thirdMatched, thirdEq⟩ := thirdResult
  cases firstEq
  cases secondEq
  cases thirdEq
  exact ⟨afterFirst, afterSecond, firstAtom, secondAtom, thirdAtom,
    firstMember, secondMember, thirdMember,
    firstMatched, secondMatched, thirdMatched⟩

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

/-- A variable at an aligned list position is bound to the concrete atom at
that position in the final matcher substitution, even after the suffix has
introduced further bindings. -/
private theorem matchAtomList_variable_lookup
    (prefixPatterns prefixAtoms suffixPatterns suffixAtoms : List Atom)
    (initial final : Subst) (variableName : String) (value : Atom)
    (prefixLength : prefixPatterns.length = prefixAtoms.length)
    (matched :
      matchAtom.matchAtomList initial
          (prefixPatterns ++ .var variableName :: suffixPatterns)
          (prefixAtoms ++ value :: suffixAtoms) = some final) :
    final.lookup variableName = some value := by
  induction prefixPatterns generalizing prefixAtoms initial with
  | nil =>
      cases prefixAtoms with
      | nil =>
          simp only [List.nil_append, matchAtom.matchAtomList] at matched
          cases variableMatched : matchAtom initial (.var variableName) value with
          | none => simp [variableMatched] at matched
          | some afterVariable =>
              simp only [variableMatched] at matched
              have bound : afterVariable.lookup variableName = some value := by
                have relation := matchAtom_sound variableMatched
                cases relation with
                | var_fresh _ => simp [Subst.lookup]
                | var_bound lookup => exact lookup
              exact
                (matchAtom_lookupExtends.matchAtomList_lookupExtends matched)
                  variableName value bound
      | cons atom atoms =>
          simp at prefixLength
  | cons pattern patterns induction =>
      cases prefixAtoms with
      | nil => simp at prefixLength
      | cons atom atoms =>
          simp only [List.length_cons, Nat.succ.injEq] at prefixLength
          simp only [List.cons_append, matchAtom.matchAtomList] at matched
          cases headMatched : matchAtom initial pattern atom with
          | none => simp [headMatched] at matched
          | some afterHead =>
              simp only [headMatched] at matched
              exact induction atoms afterHead prefixLength matched

/-- The body reloader's self pattern can only match an executable shell at
its exact scheduler location, while retaining the two opaque byte fields. -/
private theorem matchAtom_bodyReload_self
    {result : Subst} {atom : Atom}
    (matched : matchAtom []
      (.expression
        [.symbol "exec",
          .expression [.symbol "11", .symbol "mm-normal-body-reload"],
          .var "body-reload-self-input",
          .var "body-reload-self-output"]) atom = some result) :
    ∃ input output,
      atom =
          .expression
            [.symbol "exec",
              .expression [.symbol "11", .symbol "mm-normal-body-reload"],
              input, output] ∧
        result.lookup "body-reload-self-input" = some input ∧
        result.lookup "body-reload-self-output" = some output := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons execMatch tail1 =>
      cases execMatch
      cases tail1 with
      | expr_cons locationMatch tail2 =>
          cases locationMatch with
          | expr_cons locationHead locationTail =>
              cases locationHead
              cases locationTail with
              | expr_cons locationName locationNil =>
                  cases locationName
                  cases locationNil
                  cases tail2 with
                  | expr_cons inputMatch tail3 =>
                      cases inputMatch with
                      | var_fresh _ =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  refine ⟨_, _, rfl, ?_, ?_⟩
                                  · simp [Subst.lookup]
                                  · simp [Subst.lookup]
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl,
                                    by simp [Subst.lookup], outputLookup⟩
                      | var_bound inputLookup =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    by simp [Subst.lookup]⟩
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    outputLookup⟩

/-- A successful body-bundle match fixes the complete six-cell carrier
shape.  The five payload atoms are still opaque at this point. -/
private theorem matchAtom_bodyReload_bundle_shape
    {before result : Subst} {atom : Atom}
    (matched : matchAtom before
      (.expression
        [.symbol "mm-internal-body-match-rules",
          .var "body-rule-const", .var "body-rule-variable",
          .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
          .var "body-rule-nil"]) atom = some result) :
    ∃ constRule variableRule prefixNilRule prefixConsRule nilRule,
      atom =
        .expression
          [.symbol "mm-internal-body-match-rules", constRule, variableRule,
            prefixNilRule, prefixConsRule, nilRule] := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatch tail1 =>
      cases headMatch
      cases tail1 with
      | expr_cons _ tail2 =>
          cases tail2 with
          | expr_cons _ tail3 =>
              cases tail3 with
              | expr_cons _ tail4 =>
                  cases tail4 with
                  | expr_cons _ tail5 =>
                      cases tail5 with
                      | expr_cons _ nilMatch =>
                          cases nilMatch
                          exact ⟨_, _, _, _, _, rfl⟩

/-- In an owned machine state, the body reloader's third matcher witness is
the one exact generated body-rule bundle.  A same-shaped row with altered
payloads is not authorized merely by its head symbol. -/
private theorem normalBodyReload_bundle_witness_exact
    {space : List Atom} (state : NormalProofMachineExecutionContext space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        normalBodyReloadDirective.rule.input).map Prod.fst) :
    ∃ afterFirst afterSecond firstAtom secondAtom,
      firstAtom ∈
          (normalBodyReloadDirective.atom ::
            space.erase normalBodyReloadDirective.atom) ∧
        secondAtom ∈
          (normalBodyReloadDirective.atom ::
            space.erase normalBodyReloadDirective.atom) ∧
        Conformance.Computable.cmatchAtom []
            (.expression
              [.symbol "exec",
                .expression
                  [.symbol "11", .symbol "mm-normal-body-reload"],
                .var "body-reload-self-input",
                .var "body-reload-self-output"])
            firstAtom = some afterFirst ∧
        Conformance.Computable.cmatchAtom afterFirst
            (.expression
              [.symbol "mm-reload-body-match",
                .var "body-reload-proof", .var "body-reload-pc"])
            secondAtom = some afterSecond ∧
        Conformance.Computable.cmatchAtom afterSecond
            (.expression
              [.symbol "mm-internal-body-match-rules",
                .var "body-rule-const", .var "body-rule-variable",
                .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
                .var "body-rule-nil"])
            normalBodyMatchRuleBundle = some substitution := by
  have rowMember' : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        (.compat (mkPattern
          [(.expression
              [.symbol "exec",
                .expression
                  [.symbol "11", .symbol "mm-normal-body-reload"],
                .var "body-reload-self-input",
                .var "body-reload-self-output"] : Atom),
           .expression
              [.symbol "mm-reload-body-match",
                .var "body-reload-proof", .var "body-reload-pc"],
           .expression
              [.symbol "mm-internal-body-match-rules",
                .var "body-rule-const", .var "body-rule-variable",
                .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
                .var "body-rule-nil"]]))).map Prod.fst := by
    change substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        normalBodyReloadDirective.rule.input).map Prod.fst
    exact rowMember
  obtain ⟨afterFirst, afterSecond, firstAtom, secondAtom, thirdAtom,
      firstMember, secondMember, thirdMember,
      firstMatched, secondMatched, thirdMatched⟩ :=
    cmatchInputSpec_three_match_chain rowMember'
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  obtain ⟨constRule, variableRule, prefixNilRule, prefixConsRule,
      nilRule, thirdEq⟩ :=
    matchAtom_bodyReload_bundle_shape thirdMatched
  have thirdInSpace : thirdAtom ∈ space := by
    rcases List.mem_cons.mp thirdMember with selected | erased
    · rw [thirdEq] at selected
      simp [normalBodyReloadDirective, normalBodyReloadRule] at selected
    · exact List.mem_of_mem_erase erased
  have authorized := state.2 thirdAtom thirdInSpace
  have internalShape : isVerifierOwnedInternalRowShape thirdAtom = true := by
    rw [thirdEq]
    rfl
  have authorizedMember := authorized internalShape
  have thirdExact : thirdAtom = normalBodyMatchRuleBundle := by
    rw [thirdEq] at authorizedMember
    simp [normalVerifierInternalRows, normalBodyMatchRuleBundle,
      normalDVRuleBundle, normalBodyBuildRuleBundle, normalDispatchRuleRows,
      normalDispatchRuleRow] at authorizedMember
    rcases authorizedMember with
      ⟨rfl, rfl, rfl, rfl, rfl⟩
    simpa [normalBodyMatchRuleBundle] using thirdEq
  rw [thirdExact] at thirdMatched
  rw [← Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  exact ⟨afterFirst, afterSecond, firstAtom, secondAtom,
    firstMember, secondMember, firstMatched, secondMatched, thirdMatched⟩

/-- Exact ownership of the body-rule carrier determines all five final
matcher bindings.  These equalities are the authorization facts consumed by
the variable-valued add sinks. -/
private theorem normalBodyReload_bundle_lookups
    {space : List Atom} (state : NormalProofMachineExecutionContext space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        normalBodyReloadDirective.rule.input).map Prod.fst) :
    substitution.lookup "body-rule-const" =
        some normalBodyMatchConstRule ∧
      substitution.lookup "body-rule-variable" =
        some normalBodyMatchVariableRule ∧
      substitution.lookup "body-rule-prefix-nil" =
        some normalBodyPrefixNilRule ∧
      substitution.lookup "body-rule-prefix-cons" =
        some normalBodyPrefixConsRule ∧
      substitution.lookup "body-rule-nil" =
        some normalBodyMatchNilRule := by
  obtain ⟨afterFirst, afterSecond, firstAtom, secondAtom,
      _firstMember, _secondMember, _firstMatched, _secondMatched,
      thirdMatched⟩ := normalBodyReload_bundle_witness_exact state rowMember
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  have listMatched :
      matchAtom.matchAtomList afterSecond
        [.symbol "mm-internal-body-match-rules",
          .var "body-rule-const", .var "body-rule-variable",
          .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
          .var "body-rule-nil"]
        [.symbol "mm-internal-body-match-rules",
          normalBodyMatchConstRule, normalBodyMatchVariableRule,
          normalBodyPrefixNilRule, normalBodyPrefixConsRule,
          normalBodyMatchNilRule] = some substitution := by
    simpa [normalBodyMatchRuleBundle, matchAtom] using thirdMatched
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-match-rules"]
      [.symbol "mm-internal-body-match-rules"]
      [.var "body-rule-variable", .var "body-rule-prefix-nil",
        .var "body-rule-prefix-cons", .var "body-rule-nil"]
      [normalBodyMatchVariableRule, normalBodyPrefixNilRule,
        normalBodyPrefixConsRule, normalBodyMatchNilRule]
      afterSecond substitution "body-rule-const" normalBodyMatchConstRule
      rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-match-rules", .var "body-rule-const"]
      [.symbol "mm-internal-body-match-rules", normalBodyMatchConstRule]
      [.var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
        .var "body-rule-nil"]
      [normalBodyPrefixNilRule, normalBodyPrefixConsRule,
        normalBodyMatchNilRule]
      afterSecond substitution "body-rule-variable"
      normalBodyMatchVariableRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-match-rules", .var "body-rule-const",
        .var "body-rule-variable"]
      [.symbol "mm-internal-body-match-rules", normalBodyMatchConstRule,
        normalBodyMatchVariableRule]
      [.var "body-rule-prefix-cons", .var "body-rule-nil"]
      [normalBodyPrefixConsRule, normalBodyMatchNilRule]
      afterSecond substitution "body-rule-prefix-nil"
      normalBodyPrefixNilRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-match-rules", .var "body-rule-const",
        .var "body-rule-variable", .var "body-rule-prefix-nil"]
      [.symbol "mm-internal-body-match-rules", normalBodyMatchConstRule,
        normalBodyMatchVariableRule, normalBodyPrefixNilRule]
      [.var "body-rule-nil"] [normalBodyMatchNilRule]
      afterSecond substitution "body-rule-prefix-cons"
      normalBodyPrefixConsRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-match-rules", .var "body-rule-const",
        .var "body-rule-variable", .var "body-rule-prefix-nil",
        .var "body-rule-prefix-cons"]
      [.symbol "mm-internal-body-match-rules", normalBodyMatchConstRule,
        normalBodyMatchVariableRule, normalBodyPrefixNilRule,
        normalBodyPrefixConsRule]
      [] [] afterSecond substitution "body-rule-nil"
      normalBodyMatchNilRule rfl listMatched

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
  obtain ⟨afterFirst, afterSecond, firstAtom, secondAtom,
      firstMember, _secondMember, firstMatched, secondMatched,
      thirdMatched⟩ := normalBodyReload_bundle_witness_exact state rowMember
  rw [Conformance.cmatchAtom_eq_matchAtom] at firstMatched secondMatched
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  obtain ⟨input, output, firstEq, inputLookup, outputLookup⟩ :=
    matchAtom_bodyReload_self firstMatched
  have finalExtends : substitution.lookupExtends afterFirst :=
    Subst.lookupExtends_trans
      (matchAtom_lookupExtends secondMatched)
      (matchAtom_lookupExtends thirdMatched)
  have finalInputLookup :
      substitution.lookup "body-reload-self-input" = some input :=
    finalExtends "body-reload-self-input" input inputLookup
  have finalOutputLookup :
      substitution.lookup "body-reload-self-output" = some output :=
    finalExtends "body-reload-self-output" output outputLookup
  have applied :
      applySubst substitution
          (.expression
            [.symbol "exec",
              .expression [.symbol "11", .symbol "mm-normal-body-reload"],
              .var "body-reload-self-input",
              .var "body-reload-self-output"]) = captured := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · exact Option.some.inj instantiates
    · simp at instantiates
  have appliedFirst :
      applySubst substitution
          (.expression
            [.symbol "exec",
              .expression [.symbol "11", .symbol "mm-normal-body-reload"],
              .var "body-reload-self-input",
              .var "body-reload-self-output"]) = firstAtom := by
    rw [firstEq]
    change
      Atom.expression
          [.symbol "exec",
            .expression [.symbol "11", .symbol "mm-normal-body-reload"],
            (substitution.lookup "body-reload-self-input").getD
              (.var "body-reload-self-input"),
            (substitution.lookup "body-reload-self-output").getD
              (.var "body-reload-self-output")] =
        Atom.expression
          [.symbol "exec",
            .expression [.symbol "11", .symbol "mm-normal-body-reload"],
            input, output]
    rw [finalInputLookup, finalOutputLookup]
    rfl
  have capturedEq : captured = firstAtom := applied.symm.trans appliedFirst
  rw [capturedEq] at extracts
  rcases List.mem_cons.mp firstMember with selected | prior
  · rw [selected] at extracts
    exact List.mem_filterMap.mpr
      ⟨normalBodyReloadDirective.atom,
        by simp [normalBodyReloadDirective, normalProofMachineRules],
        extracts⟩
  · apply authoredNormalVerifierRawFact_mem_normal_of_loc_mem
    · apply state.1 raw
      exact List.mem_filterMap.mpr
        ⟨firstAtom, List.mem_of_mem_erase prior, extracts⟩
    · rw [firstEq] at extracts
      simp only [extractRawExecFact] at extracts
      injection extracts with rawEqual
      subst raw
      change (.expression
        [.symbol "11", .symbol "mm-normal-body-reload"] : Atom) ∈
          normalProofMachineRawFacts.map RawExecFact.loc
      decide +kernel

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
  obtain ⟨constLookup, variableLookup, prefixNilLookup,
      prefixConsLookup, nilLookup⟩ :=
    normalBodyReload_bundle_lookups state rowMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at authoredMember
  rcases authoredMember with rfl | rfl | rfl | rfl | rfl
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      constLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      variableLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      prefixNilLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      prefixConsLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      nilLookup] at instantiates
    subst captured
    simp

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
      normalBodyReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added raw extracts
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression [.symbol "11", .symbol "mm-normal-body-reload"],
          .var "body-reload-self-input", .var "body-reload-self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-reload-body-match", .var "body-reload-proof",
          .var "body-reload-pc"]),
     Sink.add (.var "body-rule-const"),
     Sink.add (.var "body-rule-variable"),
     Sink.add (.var "body-rule-prefix-nil"),
     Sink.add (.var "body-rule-prefix-cons"),
     Sink.add (.var "body-rule-nil")] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression [.symbol "11", .symbol "mm-normal-body-reload"],
              .var "body-reload-self-input",
              .var "body-reload-self-output"] : Atom) ∨
        authored ∈
          [(.var "body-rule-const" : Atom), .var "body-rule-variable",
            .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
            .var "body-rule-nil"] := by
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · rw [selfSink] at instantiates
    exact normalBodyReload_captured_self_raw_authorized state rowMember
      instantiates extracts
  · have authorized :=
      normalBodyReload_captured_rule_authorized state rowMember ruleSink
        instantiates
    have machineMember : atom ∈ normalProofMachineRules := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at authorized
      rcases authorized with rfl | rfl | rfl | rfl | rfl <;>
        simp [normalProofMachineRules]
    exact List.mem_filterMap.mpr ⟨atom, machineMember, extracts⟩

/-- The same body-reload firing cannot create a reserved inert carrier: its
self shell and all five recovered payloads are executable verifier rules. -/
theorem normalBodyReload_additions_internal_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyReloadDirective.atom ::
        space.erase normalBodyReloadDirective.atom)
      normalBodyReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalBodyReloadDirective.rule.tmpl := by
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
          .expression [.symbol "11", .symbol "mm-normal-body-reload"],
          .var "body-reload-self-input", .var "body-reload-self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-reload-body-match", .var "body-reload-proof",
          .var "body-reload-pc"]),
     Sink.add (.var "body-rule-const"),
     Sink.add (.var "body-rule-variable"),
     Sink.add (.var "body-rule-prefix-nil"),
     Sink.add (.var "body-rule-prefix-cons"),
     Sink.add (.var "body-rule-nil")] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression [.symbol "11", .symbol "mm-normal-body-reload"],
              .var "body-reload-self-input",
              .var "body-reload-self-output"] : Atom) ∨
        authored ∈
          [(.var "body-rule-const" : Atom), .var "body-rule-variable",
            .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
            .var "body-rule-nil"] := by
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · rw [selfSink] at instantiates
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · have applied := Option.some.inj instantiates
      have atomShape :
          ∃ input output,
            atom =
              .expression
                [.symbol "exec",
                  .expression
                    [.symbol "11", .symbol "mm-normal-body-reload"],
                  input, output] :=
        ⟨_, _, applied.symm⟩
      rcases atomShape with ⟨input, output, rfl⟩
      simp [isVerifierOwnedInternalRowShape,
        isVerifierOwnedInternalNamespace] at internalShape
    · simp at instantiates
  · have authorized :=
      normalBodyReload_captured_rule_authorized state rowMember ruleSink
        instantiates
    have machineMember : atom ∈ normalProofMachineRules := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at authorized
      rcases authorized with rfl | rfl | rfl | rfl | rfl <;>
        simp [normalProofMachineRules]
    have safe :=
      (List.all_eq_true.mp normalProofMachineRules_no_internal_row_shape)
        atom machineMember
    have notInternal : isVerifierOwnedInternalRowShape atom = false := by
      simpa only [Bool.not_eq_true'] using safe
    rw [notInternal] at internalShape
    contradiction

/-- The body reloader satisfies the complete owned-addition obligation in
every represented space. -/
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
  exact ⟨normalBodyReload_additions_raw_closed state,
    normalBodyReload_additions_internal_closed state⟩

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

/-- The result-body builder reloader's executable self pattern fixes its
scheduler location and retains exactly its two opaque byte fields. -/
private theorem matchAtom_bodyBuildReload_self
    {result : Subst} {atom : Atom}
    (matched : matchAtom []
      (.expression
        [.symbol "exec",
          .expression [.symbol "30", .symbol "mm-normal-body-build-reload"],
          .var "build-reload-self-input",
          .var "build-reload-self-output"]) atom = some result) :
    ∃ input output,
      atom =
          .expression
            [.symbol "exec",
              .expression
                [.symbol "30", .symbol "mm-normal-body-build-reload"],
              input, output] ∧
        result.lookup "build-reload-self-input" = some input ∧
        result.lookup "build-reload-self-output" = some output := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons execMatch tail1 =>
      cases execMatch
      cases tail1 with
      | expr_cons locationMatch tail2 =>
          cases locationMatch with
          | expr_cons locationHead locationTail =>
              cases locationHead
              cases locationTail with
              | expr_cons locationName locationNil =>
                  cases locationName
                  cases locationNil
                  cases tail2 with
                  | expr_cons inputMatch tail3 =>
                      cases inputMatch with
                      | var_fresh _ =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  refine ⟨_, _, rfl, ?_, ?_⟩
                                  · simp [Subst.lookup]
                                  · simp [Subst.lookup]
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl,
                                    by simp [Subst.lookup], outputLookup⟩
                      | var_bound inputLookup =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    by simp [Subst.lookup]⟩
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    outputLookup⟩

/-- A successful body-builder carrier match fixes all seven payload cells.
The payload atoms remain opaque until ownership identifies the carrier. -/
private theorem matchAtom_bodyBuildReload_bundle_shape
    {before result : Subst} {atom : Atom}
    (matched : matchAtom before
      (.expression
        [.symbol "mm-internal-body-build-rules",
          .var "build-rule-const", .var "build-rule-variable",
          .var "build-rule-prefix-nil", .var "build-rule-prefix-cons",
          .var "build-rule-nil", .var "build-rule-reverse-cons",
          .var "build-rule-reverse-nil"]) atom = some result) :
    ∃ constRule variableRule prefixNilRule prefixConsRule nilRule
        reverseConsRule reverseNilRule,
      atom =
        .expression
          [.symbol "mm-internal-body-build-rules", constRule, variableRule,
            prefixNilRule, prefixConsRule, nilRule, reverseConsRule,
            reverseNilRule] := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatch tail1 =>
      cases headMatch
      cases tail1 with
      | expr_cons _ tail2 =>
          cases tail2 with
          | expr_cons _ tail3 =>
              cases tail3 with
              | expr_cons _ tail4 =>
                  cases tail4 with
                  | expr_cons _ tail5 =>
                      cases tail5 with
                      | expr_cons _ tail6 =>
                          cases tail6 with
                          | expr_cons _ tail7 =>
                              cases tail7 with
                              | expr_cons _ nilMatch =>
                                  cases nilMatch
                                  exact ⟨_, _, _, _, _, _, _, rfl⟩

/-- In an owned state, a body-builder reload match can use only the canonical
seven-rule carrier. -/
private theorem normalBodyBuildReload_bundle_witness_exact
    {space : List Atom} (state : NormalProofMachineExecutionContext space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyBuildReloadDirective.atom ::
          space.erase normalBodyBuildReloadDirective.atom)
        normalBodyBuildReloadDirective.rule.input).map Prod.fst) :
    ∃ afterFirst afterSecond firstAtom secondAtom,
      firstAtom ∈
          (normalBodyBuildReloadDirective.atom ::
            space.erase normalBodyBuildReloadDirective.atom) ∧
        secondAtom ∈
          (normalBodyBuildReloadDirective.atom ::
            space.erase normalBodyBuildReloadDirective.atom) ∧
        Conformance.Computable.cmatchAtom []
            (.expression
              [.symbol "exec",
                .expression
                  [.symbol "30", .symbol "mm-normal-body-build-reload"],
                .var "build-reload-self-input",
                .var "build-reload-self-output"])
            firstAtom = some afterFirst ∧
        Conformance.Computable.cmatchAtom afterFirst
            (.expression
              [.symbol "mm-reload-body-build",
                .var "build-reload-proof", .var "build-reload-pc"])
            secondAtom = some afterSecond ∧
        Conformance.Computable.cmatchAtom afterSecond
            (.expression
              [.symbol "mm-internal-body-build-rules",
                .var "build-rule-const", .var "build-rule-variable",
                .var "build-rule-prefix-nil",
                .var "build-rule-prefix-cons", .var "build-rule-nil",
                .var "build-rule-reverse-cons",
                .var "build-rule-reverse-nil"])
            normalBodyBuildRuleBundle = some substitution := by
  have rowMember' : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyBuildReloadDirective.atom ::
          space.erase normalBodyBuildReloadDirective.atom)
        (.compat (mkPattern
          [(.expression
              [.symbol "exec",
                .expression
                  [.symbol "30", .symbol "mm-normal-body-build-reload"],
                .var "build-reload-self-input",
                .var "build-reload-self-output"] : Atom),
           .expression
              [.symbol "mm-reload-body-build",
                .var "build-reload-proof", .var "build-reload-pc"],
           .expression
              [.symbol "mm-internal-body-build-rules",
                .var "build-rule-const", .var "build-rule-variable",
                .var "build-rule-prefix-nil",
                .var "build-rule-prefix-cons", .var "build-rule-nil",
                .var "build-rule-reverse-cons",
                .var "build-rule-reverse-nil"]]))).map Prod.fst := by
    change substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyBuildReloadDirective.atom ::
          space.erase normalBodyBuildReloadDirective.atom)
        normalBodyBuildReloadDirective.rule.input).map Prod.fst
    exact rowMember
  obtain ⟨afterFirst, afterSecond, firstAtom, secondAtom, thirdAtom,
      firstMember, secondMember, thirdMember,
      firstMatched, secondMatched, thirdMatched⟩ :=
    cmatchInputSpec_three_match_chain rowMember'
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  obtain ⟨constRule, variableRule, prefixNilRule, prefixConsRule, nilRule,
      reverseConsRule, reverseNilRule, thirdEq⟩ :=
    matchAtom_bodyBuildReload_bundle_shape thirdMatched
  have thirdInSpace : thirdAtom ∈ space := by
    rcases List.mem_cons.mp thirdMember with selected | erased
    · rw [thirdEq] at selected
      simp [normalBodyBuildReloadDirective,
        normalBodyBuildReloadRule] at selected
    · exact List.mem_of_mem_erase erased
  have authorized := state.2 thirdAtom thirdInSpace
  have internalShape : isVerifierOwnedInternalRowShape thirdAtom = true := by
    rw [thirdEq]
    rfl
  have authorizedMember := authorized internalShape
  have thirdExact : thirdAtom = normalBodyBuildRuleBundle := by
    rw [thirdEq] at authorizedMember
    simp [normalVerifierInternalRows, normalBodyMatchRuleBundle,
      normalDVRuleBundle, normalBodyBuildRuleBundle, normalDispatchRuleRows,
      normalDispatchRuleRow] at authorizedMember
    rcases authorizedMember with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simpa [normalBodyBuildRuleBundle] using thirdEq
  rw [thirdExact] at thirdMatched
  rw [← Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  exact ⟨afterFirst, afterSecond, firstAtom, secondAtom,
    firstMember, secondMember, firstMatched, secondMatched, thirdMatched⟩

/-- Exact carrier ownership fixes every variable-valued rule emitted by the
body-builder reloader. -/
private theorem normalBodyBuildReload_bundle_lookups
    {space : List Atom} (state : NormalProofMachineExecutionContext space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyBuildReloadDirective.atom ::
          space.erase normalBodyBuildReloadDirective.atom)
        normalBodyBuildReloadDirective.rule.input).map Prod.fst) :
    substitution.lookup "build-rule-const" =
        some normalBodyBuildConstRule ∧
      substitution.lookup "build-rule-variable" =
        some normalBodyBuildVariableRule ∧
      substitution.lookup "build-rule-prefix-nil" =
        some normalBodyBuildPrefixNilRule ∧
      substitution.lookup "build-rule-prefix-cons" =
        some normalBodyBuildPrefixConsRule ∧
      substitution.lookup "build-rule-nil" =
        some normalBodyBuildNilRule ∧
      substitution.lookup "build-rule-reverse-cons" =
        some normalBodyReverseConsRule ∧
      substitution.lookup "build-rule-reverse-nil" =
        some normalBodyReverseNilRule := by
  obtain ⟨afterFirst, afterSecond, firstAtom, secondAtom,
      _firstMember, _secondMember, _firstMatched, _secondMatched,
      thirdMatched⟩ := normalBodyBuildReload_bundle_witness_exact state rowMember
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  have listMatched :
      matchAtom.matchAtomList afterSecond
        [.symbol "mm-internal-body-build-rules",
          .var "build-rule-const", .var "build-rule-variable",
          .var "build-rule-prefix-nil", .var "build-rule-prefix-cons",
          .var "build-rule-nil", .var "build-rule-reverse-cons",
          .var "build-rule-reverse-nil"]
        [.symbol "mm-internal-body-build-rules",
          normalBodyBuildConstRule, normalBodyBuildVariableRule,
          normalBodyBuildPrefixNilRule, normalBodyBuildPrefixConsRule,
          normalBodyBuildNilRule, normalBodyReverseConsRule,
          normalBodyReverseNilRule] = some substitution := by
    simpa [normalBodyBuildRuleBundle, matchAtom] using thirdMatched
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-build-rules"]
      [.symbol "mm-internal-body-build-rules"]
      [.var "build-rule-variable", .var "build-rule-prefix-nil",
        .var "build-rule-prefix-cons", .var "build-rule-nil",
        .var "build-rule-reverse-cons", .var "build-rule-reverse-nil"]
      [normalBodyBuildVariableRule, normalBodyBuildPrefixNilRule,
        normalBodyBuildPrefixConsRule, normalBodyBuildNilRule,
        normalBodyReverseConsRule, normalBodyReverseNilRule]
      afterSecond substitution "build-rule-const" normalBodyBuildConstRule
      rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-build-rules", .var "build-rule-const"]
      [.symbol "mm-internal-body-build-rules", normalBodyBuildConstRule]
      [.var "build-rule-prefix-nil", .var "build-rule-prefix-cons",
        .var "build-rule-nil", .var "build-rule-reverse-cons",
        .var "build-rule-reverse-nil"]
      [normalBodyBuildPrefixNilRule, normalBodyBuildPrefixConsRule,
        normalBodyBuildNilRule, normalBodyReverseConsRule,
        normalBodyReverseNilRule]
      afterSecond substitution "build-rule-variable"
      normalBodyBuildVariableRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-build-rules", .var "build-rule-const",
        .var "build-rule-variable"]
      [.symbol "mm-internal-body-build-rules", normalBodyBuildConstRule,
        normalBodyBuildVariableRule]
      [.var "build-rule-prefix-cons", .var "build-rule-nil",
        .var "build-rule-reverse-cons", .var "build-rule-reverse-nil"]
      [normalBodyBuildPrefixConsRule, normalBodyBuildNilRule,
        normalBodyReverseConsRule, normalBodyReverseNilRule]
      afterSecond substitution "build-rule-prefix-nil"
      normalBodyBuildPrefixNilRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-build-rules", .var "build-rule-const",
        .var "build-rule-variable", .var "build-rule-prefix-nil"]
      [.symbol "mm-internal-body-build-rules", normalBodyBuildConstRule,
        normalBodyBuildVariableRule, normalBodyBuildPrefixNilRule]
      [.var "build-rule-nil", .var "build-rule-reverse-cons",
        .var "build-rule-reverse-nil"]
      [normalBodyBuildNilRule, normalBodyReverseConsRule,
        normalBodyReverseNilRule]
      afterSecond substitution "build-rule-prefix-cons"
      normalBodyBuildPrefixConsRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-build-rules", .var "build-rule-const",
        .var "build-rule-variable", .var "build-rule-prefix-nil",
        .var "build-rule-prefix-cons"]
      [.symbol "mm-internal-body-build-rules", normalBodyBuildConstRule,
        normalBodyBuildVariableRule, normalBodyBuildPrefixNilRule,
        normalBodyBuildPrefixConsRule]
      [.var "build-rule-reverse-cons", .var "build-rule-reverse-nil"]
      [normalBodyReverseConsRule, normalBodyReverseNilRule]
      afterSecond substitution "build-rule-nil" normalBodyBuildNilRule
      rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-build-rules", .var "build-rule-const",
        .var "build-rule-variable", .var "build-rule-prefix-nil",
        .var "build-rule-prefix-cons", .var "build-rule-nil"]
      [.symbol "mm-internal-body-build-rules", normalBodyBuildConstRule,
        normalBodyBuildVariableRule, normalBodyBuildPrefixNilRule,
        normalBodyBuildPrefixConsRule, normalBodyBuildNilRule]
      [.var "build-rule-reverse-nil"] [normalBodyReverseNilRule]
      afterSecond substitution "build-rule-reverse-cons"
      normalBodyReverseConsRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-build-rules", .var "build-rule-const",
        .var "build-rule-variable", .var "build-rule-prefix-nil",
        .var "build-rule-prefix-cons", .var "build-rule-nil",
        .var "build-rule-reverse-cons"]
      [.symbol "mm-internal-body-build-rules", normalBodyBuildConstRule,
        normalBodyBuildVariableRule, normalBodyBuildPrefixNilRule,
        normalBodyBuildPrefixConsRule, normalBodyBuildNilRule,
        normalBodyReverseConsRule]
      [] [] afterSecond substitution "build-rule-reverse-nil"
      normalBodyReverseNilRule rfl listMatched

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
  obtain ⟨afterFirst, afterSecond, firstAtom, secondAtom,
      firstMember, _secondMember, firstMatched, secondMatched,
      thirdMatched⟩ := normalBodyBuildReload_bundle_witness_exact state rowMember
  rw [Conformance.cmatchAtom_eq_matchAtom] at firstMatched secondMatched
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  obtain ⟨input, output, firstEq, inputLookup, outputLookup⟩ :=
    matchAtom_bodyBuildReload_self firstMatched
  have finalExtends : substitution.lookupExtends afterFirst :=
    Subst.lookupExtends_trans
      (matchAtom_lookupExtends secondMatched)
      (matchAtom_lookupExtends thirdMatched)
  have finalInputLookup :
      substitution.lookup "build-reload-self-input" = some input :=
    finalExtends "build-reload-self-input" input inputLookup
  have finalOutputLookup :
      substitution.lookup "build-reload-self-output" = some output :=
    finalExtends "build-reload-self-output" output outputLookup
  have applied :
      applySubst substitution
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "30", .symbol "mm-normal-body-build-reload"],
              .var "build-reload-self-input",
              .var "build-reload-self-output"]) = captured := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · exact Option.some.inj instantiates
    · simp at instantiates
  have appliedFirst :
      applySubst substitution
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "30", .symbol "mm-normal-body-build-reload"],
              .var "build-reload-self-input",
              .var "build-reload-self-output"]) = firstAtom := by
    rw [firstEq]
    change
      Atom.expression
          [.symbol "exec",
            .expression
              [.symbol "30", .symbol "mm-normal-body-build-reload"],
            (substitution.lookup "build-reload-self-input").getD
              (.var "build-reload-self-input"),
            (substitution.lookup "build-reload-self-output").getD
              (.var "build-reload-self-output")] =
        Atom.expression
          [.symbol "exec",
            .expression
              [.symbol "30", .symbol "mm-normal-body-build-reload"],
            input, output]
    rw [finalInputLookup, finalOutputLookup]
    rfl
  have capturedEq : captured = firstAtom := applied.symm.trans appliedFirst
  rw [capturedEq] at extracts
  rcases List.mem_cons.mp firstMember with selected | prior
  · rw [selected] at extracts
    exact List.mem_filterMap.mpr
      ⟨normalBodyBuildReloadDirective.atom,
        by simp [normalBodyBuildReloadDirective, normalProofMachineRules],
        extracts⟩
  · apply authoredNormalVerifierRawFact_mem_normal_of_loc_mem
    · apply state.1 raw
      exact List.mem_filterMap.mpr
        ⟨firstAtom, List.mem_of_mem_erase prior, extracts⟩
    · rw [firstEq] at extracts
      simp only [extractRawExecFact] at extracts
      injection extracts with rawEqual
      subst raw
      change (.expression
        [.symbol "30", .symbol "mm-normal-body-build-reload"] : Atom) ∈
          normalProofMachineRawFacts.map RawExecFact.loc
      decide +kernel

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
  obtain ⟨constLookup, variableLookup, prefixNilLookup, prefixConsLookup,
      nilLookup, reverseConsLookup, reverseNilLookup⟩ :=
    normalBodyBuildReload_bundle_lookups state rowMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at authoredMember
  rcases authoredMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      constLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      variableLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      prefixNilLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      prefixConsLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      nilLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      reverseConsLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      reverseNilLookup] at instantiates
    subst captured
    simp

/-- Every executable addition made by the result-body reloader comes from its
authorized self shell or the exact seven-rule carrier. -/
theorem normalBodyBuildReload_additions_raw_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyBuildReloadDirective.atom ::
        space.erase normalBodyBuildReloadDirective.atom)
      normalBodyBuildReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalBodyBuildReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added raw extracts
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "30", .symbol "mm-normal-body-build-reload"],
              .var "build-reload-self-input",
              .var "build-reload-self-output"] : Atom) ∨
        authored ∈
          [(.var "build-rule-const" : Atom), .var "build-rule-variable",
            .var "build-rule-prefix-nil", .var "build-rule-prefix-cons",
            .var "build-rule-nil", .var "build-rule-reverse-cons",
            .var "build-rule-reverse-nil"] := by
    change Sink.add authored ∈
      [Sink.add
        (.expression
          [.symbol "exec",
            .expression
              [.symbol "30", .symbol "mm-normal-body-build-reload"],
            .var "build-reload-self-input",
            .var "build-reload-self-output"]),
       Sink.remove
        (.expression
          [.symbol "mm-reload-body-build", .var "build-reload-proof",
            .var "build-reload-pc"]),
       Sink.add (.var "build-rule-const"),
       Sink.add (.var "build-rule-variable"),
       Sink.add (.var "build-rule-prefix-nil"),
       Sink.add (.var "build-rule-prefix-cons"),
       Sink.add (.var "build-rule-nil"),
       Sink.add (.var "build-rule-reverse-cons"),
       Sink.add (.var "build-rule-reverse-nil")] at sinkMember
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · rw [selfSink] at instantiates
    exact normalBodyBuildReload_captured_self_raw_authorized state rowMember
      instantiates extracts
  · have authorized :=
      normalBodyBuildReload_captured_rule_authorized state rowMember ruleSink
        instantiates
    have machineMember : atom ∈ normalProofMachineRules := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at authorized
      rcases authorized with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [normalProofMachineRules]
    exact List.mem_filterMap.mpr ⟨atom, machineMember, extracts⟩

/-- Result-body reload cannot forge a protected inert carrier: every emitted
atom is either an executable shell or one of the seven executable rules. -/
theorem normalBodyBuildReload_additions_internal_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyBuildReloadDirective.atom ::
        space.erase normalBodyBuildReloadDirective.atom)
      normalBodyBuildReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalBodyBuildReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "30", .symbol "mm-normal-body-build-reload"],
              .var "build-reload-self-input",
              .var "build-reload-self-output"] : Atom) ∨
        authored ∈
          [(.var "build-rule-const" : Atom), .var "build-rule-variable",
            .var "build-rule-prefix-nil", .var "build-rule-prefix-cons",
            .var "build-rule-nil", .var "build-rule-reverse-cons",
            .var "build-rule-reverse-nil"] := by
    change Sink.add authored ∈
      [Sink.add
        (.expression
          [.symbol "exec",
            .expression
              [.symbol "30", .symbol "mm-normal-body-build-reload"],
            .var "build-reload-self-input",
            .var "build-reload-self-output"]),
       Sink.remove
        (.expression
          [.symbol "mm-reload-body-build", .var "build-reload-proof",
            .var "build-reload-pc"]),
       Sink.add (.var "build-rule-const"),
       Sink.add (.var "build-rule-variable"),
       Sink.add (.var "build-rule-prefix-nil"),
       Sink.add (.var "build-rule-prefix-cons"),
       Sink.add (.var "build-rule-nil"),
       Sink.add (.var "build-rule-reverse-cons"),
       Sink.add (.var "build-rule-reverse-nil")] at sinkMember
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · rw [selfSink] at instantiates
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · have applied := Option.some.inj instantiates
      have atomShape :
          ∃ input output,
            atom =
              .expression
                [.symbol "exec",
                  .expression
                    [.symbol "30", .symbol "mm-normal-body-build-reload"],
                  input, output] := ⟨_, _, applied.symm⟩
      rcases atomShape with ⟨input, output, rfl⟩
      simp [isVerifierOwnedInternalRowShape,
        isVerifierOwnedInternalNamespace] at internalShape
    · simp at instantiates
  · have authorized :=
      normalBodyBuildReload_captured_rule_authorized state rowMember ruleSink
        instantiates
    have machineMember : atom ∈ normalProofMachineRules := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at authorized
      rcases authorized with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [normalProofMachineRules]
    have safe :=
      (List.all_eq_true.mp normalProofMachineRules_no_internal_row_shape)
        atom machineMember
    have notInternal : isVerifierOwnedInternalRowShape atom = false := by
      simpa only [Bool.not_eq_true'] using safe
    rw [notInternal] at internalShape
    contradiction

/-- The result-body reloader satisfies both source-relative owned-addition
obligations. -/
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
  exact ⟨normalBodyBuildReload_additions_raw_closed state,
    normalBodyBuildReload_additions_internal_closed state⟩

/-- Firing the actual result-body reloader preserves the complete owned
normal-proof machine invariant. -/
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

/-- The DV reloader's self pattern retains the exact scheduler shell and its
two opaque byte fields. -/
private theorem matchAtom_dvReload_self
    {result : Subst} {atom : Atom}
    (matched : matchAtom []
      (.expression
        [.symbol "exec",
          .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
          .var "dv-reload-self-input", .var "dv-reload-self-output"])
      atom = some result) :
    ∃ input output,
      atom =
          .expression
            [.symbol "exec",
              .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
              input, output] ∧
        result.lookup "dv-reload-self-input" = some input ∧
        result.lookup "dv-reload-self-output" = some output := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons execMatch tail1 =>
      cases execMatch
      cases tail1 with
      | expr_cons locationMatch tail2 =>
          cases locationMatch with
          | expr_cons locationHead locationTail =>
              cases locationHead
              cases locationTail with
              | expr_cons locationName locationNil =>
                  cases locationName
                  cases locationNil
                  cases tail2 with
                  | expr_cons inputMatch tail3 =>
                      cases inputMatch with
                      | var_fresh _ =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  refine ⟨_, _, rfl, ?_, ?_⟩
                                  · simp [Subst.lookup]
                                  · simp [Subst.lookup]
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl,
                                    by simp [Subst.lookup], outputLookup⟩
                      | var_bound inputLookup =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    by simp [Subst.lookup]⟩
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    outputLookup⟩

/-- A successful match against the owned DV carrier exposes exactly its eight
opaque rule fields. -/
private theorem matchAtom_dvReload_bundle_shape
    {before result : Subst} {atom : Atom}
    (matched : matchAtom before
      (.expression
        [.symbol "mm-internal-dv-rules",
          .var "dv-rule-pair-begin", .var "dv-rule-left-const",
          .var "dv-rule-left-variable", .var "dv-rule-right-const",
          .var "dv-rule-right-variable", .var "dv-rule-right-nil",
          .var "dv-rule-left-nil", .var "dv-rule-complete"])
      atom = some result) :
    ∃ pairBegin leftConst leftVariable rightConst rightVariable rightNil
        leftNil complete,
      atom =
        .expression
          [.symbol "mm-internal-dv-rules", pairBegin, leftConst,
            leftVariable, rightConst, rightVariable, rightNil, leftNil,
            complete] := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatch tail1 =>
      cases headMatch
      cases tail1 with
      | expr_cons _ tail2 =>
          cases tail2 with
          | expr_cons _ tail3 =>
              cases tail3 with
              | expr_cons _ tail4 =>
                  cases tail4 with
                  | expr_cons _ tail5 =>
                      cases tail5 with
                      | expr_cons _ tail6 =>
                          cases tail6 with
                          | expr_cons _ tail7 =>
                              cases tail7 with
                              | expr_cons _ tail8 =>
                                  cases tail8 with
                                  | expr_cons _ nilMatch =>
                                      cases nilMatch
                                      exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- In an owned state the third DV-reload witness is the one exact carrier
emitted by the generic verifier, never a same-headed row with altered code. -/
private theorem normalDVReload_bundle_witness_exact
    {space : List Atom} (state : NormalProofMachineExecutionContext space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDVReloadDirective.atom ::
          space.erase normalDVReloadDirective.atom)
        normalDVReloadDirective.rule.input).map Prod.fst) :
    ∃ afterFirst afterSecond firstAtom secondAtom,
      firstAtom ∈
          (normalDVReloadDirective.atom ::
            space.erase normalDVReloadDirective.atom) ∧
        secondAtom ∈
          (normalDVReloadDirective.atom ::
            space.erase normalDVReloadDirective.atom) ∧
        Conformance.Computable.cmatchAtom []
            (.expression
              [.symbol "exec",
                .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
                .var "dv-reload-self-input",
                .var "dv-reload-self-output"])
            firstAtom = some afterFirst ∧
        Conformance.Computable.cmatchAtom afterFirst
            (.expression
              [.symbol "mm-reload-dv", .var "dv-reload-proof",
                .var "dv-reload-pc"])
            secondAtom = some afterSecond ∧
        Conformance.Computable.cmatchAtom afterSecond
            (.expression
              [.symbol "mm-internal-dv-rules",
                .var "dv-rule-pair-begin", .var "dv-rule-left-const",
                .var "dv-rule-left-variable", .var "dv-rule-right-const",
                .var "dv-rule-right-variable", .var "dv-rule-right-nil",
                .var "dv-rule-left-nil", .var "dv-rule-complete"])
            normalDVRuleBundle = some substitution := by
  rw [normalDVReload_input_exact] at rowMember
  obtain ⟨afterFirst, afterSecond, firstAtom, secondAtom, thirdAtom,
      firstMember, secondMember, thirdMember,
      firstMatched, secondMatched, thirdMatched⟩ :=
    cmatchInputSpec_three_match_chain rowMember
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  obtain ⟨pairBegin, leftConst, leftVariable, rightConst, rightVariable,
      rightNil, leftNil, complete, thirdEq⟩ :=
    matchAtom_dvReload_bundle_shape thirdMatched
  have thirdInSpace : thirdAtom ∈ space := by
    rcases List.mem_cons.mp thirdMember with selected | erased
    · rw [thirdEq] at selected
      simp [normalDVReloadDirective, normalDVReloadRule] at selected
    · exact List.mem_of_mem_erase erased
  have authorized := state.2 thirdAtom thirdInSpace
  have internalShape : isVerifierOwnedInternalRowShape thirdAtom = true := by
    rw [thirdEq]
    rfl
  have authorizedMember := authorized internalShape
  have thirdExact : thirdAtom = normalDVRuleBundle := by
    rw [thirdEq] at authorizedMember
    simp [normalVerifierInternalRows, normalBodyMatchRuleBundle,
      normalDVRuleBundle, normalBodyBuildRuleBundle,
      normalDispatchRuleRows, normalDispatchRuleRow] at authorizedMember
    rcases authorizedMember with
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simpa [normalDVRuleBundle] using thirdEq
  rw [thirdExact] at thirdMatched
  rw [← Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  exact ⟨afterFirst, afterSecond, firstAtom, secondAtom,
    firstMember, secondMember, firstMatched, secondMatched, thirdMatched⟩

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
  obtain ⟨afterFirst, afterSecond, firstAtom, _secondAtom,
      firstMember, _secondMember, firstMatched, secondMatched,
      thirdMatched⟩ := normalDVReload_bundle_witness_exact state rowMember
  rw [Conformance.cmatchAtom_eq_matchAtom] at firstMatched secondMatched
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  obtain ⟨input, output, firstEq, inputLookup, outputLookup⟩ :=
    matchAtom_dvReload_self firstMatched
  have finalExtends : substitution.lookupExtends afterFirst :=
    Subst.lookupExtends_trans
      (matchAtom_lookupExtends secondMatched)
      (matchAtom_lookupExtends thirdMatched)
  have finalInputLookup :
      substitution.lookup "dv-reload-self-input" = some input :=
    finalExtends "dv-reload-self-input" input inputLookup
  have finalOutputLookup :
      substitution.lookup "dv-reload-self-output" = some output :=
    finalExtends "dv-reload-self-output" output outputLookup
  have applied :
      applySubst substitution
          (.expression
            [.symbol "exec",
              .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
              .var "dv-reload-self-input", .var "dv-reload-self-output"]) =
        captured := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · exact Option.some.inj instantiates
    · simp at instantiates
  have appliedFirst :
      applySubst substitution
          (.expression
            [.symbol "exec",
              .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
              .var "dv-reload-self-input", .var "dv-reload-self-output"]) =
        firstAtom := by
    rw [firstEq]
    change
      Atom.expression
          [.symbol "exec",
            .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
            (substitution.lookup "dv-reload-self-input").getD
              (.var "dv-reload-self-input"),
            (substitution.lookup "dv-reload-self-output").getD
              (.var "dv-reload-self-output")] =
        Atom.expression
          [.symbol "exec",
            .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
            input, output]
    rw [finalInputLookup, finalOutputLookup]
    rfl
  have capturedEq : captured = firstAtom := applied.symm.trans appliedFirst
  rw [capturedEq] at extracts
  rcases List.mem_cons.mp firstMember with selected | prior
  · rw [selected] at extracts
    exact List.mem_filterMap.mpr
      ⟨normalDVReloadDirective.atom,
        by simp [normalDVReloadDirective, normalProofMachineRules],
        extracts⟩
  · apply authoredNormalVerifierRawFact_mem_normal_of_loc_mem
    · apply state.1 raw
      exact List.mem_filterMap.mpr
        ⟨firstAtom, List.mem_of_mem_erase prior, extracts⟩
    · rw [firstEq] at extracts
      simp only [extractRawExecFact] at extracts
      injection extracts with rawEqual
      subst raw
      change (.expression
        [.symbol "22", .symbol "mm-normal-dv-reload"] : Atom) ∈
          normalProofMachineRawFacts.map RawExecFact.loc
      decide +kernel

/-- Exact ownership of the DV carrier fixes all eight rule bindings used by
the variable-valued output sinks. -/
private theorem normalDVReload_bundle_lookups
    {space : List Atom} (state : NormalProofMachineExecutionContext space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDVReloadDirective.atom ::
          space.erase normalDVReloadDirective.atom)
        normalDVReloadDirective.rule.input).map Prod.fst) :
    substitution.lookup "dv-rule-pair-begin" =
        some normalDVPairBeginRule ∧
      substitution.lookup "dv-rule-left-const" =
        some normalDVLeftConstRule ∧
      substitution.lookup "dv-rule-left-variable" =
        some normalDVLeftVariableRule ∧
      substitution.lookup "dv-rule-right-const" =
        some normalDVRightConstRule ∧
      substitution.lookup "dv-rule-right-variable" =
        some normalDVRightVariableRule ∧
      substitution.lookup "dv-rule-right-nil" =
        some normalDVRightNilRule ∧
      substitution.lookup "dv-rule-left-nil" =
        some normalDVLeftNilRule ∧
      substitution.lookup "dv-rule-complete" =
        some normalDVCompleteRule := by
  obtain ⟨_afterFirst, afterSecond, _firstAtom, _secondAtom,
      _firstMember, _secondMember, _firstMatched, _secondMatched,
      thirdMatched⟩ := normalDVReload_bundle_witness_exact state rowMember
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  have listMatched :
      matchAtom.matchAtomList afterSecond
        [.symbol "mm-internal-dv-rules",
          .var "dv-rule-pair-begin", .var "dv-rule-left-const",
          .var "dv-rule-left-variable", .var "dv-rule-right-const",
          .var "dv-rule-right-variable", .var "dv-rule-right-nil",
          .var "dv-rule-left-nil", .var "dv-rule-complete"]
        [.symbol "mm-internal-dv-rules",
          normalDVPairBeginRule, normalDVLeftConstRule,
          normalDVLeftVariableRule, normalDVRightConstRule,
          normalDVRightVariableRule, normalDVRightNilRule,
          normalDVLeftNilRule, normalDVCompleteRule] = some substitution := by
    simpa [normalDVRuleBundle, matchAtom] using thirdMatched
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-dv-rules"]
      [.symbol "mm-internal-dv-rules"]
      [.var "dv-rule-left-const", .var "dv-rule-left-variable",
        .var "dv-rule-right-const", .var "dv-rule-right-variable",
        .var "dv-rule-right-nil", .var "dv-rule-left-nil",
        .var "dv-rule-complete"]
      [normalDVLeftConstRule, normalDVLeftVariableRule,
        normalDVRightConstRule, normalDVRightVariableRule,
        normalDVRightNilRule, normalDVLeftNilRule, normalDVCompleteRule]
      afterSecond substitution "dv-rule-pair-begin" normalDVPairBeginRule
      rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-dv-rules", .var "dv-rule-pair-begin"]
      [.symbol "mm-internal-dv-rules", normalDVPairBeginRule]
      [.var "dv-rule-left-variable", .var "dv-rule-right-const",
        .var "dv-rule-right-variable", .var "dv-rule-right-nil",
        .var "dv-rule-left-nil", .var "dv-rule-complete"]
      [normalDVLeftVariableRule, normalDVRightConstRule,
        normalDVRightVariableRule, normalDVRightNilRule,
        normalDVLeftNilRule, normalDVCompleteRule]
      afterSecond substitution "dv-rule-left-const" normalDVLeftConstRule
      rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-dv-rules", .var "dv-rule-pair-begin",
        .var "dv-rule-left-const"]
      [.symbol "mm-internal-dv-rules", normalDVPairBeginRule,
        normalDVLeftConstRule]
      [.var "dv-rule-right-const", .var "dv-rule-right-variable",
        .var "dv-rule-right-nil", .var "dv-rule-left-nil",
        .var "dv-rule-complete"]
      [normalDVRightConstRule, normalDVRightVariableRule,
        normalDVRightNilRule, normalDVLeftNilRule, normalDVCompleteRule]
      afterSecond substitution "dv-rule-left-variable"
      normalDVLeftVariableRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-dv-rules", .var "dv-rule-pair-begin",
        .var "dv-rule-left-const", .var "dv-rule-left-variable"]
      [.symbol "mm-internal-dv-rules", normalDVPairBeginRule,
        normalDVLeftConstRule, normalDVLeftVariableRule]
      [.var "dv-rule-right-variable", .var "dv-rule-right-nil",
        .var "dv-rule-left-nil", .var "dv-rule-complete"]
      [normalDVRightVariableRule, normalDVRightNilRule,
        normalDVLeftNilRule, normalDVCompleteRule]
      afterSecond substitution "dv-rule-right-const"
      normalDVRightConstRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-dv-rules", .var "dv-rule-pair-begin",
        .var "dv-rule-left-const", .var "dv-rule-left-variable",
        .var "dv-rule-right-const"]
      [.symbol "mm-internal-dv-rules", normalDVPairBeginRule,
        normalDVLeftConstRule, normalDVLeftVariableRule,
        normalDVRightConstRule]
      [.var "dv-rule-right-nil", .var "dv-rule-left-nil",
        .var "dv-rule-complete"]
      [normalDVRightNilRule, normalDVLeftNilRule, normalDVCompleteRule]
      afterSecond substitution "dv-rule-right-variable"
      normalDVRightVariableRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-dv-rules", .var "dv-rule-pair-begin",
        .var "dv-rule-left-const", .var "dv-rule-left-variable",
        .var "dv-rule-right-const", .var "dv-rule-right-variable"]
      [.symbol "mm-internal-dv-rules", normalDVPairBeginRule,
        normalDVLeftConstRule, normalDVLeftVariableRule,
        normalDVRightConstRule, normalDVRightVariableRule]
      [.var "dv-rule-left-nil", .var "dv-rule-complete"]
      [normalDVLeftNilRule, normalDVCompleteRule]
      afterSecond substitution "dv-rule-right-nil" normalDVRightNilRule
      rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-dv-rules", .var "dv-rule-pair-begin",
        .var "dv-rule-left-const", .var "dv-rule-left-variable",
        .var "dv-rule-right-const", .var "dv-rule-right-variable",
        .var "dv-rule-right-nil"]
      [.symbol "mm-internal-dv-rules", normalDVPairBeginRule,
        normalDVLeftConstRule, normalDVLeftVariableRule,
        normalDVRightConstRule, normalDVRightVariableRule,
        normalDVRightNilRule]
      [.var "dv-rule-complete"] [normalDVCompleteRule]
      afterSecond substitution "dv-rule-left-nil" normalDVLeftNilRule
      rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-dv-rules", .var "dv-rule-pair-begin",
        .var "dv-rule-left-const", .var "dv-rule-left-variable",
        .var "dv-rule-right-const", .var "dv-rule-right-variable",
        .var "dv-rule-right-nil", .var "dv-rule-left-nil"]
      [.symbol "mm-internal-dv-rules", normalDVPairBeginRule,
        normalDVLeftConstRule, normalDVLeftVariableRule,
        normalDVRightConstRule, normalDVRightVariableRule,
        normalDVRightNilRule, normalDVLeftNilRule]
      [] [] afterSecond substitution "dv-rule-complete"
      normalDVCompleteRule rfl listMatched

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
  obtain ⟨pairBeginLookup, leftConstLookup, leftVariableLookup,
      rightConstLookup, rightVariableLookup, rightNilLookup,
      leftNilLookup, completeLookup⟩ :=
    normalDVReload_bundle_lookups state rowMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at authoredMember
  rcases authoredMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      pairBeginLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      leftConstLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      leftVariableLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      rightConstLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      rightVariableLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      rightNilLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      leftNilLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      completeLookup] at instantiates
    subst captured
    simp

/-- Every executable addition made by the DV reloader is either its authorized
self shell or one of the eight rules recovered from the exact owned carrier. -/
theorem normalDVReload_additions_raw_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDVReloadDirective.atom ::
        space.erase normalDVReloadDirective.atom)
      normalDVReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalDVReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added raw extracts
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
              .var "dv-reload-self-input",
              .var "dv-reload-self-output"] : Atom) ∨
        authored ∈
          [(.var "dv-rule-pair-begin" : Atom), .var "dv-rule-left-const",
            .var "dv-rule-left-variable", .var "dv-rule-right-const",
            .var "dv-rule-right-variable", .var "dv-rule-right-nil",
            .var "dv-rule-left-nil", .var "dv-rule-complete"] := by
    rw [normalDVReload_sinks_exact] at sinkMember
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · rw [selfSink] at instantiates
    exact normalDVReload_captured_self_raw_authorized state rowMember
      instantiates extracts
  · have authorized :=
      normalDVReload_captured_rule_authorized state rowMember ruleSink
        instantiates
    have machineMember : atom ∈ normalProofMachineRules := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at authorized
      rcases authorized with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [normalProofMachineRules]
    exact List.mem_filterMap.mpr ⟨atom, machineMember, extracts⟩

/-- Captured DV rules are executable atoms and the recovered self shell has an
ordinary `exec` head, so DV reload cannot create a protected inert carrier. -/
theorem normalDVReload_additions_internal_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDVReloadDirective.atom ::
        space.erase normalDVReloadDirective.atom)
      normalDVReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalDVReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
              .var "dv-reload-self-input",
              .var "dv-reload-self-output"] : Atom) ∨
        authored ∈
          [(.var "dv-rule-pair-begin" : Atom), .var "dv-rule-left-const",
            .var "dv-rule-left-variable", .var "dv-rule-right-const",
            .var "dv-rule-right-variable", .var "dv-rule-right-nil",
            .var "dv-rule-left-nil", .var "dv-rule-complete"] := by
    rw [normalDVReload_sinks_exact] at sinkMember
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · rw [selfSink] at instantiates
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · have applied := Option.some.inj instantiates
      have atomShape :
          ∃ input output,
            atom =
              .expression
                [.symbol "exec",
                  .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
                  input, output] := ⟨_, _, applied.symm⟩
      rcases atomShape with ⟨input, output, rfl⟩
      simp [isVerifierOwnedInternalRowShape,
        isVerifierOwnedInternalNamespace] at internalShape
    · simp at instantiates
  · have authorized :=
      normalDVReload_captured_rule_authorized state rowMember ruleSink
        instantiates
    have machineMember : atom ∈ normalProofMachineRules := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at authorized
      rcases authorized with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [normalProofMachineRules]
    have safe :=
      (List.all_eq_true.mp normalProofMachineRules_no_internal_row_shape)
        atom machineMember
    have notInternal : isVerifierOwnedInternalRowShape atom = false := by
      simpa only [Bool.not_eq_true'] using safe
    rw [notInternal] at internalShape
    contradiction

/-- The DV reloader satisfies both owned-addition obligations in every
represented space. -/
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
  exact ⟨normalDVReload_additions_raw_closed state,
    normalDVReload_additions_internal_closed state⟩

/-- Firing the actual DV reloader preserves the complete owned normal-proof
machine invariant for an arbitrary represented space. -/
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
  .expression
    [.symbol "exec",
      .expression [.symbol priority, .symbol name],
      .var "self-input", .var "self-output"]

/-- Matching a persistent self shell reconstructs its exact scheduler key and
retains the two opaque parsed fields. -/
private theorem matchAtom_normalPersistent_self
    {priority name : String} {result : Subst} {atom : Atom}
    (matched : matchAtom []
      (normalPersistentSelfTemplate priority name) atom = some result) :
    ∃ input output,
      atom =
          .expression
            [.symbol "exec",
              .expression [.symbol priority, .symbol name],
              input, output] ∧
        result.lookup "self-input" = some input ∧
        result.lookup "self-output" = some output := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons execMatch tail1 =>
      cases execMatch
      cases tail1 with
      | expr_cons locationMatch tail2 =>
          cases locationMatch with
          | expr_cons locationHead locationTail =>
              cases locationHead
              cases locationTail with
              | expr_cons locationName locationNil =>
                  cases locationName
                  cases locationNil
                  cases tail2 with
                  | expr_cons inputMatch tail3 =>
                      cases inputMatch with
                      | var_fresh _ =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  refine ⟨_, _, rfl, ?_, ?_⟩
                                  · simp [Subst.lookup]
                                  · simp [Subst.lookup]
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl,
                                    by simp [Subst.lookup], outputLookup⟩
                      | var_bound inputLookup =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    by simp [Subst.lookup]⟩
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    outputLookup⟩

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
  have rowMember' : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (directive.atom :: space.erase directive.atom)
        (.compat (mkPattern
          (normalPersistentSelfTemplate priority name :: rest)))).map
            Prod.fst := by
    rw [← inputExact]
    exact rowMember
  obtain ⟨afterFirst, firstAtom, firstMember, firstMatched, finalExtends⟩ :=
    cmatchInputSpec_first_match_chain rowMember'
  rw [Conformance.cmatchAtom_eq_matchAtom] at firstMatched
  obtain ⟨input, output, firstEq, inputLookup, outputLookup⟩ :=
    matchAtom_normalPersistent_self firstMatched
  have finalInputLookup : substitution.lookup "self-input" = some input :=
    finalExtends "self-input" input inputLookup
  have finalOutputLookup : substitution.lookup "self-output" = some output :=
    finalExtends "self-output" output outputLookup
  have applied :
      applySubst substitution
          (normalPersistentSelfTemplate priority name) = captured := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · exact Option.some.inj instantiates
    · simp at instantiates
  have appliedFirst :
      applySubst substitution
          (normalPersistentSelfTemplate priority name) = firstAtom := by
    rw [firstEq]
    change
      Atom.expression
          [.symbol "exec",
            .expression [.symbol priority, .symbol name],
            (substitution.lookup "self-input").getD (.var "self-input"),
            (substitution.lookup "self-output").getD (.var "self-output")] =
        Atom.expression
          [.symbol "exec", .expression [.symbol priority, .symbol name],
            input, output]
    rw [finalInputLookup, finalOutputLookup]
    rfl
  have capturedEq : captured = firstAtom := applied.symm.trans appliedFirst
  rw [capturedEq] at extracts
  rcases List.mem_cons.mp firstMember with selected | prior
  · rw [selected] at extracts
    exact List.mem_filterMap.mpr
      ⟨directive.atom, directiveMember, extracts⟩
  · apply authoredNormalVerifierRawFact_mem_normal_of_loc_mem
    · apply state.1 raw
      exact List.mem_filterMap.mpr
        ⟨firstAtom, List.mem_of_mem_erase prior, extracts⟩
    · rw [firstEq] at extracts
      simp only [extractRawExecFact] at extracts
      injection extracts with rawEqual
      subst raw
      exact locationMember

/-- A substituted persistent self shell can be executable, but its outer
`exec` head prevents it from masquerading as a protected inert carrier. -/
private theorem normalPersistent_self_internal_impossible
    {priority name : String} {substitution : Subst} {atom : Atom}
    (instantiates : instantiateTemplateAtom? substitution
      (normalPersistentSelfTemplate priority name) = some atom)
    (internalShape : isVerifierOwnedInternalRowShape atom = true) : False := by
  unfold instantiateTemplateAtom? at instantiates
  split at instantiates
  · have applied := Option.some.inj instantiates
    have atomShape :
        ∃ input output,
          atom =
            .expression
              [.symbol "exec",
                .expression [.symbol priority, .symbol name],
                input, output] := ⟨_, _, applied.symm⟩
    rcases atomShape with ⟨input, output, rfl⟩
    simp [isVerifierOwnedInternalRowShape,
      isVerifierOwnedInternalNamespace] at internalShape
  · simp at instantiates

/-! ## Persistent hypothesis-step self shell -/

/-- Matching the persistent hypothesis rule's self factor fixes the exact
location and retains its opaque input and output bytes. -/
private theorem matchAtom_normalHypothesis_self
    {result : Subst} {atom : Atom}
    (matched : matchAtom []
      (.expression
        [.symbol "exec",
          .expression [.symbol "00", .symbol "mm-normal-hypothesis-step"],
          .var "self-input", .var "self-output"]) atom = some result) :
    ∃ input output,
      atom =
          .expression
            [.symbol "exec",
              .expression
                [.symbol "00", .symbol "mm-normal-hypothesis-step"],
              input, output] ∧
        result.lookup "self-input" = some input ∧
        result.lookup "self-output" = some output := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons execMatch tail1 =>
      cases execMatch
      cases tail1 with
      | expr_cons locationMatch tail2 =>
          cases locationMatch with
          | expr_cons locationHead locationTail =>
              cases locationHead
              cases locationTail with
              | expr_cons locationName locationNil =>
                  cases locationName
                  cases locationNil
                  cases tail2 with
                  | expr_cons inputMatch tail3 =>
                      cases inputMatch with
                      | var_fresh _ =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  refine ⟨_, _, rfl, ?_, ?_⟩
                                  · simp [Subst.lookup]
                                  · simp [Subst.lookup]
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl,
                                    by simp [Subst.lookup], outputLookup⟩
                      | var_bound inputLookup =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    by simp [Subst.lookup]⟩
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    outputLookup⟩

/-- A hypothesis-step self shell emitted from a successful matcher row is
the exact selected shell or an already-authorized copy in the input state. -/
private theorem normalHypothesis_captured_self_raw_authorized
    {space : List Atom} {substitution : Subst} {captured : Atom}
    {raw : RawExecFact}
    (state : NormalProofMachineExecutionContext space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalHypothesisDirective.atom ::
          space.erase normalHypothesisDirective.atom)
        normalHypothesisDirective.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution
        (.expression
          [.symbol "exec",
            .expression
              [.symbol "00", .symbol "mm-normal-hypothesis-step"],
            .var "self-input", .var "self-output"]) = some captured)
    (extracts : extractRawExecFact captured = some raw) :
    raw ∈ normalProofMachineRawFacts := by
  have rowMember' : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalHypothesisDirective.atom ::
          space.erase normalHypothesisDirective.atom)
        (.compat (mkPattern
          [(.expression
              [.symbol "exec",
                .expression
                  [.symbol "00", .symbol "mm-normal-hypothesis-step"],
                .var "self-input", .var "self-output"] : Atom),
           .expression
              [.symbol "mm-normal-control", .var "scope", .var "proof",
                .var "pc", .var "top"],
           .expression
              [.symbol "mm-linked-row",
                MM2DataEncoding.stringAtom "normal-proof-label",
                .var "proof", .var "pc", .var "next-pc", .var "label"],
           .expression
              [.symbol "mm-hypothesis-lookup", .var "scope", .var "label",
                .var "formula"],
           .expression
              [.symbol "mm-index-successor", .var "proof", .var "top",
                .var "next-top"]]))).map Prod.fst := by
    change substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalHypothesisDirective.atom ::
          space.erase normalHypothesisDirective.atom)
        normalHypothesisDirective.rule.input).map Prod.fst
    exact rowMember
  obtain ⟨afterFirst, firstAtom, firstMember, firstMatched, finalExtends⟩ :=
    cmatchInputSpec_first_match_chain rowMember'
  rw [Conformance.cmatchAtom_eq_matchAtom] at firstMatched
  obtain ⟨input, output, firstEq, inputLookup, outputLookup⟩ :=
    matchAtom_normalHypothesis_self firstMatched
  have finalInputLookup : substitution.lookup "self-input" = some input :=
    finalExtends "self-input" input inputLookup
  have finalOutputLookup : substitution.lookup "self-output" = some output :=
    finalExtends "self-output" output outputLookup
  have applied :
      applySubst substitution
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "00", .symbol "mm-normal-hypothesis-step"],
              .var "self-input", .var "self-output"]) = captured := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · exact Option.some.inj instantiates
    · simp at instantiates
  have appliedFirst :
      applySubst substitution
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "00", .symbol "mm-normal-hypothesis-step"],
              .var "self-input", .var "self-output"]) = firstAtom := by
    rw [firstEq]
    change
      Atom.expression
          [.symbol "exec",
            .expression
              [.symbol "00", .symbol "mm-normal-hypothesis-step"],
            (substitution.lookup "self-input").getD (.var "self-input"),
            (substitution.lookup "self-output").getD (.var "self-output")] =
        Atom.expression
          [.symbol "exec",
            .expression
              [.symbol "00", .symbol "mm-normal-hypothesis-step"],
            input, output]
    rw [finalInputLookup, finalOutputLookup]
    rfl
  have capturedEq : captured = firstAtom := applied.symm.trans appliedFirst
  rw [capturedEq] at extracts
  rcases List.mem_cons.mp firstMember with selected | prior
  · rw [selected] at extracts
    exact List.mem_filterMap.mpr
      ⟨normalHypothesisDirective.atom,
        by simp [normalHypothesisDirective, normalProofMachineRules],
        extracts⟩
  · apply authoredNormalVerifierRawFact_mem_normal_of_loc_mem
    · apply state.1 raw
      exact List.mem_filterMap.mpr
        ⟨firstAtom, List.mem_of_mem_erase prior, extracts⟩
    · rw [firstEq] at extracts
      simp only [extractRawExecFact] at extracts
      injection extracts with rawEqual
      subst raw
      change (.expression
        [.symbol "00", .symbol "mm-normal-hypothesis-step"] : Atom) ∈
          normalProofMachineRawFacts.map RawExecFact.loc
      decide +kernel

/-- Hypothesis-step additions preserve the executable whitelist: its only
executable output is the exact persistent self shell. -/
theorem normalHypothesis_additions_raw_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalHypothesisDirective.atom ::
        space.erase normalHypothesisDirective.atom)
      normalHypothesisDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalHypothesisDirective.rule.tmpl := by
  dsimp only
  intro atom added raw extracts
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression [.symbol "00", .symbol "mm-normal-hypothesis-step"],
          .var "self-input", .var "self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-normal-control", .var "scope", .var "proof",
          .var "pc", .var "top"]),
     Sink.add
      (.expression
        [.symbol "mm-normal-control", .var "scope", .var "proof",
          .var "next-pc", .var "next-top"]),
     Sink.add
      (.expression
        [.symbol "mm-stack-cell", .var "proof", .var "top",
          .var "formula", .var "pc"])] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "00", .symbol "mm-normal-hypothesis-step"],
              .var "self-input", .var "self-output"] : Atom) ∨
        authored =
          .expression
            [.symbol "mm-normal-control", .var "scope", .var "proof",
              .var "next-pc", .var "next-top"] ∨
        authored =
          .expression
            [.symbol "mm-stack-cell", .var "proof", .var "top",
              .var "formula", .var "pc"] := by
    simpa using sinkMember
  rcases authoredCases with self | nextControl | stack
  · rw [self] at instantiates
    exact normalHypothesis_captured_self_raw_authorized state rowMember
      instantiates extracts
  · rw [nextControl] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_raw_impossible rfl
      instantiates extracts)
  · rw [stack] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_raw_impossible rfl
      instantiates extracts)

/-- Hypothesis-step additions also preserve the protected inert-row
invariant. -/
theorem normalHypothesis_additions_internal_closed
    {space : List Atom} (_state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalHypothesisDirective.atom ::
        space.erase normalHypothesisDirective.atom)
      normalHypothesisDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalHypothesisDirective.rule.tmpl := by
  dsimp only
  intro atom added
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, _rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression [.symbol "00", .symbol "mm-normal-hypothesis-step"],
          .var "self-input", .var "self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-normal-control", .var "scope", .var "proof",
          .var "pc", .var "top"]),
     Sink.add
      (.expression
        [.symbol "mm-normal-control", .var "scope", .var "proof",
          .var "next-pc", .var "next-top"]),
     Sink.add
      (.expression
        [.symbol "mm-stack-cell", .var "proof", .var "top",
          .var "formula", .var "pc"])] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "00", .symbol "mm-normal-hypothesis-step"],
              .var "self-input", .var "self-output"] : Atom) ∨
        authored =
          .expression
            [.symbol "mm-normal-control", .var "scope", .var "proof",
              .var "next-pc", .var "next-top"] ∨
        authored =
          .expression
            [.symbol "mm-stack-cell", .var "proof", .var "top",
              .var "formula", .var "pc"] := by
    simpa using sinkMember
  rcases authoredCases with self | nextControl | stack
  · rw [self] at instantiates
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · have applied := Option.some.inj instantiates
      have atomShape :
          ∃ input output,
            atom =
              .expression
                [.symbol "exec",
                  .expression
                    [.symbol "00", .symbol "mm-normal-hypothesis-step"],
                  input, output] := ⟨_, _, applied.symm⟩
      rcases atomShape with ⟨input, output, rfl⟩
      simp [isVerifierOwnedInternalRowShape,
        isVerifierOwnedInternalNamespace] at internalShape
    · simp at instantiates
  · rw [nextControl] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_internal_impossible rfl
      instantiates internalShape)
  · rw [stack] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_internal_impossible rfl
      instantiates internalShape)

theorem normalHypothesis_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalHypothesisDirective.atom ::
        space.erase normalHypothesisDirective.atom)
      normalHypothesisDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalHypothesisDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalHypothesisDirective.rule.tmpl := by
  exact ⟨normalHypothesis_additions_raw_closed state,
    normalHypothesis_additions_internal_closed state⟩

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
      normalAssertionPopDirective.rule.tmpl := by
  dsimp only
  intro atom added raw extracts
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression [.symbol "02", .symbol "mm-normal-assertion-pop"],
          .var "self-input", .var "self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-assertion-pop", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label",
          .var "hyp-cursor", .var "stack-cursor"]),
     Sink.add
      (.expression
        [.symbol "mm-assertion-pop", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label",
          .var "previous-hyp", .var "previous-stack"])] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "02", .symbol "mm-normal-assertion-pop"],
              .var "self-input", .var "self-output"] : Atom) ∨
        authored =
          .expression
            [.symbol "mm-assertion-pop", .var "scope", .var "proof",
              .var "pc", .var "next-pc", .var "label",
              .var "previous-hyp", .var "previous-stack"] := by
    simpa using sinkMember
  rcases authoredCases with self | previous
  · rw [self] at instantiates
    exact normalPersistent_captured_self_raw_authorized
      (priority := "02") (name := "mm-normal-assertion-pop")
      (directive := normalAssertionPopDirective)
      (rest :=
        [.expression
            [.symbol "mm-assertion-pop", .var "scope", .var "proof",
              .var "pc", .var "next-pc", .var "label",
              .var "hyp-cursor", .var "stack-cursor"],
         .expression
            [.symbol "mm-assertion-hypothesis-successor", .var "scope",
              .var "label", .var "previous-hyp", .var "hyp-cursor"],
         .expression
            [.symbol "mm-index-successor", .var "proof",
              .var "previous-stack", .var "stack-cursor"]])
      state
      (by decide +kernel)
      (by
        change normalAssertionPopRule ∈ normalProofMachineRules
        simp [normalProofMachineRules])
      (by rfl) rowMember
      (by simpa [normalPersistentSelfTemplate] using instantiates) extracts
  · rw [previous] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_raw_impossible rfl
      instantiates extracts)

theorem normalAssertionPop_additions_internal_closed
    {space : List Atom} (_state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalAssertionPopDirective.atom ::
        space.erase normalAssertionPopDirective.atom)
      normalAssertionPopDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalAssertionPopDirective.rule.tmpl := by
  dsimp only
  intro atom added
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, _rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression [.symbol "02", .symbol "mm-normal-assertion-pop"],
          .var "self-input", .var "self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-assertion-pop", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label",
          .var "hyp-cursor", .var "stack-cursor"]),
     Sink.add
      (.expression
        [.symbol "mm-assertion-pop", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label",
          .var "previous-hyp", .var "previous-stack"])] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "02", .symbol "mm-normal-assertion-pop"],
              .var "self-input", .var "self-output"] : Atom) ∨
        authored =
          .expression
            [.symbol "mm-assertion-pop", .var "scope", .var "proof",
              .var "pc", .var "next-pc", .var "label",
              .var "previous-hyp", .var "previous-stack"] := by
    simpa using sinkMember
  rcases authoredCases with self | previous
  · rw [self] at instantiates
    exact False.elim (normalPersistent_self_internal_impossible
      (priority := "02") (name := "mm-normal-assertion-pop")
      (by simpa [normalPersistentSelfTemplate] using instantiates)
      internalShape)
  · rw [previous] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_internal_impossible rfl
      instantiates internalShape)

theorem normalAssertionPop_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalAssertionPopDirective.atom ::
        space.erase normalAssertionPopDirective.atom)
      normalAssertionPopDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalAssertionPopDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalAssertionPopDirective.rule.tmpl := by
  exact ⟨normalAssertionPop_additions_raw_closed state,
    normalAssertionPop_additions_internal_closed state⟩

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
      normalAssertionFloatingDirective.rule.tmpl := by
  dsimp only
  intro atom added raw extracts
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression
            [.symbol "04", .symbol "mm-normal-assertion-floating"],
          .var "self-input", .var "self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-assertion-bind", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label",
          .var "hyp-position", .var "hyp-end",
          .var "stack-position", .var "stack-base"]),
     Sink.remove
      (.expression
        [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
          .expression
            [.symbol "mm-formula", .var "typecode", .var "body"],
          .var "child-occurrence"]),
     Sink.add
      (.expression
        [.symbol "mm-assertion-bind", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label",
          .var "next-hyp-position", .var "hyp-end",
          .var "next-stack-position", .var "stack-base"]),
     Sink.add
      (.expression
        [.symbol "mm-substitution", .var "proof", .var "pc",
          .var "variable-name", .var "body"]),
     Sink.add
      (.expression
        [.symbol "mm-assertion-child", .var "proof", .var "pc",
          .var "hyp-position", .var "child-occurrence"])] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "04", .symbol "mm-normal-assertion-floating"],
              .var "self-input", .var "self-output"] : Atom) ∨
        authored =
          .expression
            [.symbol "mm-assertion-bind", .var "scope", .var "proof",
              .var "pc", .var "next-pc", .var "label",
              .var "next-hyp-position", .var "hyp-end",
              .var "next-stack-position", .var "stack-base"] ∨
        authored =
          .expression
            [.symbol "mm-substitution", .var "proof", .var "pc",
              .var "variable-name", .var "body"] ∨
        authored =
          .expression
            [.symbol "mm-assertion-child", .var "proof", .var "pc",
              .var "hyp-position", .var "child-occurrence"] := by
    simpa using sinkMember
  rcases authoredCases with self | nextBind | substitutionRow | child
  · rw [self] at instantiates
    exact normalPersistent_captured_self_raw_authorized
      (priority := "04") (name := "mm-normal-assertion-floating")
      (directive := normalAssertionFloatingDirective)
      (rest :=
        [.expression
            [.symbol "mm-assertion-bind", .var "scope", .var "proof",
              .var "pc", .var "next-pc", .var "label",
              .var "hyp-position", .var "hyp-end",
              .var "stack-position", .var "stack-base"],
         .expression
            [.symbol "mm-assertion-hypothesis", .var "scope", .var "label",
              .var "hyp-position",
              .expression
                [.symbol "mm-floating", .var "hyp-label", .var "typecode",
                  .var "variable-name"]],
         .expression
            [.symbol "mm-assertion-hypothesis-successor", .var "scope",
              .var "label", .var "hyp-position", .var "next-hyp-position"],
         .expression
            [.symbol "mm-index-successor", .var "proof",
              .var "stack-position", .var "next-stack-position"],
         .expression
            [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
              .expression
                [.symbol "mm-formula", .var "typecode", .var "body"],
              .var "child-occurrence"]])
      state
      (by decide +kernel)
      (by
        change normalAssertionFloatingRule ∈ normalProofMachineRules
        simp [normalProofMachineRules])
      (by rfl) rowMember
      (by simpa [normalPersistentSelfTemplate] using instantiates) extracts
  · rw [nextBind] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_raw_impossible rfl
      instantiates extracts)
  · rw [substitutionRow] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_raw_impossible rfl
      instantiates extracts)
  · rw [child] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_raw_impossible rfl
      instantiates extracts)

theorem normalAssertionFloating_additions_internal_closed
    {space : List Atom} (_state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalAssertionFloatingDirective.atom ::
        space.erase normalAssertionFloatingDirective.atom)
      normalAssertionFloatingDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalAssertionFloatingDirective.rule.tmpl := by
  dsimp only
  intro atom added
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, _rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression
            [.symbol "04", .symbol "mm-normal-assertion-floating"],
          .var "self-input", .var "self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-assertion-bind", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label",
          .var "hyp-position", .var "hyp-end",
          .var "stack-position", .var "stack-base"]),
     Sink.remove
      (.expression
        [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
          .expression
            [.symbol "mm-formula", .var "typecode", .var "body"],
          .var "child-occurrence"]),
     Sink.add
      (.expression
        [.symbol "mm-assertion-bind", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label",
          .var "next-hyp-position", .var "hyp-end",
          .var "next-stack-position", .var "stack-base"]),
     Sink.add
      (.expression
        [.symbol "mm-substitution", .var "proof", .var "pc",
          .var "variable-name", .var "body"]),
     Sink.add
      (.expression
        [.symbol "mm-assertion-child", .var "proof", .var "pc",
          .var "hyp-position", .var "child-occurrence"])] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "04", .symbol "mm-normal-assertion-floating"],
              .var "self-input", .var "self-output"] : Atom) ∨
        authored =
          .expression
            [.symbol "mm-assertion-bind", .var "scope", .var "proof",
              .var "pc", .var "next-pc", .var "label",
              .var "next-hyp-position", .var "hyp-end",
              .var "next-stack-position", .var "stack-base"] ∨
        authored =
          .expression
            [.symbol "mm-substitution", .var "proof", .var "pc",
              .var "variable-name", .var "body"] ∨
        authored =
          .expression
            [.symbol "mm-assertion-child", .var "proof", .var "pc",
              .var "hyp-position", .var "child-occurrence"] := by
    simpa using sinkMember
  rcases authoredCases with self | nextBind | substitutionRow | child
  · rw [self] at instantiates
    exact False.elim (normalPersistent_self_internal_impossible
      (priority := "04") (name := "mm-normal-assertion-floating")
      (by simpa [normalPersistentSelfTemplate] using instantiates)
      internalShape)
  · rw [nextBind] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_internal_impossible rfl
      instantiates internalShape)
  · rw [substitutionRow] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_internal_impossible rfl
      instantiates internalShape)
  · rw [child] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_internal_impossible rfl
      instantiates internalShape)

theorem normalAssertionFloating_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalAssertionFloatingDirective.atom ::
        space.erase normalAssertionFloatingDirective.atom)
      normalAssertionFloatingDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalAssertionFloatingDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalAssertionFloatingDirective.rule.tmpl := by
  exact ⟨normalAssertionFloating_additions_raw_closed state,
    normalAssertionFloating_additions_internal_closed state⟩

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

theorem normalBodyMatchNil_additions_raw_closed
    {space : List Atom}
    (state : NormalBodyContinuationCapabilities space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyMatchNilDirective.atom ::
        space.erase normalBodyMatchNilDirective.atom)
      normalBodyMatchNilDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalBodyMatchNilDirective.rule.tmpl := by
  dsimp only
  intro atom added raw extracts
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.remove normalBodyMatchNilCarrierPattern,
     Sink.add (.var "continuation"),
     Sink.add
       (.expression
         [.symbol "mm-reload-body-match", .var "proof", .var "pc"])]
    at sinkMember
  have authoredCases :
      authored = (.var "continuation" : Atom) ∨
        authored =
          .expression
            [.symbol "mm-reload-body-match", .var "proof", .var "pc"] := by
    simpa using sinkMember
  rcases authoredCases with continuationSink | reloadSink
  · rw [continuationSink] at instantiates
    obtain ⟨carrier, carrierMember, capture⟩ :=
      normalBodyMatchNil_continuation_origin rowMember instantiates
    exact (state carrier carrierMember atom capture).1 raw extracts
  · rw [reloadSink] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_raw_impossible rfl
      instantiates extracts)

theorem normalBodyMatchNil_additions_internal_closed
    {space : List Atom}
    (state : NormalBodyContinuationCapabilities space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyMatchNilDirective.atom ::
        space.erase normalBodyMatchNilDirective.atom)
      normalBodyMatchNilDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalBodyMatchNilDirective.rule.tmpl := by
  dsimp only
  intro atom added
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.remove normalBodyMatchNilCarrierPattern,
     Sink.add (.var "continuation"),
     Sink.add
       (.expression
         [.symbol "mm-reload-body-match", .var "proof", .var "pc"])]
    at sinkMember
  have authoredCases :
      authored = (.var "continuation" : Atom) ∨
        authored =
          .expression
            [.symbol "mm-reload-body-match", .var "proof", .var "pc"] := by
    simpa using sinkMember
  rcases authoredCases with continuationSink | reloadSink
  · rw [continuationSink] at instantiates
    obtain ⟨carrier, carrierMember, capture⟩ :=
      normalBodyMatchNil_continuation_origin rowMember instantiates
    exact (state carrier carrierMember atom capture).2 internalShape
  · rw [reloadSink] at instantiates
    exact False.elim (normalOwnedSafeInstantiation_internal_impossible rfl
      instantiates internalShape)

/-- Under the source-derived capability invariant, the final body matcher
preserves both executable provenance and protected internal-row integrity. -/
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
