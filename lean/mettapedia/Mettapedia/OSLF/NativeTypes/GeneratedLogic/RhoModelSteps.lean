import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelEquality

/-!
# ρ's runtime model: its rules fire where the plan fires

The model language (`RhoModel.language`) reads ρ's rules as the plan reads them: at a closed process sorted in the
plan's sorting, matching syntactically, substituting by ρ's reflective substitution. Its steps are the plan's
firings, up to the order of a bag's members:

- **A firing of the plan at the root of a bag is a COMM of the model** (`rootFiring_step`): an input and an output on
  one channel, the residue in order, and the reflective substitution, which on well-sorted bodies is ρ's semantic
  substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel

open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep (StepAt PremisesAt PremiseAt)
open Mettapedia.OSLF.MeTTaIL.Complete.RhoPresented (rules_zipIdx rule_at bare_rule)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectionExtension (rhoReflectionProfile)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRuleUsing)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (rhoBasePremises rho_input_wellSorted_inv
  rho_output_wellSorted_inv)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness (commBindingsAt apply_commBindingsAt
  rho_parallel_wellSorted_inv closed_member)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping (procListWellSorted_iff_forall_mem)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus (semanticCommSubst)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (rhoParCong_no_substitutionPresentation)
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence GeneralTypedSites

/-- One step of the model's rules, at a bounded depth of contexts. -/
abbrev Step (fuel : ℕ) : Pattern → Pattern → Prop := StepAt interpretation rhoBasePremises language fuel

/-! ## COMM matched syntactically -/

theorem comm_rule_mem : rhoCommRewrite ∈ language.rewrites := by simp [rewrites_eq]

theorem parCong_rule_mem : rhoParCongRewrite ∈ language.rewrites := by simp [rewrites_eq]

/-- **COMM matches an input and an output on one channel, at any two positions.** -/
theorem comm_matches {elements : List Pattern} {inputIndex outputIndex : ℕ}
    (inputBound : inputIndex < elements.length) (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
    {channel body payload : Pattern} {binder : Option String}
    (inputEq : elements[inputIndex] = .apply "PInput" [channel, .lambda binder body])
    (outputEq : (elements.eraseIdx inputIndex)[outputIndex] = .apply "POutput" [channel, payload]) :
    commBindingsAt elements inputIndex outputIndex channel body payload ∈
      matchPattern rhoCommRewrite.left (.collection .hashBag elements none) := by
  rw [matchPattern_iff_matchRel]
  apply MatchRel.collection (by decide)
  refine MatchBagRel.cons (hb := [("p", body), ("n", channel)])
    (restB := [("rest", .collection .hashBag ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none),
      ("q", payload), ("n", channel)]) inputIndex inputBound ?_ ?_ ?_
  · rw [inputEq]
    exact .apply (.cons .fvar (.cons (.lambda .fvar) .nil rfl) rfl) rfl
  · refine MatchBagRel.cons (hb := [("q", payload), ("n", channel)])
      (restB := [("rest", .collection .hashBag ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none)])
      outputIndex outputBound ?_ .nilRest ?_
    · rw [outputEq]
      exact .apply (.cons .fvar (.cons .fvar .nil rfl) rfl) rfl
    · simp [mergeBindings]
  · simp [commBindingsAt, mergeBindings]


/-! ## A root firing is a COMM -/

theorem sorted_of_plan {term : Pattern}
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] proc term) : sorted term = true :=
  sorted_iff.mpr ((GeneralPlanEnvironment.typing_iff plan [] proc term).mp typed)

theorem plan_of_sorted {term : Pattern} (typed : sorted term = true) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] proc term :=
  (GeneralPlanEnvironment.typing_iff plan [] proc term).mpr (sorted_iff.mp typed)

/-- **A firing of the plan at the root of a sealed bag is a COMM of the model**, with the same target. -/
theorem rootFiring_step {source : Pattern} {index : ℕ} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event} {target : Pattern}
    (safe : sealed source = true)
    (fired : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] proc source index trace captured
      completed history target) :
    Step 1 source target := by
  cases fired with
  | @fire _ _ _ _ _ rule spec _ _ _ _ ruleFound specFound _ sourceSorted matched _ premises reduct _ =>
    have zero : index = 0 := by
      rw [Complete.RhoPresented.rewrites_eq] at ruleFound
      cases index with
      | zero => rfl
      | succ => simp at ruleFound
    subst zero
    obtain ⟨_, rfl, rfl⟩ := rule_at (declaration := GeneralRho.declaration) (by rw [rules_zipIdx]; exact .head _)
      ruleFound specFound
    have typed := Complete.RhoReference.procWellSorted_of_sorted sourceSorted
    have noPremises : GeneralRho.comm.premises = [] := rfl
    rw [noPremises] at premises
    cases premises
    obtain ⟨elements, inputIndex, outputIndex, channel, display, body, payload, rfl, inputAt, outputAt,
      _, capturedEq, _, _, _, residueSafe⟩ := GeneralRho.DepthOne.traced_comm_inv matched
    rw [capturedEq] at reduct
    obtain ⟨_, elementsTyped⟩ := rho_parallel_wellSorted_inv typed
    have inputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ (List.mem_of_getElem? inputAt)
    obtain ⟨rfl, _, bodyTyped⟩ := rho_input_wellSorted_inv inputTyped
    have outputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _
      (List.mem_of_mem_eraseIdx (List.mem_of_getElem? outputAt))
    obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outputTyped
    have semantic := GeneralRho.reflective_reduct_semantic (channel := channel) bodyTyped payloadTyped residueSafe
    have localTarget := Option.some.inj (reduct.symm.trans semantic)
    subst localTarget
    obtain ⟨inputBound, inputEq⟩ := List.getElem?_eq_some_iff.mp inputAt
    obtain ⟨outputBound, outputEq⟩ := List.getElem?_eq_some_iff.mp outputAt
    refine StepAt.rule (rule := rhoCommRewrite)
      (initialBindings := commBindingsAt elements inputIndex outputIndex channel body payload)
      (finalBindings := commBindingsAt elements inputIndex outputIndex channel body payload)
      comm_rule_mem ?_ (PremisesAt.nil _) ?_
    · show _ ∈ (if carrier (.collection .hashBag elements none) then _ else [])
      rw [if_pos (by simp [carrier, sorted_of_plan sourceSorted, safe])]
      exact comm_matches inputBound outputBound inputEq outputEq
    · exact apply_commBindingsAt bodyTyped payloadTyped elements inputIndex outputIndex channel


/-! ## A firing inside a bag is a congruence -/

/-- A member of a sorted bag is sorted. -/
theorem sorted_member {elements : List Pattern} {member : Pattern}
    (typed : sorted (.collection .hashBag elements none) = true) (found : member ∈ elements) : sorted member = true := by
  have rho := Complete.RhoReference.procWellSorted_of_sorted (plan_of_sorted typed)
  obtain ⟨_, elementsTyped⟩ := rho_parallel_wellSorted_inv rho
  have memberTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ found
  exact sorted_of_plan ((GeneralPlanEnvironment.typing_iff plan [] proc _).mpr
    (GeneralRho.derived_process_open memberTyped))

/-- A member of a sealed bag is sealed. -/
theorem sealed_member {elements : List Pattern} {member : Pattern}
    (safe : sealed (.collection .hashBag elements none) = true) (found : member ∈ elements) : sealed member = true := by
  simp only [sealed, ScopedPattern.binderSafeAt] at safe ⊢
  induction elements with
  | nil => cases found
  | cons head tail ih =>
    simp only [ScopedPattern.binderSafeListAt, Bool.and_eq_true] at safe
    rcases List.mem_cons.mp found with rfl | found
    · exact safe.1
    · exact ih safe.2 found

/-- A member of a bag of ρ's carrier is in it. -/
theorem carrier_member {elements : List Pattern} {member : Pattern}
    (admitted : carrier (.collection .hashBag elements none) = true) (found : member ∈ elements) :
    carrier member = true := by
  simp only [carrier, Bool.and_eq_true] at admitted ⊢
  exact ⟨sorted_member admitted.1 found, sealed_member admitted.2 found⟩

/-- **ParCong steps a member of a bag**, writing its step in front. -/
theorem parCong_step {elements : List Pattern} {index : ℕ} (bound : index < elements.length) {fuel : ℕ}
    {target : Pattern} (typed : carrier (.collection .hashBag elements none) = true)
    (step : Step fuel elements[index] target) :
    Step (fuel + 1) (.collection .hashBag elements none) (.collection .hashBag (target :: elements.eraseIdx index) none) := by
  refine StepAt.rule (rule := rhoParCongRewrite)
    (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx index) none), ("S", elements[index])])
    (finalBindings := [("T", target), ("rest", .collection .hashBag (elements.eraseIdx index) none),
      ("S", elements[index])])
    parCong_rule_mem ?_ ?_ ?_
  · show _ ∈ (if carrier (.collection .hashBag elements none) then _ else [])
    rw [if_pos typed, matchPattern_iff_matchRel]
    exact .collection (by decide) (.cons index bound .fvar .nilRest rfl)
  · refine PremisesAt.cons (PremiseAt.congruence (candidate := target) (premiseBindings := [("T", target)]) ?_ ?_ rfl)
      (PremisesAt.nil _)
    · simpa [applyBindings] using step
    · simp [matchPattern]
  · show applyBindingsForRuleUsing rhoReflectionProfile rhoParCongRewrite _ = _
    rw [applyBindingsForRuleUsing, rhoParCong_no_substitutionPresentation, applyRuleBindings,
      applyBindingsScoped_zero_of_binderFree _ _ _ (by decide)]
    simp [rhoParCongRewrite, applyBindings]

/-- **Every firing of the plan is a step of the model**, up to the order of a bag's members: a firing at the root is a
COMM, one inside a member of a bag is ParCong around the member's step. -/
theorem licensed_step {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      plan.permissions.sites bound expected source site) :
    bound = [] → expected = proc → carrier source = true →
      ∀ {index : ℕ} {trace : List GeneralScopedMatchMachine.BagChoice}
        {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event} {localTarget : Pattern},
        GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) site.focusBound site.focusType site.focus index
          trace captured completed history localTarget →
        ∃ target fuel, Step fuel source target ∧ Relation.EqvGen Move target (site.context.fill localTarget) := by
  induction licensed with
  | here _ _ _ =>
    intro closed procType admitted _ _ _ _ _ _ fired
    subst closed procType
    exact ⟨_, 1, rootFiring_step (Bool.and_eq_true_iff.mp admitted).2 fired, .refl _⟩
  | application _ _ _ _ _ _ _ permitted _ _ =>
    intro _ _ _
    change GeneralRho.Standard.sites.allConstructorArguments = true ∨ _ ∈ GeneralRho.Standard.sites.constructorArguments
      at permitted
    simp [GeneralRho.Standard.sites] at permitted
  | lambda enabled _ _ =>
    intro _ _ _
    change GeneralRho.Standard.sites.underLambda = true at enabled
    simp [GeneralRho.Standard.sites] at enabled
  | multiLambda enabled _ _ =>
    intro _ _ _
    change GeneralRho.Standard.sites.underMultiLambda = true at enabled
    simp [GeneralRho.Standard.sites] at enabled
  | directCollection _ _ _ _ _ _ =>
    intro _ procType
    cases procType
  | @authoredCollection bound rule declarationIndex parameterName kind elements index element elementType inner
      declared shape permitted elementsTyped objects selected _ ih =>
    intro closed _ typed _ _ _ _ _ _ fired
    obtain ⟨_, rfl, rfl⟩ := bare_rule (List.fst_mem_of_mem_zipIdx declared)
      ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2
    obtain ⟨bound', elementEq⟩ := List.getElem?_eq_some_iff.mp selected
    subst elementEq
    obtain ⟨target, fuel, step, related⟩ := ih closed rfl (carrier_member typed (List.getElem_mem bound')) fired
    refine ⟨_, fuel + 1, parCong_step bound' typed step, ?_⟩
    have inside := equiv_fill (.collection .hashBag [] .hole (elements.eraseIdx index) none) related
    simp only [OneHoleContext.fill, List.nil_append] at inside
    refine .trans _ _ _ inside (bag_perm ?_)
    rw [eraseIdx_eq index]
    exact List.perm_middle.symm


/-! ## A COMM is a firing of the plan -/

/-- **The shape of a syntactic COMM match**: an input and an output on one channel, and the residue in order. -/
theorem comm_shape {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern rhoCommRewrite.left source) :
    ∃ (elements : List Pattern) (termRest : Option String) (inputIndex : ℕ) (inputBound : inputIndex < elements.length)
      (outputIndex : ℕ) (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
      (channel body : Pattern) (binder : Option String) (payload : Pattern),
      source = .collection .hashBag elements termRest ∧
      elements[inputIndex] = .apply "PInput" [channel, .lambda binder body] ∧
      (elements.eraseIdx inputIndex)[outputIndex] = .apply "POutput" [channel, payload] ∧
      bindings = commBindingsAt elements inputIndex outputIndex channel body payload := by
  rw [matchPattern_iff_matchRel] at matched
  obtain ⟨elements, termRest, rfl, bagMatch⟩ := collection_inv (by decide) matched
  cases bagMatch with
  | cons inputIndex inputBound inputMatch tailMatch mergeAll =>
    obtain ⟨inputArguments, inputEq, inputArgumentsMatch⟩ := apply_inv inputMatch
    cases inputArgumentsMatch with
    | cons channelMatch inputRest mergeInput =>
      cases channelMatch
      cases inputRest with
      | cons lambdaMatch noMore mergeLambda =>
        cases noMore
        cases lambdaMatch with
        | lambda bodyMatch =>
          cases bodyMatch
          cases tailMatch with
          | cons outputIndex outputBound outputMatch restMatch mergeTail =>
            obtain ⟨outputArguments, outputEq, outputArgumentsMatch⟩ := apply_inv outputMatch
            cases outputArgumentsMatch with
            | cons outputChannelMatch outputRest mergeOutput =>
              cases outputChannelMatch
              cases outputRest with
              | cons payloadMatch noMoreOutput mergePayload =>
                cases noMoreOutput
                cases payloadMatch
                cases restMatch
                simp [mergeBindings] at mergeLambda
                subst mergeLambda
                simp [mergeBindings] at mergePayload
                subst mergePayload
                simp [mergeBindings] at mergeInput
                subst mergeInput
                simp [mergeBindings] at mergeOutput
                subst mergeOutput
                simp [mergeBindings] at mergeTail
                subst mergeTail
                simp [mergeBindings] at mergeAll
                obtain ⟨sameChannel, rfl⟩ := mergeAll
                subst sameChannel
                exact ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound, _, _, _, _, rfl, inputEq,
                  outputEq, rfl⟩


open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax (ProcWellSorted ProcListWellSorted) in
open Mettapedia.GSLT.Examples.ScopedRhoBinding (scopedCommBindingSpec) in
/-- **A COMM at any two positions of a bag of ρ's carrier is a firing of the plan at the root**, with the target of
ρ's reflective substitution. -/
theorem comm_receipt {elements : List Pattern} {inputIndex outputIndex : ℕ}
    (inputBound : inputIndex < elements.length) (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
    {channel body payload : Pattern} {binder : Option String}
    (inputEq : elements[inputIndex] = .apply "PInput" [channel, .lambda binder body])
    (outputEq : (elements.eraseIdx inputIndex)[outputIndex] = .apply "POutput" [channel, payload])
    (admitted : carrier (.collection .hashBag elements none) = true) :
    ∃ receipt : GeneralRuleJobs.Receipt,
      GeneralOccurrenceSemantics.Primitive plan [] proc (.collection .hashBag elements none) receipt ∧
        receipt.target = applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
          (commBindingsAt elements inputIndex outputIndex channel body payload) := by
  obtain ⟨sortedSource, safe⟩ := Bool.and_eq_true_iff.mp admitted
  have typed := Complete.RhoReference.procWellSorted_of_sorted (plan_of_sorted sortedSource)
  obtain ⟨_, elementsTyped⟩ := rho_parallel_wellSorted_inv typed
  have inputMember := List.getElem_mem inputBound
  have outputMember := List.mem_of_mem_eraseIdx (List.getElem_mem outputBound)
  have inputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ inputMember
  rw [inputEq] at inputTyped
  obtain ⟨rfl, channelTyped, bodyTyped⟩ := rho_input_wellSorted_inv inputTyped
  have outputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ outputMember
  rw [outputEq] at outputTyped
  obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outputTyped
  have residueMember : ∀ pattern ∈ (elements.eraseIdx inputIndex).eraseIdx outputIndex, pattern ∈ elements :=
    fun _ member => List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member)
  have residueTyped : ProcListWellSorted rhoReflectivePresentation _ []
      ((elements.eraseIdx inputIndex).eraseIdx outputIndex) :=
    procListWellSorted_iff_forall_mem.mpr fun pattern member =>
      procListWellSorted_iff_forall_mem.mp elementsTyped pattern (residueMember pattern member)
  have channelOpen := GeneralRho.derived_name_open channelTyped
  have bodyOpen := GeneralRho.derived_process_open bodyTyped
  have payloadOpen := GeneralRho.derived_process_open payloadTyped
  have residueOpen := GeneralRho.derived_processes_typed residueTyped
  have residueRepresented := GeneralRho.derived_processes_represented residueTyped
  have sourceOpen := GeneralRho.derived_process_open typed
  have channelSafe : channel.isWellScopedAt 0 = true := channelOpen.1.isWellScopedAt
  have bodySafe : body.isWellScopedAt (0 + 1) = true := bodyOpen.1.isWellScopedAt
  have payloadSafe : payload.isWellScopedAt 0 = true := payloadOpen.1.isWellScopedAt
  have residueSafe := residueOpen.isWellScopedListAt
  have bodySealed : ScopedPattern.binderSafeAt "NQuote" 1 body = true := by
    have memberSafe := (closed_member typed safe inputMember).2
    rw [inputEq] at memberSafe
    simp only [ScopedPattern.binderSafeAt, ScopedPattern.binderSafeListAt] at memberSafe
    simp at memberSafe
    exact memberSafe.2
  have names := GeneralRho.derived_names_admitted bodyTyped bodySealed
  have semantic := GeneralRho.reflective_reduct_semantic (channel := channel) bodyTyped payloadTyped residueSafe
  have literal := GeneralRho.reflective_reduct (ambient := 0) (channel := channel) bodySafe payloadSafe residueSafe
  have bodiesEq : GeneralRho.reflectiveBody body payload = semanticCommSubst body payload := by
    have both := literal.symm.trans semantic
    simp only [Option.some.injEq, Pattern.collection.injEq, List.cons.injEq] at both
    exact both.2.1.1
  have targetBodyOpen := GeneralRho.reflective_body_open bodyOpen bodySealed names payloadOpen
  rw [bodiesEq] at targetBodyOpen
  have targetTyped : HasType GeneralRho.language (GeneralRho.typeFree fun _ => none) []
      (.collection .hashBag (semanticCommSubst body payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex) none)
      (.base "Proc") := GeneralRho.parallel_typed (.cons targetBodyOpen.1 residueOpen)
  have targetRepresented : GeneralRho.Represented
      (.collection .hashBag (semanticCommSubst body payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex) none) :=
    (GeneralRho.represented_collection_iff _ _).mpr fun pattern member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨targetBodyOpen.2.1, targetBodyOpen.2.2.1⟩
      · exact residueRepresented pattern member
  have targetOpen : OpenPatternWellSorted GeneralRho.language (GeneralRho.typeFree fun _ => none) [] (.base "Proc")
      (.collection .hashBag (semanticCommSubst body payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex) none) :=
    ⟨targetTyped, targetRepresented.1, targetRepresented.2, targetTyped.isWellScopedAt⟩
  have position : plan.rules[0]? = some GeneralRho.declaration := by rw [GeneralRho.Standard.compiled_rules]; rfl
  have captureTyped := GeneralRho.captured_typed channelOpen.1 bodyOpen.1 payloadOpen.1 residueOpen
  have captureObjects := GeneralRho.captured_objects (ambient := 0) ⟨channelOpen.2.1, channelOpen.2.2.1⟩
    ⟨bodyOpen.2.1, bodyOpen.2.2.1⟩ ⟨payloadOpen.2.1, payloadOpen.2.2.1⟩ residueRepresented
  have sourceInPlan := (GeneralPlanEnvironment.typing_iff plan [] (.base "Proc") _).mpr sourceOpen
  have firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "Proc")
      (.collection .hashBag elements none) 0
      [{ path := [0], selected := inputIndex }, { path := [1], selected := outputIndex }]
      (GeneralRho.captured 0 channel body payload ((elements.eraseIdx inputIndex).eraseIdx outputIndex))
      (GeneralRho.captured 0 channel body payload ((elements.eraseIdx inputIndex).eraseIdx outputIndex)) []
      (.collection .hashBag (semanticCommSubst body payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex)
        none) := by
    refine .fire (GeneralPlanEnvironment.selected_rule plan position)
      (GeneralPlanEnvironment.selected_specification plan position) GeneralRho.comm_admitted sourceInPlan
      (GeneralRho.DepthOne.comm_matching_at inputBound inputEq outputBound outputEq channelSafe bodySafe payloadSafe
        residueSafe)
      ?_ .nil semantic ((GeneralPlanEnvironment.typing_iff plan _ _ _).mpr targetOpen)
    refine ⟨?_, captureObjects⟩
    intro name value member
    obtain ⟨dependencies, expected, declared, sorted, metadata, ambient, valueTyped⟩ :=
      captureTyped name value member
    exact ⟨dependencies, expected, declared, sorted, metadata, ambient,
      GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar plan).symm valueTyped⟩
  refine ⟨⟨⟨0, GeneralRho.declaration, SiteData.here [] (.base "Proc") (.collection .hashBag elements none)⟩,
    [{ path := [0], selected := inputIndex }, { path := [1], selected := outputIndex }],
    GeneralRho.captured 0 channel body payload ((elements.eraseIdx inputIndex).eraseIdx outputIndex),
    GeneralRho.captured 0 channel body payload ((elements.eraseIdx inputIndex).eraseIdx outputIndex), [],
    .collection .hashBag (semanticCommSubst body payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex) none,
    .collection .hashBag (semanticCommSubst body payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex) none⟩,
    ⟨⟨by rw [GeneralRho.Standard.compiled_rules]; simp, .here rfl sourceInPlan.2.2.1 sourceInPlan.1⟩, firing, rfl, rfl,
      (GeneralPlanEnvironment.typing_iff plan _ _ _).mpr targetOpen⟩, ?_⟩
  exact (apply_commBindingsAt bodyTyped payloadTyped elements inputIndex outputIndex channel).symm


/-! ## A step inside a member is a firing at a bag site -/

open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax (ProcWellSorted ProcListWellSorted) in
theorem sorted_of_rho {term : Pattern} (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] term) :
    sorted term = true :=
  sorted_of_plan ((GeneralPlanEnvironment.typing_iff plan [] proc _).mpr (GeneralRho.derived_process_open typed))

open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax (ProcWellSorted ProcListWellSorted) in
/-- Replacing a member of a sorted bag by a sorted process keeps the bag sorted. -/
theorem bag_replace_sorted {elements : List Pattern} {index : ℕ}
    (typed : sorted (.collection .hashBag elements none) = true) {replacement : Pattern}
    (replacementSorted : sorted replacement = true) :
    sorted (.collection .hashBag (elements.take index ++ replacement :: elements.drop (index + 1)) none) = true := by
  have rho := Complete.RhoReference.procWellSorted_of_sorted (plan_of_sorted typed)
  obtain ⟨_, elementsTyped⟩ := rho_parallel_wellSorted_inv rho
  have replacementTyped := Complete.RhoReference.procWellSorted_of_sorted (plan_of_sorted replacementSorted)
  refine sorted_of_rho (.parallel (procListWellSorted_iff_forall_mem.mpr fun member found => ?_))
  simp only [List.mem_append, List.mem_cons] at found
  rcases found with inTake | rfl | inDrop
  · exact procListWellSorted_iff_forall_mem.mp elementsTyped _ (List.mem_of_mem_take inTake)
  · exact replacementTyped
  · exact procListWellSorted_iff_forall_mem.mp elementsTyped _ (List.mem_of_mem_drop inDrop)

theorem parallel_mem_zipIdx :
    ((rhoCalc.terms[3]'(by decide)), 3) ∈ (GeneralPlanEnvironment.environment plan).language.terms.zipIdx := by
  rw [Complete.RhoPresented.terms_eq]
  exact List.mk_mem_zipIdx_iff_getElem?.mpr rfl

/-- **A firing inside a member of a bag of ρ's carrier is a firing at the member's bag site**, with the member's
target in its place. -/
theorem wrap_receipt {elements : List Pattern} {index : ℕ} (bound : index < elements.length)
    (admitted : carrier (.collection .hashBag elements none) = true) {inner : GeneralRuleJobs.Receipt}
    (fired : GeneralOccurrenceSemantics.Primitive plan [] proc elements[index] inner) :
    ∃ receipt : GeneralRuleJobs.Receipt,
      GeneralOccurrenceSemantics.Primitive plan [] proc (.collection .hashBag elements none) receipt ∧
        receipt.target = .collection .hashBag (elements.take index ++ inner.target :: elements.drop (index + 1)) none := by
  obtain ⟨⟨declared, licensed⟩, firing, accepted, filled, targetTyped⟩ := fired
  have sortedSource := (Bool.and_eq_true_iff.mp admitted).1
  have sourceOpen := plan_of_sorted sortedSource
  have rho := Complete.RhoReference.procWellSorted_of_sorted sourceOpen
  obtain ⟨_, elementsTyped⟩ := rho_parallel_wellSorted_inv rho
  have elementsOpen := GeneralLanguageTyping.elements_transport (GeneralPlanEnvironment.grammar plan).symm
    (GeneralRho.derived_processes_typed elementsTyped)
  have objects : isObjectPatternList elements = true :=
    objectList_iff.mpr (object_collection_iff.mp sourceOpen.2.2.1).2
  refine ⟨⟨⟨inner.job.ordinal, inner.job.declaration,
      inner.job.site.wrapCollection (.authoredCollection 3) .hashBag elements index⟩,
    inner.matcherTrace, inner.captured, inner.completed, inner.premiseHistory, inner.localTarget,
    .collection .hashBag (elements.take index ++ inner.target :: elements.drop (index + 1)) none⟩,
    ⟨⟨declared, .authoredCollection parallel_mem_zipIdx (parameterName := "ps") (by decide) (by decide) elementsOpen
      objects (List.getElem?_eq_getElem bound) licensed⟩, firing, accepted, ?_, ?_⟩, rfl⟩
  · show _ = (SiteData.wrapCollection (.authoredCollection 3) .hashBag elements index inner.job.site).context.fill _
    rw [filled]
    rfl
  · exact plan_of_sorted (bag_replace_sorted sortedSource (sorted_of_plan targetTyped))

/-! ## Every step of the model is a firing of the plan -/

/-- **The shape of a ParCong match**: a member, and the rest in order. -/
theorem parCong_shape {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern rhoParCongRewrite.left source) :
    ∃ (elements : List Pattern) (termRest : Option String) (index : ℕ) (_ : index < elements.length),
      source = .collection .hashBag elements termRest ∧
      bindings = [("rest", .collection .hashBag (elements.eraseIdx index) none), ("S", elements[index])] := by
  rw [matchPattern_iff_matchRel] at matched
  obtain ⟨elements, termRest, rfl, bagMatch⟩ := collection_inv (by decide) matched
  cases bagMatch with
  | cons index bound headMatch restMatch merged =>
    cases headMatch
    cases restMatch
    simp [mergeBindings] at merged
    exact ⟨elements, termRest, index, bound, rfl, merged.symm⟩

theorem parCong_instantiate (target : Pattern) (rest : List Pattern) (selected : Pattern) :
    applyBindingsForRuleUsing rhoReflectionProfile rhoParCongRewrite
        [("T", target), ("rest", .collection .hashBag rest none), ("S", selected)] =
      .collection .hashBag (target :: rest) none := by
  rw [applyBindingsForRuleUsing, rhoParCong_no_substitutionPresentation, applyRuleBindings,
    applyBindingsScoped_zero_of_binderFree _ _ _ (by decide)]
  simp [rhoParCongRewrite, applyBindings]

/-- **Every step of the model is a firing of the plan**, up to the order of a bag's members: a COMM is a firing at
the root, ParCong a firing at the member's bag site. -/
theorem step_receipt : ∀ (fuel : ℕ) {source target : Pattern}, Step fuel source target →
    ∃ receipt : GeneralRuleJobs.Receipt,
      GeneralOccurrenceSemantics.Primitive plan [] proc source receipt ∧ Relation.EqvGen Move receipt.target target
  | 0, _, _, step => by cases step
  | fuel + 1, source, target, step => by
    cases step with
    | rule member matched premises applied =>
      have admitted : carrier source = true := by
        by_contra outside
        simp only [interpretation, outside, if_false] at matched
        cases matched
      change _ ∈ (if carrier source then _ else []) at matched
      rw [if_pos admitted] at matched
      rw [rewrites_eq] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change PremisesAt _ _ _ _ _ [] _ at premises
        cases premises
        obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound, channel, body, binder, payload,
          rfl, inputEq, outputEq, rfl⟩ := comm_shape matched
        have restNone : termRest = none := (object_collection_iff.mp (sorted_iff.mp
          (Bool.and_eq_true_iff.mp admitted).1).2.2.1).1
        subst restNone
        obtain ⟨receipt, fired, targetEq⟩ := comm_receipt inputBound outputBound inputEq outputEq admitted
        refine ⟨receipt, fired, ?_⟩
        rw [targetEq]
        exact applied ▸ .refl _
      · obtain ⟨elements, termRest, index, bound, rfl, rfl⟩ := parCong_shape matched
        have restNone : termRest = none := (object_collection_iff.mp (sorted_iff.mp
          (Bool.and_eq_true_iff.mp admitted).1).2.2.1).1
        subst restNone
        change PremisesAt _ _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons first rest =>
          cases rest
          cases first with
          | congruence recursive targetMatch merged =>
            simp only [applyBindings, List.find?] at recursive
            simp at recursive
            simp [matchPattern] at targetMatch
            subst targetMatch
            simp [mergeBindings] at merged
            subst merged
            obtain ⟨inner, innerFired, innerRelated⟩ := step_receipt fuel recursive
            obtain ⟨receipt, fired, targetEq⟩ := wrap_receipt bound admitted innerFired
            refine ⟨receipt, fired, ?_⟩
            have instantiated : target = .collection .hashBag (_ :: elements.eraseIdx index) none :=
              applied.symm.trans (parCong_instantiate _ _ _)
            rw [targetEq, instantiated]
            have inside := equiv_fill (.collection .hashBag (elements.take index) .hole (elements.drop (index + 1)) none)
              innerRelated
            simp only [OneHoleContext.fill] at inside
            refine .trans _ _ _ inside (bag_perm ?_)
            rw [eraseIdx_eq index]
            exact List.perm_middle


/-! ## Every step of the model is a step of ρ -/

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep rhoRuleInterpretation
  rhoParCong_no_matchingPresentation rhoStep_preserves_closed) in
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness (rhoStepAt_one_comm
  rhoCanonicalEquivalent_iff) in
/-- **Every step of the model is a step of ρ in its own reading**: literally equal channels are canonically
equivalent, and ParCong matches alike. -/
theorem step_rho : ∀ (fuel : ℕ) {source target : Pattern}, Step fuel source target → RhoStep source target
  | 0, _, _, step => by cases step
  | fuel + 1, source, target, step => by
    cases step with
    | rule member matched premises applied =>
      have admitted : carrier source = true := by
        by_contra outside
        simp only [interpretation, outside, if_false] at matched
        cases matched
      change _ ∈ (if carrier source then _ else []) at matched
      rw [if_pos admitted] at matched
      rw [rewrites_eq] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change PremisesAt _ _ _ _ _ [] _ at premises
        cases premises
        obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound, channel, body, binder, payload,
          rfl, inputEq, outputEq, rfl⟩ := comm_shape matched
        have sortedSource := (Bool.and_eq_true_iff.mp admitted).1
        have restNone : termRest = none := (object_collection_iff.mp (sorted_iff.mp sortedSource).2.2.1).1
        subst restNone
        have rho := Complete.RhoReference.procWellSorted_of_sorted (plan_of_sorted sortedSource)
        obtain ⟨_, elementsTyped⟩ := rho_parallel_wellSorted_inv rho
        have inputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ (List.getElem_mem inputBound)
        rw [inputEq] at inputTyped
        obtain ⟨rfl, _, _⟩ := rho_input_wellSorted_inv inputTyped
        exact ⟨1, applied ▸ rhoStepAt_one_comm inputBound outputBound inputEq outputEq
          ((rhoCanonicalEquivalent_iff channel channel).mpr rfl)⟩
      · obtain ⟨elements, termRest, index, bound, rfl, rfl⟩ := parCong_shape matched
        change PremisesAt _ _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons first rest =>
          cases rest
          cases first with
          | congruence recursive targetMatch merged =>
            simp only [applyBindings, List.find?] at recursive
            simp at recursive
            simp [matchPattern] at targetMatch
            subst targetMatch
            simp [mergeBindings] at merged
            subst merged
            rename_i candidate
            refine Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.step_of_single_congruence_rule
              (rule := rhoParCongRewrite) (premiseSource := .fvar "S") (premiseTarget := .fvar "T")
              (candidate := candidate) (premiseBindings := [("T", candidate)])
              (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx index) none), ("S", elements[index])])
              (by simp [rhoCalc]) ?_ rfl ?_ (by simp [matchPattern]) rfl ?_
            · show _ ∈ Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRuleUsing rhoReflectionProfile
                rhoParCongRewrite _
              rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec.matchPatternForRuleUsing_iff_matchRel_of_no_presentation
                  rhoParCong_no_matchingPresentation]
              exact .collection (by decide) (.cons index bound .fvar .nilRest rfl)
            · simpa [applyBindings] using step_rho fuel recursive
            · exact applied

/-- **A step of the model stays in ρ's carrier.** -/
theorem step_carrier {fuel : ℕ} {source target : Pattern} (admitted : carrier source = true)
    (step : Step fuel source target) : carrier target = true := by
  obtain ⟨sortedSource, safe⟩ := Bool.and_eq_true_iff.mp admitted
  have rho := Complete.RhoReference.procWellSorted_of_sorted (plan_of_sorted sortedSource)
  obtain ⟨typed, sealedTarget⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.rhoStep_preserves_closed rho safe
      (step_rho fuel step)
  simp only [carrier, Bool.and_eq_true]
  exact ⟨sorted_of_rho typed, sealedTarget⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel
