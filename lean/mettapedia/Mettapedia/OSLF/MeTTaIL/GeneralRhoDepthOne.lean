import Mettapedia.OSLF.MeTTaIL.GeneralRhoStandardSites
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalCompletion

/-!
# Rho's depth-one step in the GSLT occurrence semantics

A canonical rho process is a sorted bag of components that are neither nil nor
parallel, so every step from it is a COMM at the root of its bag
(`CanonicalStepperCompleteness`). The plan below licenses only the root. On
closed, quotation-sealed sources whose canonically equivalent channels are
equal, its receipts are exactly the authored depth-one steps `RhoStepAt 1`:

- `receipt_step`: every valid receipt is a depth-one step with the same target;
- `step_receipt`: every depth-one step is the target of a valid receipt;
- `step_iff`: the plan's GSLT steps are the depth-one steps.

`traced_comm_inv` reads every match of the COMM left side: an input, then an
output on the same channel among the remaining components, and the residue in
order. Canonical forms (`isCanonical_channelsDecided`) and lexicographic forms
(`LexCanonical.lexCanon_channelsDecided`) decide their channels by equality, so
the literal matcher finds every pair that the rho comparator accepts. Together
with the canonical stepper theorems, a runtime that keeps processes in either
form and fires these receipts is faithful to rho modulo structural congruence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho.DepthOne

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open GeneralScopedMatchMachine
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus (semanticCommSubst)

/-! ## The plan -/

/-- The rho plan whose only reduction context is the root. -/
def permissions : GeneralExecutionAdmission.Permissions :=
  { GeneralRho.permissions with sites := GeneralTypedSites.OperationalPermissions.rootOnly }

def plan : GeneralExecutionAdmission.Plan := GeneralExecutionAdmission.compile snapshot permissions

theorem compiled_rules : plan.rules = [declaration] := GeneralRho.compiled_rules

theorem compilation_has_no_equations : plan.equations = [] := rfl

theorem environment_eq : GeneralPlanEnvironment.environment plan = GeneralPlanEnvironment.environment GeneralRho.plan :=
  rfl

theorem compilation_complete : plan.complete = true := GeneralRho.compilation_complete

theorem stratified :
    GeneralPremise.checkStepStratification (GeneralPlanEnvironment.environment plan).language = true := by
  change GeneralPremise.checkStepStratification
    { GeneralRho.language with rewrites := plan.rules.map GeneralExecutionAdmission.RulePlan.rule } = true
  rw [compiled_rules]
  rfl

/-- Root-only permissions license the root and nothing below it. -/
theorem generate_rootOnly {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {site : GeneralTypedSites.SiteData}
    (generated : site ∈ GeneralTypedSites.generate language free GeneralTypedSites.OperationalPermissions.rootOnly
      bound expected source) :
    site = GeneralTypedSites.SiteData.here bound expected source := by
  rw [GeneralTypedSites.generate.eq_def] at generated
  split at generated
  · rcases List.mem_cons.mp generated with same | below
    · exact same
    · exfalso
      cases source with
      | lambda binder body =>
        cases expected <;> simp [GeneralTypedSites.OperationalPermissions.rootOnly] at below
      | multiLambda arity binders body =>
        cases expected with
        | arrow domain codomain =>
          cases domain <;> simp [GeneralTypedSites.OperationalPermissions.rootOnly] at below
        | _ => simp at below
      | collection kind elements rest =>
        cases rest <;> simp [GeneralTypedSites.OperationalPermissions.rootOnly] at below
      | _ =>
        simp [GeneralTypedSites.OperationalPermissions.rootOnly,
          GeneralTypedSites.OperationalPermissions.permitsArgument] at below
  · simp at generated

/-! ## Matching the COMM left side -/

theorem recover_root_inv {ambient : Nat} {target : Pattern} {value : ContextualValue}
    (recovered : recoverValue? [] ambient 0 [] target = some value) :
    target.isWellScopedAt ambient = true ∧ value = rootValue ambient target := by
  cases safe : target.isWellScopedAt ambient with
  | false => simp [recoverValue?, safe] at recovered
  | true =>
    rw [recover_root safe] at recovered
    exact ⟨rfl, (Option.some.inj recovered).symm⟩

theorem recover_body_inv {ambient : Nat} {target : Pattern} {value : ContextualValue}
    (recovered : recoverValue? [.base "Name"] ambient 1 [.bvar 0] target = some value) :
    target.isWellScopedAt (ambient + 1) = true ∧ value = bodyValue ambient target := by
  cases safe : target.isWellScopedAt (ambient + 1) with
  | false =>
    have unscoped : target.isWellScopedAt (1 + ambient) = false := by rw [Nat.add_comm]; exact safe
    simp [recoverValue?, unscoped] at recovered
  | true =>
    rw [recover_body safe] at recovered
    exact ⟨rfl, (Option.some.inj recovered).symm⟩

theorem rootValue_injective {ambient : Nat} {left right : Pattern}
    (leftSafe : left.isWellScopedAt ambient = true) (rightSafe : right.isWellScopedAt ambient = true)
    (same : rootValue ambient left = rootValue ambient right) : left = right := by
  have leftBack := instantiate_root leftSafe
  rw [same, instantiate_root rightSafe] at leftBack
  exact (Option.some.inj leftBack).symm

theorem dependencies_n : dependencies? scopedCommBindingSpec "n" = some [] := by decide +kernel
theorem dependencies_p : dependencies? scopedCommBindingSpec "p" = some [.base "Name"] := by decide +kernel
theorem dependencies_q : dependencies? scopedCommBindingSpec "q" = some [] := by decide +kernel
theorem dependencies_rest : dependencies? scopedCommBindingSpec "rest" = some [] := by decide +kernel

theorem input_n_arguments : arguments? comm scopedCommBindingSpec "n" .left [0, 0] = some [] := by decide +kernel
theorem input_p_arguments : arguments? comm scopedCommBindingSpec "p" .left [0, 1, 0] = some [.bvar 0] := by
  decide +kernel
theorem output_n_arguments : arguments? comm scopedCommBindingSpec "n" .left [1, 0] = some [] := by decide +kernel
theorem output_q_arguments : arguments? comm scopedCommBindingSpec "q" .left [1, 1] = some [] := by decide +kernel
theorem rest_arguments : arguments? comm scopedCommBindingSpec "rest" .left [2] = some [] := by decide +kernel

/-- The first channel occurrence records a root value. -/
theorem input_n_inv {ambient : Nat} {target : Pattern} {final : Assignment}
    (captured : capture? comm scopedCommBindingSpec ambient 0 .left [0, 0] [] "n" target = some final) :
    target.isWellScopedAt ambient = true ∧ final = [("n", rootValue ambient target)] := by
  simp only [capture?, Option.bind_eq_bind, dependencies_n, input_n_arguments, Option.bind_some] at captured
  cases recovered : recoverValue? [] ambient 0 [] target with
  | none => simp [recovered] at captured
  | some value =>
    obtain ⟨safe, rfl⟩ := recover_root_inv recovered
    simp only [recovered, Option.bind_some, assign, lookup, List.find?_nil, Option.map_none,
      Option.some.injEq] at captured
    exact ⟨safe, captured.symm⟩

/-- The received body records a value under the input's binder. -/
theorem input_p_inv {ambient : Nat} {channel target : Pattern} {final : Assignment}
    (captured : capture? comm scopedCommBindingSpec ambient 1 .left [0, 1, 0]
      [("n", rootValue ambient channel)] "p" target = some final) :
    target.isWellScopedAt (ambient + 1) = true ∧
      final = [("p", bodyValue ambient target), ("n", rootValue ambient channel)] := by
  simp only [capture?, Option.bind_eq_bind, dependencies_p, input_p_arguments, Option.bind_some] at captured
  cases recovered : recoverValue? [.base "Name"] ambient 1 [.bvar 0] target with
  | none => simp [recovered] at captured
  | some value =>
    obtain ⟨safe, rfl⟩ := recover_body_inv recovered
    simp only [recovered, Option.bind_some, assign, lookup] at captured
    simp at captured
    exact ⟨safe, captured.symm⟩

/-- The output's channel must be the input's channel itself. -/
theorem output_n_inv {ambient : Nat} {channel body target : Pattern} {final : Assignment}
    (channelSafe : channel.isWellScopedAt ambient = true)
    (captured : capture? comm scopedCommBindingSpec ambient 0 .left [1, 0]
      [("p", bodyValue ambient body), ("n", rootValue ambient channel)] "n" target = some final) :
    target = channel ∧ final = [("p", bodyValue ambient body), ("n", rootValue ambient channel)] := by
  simp only [capture?, Option.bind_eq_bind, dependencies_n, output_n_arguments, Option.bind_some] at captured
  cases recovered : recoverValue? [] ambient 0 [] target with
  | none => simp [recovered] at captured
  | some value =>
    obtain ⟨safe, rfl⟩ := recover_root_inv recovered
    simp only [recovered, Option.bind_some, assign, lookup] at captured
    simp only [List.find?, beq_iff_eq] at captured
    by_cases same : rootValue ambient channel = rootValue ambient target
    · have equal := rootValue_injective channelSafe safe same
      subst equal
      simp at captured
      exact ⟨rfl, captured.symm⟩
    · simp [same] at captured

/-- The payload records a root value. -/
theorem output_q_inv {ambient : Nat} {channel body target : Pattern} {final : Assignment}
    (captured : capture? comm scopedCommBindingSpec ambient 0 .left [1, 1]
      [("p", bodyValue ambient body), ("n", rootValue ambient channel)] "q" target = some final) :
    target.isWellScopedAt ambient = true ∧
      final = [("q", rootValue ambient target), ("p", bodyValue ambient body), ("n", rootValue ambient channel)] := by
  simp only [capture?, Option.bind_eq_bind, dependencies_q, output_q_arguments, Option.bind_some] at captured
  cases recovered : recoverValue? [] ambient 0 [] target with
  | none => simp [recovered] at captured
  | some value =>
    obtain ⟨safe, rfl⟩ := recover_root_inv recovered
    simp only [recovered, Option.bind_some, assign, lookup] at captured
    simp at captured
    exact ⟨safe, captured.symm⟩

/-- The residue records the unmatched components, in their order. -/
theorem rest_inv {ambient : Nat} {channel body payload : Pattern} {residue : List Pattern} {final : Assignment}
    (recorded : captureRest? comm scopedCommBindingSpec ambient 0 .left [2]
      [("q", rootValue ambient payload), ("p", bodyValue ambient body), ("n", rootValue ambient channel)]
      "rest" .hashBag residue = some final) :
    Pattern.isWellScopedListAt ambient residue = true ∧ final = captured ambient channel body payload residue := by
  simp only [captureRest?, capture?, Option.bind_eq_bind, dependencies_rest, rest_arguments,
    Option.bind_some] at recorded
  cases recovered : recoverValue? [] ambient 0 [] (.collection .hashBag residue none) with
  | none => simp [recovered] at recorded
  | some value =>
    obtain ⟨safe, rfl⟩ := recover_root_inv recovered
    simp only [recovered, Option.bind_some, assign, lookup] at recorded
    simp at recorded
    exact ⟨safe, by rw [← recorded]; rfl⟩

theorem comm_left_shape : comm.left = .collection .hashBag
    [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")], .apply "POutput" [.fvar "n", .fvar "q"]]
    (some "rest") := rfl

/-- **Every COMM match.** A match of the COMM left side selects an input, then an output on the
same channel among the remaining components; the residue keeps everything else in order. -/
theorem traced_comm_inv {ambient : Nat} {source : Pattern} {trace : List BagChoice} {final : Assignment}
    (matched : TracedMatches comm scopedCommBindingSpec ambient .left [] 0 [] comm.left source trace final) :
    ∃ elements inputIndex outputIndex channel display body payload,
      source = .collection .hashBag elements none ∧
      elements[inputIndex]? = some (.apply "PInput" [channel, .lambda display body]) ∧
      (elements.eraseIdx inputIndex)[outputIndex]? = some (output channel payload) ∧
      trace = [{ path := [0], selected := inputIndex }, { path := [1], selected := outputIndex }] ∧
      final = captured ambient channel body payload ((elements.eraseIdx inputIndex).eraseIdx outputIndex) ∧
      channel.isWellScopedAt ambient = true ∧ body.isWellScopedAt (ambient + 1) = true ∧
      payload.isWellScopedAt ambient = true ∧
      Pattern.isWellScopedListAt ambient ((elements.eraseIdx inputIndex).eraseIdx outputIndex) = true := by
  rw [comm_left_shape] at matched
  cases matched with
  | bag notVector bagged =>
    rename_i elements
    cases bagged with
    | cons inputIndex inputBound inputMatched afterInput =>
      rename_i afterInputAssignment inputTrace restTrace
      generalize inputTarget : elements[inputIndex] = inputTerm at inputMatched
      cases inputMatched with
      | constructor inputArguments =>
        rename_i inputTargets
        cases inputArguments with
        | cons channelMatched bodyArguments =>
          rename_i channelTerm bodyTerms channelAssignment channelTrace bodyTrace
          cases channelMatched with
          | capture channelCaptured =>
            cases bodyArguments with
            | cons bodyMatched noMore =>
              rename_i lambdaTerm noTerms bodyAssignment lambdaTrace noTrace
              cases noMore
              cases bodyMatched with
              | binder bodyInner =>
                rename_i bodyDisplay bodyTerm
                cases bodyInner with
                | capture bodyCaptured =>
                  simp only [List.nil_append, List.cons_append] at channelCaptured bodyCaptured
                  obtain ⟨channelSafe, rfl⟩ := input_n_inv channelCaptured
                  obtain ⟨bodySafe, rfl⟩ := input_p_inv bodyCaptured
                  cases afterInput with
                  | cons outputIndex outputBound outputMatched afterOutput =>
                    rename_i afterOutputAssignment outputTrace residueTrace
                    generalize outputTarget : (elements.eraseIdx inputIndex)[outputIndex] = outputTerm
                      at outputMatched
                    cases outputMatched with
                    | constructor outputArguments =>
                      cases outputArguments with
                      | cons outputChannelMatched payloadArguments =>
                        rename_i outputChannel payloadTerms outputChannelAssignment outputChannelTrace payloadTrace
                        cases outputChannelMatched with
                        | capture outputChannelCaptured =>
                          cases payloadArguments with
                          | cons payloadMatched noMore =>
                            rename_i payloadTerm noTerms payloadAssignment payloadTermTrace noTrace
                            cases noMore
                            cases payloadMatched with
                            | capture payloadCaptured =>
                              simp only [List.nil_append, List.cons_append, Nat.zero_add]
                                at outputChannelCaptured payloadCaptured
                              obtain ⟨rfl, rfl⟩ := output_n_inv channelSafe outputChannelCaptured
                              obtain ⟨payloadSafe, rfl⟩ := output_q_inv payloadCaptured
                              cases afterOutput with
                              | rest restCaptured =>
                                simp only [List.nil_append, Nat.zero_add] at restCaptured
                                obtain ⟨residueSafe, rfl⟩ := rest_inv restCaptured
                                refine ⟨elements, inputIndex, outputIndex, outputChannel, bodyDisplay, bodyTerm, payloadTerm,
                                  rfl, ?_, ?_, ?_, rfl, channelSafe, bodySafe, payloadSafe, residueSafe⟩
                                · rw [List.getElem?_eq_getElem inputBound, inputTarget]
                                · rw [List.getElem?_eq_getElem outputBound, outputTarget]
                                  rfl
                                · simp

/-! ## Every root receipt is an authored depth-one step -/

/-- The only valid job of a source is the COMM declaration at the root. -/
theorem job_root {source : Pattern} {job : GeneralRuleJobs.Job}
    (valid : job.Valid plan [] (.base "Proc") source) :
    job.declaration = declaration ∧ job.ordinal = 0 ∧
      job.site = GeneralTypedSites.SiteData.here [] (.base "Proc") source := by
  obtain ⟨declared, licensed⟩ := valid
  rw [compiled_rules] at declared
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.mem_singleton, Prod.mk.injEq] at declared
  refine ⟨declared.1, declared.2, ?_⟩
  exact generate_rootOnly ((GeneralTypedSites.generate_spec _ _ _ _ _ _ _).mpr licensed)

/-- **Soundness.** Every valid receipt of the depth-one plan on a well-sorted closed source is an
authored depth-one rho step with the same target. -/
theorem receipt_step {free : FreeSortContext} {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (valid : receipt.Valid plan [] (.base "Proc") source) :
    RhoStepAt 1 source receipt.target := by
  obtain ⟨jobValid, firing, _, filled, _⟩ := valid
  simp only [GeneralPlanEnvironment.environmentWith_empty] at firing
  obtain ⟨_, ordinal, site⟩ := job_root jobValid
  rw [site, ordinal] at firing
  rw [site] at filled
  cases firing with
  | fire ruleFound specFound _ _ matched _ premises reduct _ =>
    simp only [GeneralTypedSites.SiteData.here, List.length_nil] at matched premises reduct filled
    have ruleIsComm := ruleFound
    simp only [GeneralPlanEnvironment.environment, compiled_rules, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, Option.some.injEq] at ruleIsComm
    subst ruleIsComm
    have specIsComm := specFound
    simp [GeneralPremise.specification?, GeneralPlanEnvironment.environment, compiled_rules] at specIsComm
    subst specIsComm
    have noPremises : declaration.rule.premises = [] := rfl
    rw [noPremises] at premises
    generalize receipt.completed = completed at premises reduct
    generalize receipt.premiseHistory = history at premises
    cases premises
    obtain ⟨elements, inputIndex, outputIndex, channel, display, body, payload, rfl, inputAt, outputAt,
      _, capturedEq, _, _, _, residueSafe⟩ := traced_comm_inv matched
    rw [capturedEq] at reduct
    obtain ⟨_, elementsTyped⟩ := rho_parallel_wellSorted_inv typed
    have inputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ (List.mem_of_getElem? inputAt)
    obtain ⟨rfl, _, bodyTyped⟩ := rho_input_wellSorted_inv inputTyped
    have outputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _
      (List.mem_of_mem_eraseIdx (List.mem_of_getElem? outputAt))
    obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outputTyped
    have semantic := reflective_reduct_resolved (channel := channel) bodyTyped payloadTyped residueSafe
    have localTarget := Option.some.inj (reduct.symm.trans semantic)
    rw [filled, DerivedContexts.OneHoleContext.fill, localTarget]
    obtain ⟨inputBound, inputEq⟩ := List.getElem?_eq_some_iff.mp inputAt
    obtain ⟨outputBound, outputEq⟩ := List.getElem?_eq_some_iff.mp outputAt
    have step := rhoStepAt_one_comm inputBound outputBound inputEq outputEq
      ((rhoCanonicalEquivalent_iff channel channel).mpr rfl)
    rwa [apply_commBindingsAt_resolved bodyTyped payloadTyped elements inputIndex outputIndex channel] at step

/-! ## Every authored depth-one step on a canonical source is a root receipt

The captures are those of `GeneralRho.source_matching`, at arbitrary bag positions. -/

theorem input_n_capture {ambient : Nat} {channel : Pattern} (safe : channel.isWellScopedAt ambient = true) :
    capture? comm scopedCommBindingSpec ambient 0 .left [0, 0] [] "n" channel =
      some [("n", rootValue ambient channel)] := by
  simp only [Option.bind_eq_bind, capture?, dependencies_n, input_n_arguments, Option.bind_some, recover_root safe]
  rfl

theorem input_p_capture {ambient : Nat} {channel body : Pattern} (safe : body.isWellScopedAt (ambient + 1) = true) :
    capture? comm scopedCommBindingSpec ambient 1 .left [0, 1, 0] [("n", rootValue ambient channel)] "p" body =
      some [("p", bodyValue ambient body), ("n", rootValue ambient channel)] := by
  simp only [Option.bind_eq_bind, capture?, dependencies_p, input_p_arguments, Option.bind_some, recover_body safe]
  rfl

theorem output_n_capture {ambient : Nat} {channel body : Pattern} (safe : channel.isWellScopedAt ambient = true) :
    capture? comm scopedCommBindingSpec ambient 0 .left [1, 0]
      [("p", bodyValue ambient body), ("n", rootValue ambient channel)] "n" channel =
      some [("p", bodyValue ambient body), ("n", rootValue ambient channel)] := by
  simp only [Option.bind_eq_bind, capture?, dependencies_n, output_n_arguments, Option.bind_some, recover_root safe]
  simp [assign, lookup]

theorem output_q_capture {ambient : Nat} {channel body payload : Pattern}
    (safe : payload.isWellScopedAt ambient = true) :
    capture? comm scopedCommBindingSpec ambient 0 .left [1, 1]
      [("p", bodyValue ambient body), ("n", rootValue ambient channel)] "q" payload =
      some [("q", rootValue ambient payload), ("p", bodyValue ambient body), ("n", rootValue ambient channel)] := by
  simp only [Option.bind_eq_bind, capture?, dependencies_q, output_q_arguments, Option.bind_some, recover_root safe]
  rfl

theorem rest_capture {ambient : Nat} {channel body payload : Pattern} {residue : List Pattern}
    (safe : Pattern.isWellScopedListAt ambient residue = true) :
    captureRest? comm scopedCommBindingSpec ambient 0 .left [2]
      [("q", rootValue ambient payload), ("p", bodyValue ambient body), ("n", rootValue ambient channel)]
      "rest" .hashBag residue = some (captured ambient channel body payload residue) := by
  have collectionSafe : (Pattern.collection .hashBag residue none).isWellScopedAt ambient = true := safe
  simp only [Option.bind_eq_bind, captureRest?, capture?, dependencies_rest, rest_arguments,
    Option.bind_some, recover_root collectionSafe]
  rfl

/-- The COMM left side matches an input and an output on one channel at any two positions. -/
theorem comm_matching_at {ambient : Nat} {elements : List Pattern} {inputIndex outputIndex : Nat}
    {channel body payload : Pattern}
    (inputBound : inputIndex < elements.length) (inputEq : elements[inputIndex] = input channel body)
    (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
    (outputEq : (elements.eraseIdx inputIndex)[outputIndex] = output channel payload)
    (channelSafe : channel.isWellScopedAt ambient = true) (bodySafe : body.isWellScopedAt (ambient + 1) = true)
    (payloadSafe : payload.isWellScopedAt ambient = true)
    (residueSafe : Pattern.isWellScopedListAt ambient ((elements.eraseIdx inputIndex).eraseIdx outputIndex) = true) :
    TracedMatches comm scopedCommBindingSpec ambient .left [] 0 [] comm.left (.collection .hashBag elements none)
      [{ path := [0], selected := inputIndex }, { path := [1], selected := outputIndex }]
      (captured ambient channel body payload ((elements.eraseIdx inputIndex).eraseIdx outputIndex)) := by
  rw [comm_left_shape]
  apply TracedMatches.bag (by decide)
  apply TracedBag.cons (headTrace := []) (tailTrace := [{ path := [1], selected := outputIndex }])
    inputIndex inputBound
  · rw [inputEq]
    exact .constructor (.cons (.capture (input_n_capture channelSafe))
      (.cons (.binder (.capture (input_p_capture bodySafe))) .nil))
  · apply TracedBag.cons (headTrace := []) (tailTrace := []) outputIndex outputBound
    · rw [outputEq]
      exact .constructor (.cons (.capture (output_n_capture channelSafe))
        (.cons (.capture (output_q_capture payloadSafe)) .nil))
    · exact .rest (rest_capture residueSafe)

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical (ChannelsDecided)

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (IsCanonical IsCanonicalList isCanonicalList_mem
  isCanonical_apply_general canonicalize_eq_of_isCanonical) in
/-- Canonical sources decide their channels by equality. -/
theorem isCanonical_channelsDecided {source : Pattern} (canonical : IsCanonical source) :
    ChannelsDecided source := by
  intro elements form input inputIn output outputIn inputChannel outputChannel body payload binder
    inputShape outputShape equivalent
  rw [form] at canonical
  have bagCanonical : IsCanonicalList elements := by
    unfold IsCanonical at canonical
    exact canonical.2.2.2
  have inputCanonical := isCanonicalList_mem bagCanonical inputIn
  rw [inputShape, isCanonical_apply_general "PInput" _ (by simp)] at inputCanonical
  have outputCanonical := isCanonicalList_mem bagCanonical outputIn
  rw [outputShape, isCanonical_apply_general "POutput" _ (by simp)] at outputCanonical
  have canonicalSame := (rhoCanonicalEquivalent_iff inputChannel outputChannel).mp equivalent
  rwa [canonicalize_eq_of_isCanonical inputCanonical.1,
    canonicalize_eq_of_isCanonical outputCanonical.1] at canonicalSame

/-- **Completeness.** On a closed, quotation-sealed source whose canonically equivalent channels are
equal, every authored depth-one rho step is the target of a valid receipt of the depth-one plan.
Canonical and lexicographic forms are such sources. -/
theorem step_receipt {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] source)
    (safe : ScopedPattern.binderSafeAt "NQuote" 0 source = true)
    (channels : ChannelsDecided source)
    (step : RhoStepAt 1 source target) :
    ∃ receipt : GeneralRuleJobs.Receipt,
      receipt.Valid plan [] (.base "Proc") source ∧ receipt.target = target := by
  obtain ⟨bindings, matched, applied⟩ := rhoStepAt_one_inv step
  obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound, inputChannel, body,
    inputBinder, outputChannel, payload, rfl, inputEq, outputEq, equivalent, rfl⟩ :=
    rhoComm_match_shape matched
  obtain ⟨rfl, elementsTyped⟩ := rho_parallel_wellSorted_inv typed
  have inputMember := List.getElem_mem inputBound
  have outputMember := List.mem_of_mem_eraseIdx (List.getElem_mem outputBound)
  have inputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ inputMember
  rw [inputEq] at inputTyped
  obtain ⟨rfl, channelTyped, bodyTyped⟩ := rho_input_wellSorted_inv inputTyped
  have outputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ outputMember
  rw [outputEq] at outputTyped
  obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outputTyped
  have sameChannel : inputChannel = outputChannel :=
    channels elements rfl _ inputMember _ outputMember inputChannel outputChannel body payload none
      inputEq outputEq equivalent
  subst sameChannel
  have residueMember : ∀ pattern ∈ (elements.eraseIdx inputIndex).eraseIdx outputIndex, pattern ∈ elements :=
    fun _ member => List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member)
  have residueTyped : ProcListWellSorted rhoReflectivePresentation (fun _ => none) []
      ((elements.eraseIdx inputIndex).eraseIdx outputIndex) :=
    procListWellSorted_iff_forall_mem.mpr fun pattern member =>
      procListWellSorted_iff_forall_mem.mp elementsTyped pattern (residueMember pattern member)
  have channelOpen := derived_name_open channelTyped
  have bodyOpen := derived_process_open bodyTyped
  have payloadOpen := derived_process_open payloadTyped
  have residueOpen := derived_processes_typed residueTyped
  have residueRepresented := derived_processes_represented residueTyped
  have sourceOpen := derived_process_open typed
  have channelSafe : inputChannel.isWellScopedAt 0 = true := channelOpen.1.isWellScopedAt
  have bodySafe : body.isWellScopedAt (0 + 1) = true := bodyOpen.1.isWellScopedAt
  have payloadSafe : payload.isWellScopedAt 0 = true := payloadOpen.1.isWellScopedAt
  have residueSafe := residueOpen.isWellScopedListAt
  have bodySealed : ScopedPattern.binderSafeAt "NQuote" 1 body = true := by
    have memberSafe := (closed_member typed safe inputMember).2
    rw [inputEq] at memberSafe
    simp only [ScopedPattern.binderSafeAt, ScopedPattern.binderSafeListAt] at memberSafe
    simp at memberSafe
    exact memberSafe.2
  have names := derived_names_admitted bodyTyped bodySealed
  have semantic := reflective_reduct_resolved (channel := inputChannel) bodyTyped payloadTyped residueSafe
  have literal := reflective_reduct (ambient := 0) (channel := inputChannel) bodySafe payloadSafe residueSafe
  have bodiesEq : reflectiveBody body payload = semanticCommSubst (ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload := by
    have both := literal.symm.trans semantic
    simp only [Option.some.injEq, Pattern.collection.injEq, List.cons.injEq] at both
    exact both.2.1.1
  have targetBodyOpen := reflective_body_open bodyOpen bodySealed names payloadOpen
  rw [bodiesEq] at targetBodyOpen
  have targetTyped : HasType language (typeFree fun _ => none) []
      (.collection .hashBag (semanticCommSubst (ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex) none)
      (.base "Proc") := parallel_typed (.cons targetBodyOpen.1 residueOpen)
  have targetRepresented : Represented
      (.collection .hashBag (semanticCommSubst (ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex) none) :=
    (represented_collection_iff _ _).mpr fun pattern member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨targetBodyOpen.2.1, targetBodyOpen.2.2.1⟩
      · exact residueRepresented pattern member
  have targetOpen : OpenPatternWellSorted language (typeFree fun _ => none) [] (.base "Proc")
      (.collection .hashBag (semanticCommSubst (ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex) none) :=
    ⟨targetTyped, targetRepresented.1, targetRepresented.2, targetTyped.isWellScopedAt⟩
  have position : plan.rules[0]? = some declaration := by rw [compiled_rules]; rfl
  have captureTyped := captured_typed channelOpen.1 bodyOpen.1 payloadOpen.1 residueOpen
  have captureObjects := captured_objects (ambient := 0) ⟨channelOpen.2.1, channelOpen.2.2.1⟩
    ⟨bodyOpen.2.1, bodyOpen.2.2.1⟩ ⟨payloadOpen.2.1, payloadOpen.2.2.1⟩ residueRepresented
  have sourceInPlan := (GeneralPlanEnvironment.typing_iff plan [] (.base "Proc") _).mpr sourceOpen
  have firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "Proc")
      (.collection .hashBag elements none) 0
      [{ path := [0], selected := inputIndex }, { path := [1], selected := outputIndex }]
      (captured 0 inputChannel body payload ((elements.eraseIdx inputIndex).eraseIdx outputIndex))
      (captured 0 inputChannel body payload ((elements.eraseIdx inputIndex).eraseIdx outputIndex)) []
      (.collection .hashBag (semanticCommSubst (ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex)
        none) := by
    refine .fire (GeneralPlanEnvironment.selected_rule plan position)
      (GeneralPlanEnvironment.selected_specification plan position) comm_admitted sourceInPlan
      (comm_matching_at inputBound inputEq outputBound outputEq channelSafe bodySafe payloadSafe residueSafe)
      ?_ .nil semantic ((GeneralPlanEnvironment.typing_iff plan _ _ _).mpr targetOpen)
    refine ⟨?_, captureObjects⟩
    intro name value member
    obtain ⟨dependencies, expected, declared, sorted, metadata, ambient, valueTyped⟩ :=
      captureTyped name value member
    exact ⟨dependencies, expected, declared, sorted, metadata, ambient,
      GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar plan).symm valueTyped⟩
  refine ⟨⟨⟨0, declaration, GeneralTypedSites.SiteData.here [] (.base "Proc") (.collection .hashBag elements none)⟩,
    [{ path := [0], selected := inputIndex }, { path := [1], selected := outputIndex }],
    captured 0 inputChannel body payload ((elements.eraseIdx inputIndex).eraseIdx outputIndex),
    captured 0 inputChannel body payload ((elements.eraseIdx inputIndex).eraseIdx outputIndex), [],
    .collection .hashBag (semanticCommSubst (ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex) none,
    .collection .hashBag (semanticCommSubst (ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload :: (elements.eraseIdx inputIndex).eraseIdx outputIndex) none⟩,
    ⟨⟨by rw [compiled_rules]; simp, .here rfl sourceInPlan.2.2.1 sourceInPlan.1⟩, firing, rfl, rfl,
      (GeneralPlanEnvironment.typing_iff plan _ _ _).mpr targetOpen⟩, ?_⟩
  rw [← applied]
  exact (apply_commBindingsAt_resolved bodyTyped payloadTyped elements inputIndex outputIndex inputChannel).symm

/-- **The depth-one join.** On a closed, quotation-sealed source whose canonically equivalent channels
are equal, the steps of the depth-one plan's GSLT are exactly the authored depth-one rho steps. -/
theorem step_iff {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] source)
    (safe : ScopedPattern.binderSafeAt "NQuote" 0 source = true)
    (channels : ChannelsDecided source) :
    (GeneralOccurrenceSemantics.gslt plan [] (.base "Proc")).Step source target ↔ RhoStepAt 1 source target := by
  rw [← GeneralOccurrenceFrontier.LocalEquationFree.completedReceipts_targets_iff_step plan [] _ source target
    compilation_has_no_equations stratified]
  constructor
  · intro present
    obtain ⟨receipt, member, rfl⟩ := List.mem_map.mp present
    exact receipt_step typed
      ((GeneralRuleJobExecution.mem_completedReceipts_iff plan [] _ source stratified receipt).mp member)
  · intro step
    obtain ⟨receipt, valid, rfl⟩ := step_receipt typed safe channels step
    exact List.mem_map.mpr ⟨receipt,
      (GeneralRuleJobExecution.mem_completedReceipts_iff plan [] _ source stratified receipt).mpr valid, rfl⟩

end Mettapedia.OSLF.MeTTaIL.GeneralRho.DepthOne
