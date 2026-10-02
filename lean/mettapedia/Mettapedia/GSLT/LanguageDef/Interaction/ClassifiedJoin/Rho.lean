import Mettapedia.OSLF.Syntax.IntrinsicScopedRhoClassifiedInstance
import Mettapedia.OSLF.Syntax.RhoPayloadExecutorComparison
import Mettapedia.GSLT.LanguageDef.Interaction.ClassifiedJoin.RhoPlainSubstitution
import Mettapedia.GSLT.LanguageDef.ReactiveContexts
import Mettapedia.GSLT.LanguageDef.ClosedTermChecker
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness

/-!
# The rho iGSLT against its classified presentation

The rho calculus has two presentations in this development.  The interactive
one authors input with a bound name over raw patterns, parallel composition
as a bag, and two rules: communication, whose contractum eliminates the
binder at the quotation of the payload, and reduction of a component of a
parallel composition.  The classified one is the payload presentation: an
input binds the process it receives, parallel composition is binary, and
communication instantiates the continuation at the payload.

The translation of authored processes into the payload presentation relates
them.  Along it:

* the redex of the authored communication rule is the redex of the
  classifier's communication event, up to the presented equations, and
  component reduction is the classifier's parallel congruence;
* the contractum differs.  The authored rule leaves the drop of the quoted
  payload wherever the continuation runs the received name; the classifier
  runs the payload there.  The translated authored contractum is the
  continuation instantiated at the dropped name of the payload;
* so the authored contractum is the target of the classifier's event at that
  redex exactly when those two instances are equal up to the equations.  They
  are when the received name is only used as a name, or when the payload is
  itself a dropped name.  They are not when the continuation runs the
  received name on any other payload: the two contracta then differ by a
  Drop redex, which only the profile with the Drop rule contracts, and the
  authored step is an event of neither classifier;
* the relation that interprets communication through the reflective
  presentation contracts that redex during substitution, and each of its
  steps is one classified event.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ClassifiedJoin.Rho

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoPayloadPresentation
open Mettapedia.OSLF.Binding.IntrinsicScopedRhoClassifiedInstance
  (strictLocalRules bookLocalRules extension_iff_steps comm_classified parCong_classified
    drop_book_classified)
open Mettapedia.OSLF.Binding.IntrinsicScopedSharedLocalPolynomialComparison (localRules)
open Mettapedia.OSLF.Binding.IntrinsicScopedAuthoredClassifiedReduction (ExtendedReduction)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar liftBVars_zero)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-! ## The authored communication rule -/

/-- What the left side of the authored communication rule matches: an input
and an output on one channel in a bag, with the remaining components. -/
theorem match_comm {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern rhoCommRewrite.left source) :
    ∃ (elements : List Pattern) (tail : Option String) (i : Nat) (_ : i < elements.length)
      (j : Nat) (_ : j < (elements.eraseIdx i).length)
      (channel body payload : Pattern) (binder : Option String),
      source = .collection .hashBag elements tail ∧
      elements[i]? = some (.apply "PInput" [channel, .lambda binder body]) ∧
      (elements.eraseIdx i)[j]? = some (.apply "POutput" [channel, payload]) ∧
      bindings = [("q", payload),
        ("rest", .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none),
        ("p", body), ("n", channel)] := by
  have relation := matchPattern_sound matched
  rw [show rhoCommRewrite.left = .collection .hashBag [
      .apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
      .apply "POutput" [.fvar "n", .fvar "q"]] (some "rest") from rfl] at relation
  cases relation with
  | collection unordered bag =>
      rename_i elements tail
      cases bag with
      | cons i hi inputMatch restMatch merged =>
          cases restMatch with
          | cons j hj outputMatch tailMatch mergedRest =>
              cases tailMatch
              generalize inputEq : elements[i] = input at inputMatch
              generalize outputEq : (elements.eraseIdx i)[j] = output at outputMatch
              cases inputMatch
              rename_i inputArguments inputLength inputArgumentsMatch
              cases inputArgumentsMatch
              rename_i inputChannel channelBindings inputRest inputRestBindings channelMatch
                inputRestMatch inputMerged
              cases inputRestMatch
              rename_i abstraction abstractionBindings inputTail inputTailBindings
                abstractionMatch inputTailMatch abstractionMerged
              cases inputTailMatch
              cases channelMatch
              cases abstractionMatch
              rename_i body binder bodyMatch
              cases bodyMatch
              cases outputMatch
              rename_i outputArguments outputLength outputArgumentsMatch
              cases outputArgumentsMatch
              rename_i outputChannel outputChannelBindings outputRest outputRestBindings
                outputChannelMatch outputRestMatch outputMerged
              cases outputRestMatch
              rename_i payload payloadBindings outputTail outputTailBindings payloadMatch
                outputTailMatch payloadMerged
              cases outputTailMatch
              cases outputChannelMatch
              cases payloadMatch
              simp [mergeBindings] at abstractionMerged payloadMerged
              subst abstractionMerged
              subst payloadMerged
              simp [mergeBindings] at inputMerged outputMerged
              subst inputMerged
              subst outputMerged
              simp [mergeBindings] at mergedRest
              subst mergedRest
              simp [mergeBindings] at merged
              obtain ⟨rfl, rfl⟩ := merged
              exact ⟨elements, tail, i, hi, j, hj, inputChannel, body, payload, binder, rfl,
                by rw [List.getElem?_eq_getElem hi, inputEq],
                by rw [List.getElem?_eq_getElem hj, outputEq], rfl⟩

/-- The contractum of the authored communication rule: the binder of the
input eliminated at the quotation of the payload, beside the remaining
components. -/
theorem apply_comm (channel body payload : Pattern) (remaining : List Pattern) :
    applyBindingsForRule rhoCalc rhoCommRewrite
        [("q", payload), ("rest", .collection .hashBag remaining none), ("p", body),
          ("n", channel)] =
      .collection .hashBag (instantiateBVar (literalName payload) body :: remaining) none := by
  rw [applyBindingsForRule_eq_syntactic]
  simp [applyRuleBindings, applyBindingsScoped, restSplice, rhoCommRewrite, captureDepth,
    captureDepthList, liftBVars_zero, map_liftBVars_zero]

/-- The rule for a component of a parallel composition. -/
theorem parCong_elementCongruence :
    ElementCongruence rhoParCongRewrite .hashBag "S" "T" "rest" where
  premises := rfl
  left := rfl
  right := rfl
  unordered := by decide
  distinct := by decide

/-- Communication is a base rewrite and component reduction a congruence. -/
theorem rho_firesInContexts : FiresInContexts rhoCalc := by
  intro rule membership
  have listed : rule ∈ [rhoCommRewrite, rhoParCongRewrite] := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl
  · exact .inl (isBaseRewrite_of_premises_eq_nil rfl)
  · exact .inr (.inr ⟨_, _, _, _, parCong_elementCongruence⟩)

/-! ## The firing of the authored rule, translated -/

/-- The firing of the authored communication rule as the payload
presentation sees it: the source is a communication redex beside other
components, and the target is the continuation instantiated at the dropped
name of the payload, beside the same components. -/
def AuthoredFiring (source target : Term sig [] Srt.pr) : Prop :=
  ∃ (channel : Term sig [] Srt.nm) (payload : Term sig [] Srt.pr)
    (continuation : Term sig [Srt.pr] Srt.pr) (others : Term sig [] Srt.pr),
    EqClosure equations source
      (parT (parT (outT channel payload) (inpT channel continuation)) others) ∧
    EqClosure equations target (parT (inst continuation (droppedName payload)) others)

/-- A translatable bag has no open tail. -/
theorem tail_eq_none_of_translates {elements : List Pattern} {tail : Option String}
    {term : Term sig [] Srt.pr}
    (translated : tProc (Env.empty []) (.collection .hashBag elements tail) = some term) :
    tail = none := by
  cases tail with
  | none => rfl
  | some name =>
      rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
        at translated
      cases translated

/-- **The authored communication rule at the root.**  A base contraction of
a translatable process has a translatable contractum, and the two
translations are an authored firing. -/
theorem baseStep_translation {redex reduct : Pattern}
    (contraction : BaseStep RelationEnv.empty rhoCalc redex reduct)
    {source : Term sig [] Srt.pr} (translated : tProc (Env.empty []) redex = some source) :
    ∃ target, tProc (Env.empty []) reduct = some target ∧ AuthoredFiring source target := by
  obtain ⟨rule, membership, base, initial, matched, final, premises, targetEq⟩ := contraction
  have listed : rule ∈ [rhoCommRewrite, rhoParCongRewrite] := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl
  · obtain rfl : final = initial := by
      simpa [rhoCommRewrite, applyPremisesWithEnv] using premises
    obtain ⟨elements, tail, i, hi, j, hj, channel, body, payload, binder, rfl, inputEq,
      outputEq, rfl⟩ := match_comm (by simpa using matched)
    obtain rfl := tail_eq_none_of_translates translated
    rw [apply_comm] at targetEq
    subst targetEq
    rw [tProc.eq_5] at translated
    obtain ⟨input, afterInput, hinput, hafterInput, e₁⟩ := tProcs_select _ translated i hi
    obtain ⟨output, others, houtput, hothers, e₂⟩ := tProcs_select _ hafterInput j hj
    obtain ⟨_, inputGet⟩ := List.getElem?_eq_some_iff.mp inputEq
    obtain ⟨_, outputGet⟩ := List.getElem?_eq_some_iff.mp outputEq
    rw [inputGet] at hinput
    rw [outputGet] at houtput
    cases binder with
    | some name =>
        rw [tProc_eq_none_of_not _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
          at hinput
        cases hinput
    | none =>
        obtain ⟨inputChannel, continuation, hinputChannel, hcontinuation, rfl⟩ :=
          tProc_input_inv hinput
        obtain ⟨outputChannel, payloadTerm, houtputChannel, hpayload, rfl⟩ :=
          tProc_output_inv houtput
        obtain rfl : inputChannel = outputChannel :=
          Option.some.inj (hinputChannel.symm.trans houtputChannel)
        obtain ⟨contractum, hcontractum, econtractum⟩ :=
          translate_plainCommSubst hcontinuation hpayload
        refine ⟨parT contractum others, ?_, inputChannel, payloadTerm, continuation, others,
          ?_, equiv_parT econtractum (.refl others)⟩
        · rw [tProc.eq_5, tProcs.eq_2, hcontractum, Option.bind_some, hothers,
            Option.map_some]
        · refine e₁.trans ((equiv_parT (.refl _) e₂).trans ?_)
          exact (parT_assoc _ _ _).symm.trans (equiv_parT (parT_comm _ _) (.refl others))
  · exact absurd base (not_isBaseRewrite_of_congruence
      (source := .fvar "S") (target := .fvar "T") (List.mem_singleton.mpr rfl))

/-- **Component reduction.**  Beneath the contexts in which the authored
rules fire, an authored firing remains one: the other components of each
enclosing bag join the components beside the redex. -/
theorem reactive_translation {context residual : OneHoleContext}
    (reactive : Reactive rhoCalc context residual) {redex reduct : Pattern}
    (inner : ∀ {source : Term sig [] Srt.pr}, tProc (Env.empty []) redex = some source →
      ∃ target, tProc (Env.empty []) reduct = some target ∧ AuthoredFiring source target) :
    ∀ {source : Term sig [] Srt.pr},
      tProc (Env.empty []) (context.fill redex) = some source →
        ∃ target, tProc (Env.empty []) (residual.fill reduct) = some target ∧
          AuthoredFiring source target := by
  induction reactive with
  | hole => exact inner
  | argument beforeTerms afterTerms membership congruence _ _ _ _ =>
      have listed : _ ∈ [rhoCommRewrite, rhoParCongRewrite] := membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      intro source translated
      rcases listed with rfl | rfl
      · exact absurd congruence.left (by simp [rhoCommRewrite])
      · exact absurd congruence.left (by simp [rhoParCongRewrite])
  | @element rule kind _ _ _ innerContext innerResidual before after tail membership
      congruence _ recurse =>
      have listed : rule ∈ [rhoCommRewrite, rhoParCongRewrite] := membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      obtain rfl : kind = .hashBag := by
        rcases listed with rfl | rfl
        · exact absurd congruence.premises (by simp [rhoCommRewrite])
        · have shape := congruence.left
          simp only [rhoParCongRewrite, Pattern.collection.injEq] at shape
          exact shape.1.symm
      intro source translated
      change tProc (Env.empty [])
        (.collection .hashBag (before ++ innerContext.fill redex :: after) tail) =
          some source at translated
      obtain rfl := tail_eq_none_of_translates translated
      rw [tProc.eq_5] at translated
      have index : before.length < (before ++ innerContext.fill redex :: after).length := by
        simp
      obtain ⟨selected, others, hselected, hothers, e⟩ :=
        tProcs_select _ translated before.length index
      have selectedEq :
          (before ++ innerContext.fill redex :: after)[before.length] =
            innerContext.fill redex := by simp
      have erased : (before ++ innerContext.fill redex :: after).eraseIdx before.length =
          before ++ after := by
        rw [List.eraseIdx_append_of_length_le (Nat.le_refl _)]
        simp
      rw [selectedEq] at hselected
      rw [erased] at hothers
      obtain ⟨innerTarget, hinnerTarget, channel, payload, continuation, beside, es, et⟩ :=
        recurse hselected
      refine ⟨parT innerTarget others, ?_, channel, payload, continuation,
        parT beside others, ?_, ?_⟩
      · change tProc (Env.empty [])
          (.collection .hashBag (innerResidual.fill reduct :: (before ++ after)) none) = _
        rw [tProc.eq_5, tProcs.eq_2, hinnerTarget, Option.bind_some, hothers, Option.map_some]
      · exact e.trans ((equiv_parT es (.refl others)).trans (parT_assoc _ _ _))
      · exact (equiv_parT et (.refl others)).trans (parT_assoc _ _ _)

/-- **Every authored reduction of a translatable process is an authored
firing.**  The target translates, and the translations are a communication
redex beside other components and the continuation instantiated at the
dropped name of the payload beside the same components. -/
theorem step_translation {source target : Pattern}
    (step : Step defaultBasePremises rhoCalc source target)
    {sourceTerm : Term sig [] Srt.pr}
    (translated : tProc (Env.empty []) source = some sourceTerm) :
    ∃ targetTerm, tProc (Env.empty []) target = some targetTerm ∧
      AuthoredFiring sourceTerm targetTerm := by
  obtain ⟨context, residual, redex, reduct, reactive, rfl, rfl, contraction⟩ :=
    (step_iff_baseStep_in_context (relEnv := RelationEnv.empty) rho_firesInContexts).mp step
  exact reactive_translation reactive (fun inner => baseStep_translation contraction inner)
    translated

/-! ## The classifier at the same redex -/

/-- Events of the classifier are between equation classes. -/
theorem classified_of_equiv
    {rules : List (IntrinsicScopedConditionalPolynomial.Rule sig metas)}
    {source source' target target' : Term sig [] Srt.pr}
    (hsource : EqClosure equations source source')
    (htarget : EqClosure equations target' target)
    (event : ExtendedReduction (localRules rules) equations source' target') :
    ExtendedReduction (localRules rules) equations source target :=
  (extension_iff_steps rules _ _).mpr
    (steps_of_equiv hsource htarget ((extension_iff_steps rules _ _).mp event))

/-- **The classifier fires at the redex of every authored firing.**  Its
event is the classified communication beneath the classified parallel
congruence, and it instantiates the continuation at the payload, where the
authored contractum instantiates it at the dropped name of the payload.  The
authored target is the target of that event exactly when the two instances
are equal up to the equations, and the authored firing is then an event of
the classifier. -/
theorem AuthoredFiring.classified {source target : Term sig [] Srt.pr}
    (firing : AuthoredFiring source target) :
    ∃ (payload : Term sig [] Srt.pr) (continuation : Term sig [Srt.pr] Srt.pr)
      (others : Term sig [] Srt.pr),
      EqClosure equations target (parT (inst continuation (droppedName payload)) others) ∧
      ExtendedReduction strictLocalRules equations source
        (parT (inst continuation payload) others) ∧
      (EqClosure equations target (parT (inst continuation payload) others) ↔
        EqClosure equations (inst continuation (droppedName payload))
          (inst continuation payload)) ∧
      (EqClosure equations (inst continuation (droppedName payload))
          (inst continuation payload) →
        ExtendedReduction strictLocalRules equations source target) := by
  obtain ⟨channel, payload, continuation, others, es, et⟩ := firing
  have event : ExtendedReduction strictLocalRules equations
      (parT (parT (outT channel payload) (inpT channel continuation)) others)
      (parT (inst continuation payload) others) :=
    parCong_classified [] others (comm_classified [] channel payload continuation)
  refine ⟨payload, continuation, others, et, classified_of_equiv es (.refl _) event, ?_, ?_⟩
  · constructor
    · intro same
      have atomsEq : atoms (inst continuation (droppedName payload)) + atoms others =
          atoms (inst continuation payload) + atoms others :=
        atoms_invariant (et.symm.trans same)
      exact cls_eq_iff.mp (cls_eq_of_atoms_eq (add_right_cancel atomsEq))
    · intro agree
      exact et.trans (equiv_parT agree (.refl others))
  · intro agree
    exact classified_of_equiv es ((equiv_parT agree.symm (.refl others)).trans et.symm) event

/-- An authored firing is invariant under the presented equations at both
ends. -/
theorem AuthoredFiring.of_equiv {source source' target target' : Term sig [] Srt.pr}
    (hsource : EqClosure equations source source')
    (htarget : EqClosure equations target' target)
    (firing : AuthoredFiring source' target') : AuthoredFiring source target := by
  obtain ⟨channel, payload, continuation, others, es, et⟩ := firing
  exact ⟨channel, payload, continuation, others, hsource.trans es, htarget.symm.trans et⟩

/-! ## The relation interpreted through the reflective presentation -/

section Interpreted

open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep)

/-- **Each step of the interpreted relation is one classified event.**  The
relation that matches channels up to their canonical form and substitutes
through the reflective presentation is simulated step for step by the
payload presentation; composed with the classifier's coverage of that
presentation, each of its steps is an event of the strict classifier. -/
theorem interpreted_step_classified {free : FreeSortContext} {bound : List String}
    {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound source)
    (step : RhoStep source target) {sourceTerm : Term sig [] Srt.pr}
    (translated : tProc (Env.empty []) source = some sourceTerm) :
    ∃ targetTerm, tProc (Env.empty []) target = some targetTerm ∧
      ExtendedReduction strictLocalRules equations sourceTerm targetTerm := by
  obtain ⟨targetTerm, htarget, steps⟩ := rhoStep_simulation typed step translated
  exact ⟨targetTerm, htarget, (extension_iff_steps strictRules _ _).mpr steps⟩

/-- The same for the profile with the Drop rule and the book classifier. -/
theorem interpretedWithDrop_step_classified {free : FreeSortContext} {bound : List String}
    {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound source)
    (step : RhoCombinedInterpretedStep.RhoStepWithDrop source target)
    {sourceTerm : Term sig [] Srt.pr}
    (translated : tProc (Env.empty []) source = some sourceTerm) :
    ∃ targetTerm, tProc (Env.empty []) target = some targetTerm ∧
      ExtendedReduction bookLocalRules equations sourceTerm targetTerm := by
  obtain ⟨targetTerm, htarget, steps⟩ := rhoStepWithDrop_simulation typed step translated
  exact ⟨targetTerm, htarget, (extension_iff_steps bookRules _ _).mpr steps⟩

end Interpreted

/-! ## Static equivalence -/

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
  (rho_equivalent_iff_canonicalize_eq)

/-- The authored static equivalence is contained in the equivalence selected
by the reflective presentation. -/
theorem reflective_of_equivalent {left right : rhoIGSLT.toGSLT.Term}
    (equivalent : rhoIGSLT.toGSLT.equations.r left right) :
    (reflectiveClosedEquationSetoid rhoIGSLT
      ReflectionExtension.rhoCalcValidatedReflective.admittedReflection).r left right := by
  change Relation.EqvGen
    (presentedEquationGenerator defaultBasePremises rhoInteractivePresentation) left right
    at equivalent
  induction equivalent with
  | rel first second generator => exact Relation.EqvGen.rel _ _ (.core generator)
  | refl term => exact Relation.EqvGen.refl term
  | symm _ _ _ recurse => exact Relation.EqvGen.symm _ _ recurse
  | trans _ _ _ _ _ first second => exact Relation.EqvGen.trans _ _ _ first second

/-- **Equivalent terms of the interactive carrier that both translate have
equal classes.**  The authored static equivalence is contained in equality
of canonical forms, and a canonical form translates to the class of its
term. -/
theorem equivalent_classes {left right : rhoIGSLT.toGSLT.Term}
    (equivalent : rhoIGSLT.toGSLT.equations.r left right)
    {leftTerm rightTerm : Term sig [] Srt.pr}
    (hleft : tProc (Env.empty []) left.1 = some leftTerm)
    (hright : tProc (Env.empty []) right.1 = some rightTerm) :
    EqClosure equations leftTerm rightTerm := by
  have canonical :=
    (rho_equivalent_iff_canonicalize_eq left right).mp (reflective_of_equivalent equivalent)
  obtain ⟨left', hleft', eleft⟩ :=
    translate_canonicalize.2.1 (Env.empty []) left.1 leftTerm hleft
  obtain ⟨right', hright', eright⟩ :=
    translate_canonicalize.2.1 (Env.empty []) right.1 rightTerm hright
  rw [canonical, hright'] at hleft'
  cases hleft'
  exact eleft.symm.trans eright

/-- **A step of the interactive theory through a translatable redex is an
authored firing.**  The step is an authored reduction between two terms
equivalent to its ends; when the ends and that redex translate, the
translations of the ends are an authored firing. -/
theorem semantic_step_firing {source redex contractum target : rhoIGSLT.toGSLT.Term}
    (sourceEq : rhoIGSLT.toGSLT.equations.r source redex)
    (primitive : Step defaultBasePremises rhoCalc redex.1 contractum.1)
    (targetEq : rhoIGSLT.toGSLT.equations.r contractum target)
    {sourceTerm redexTerm targetTerm : Term sig [] Srt.pr}
    (hsource : tProc (Env.empty []) source.1 = some sourceTerm)
    (hredex : tProc (Env.empty []) redex.1 = some redexTerm)
    (htarget : tProc (Env.empty []) target.1 = some targetTerm) :
    AuthoredFiring sourceTerm targetTerm := by
  obtain ⟨contractumTerm, hcontractum, firing⟩ := step_translation primitive hredex
  exact firing.of_equiv (equivalent_classes sourceEq hsource hredex)
    (equivalent_classes targetEq hcontractum htarget)

/-! ## An instance: the received name used as a name -/

section Instances

open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The null process. -/
def zero : Pattern := .apply "PZero" []

/-- The channel `@0`. -/
def channel : Pattern := .apply "NQuote" [zero]

/-- The channel `@0` in the payload presentation. -/
def channelTerm : Term sig [] Srt.nm := quoT nilT

/-- `for(x <- @0){ x!(0) } | @0!(0)`: the continuation sends on the received
name. -/
def sendOnReceived : Pattern :=
  .collection .hashBag
    [.apply "PInput" [channel, .lambda none (.apply "POutput" [.bvar 0, zero])],
      .apply "POutput" [channel, zero]] none

/-- `@0!(0)`: the authored contractum. -/
def sendOnReceivedReduct : Pattern :=
  .collection .hashBag [.apply "POutput" [channel, zero]] none

/-- The redex as a term of the interactive carrier. -/
def sendOnReceivedTerm : rhoIGSLT.toGSLT.Term :=
  ClosedTerm.ofCheck (sort := rhoInteractivePresentation.interactingLangSort) sendOnReceived
    (by decide +kernel)

/-- The contractum as a term of the interactive carrier. -/
def sendOnReceivedReductTerm : rhoIGSLT.toGSLT.Term :=
  ClosedTerm.ofCheck (sort := rhoInteractivePresentation.interactingLangSort)
    sendOnReceivedReduct (by decide +kernel)

/-- The interactive theory steps. -/
theorem sendOnReceived_step :
    rhoIGSLT.toGSLT.Step sendOnReceivedTerm sendOnReceivedReductTerm :=
  primitiveStep_to_presentedStep (presentation := rhoInteractivePresentation)
    (exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩)

/-- The translated redex: the continuation sends on the quotation of the
received process. -/
theorem sendOnReceived_translation :
    tProc (Env.empty []) sendOnReceived =
      some (parT (inpT channelTerm (outT (quoT (.var .zero)) nilT))
        (parT (outT channelTerm nilT) nilT)) := rfl

/-- The translated contractum. -/
theorem sendOnReceivedReduct_translation :
    tProc (Env.empty []) sendOnReceivedReduct =
      some (parT (outT channelTerm nilT) nilT) := rfl

/-- **The same step is an event of the classifier.**  The received name
occurs only as a channel, so the two contracta coincide. -/
theorem sendOnReceived_classified :
    ExtendedReduction strictLocalRules equations
      (parT (inpT channelTerm (outT (quoT (.var .zero)) nilT))
        (parT (outT channelTerm nilT) nilT))
      (parT (outT channelTerm nilT) nilT) := by
  refine classified_of_equiv (rules := strictRules) ?_ ?_
    (comm_classified [] channelTerm nilT (outT (quoT (.var .zero)) nilT))
  · exact (equiv_parT (.refl _) (parT_nil _)).trans (parT_comm _ _)
  · exact (parT_nil _).symm

/-! ## A control: the received name run on a payload that is not a drop -/

/-- `for(x <- @0){ *x } | @0!(0)`: the continuation runs the received
name. -/
def runReceived : Pattern :=
  .collection .hashBag
    [.apply "PInput" [channel, .lambda none (.apply "PDrop" [.bvar 0])],
      .apply "POutput" [channel, zero]] none

/-- `*@0`: the authored contractum, the drop of the quoted payload. -/
def runReceivedReduct : Pattern :=
  .collection .hashBag [.apply "PDrop" [.apply "NQuote" [zero]]] none

/-- The redex as a term of the interactive carrier. -/
def runReceivedTerm : rhoIGSLT.toGSLT.Term :=
  ClosedTerm.ofCheck (sort := rhoInteractivePresentation.interactingLangSort) runReceived
    (by decide +kernel)

/-- The contractum as a term of the interactive carrier. -/
def runReceivedReductTerm : rhoIGSLT.toGSLT.Term :=
  ClosedTerm.ofCheck (sort := rhoInteractivePresentation.interactingLangSort)
    runReceivedReduct (by decide +kernel)

/-- The interactive theory steps. -/
theorem runReceived_step : rhoIGSLT.toGSLT.Step runReceivedTerm runReceivedReductTerm :=
  primitiveStep_to_presentedStep (presentation := rhoInteractivePresentation)
    (exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩)

/-- The translated source: a communication redex whose continuation is the
received process. -/
def runReceivedSource : Term sig [] Srt.pr :=
  parT (inpT channelTerm (.var .zero)) (parT (outT channelTerm nilT) nilT)

/-- The translated authored contractum: the drop of the quoted payload. -/
def runReceivedTarget : Term sig [] Srt.pr := parT (drpT (quoT nilT)) nilT

/-- The redex translates to the communication redex. -/
theorem runReceived_translation :
    tProc (Env.empty []) runReceived = some runReceivedSource := rfl

/-- The authored contractum translates to the drop of the quoted payload. -/
theorem runReceivedReduct_translation :
    tProc (Env.empty []) runReceivedReduct = some runReceivedTarget := rfl

/-- The classifier's event at this redex runs the payload: its target is the
null process. -/
theorem runReceived_classified_target :
    ExtendedReduction strictLocalRules equations runReceivedSource nilT := by
  refine classified_of_equiv (rules := strictRules) ?_ (.refl _)
    (comm_classified [] channelTerm nilT (.var .zero))
  exact (equiv_parT (.refl _) (parT_nil _)).trans (parT_comm _ _)

/-- The translated ends of the authored step do not have the shape of a
communication event: the redex forces the continuation to be the received
process and the payload to be null, so the contractum would have no
component, and the authored contractum has one. -/
theorem runReceived_not_commShape :
    ¬ CommShape (cls runReceivedSource) (cls runReceivedTarget) := by
  rintro ⟨c, q, K, others, hs, ht⟩
  have sourceAtoms : atoms runReceivedSource =
      {cls (inpT channelTerm (.var .zero))} + ({cls (outT channelTerm nilT)} + 0) := rfl
  have targetAtoms : atoms runReceivedTarget = {cls (drpT (quoT nilT))} + 0 := rfl
  rw [atomsQ_cls, sourceAtoms] at hs
  rw [atomsQ_cls, targetAtoms] at ht
  have othersEmpty : others = 0 := by
    have cards := congrArg Multiset.card hs
    rw [Multiset.card_add, Multiset.card_add, Multiset.card_singleton,
      Multiset.card_singleton, Multiset.card_zero, Multiset.card_cons, Multiset.card_cons]
      at cards
    exact Multiset.card_eq_zero.mp (by omega)
  subst othersEmpty
  have inputMember : cls (inpT c K) ∈
      ({cls (inpT channelTerm (.var .zero))} + ({cls (outT channelTerm nilT)} + 0) :
        Multiset (Cls [] Srt.pr)) := by
    rw [hs]
    simp
  have outputMember : cls (outT c q) ∈
      ({cls (inpT channelTerm (.var .zero))} + ({cls (outT channelTerm nilT)} + 0) :
        Multiset (Cls [] Srt.pr)) := by
    rw [hs]
    simp
  rw [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_add, Multiset.mem_singleton]
    at inputMember outputMember
  have continuationEq : EqClosure equations K (.var .zero) := by
    rcases inputMember with same | same | none
    · have parts := inpParts_invariant (cls_eq_iff.mp same)
      have pair : (cls c, cls K) = (cls channelTerm, cls (.var .zero)) :=
        Multiset.singleton_inj.mp parts
      exact cls_eq_iff.mp (Prod.mk.inj pair).2
    · have counts : (0 : Nat) = 1 := activeOutputs_equiv (cls_eq_iff.mp same)
      omega
    · exact absurd none (Multiset.notMem_zero _)
  have payloadEq : EqClosure equations q nilT := by
    rcases outputMember with same | same | none
    · have counts : (1 : Nat) = 0 := activeOutputs_equiv (cls_eq_iff.mp same)
      omega
    · have parts := outParts_invariant (cls_eq_iff.mp same)
      have pair : (cls c, cls q) = (cls channelTerm, cls nilT) :=
        Multiset.singleton_inj.mp parts
      exact cls_eq_iff.mp (Prod.mk.inj pair).2
    · exact absurd none (Multiset.notMem_zero _)
  have contractum : atoms (inst K q) = 0 :=
    atoms_invariant (eqClosure_inst continuationEq payloadEq)
  rw [contractum] at ht
  have cards := congrArg Multiset.card ht
  simp at cards

/-- Nor the shape of a Drop event: the redex has no dropped quotation among
its components. -/
theorem runReceived_not_dropShape :
    ¬ DropShape (cls runReceivedSource) (cls runReceivedTarget) := by
  rintro ⟨code, others, hs, -⟩
  have sourceAtoms : atoms runReceivedSource =
      {cls (inpT channelTerm (.var .zero))} + ({cls (outT channelTerm nilT)} + 0) := rfl
  rw [atomsQ_cls, sourceAtoms] at hs
  have dropMember : cls (drpT (quoT code)) ∈
      ({cls (inpT channelTerm (.var .zero))} + ({cls (outT channelTerm nilT)} + 0) :
        Multiset (Cls [] Srt.pr)) := by
    rw [hs]
    simp
  rw [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_add, Multiset.mem_singleton]
    at dropMember
  rcases dropMember with same | same | none
  · have parts : ({cls (quoT code)} : Multiset (Cls [] Srt.nm)) = 0 :=
      dropParts_invariant (cls_eq_iff.mp same)
    exact Multiset.singleton_ne_zero _ parts
  · have parts : ({cls (quoT code)} : Multiset (Cls [] Srt.nm)) = 0 :=
      dropParts_invariant (cls_eq_iff.mp same)
    exact Multiset.singleton_ne_zero _ parts
  · exact absurd none (Multiset.notMem_zero _)

/-- **The authored step is not an event of the strict classifier.**  The
interactive theory steps from the redex to the drop of the quoted payload;
no event of the strict classifier joins the translations of those two
terms. -/
theorem runReceived_not_classified :
    ¬ ExtendedReduction strictLocalRules equations runReceivedSource runReceivedTarget := by
  intro event
  rcases steps_inversion (rest := []) (.inl rfl)
      ((extension_iff_steps strictRules _ _).mp event) with shape | ⟨impossible, -⟩
  · exact runReceived_not_commShape shape
  · cases impossible

/-- **Nor of the classifier of the profile with the Drop rule.**  The Drop
rule contracts the residue the authored rule leaves; it does not make the
authored step one event. -/
theorem runReceived_not_classified_book :
    ¬ ExtendedReduction bookLocalRules equations runReceivedSource runReceivedTarget := by
  intro event
  rcases steps_inversion (rest := [drop]) (.inr rfl)
      ((extension_iff_steps bookRules _ _).mp event) with shape | ⟨-, shape⟩
  · exact runReceived_not_commShape shape
  · exact runReceived_not_dropShape shape

/-- **The difference is one Drop redex.**  In the profile with the Drop
rule, the translated authored contractum reduces to the target of the
classifier's event. -/
theorem runReceived_residue_drops :
    ExtendedReduction bookLocalRules equations runReceivedTarget nilT :=
  classified_of_equiv (rules := bookRules) (.refl _) (parT_nil nilT)
    (parCong_classified [drop] nilT (drop_book_classified nilT))

/-- **The obstruction.**  Some step of the interactive theory, between terms
that both translate, is not an event of either classifier on their
translations. -/
theorem step_not_always_classified :
    ∃ (source target : rhoIGSLT.toGSLT.Term) (sourceTerm targetTerm : Term sig [] Srt.pr),
      rhoIGSLT.toGSLT.Step source target ∧
      tProc (Env.empty []) source.1 = some sourceTerm ∧
      tProc (Env.empty []) target.1 = some targetTerm ∧
      ¬ ExtendedReduction strictLocalRules equations sourceTerm targetTerm ∧
      ¬ ExtendedReduction bookLocalRules equations sourceTerm targetTerm :=
  ⟨runReceivedTerm, runReceivedReductTerm, runReceivedSource, runReceivedTarget,
    runReceived_step, runReceived_translation, runReceivedReduct_translation,
    runReceived_not_classified, runReceived_not_classified_book⟩

section Interpreted

open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep)

/-- On the same redex the interpreted relation runs the payload: its
contractum is the null process, whose translation is the target of the
classifier's event. -/
theorem runReceived_interpreted_step :
    RhoStep runReceived (.collection .hashBag [zero] none) ∧
      tProc (Env.empty []) (.collection .hashBag [zero] none) = some (parT nilT nilT) := by
  refine ⟨?_, rfl⟩
  have step := RhoStep.comm (free := FreeSortContext.empty) (bound := []) channel
    (.apply "PDrop" [.bvar 0]) zero []
    (ProcWellSorted.drop (NameWellSorted.bvar (by decide))) ProcWellSorted.unit
  have contractum :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.semanticCommSubst
        (.apply "PDrop" [.bvar 0]) zero = zero := by decide +kernel
  rw [contractum] at step
  exact step

end Interpreted

/-! ## An instance: the received name run on a dropped name -/

/-- `for(x <- @0){ *x } | @0!(*@0)`: the continuation runs the received name,
and the payload is itself the drop of a name. -/
def runDropped : Pattern :=
  .collection .hashBag
    [.apply "PInput" [channel, .lambda none (.apply "PDrop" [.bvar 0])],
      .apply "POutput" [channel, .apply "PDrop" [channel]]] none

/-- `*@*@0`: the authored contractum. -/
def runDroppedReduct : Pattern :=
  .collection .hashBag [.apply "PDrop" [.apply "NQuote" [.apply "PDrop" [channel]]]] none

/-- The redex as a term of the interactive carrier. -/
def runDroppedTerm : rhoIGSLT.toGSLT.Term :=
  ClosedTerm.ofCheck (sort := rhoInteractivePresentation.interactingLangSort) runDropped
    (by decide +kernel)

/-- The contractum as a term of the interactive carrier. -/
def runDroppedReductTerm : rhoIGSLT.toGSLT.Term :=
  ClosedTerm.ofCheck (sort := rhoInteractivePresentation.interactingLangSort)
    runDroppedReduct (by decide +kernel)

/-- The interactive theory steps. -/
theorem runDropped_step : rhoIGSLT.toGSLT.Step runDroppedTerm runDroppedReductTerm :=
  primitiveStep_to_presentedStep (presentation := rhoInteractivePresentation)
    (exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩)

/-- The translated redex: the payload is the drop of the channel. -/
theorem runDropped_translation :
    tProc (Env.empty []) runDropped =
      some (parT (inpT channelTerm (.var .zero))
        (parT (outT channelTerm (drpT channelTerm)) nilT)) := rfl

/-- Quote/drop cancellation is already performed by the translation: the
drop of `@*@0` is the drop of `@0`. -/
theorem runDroppedReduct_translation :
    tProc (Env.empty []) runDroppedReduct = some (parT (drpT channelTerm) nilT) := rfl

/-- **A dropped payload is its own dropped name**, so this step is an event
of the classifier although the continuation runs the received name. -/
theorem runDropped_classified :
    ExtendedReduction strictLocalRules equations
      (parT (inpT channelTerm (.var .zero))
        (parT (outT channelTerm (drpT channelTerm)) nilT))
      (parT (drpT channelTerm) nilT) := by
  refine classified_of_equiv (rules := strictRules) ?_ ?_
    (comm_classified [] channelTerm (drpT channelTerm) (.var .zero))
  · exact (equiv_parT (.refl _) (parT_nil _)).trans (parT_comm _ _)
  · exact (parT_nil _).symm

/-- **The join, inhabited.**  A step of the interactive theory whose
translated ends are joined by an event of the strict classifier. -/
theorem step_sometimes_classified :
    ∃ (source target : rhoIGSLT.toGSLT.Term) (sourceTerm targetTerm : Term sig [] Srt.pr),
      rhoIGSLT.toGSLT.Step source target ∧
      tProc (Env.empty []) source.1 = some sourceTerm ∧
      tProc (Env.empty []) target.1 = some targetTerm ∧
      ExtendedReduction strictLocalRules equations sourceTerm targetTerm :=
  ⟨sendOnReceivedTerm, sendOnReceivedReductTerm, _, _, sendOnReceived_step,
    sendOnReceived_translation, sendOnReceivedReduct_translation, sendOnReceived_classified⟩

/-! ## Where the two presentations differ -/

/-- **Name binding against payload binding.**  Beneath an input, the bound
name translates to the quotation of the received process, and its drop to
the received process itself. -/
theorem received_name_and_process :
    tName (Env.empty []).up (.bvar 0) = some (quoT (.var .zero)) ∧
      tProc (Env.empty []).up (.apply "PDrop" [.bvar 0]) = some (.var .zero) :=
  ⟨rfl, rfl⟩

/-- `@0!(0) | for(x <- @0){ x!(0) }`: the two components of `sendOnReceived`
listed in the other order. -/
def sendOnReceivedSwapped : Pattern :=
  .collection .hashBag
    [.apply "POutput" [channel, zero],
      .apply "PInput" [channel, .lambda none (.apply "POutput" [.bvar 0, zero])]] none

/-- **A bag against binary composition.**  The two listings of one bag are
different patterns and translate to different terms; the terms are equal by
the equations of parallel composition, which the bag builds in. -/
theorem bag_order :
    sendOnReceived ≠ sendOnReceivedSwapped ∧
      ∃ first second : Term sig [] Srt.pr,
        tProc (Env.empty []) sendOnReceived = some first ∧
        tProc (Env.empty []) sendOnReceivedSwapped = some second ∧
        first ≠ second ∧ EqClosure equations first second := by
  refine ⟨by decide, _, _, rfl, rfl, ?_, parT_swap _ _ _⟩
  intro same
  cases same

/-- `@*@0!(0)`: an output on the quotation of the drop of `@0`. -/
def sendOnQuotedDrop : Pattern :=
  .apply "POutput" [.apply "NQuote" [.apply "PDrop" [channel]], zero]

/-- `@0!(0)`. -/
def sendOnChannel : Pattern := .apply "POutput" [channel, zero]

/-- **The translation is not injective.**  It resolves the quotation of a
dropped name to that name, so two different terms of the interactive
carrier, equal by the quote/drop equation, have one translation. -/
theorem translation_not_injective :
    ClosedTermWellSorted rhoCalc rhoInteractivePresentation.interactingLangSort
        sendOnQuotedDrop ∧
      ClosedTermWellSorted rhoCalc rhoInteractivePresentation.interactingLangSort
        sendOnChannel ∧
      sendOnQuotedDrop ≠ sendOnChannel ∧
      tProc (Env.empty []) sendOnQuotedDrop = tProc (Env.empty []) sendOnChannel ∧
      ∃ term, tProc (Env.empty []) sendOnChannel = some term :=
  ⟨checkClosedTerm_sound (by decide +kernel), checkClosedTerm_sound (by decide +kernel),
    by decide, rfl, _, rfl⟩

/-- `for(x <- @0){ @(x!(0))!(0) }`: a quotation whose code mentions the bound
name. -/
def quotedBound : Pattern :=
  .apply "PInput" [channel, .lambda none
    (.apply "POutput" [.apply "NQuote" [.apply "POutput" [.bvar 0, zero]], zero])]

/-- **The quotation boundary.**  A term of the interactive carrier whose
quoted code mentions an enclosing bound name has no translation: the
translation reads a quotation as closed code. -/
theorem quotedBound_closed_untranslated :
    ClosedTermWellSorted rhoCalc rhoInteractivePresentation.interactingLangSort quotedBound ∧
      tProc (Env.empty []) quotedBound = none :=
  ⟨checkClosedTerm_sound (by decide +kernel), rfl⟩

/-- `for(x <- @0){ @{*x}!(0) }`: the quotation of the singleton bag of the
drop of the bound name. -/
def quotedSingleton : Pattern :=
  .apply "PInput" [channel, .lambda none
    (.apply "POutput"
      [.apply "NQuote" [.collection .hashBag [.apply "PDrop" [.bvar 0]] none], zero])]

/-- `for(x <- @0){ @*x!(0) }`. -/
def quotedDrop : Pattern :=
  .apply "PInput" [channel, .lambda none
    (.apply "POutput" [.apply "NQuote" [.apply "PDrop" [.bvar 0]], zero])]

/-- `for(x <- @0){ x!(0) }`. -/
def boundChannel : Pattern :=
  .apply "PInput" [channel, .lambda none (.apply "POutput" [.bvar 0, zero])]

/-- The three processes as terms of the interactive carrier. -/
def quotedSingletonTerm : rhoIGSLT.toGSLT.Term :=
  ClosedTerm.ofCheck (sort := rhoInteractivePresentation.interactingLangSort)
    quotedSingleton (by decide +kernel)

/-- The middle term of the chain. -/
def quotedDropTerm : rhoIGSLT.toGSLT.Term :=
  ClosedTerm.ofCheck (sort := rhoInteractivePresentation.interactingLangSort) quotedDrop
    (by decide +kernel)

/-- The term in which the bound name is written plainly. -/
def boundChannelTerm : rhoIGSLT.toGSLT.Term :=
  ClosedTerm.ofCheck (sort := rhoInteractivePresentation.interactingLangSort) boundChannel
    (by decide +kernel)

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness
  (rhoParallelAlgebra quoteDropEquation quoteDropEquation_mem) in
/-- The three terms are equal in the interactive theory: a singleton bag is
its element, and the quotation of a dropped name is that name. -/
theorem quotedSingleton_equivalent :
    rhoIGSLT.toGSLT.equations.r quotedSingletonTerm boundChannelTerm := by
  have sorted : EquationSemantics.SortedAt rhoCalc
      (.collection .hashBag [.apply "PDrop" [.bvar 0]] none) "Proc" :=
    ⟨FreeTypeContext.empty, [TypeExpr.name], checkHasType_sound (by decide +kernel)⟩
  have first : EquationSemantics.EquationContextStep defaultBasePremises rhoCalc
      quotedSingleton quotedDrop :=
    EquationSemantics.EquationContextStep.inContext
      (.apply "PInput" [channel]
        (.lambda none (.apply "POutput" [] (.apply "NQuote" [] .hole []) [zero])) [])
      (Or.inr (EquationSemantics.DerivedInstance.singleton rhoParallelAlgebra rfl sorted))
  obtain ⟨bindings, matched, applied⟩ :
      ∃ bindings ∈ matchPattern quoteDropEquation.left
          (.apply "NQuote" [.apply "PDrop" [.bvar 0]]),
        applyBindings bindings quoteDropEquation.right = .bvar 0 := by
    decide +kernel
  have second : EquationSemantics.EquationContextStep defaultBasePremises rhoCalc
      quotedDrop boundChannel :=
    EquationSemantics.EquationContextStep.inContext
      (.apply "PInput" [channel] (.lambda none (.apply "POutput" [] .hole [zero])) [])
      (Or.inl ⟨0, EquationSemantics.EquationInstanceAt.forward
        (equation := quoteDropEquation) quoteDropEquation_mem matched (PremisesAt.nil _)
        applied⟩)
  exact Relation.EqvGen.trans _ quotedDropTerm _ (Relation.EqvGen.rel _ _ first)
    (Relation.EqvGen.rel _ _ second)

/-- **The translation is not invariant under the static equivalence.**  Two
equal terms of the interactive carrier, one with a translation and one with
none: the translation resolves the quotation of a dropped name only when it
is written as such. -/
theorem translation_not_invariant :
    ∃ left right : rhoIGSLT.toGSLT.Term, rhoIGSLT.toGSLT.equations.r left right ∧
      tProc (Env.empty []) left.1 = none ∧
      ∃ term, tProc (Env.empty []) right.1 = some term :=
  ⟨quotedSingletonTerm, boundChannelTerm, quotedSingleton_equivalent, rfl, _, rfl⟩

end Instances

end Mettapedia.GSLT.LanguageDef.ClassifiedJoin.Rho
