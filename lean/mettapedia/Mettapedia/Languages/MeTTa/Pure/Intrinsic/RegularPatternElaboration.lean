import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularBidirectionalCompleteness
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationTypingBridge

/-!
# Strict Pattern elaboration for the regular Pure kernel

The production syntax is a partial elaboration from locally nameless
`Pattern` syntax into intrinsically scoped, declaration-free `PureTm` syntax.
Only after that boundary succeeds does the exact regular checker become the
authority.  The elaborator deliberately does not reuse the more permissive
authored Pattern typing relation: that relation admits terms outside the
presupposition-closed regular kernel.

Binder bodies are opened with the established fresh-name policy before their
recursive elaboration.  This makes the executable elaborator a partial inverse
of contextual quotation while preserving locally nameless hygiene.
-/

namespace Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.PatternBridge

/-! ## Syntax boundary -/

/-- Stable failures of the Pattern-to-intrinsic syntax boundary. -/
inductive RegularPatternSyntaxError where
  | danglingBoundVariable (index : Nat)
  | unknownFreeVariable (name : String)
  | binderNameCollision (name : String)
  | malformedConstructor (name : String) (arity : Nat)
  | unexpectedBinder
  | unsupportedMultiBinder
  | unsupportedExplicitSubstitution
  | unsupportedCollection
  deriving DecidableEq, Repr

/-- A successfully elaborated Pattern is declaration-free by
construction.  Quotation agreement is theorem-layer evidence and is not
carried on the ordinary execution path. -/
structure RegularPatternTerm (n : Nat) where
  term : PureTm n
  constantFree : ConstantFree term

/-- Resolve a contextual quotation name to its intrinsic de Bruijn index. -/
def resolveQuoteName : {n : Nat} → QuoteEnv n → String → Option (Fin n)
  | 0, _, _ => none
  | n + 1, environment, name =>
      if _head : environment 0 = name then
        some 0
      else
        (resolveQuoteName (fun index : Fin n => environment index.succ) name).map
          Fin.succ

/-- Name resolution finds every variable supplied by an injective quotation
environment. -/
theorem resolveQuoteName_self {environment : QuoteEnv n}
    (injective : Function.Injective environment) (index : Fin n) :
    resolveQuoteName environment (environment index) = some index := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
      refine Fin.cases ?_ ?_ index
      · simp [resolveQuoteName]
      · intro preceding
        have head_ne : environment 0 ≠ environment preceding.succ := by
          intro equal
          have : (0 : Fin (n + 1)) = preceding.succ := injective equal
          cases this
        have tail_injective : Function.Injective
            (fun i : Fin n => environment i.succ) := by
          intro i j equal
          exact Fin.succ_inj.mp (injective equal)
        simp [resolveQuoteName, head_ne, ih tail_injective preceding]

/-- Every successful lookup names the returned contextual index. -/
theorem resolveQuoteName_sound {environment : QuoteEnv n} {name : String}
    {index : Fin n} (computed : resolveQuoteName environment name = some index) :
    environment index = name := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
      unfold resolveQuoteName at computed
      split at computed
      · rename_i head
        have index_eq : index = 0 := Option.some.inj computed.symm
        subst index
        exact head
      · rename_i head_ne
        cases tail : resolveQuoteName
            (fun preceding : Fin n => environment preceding.succ) name with
        | none => simp [tail] at computed
        | some preceding =>
            simp [tail] at computed
            subst index
            exact ih (environment := fun i : Fin n => environment i.succ)
              (index := preceding) tail

/-- Constructor count ignores payload sizes.  Unlike Lean's generic `sizeOf`,
it therefore assigns the same size to a bound variable and the fresh free
variable used to open it. -/
def patternNodeCount : Pattern → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .apply _ arguments => 1 + (arguments.map patternNodeCount).sum
  | .lambda _ body => 1 + patternNodeCount body
  | .multiLambda _ _ body => 1 + patternNodeCount body
  | .subst body replacement => 1 + patternNodeCount body + patternNodeCount replacement
  | .collection _ elements _ => 1 + (elements.map patternNodeCount).sum
termination_by pattern => sizeOf pattern

/-- Opening by a free variable preserves constructor count. -/
theorem patternNodeCount_openBVar_fvar
    (depth : Nat) (name : String) (pattern : Pattern) :
    patternNodeCount (openBVar depth (.fvar name) pattern) =
      patternNodeCount pattern := by
  apply Pattern.inductionOn
    (motive := fun current => ∀ depth,
      patternNodeCount (openBVar depth (.fvar name) current) =
        patternNodeCount current) pattern
  · intro index currentDepth
    rw [openBVar.eq_1]
    split <;> simp only [patternNodeCount]
  · intro variableName currentDepth
    rw [openBVar.eq_2]
  · intro constructorName arguments inductionHypothesis currentDepth
    simp only [openBVar, patternNodeCount]
    congr 1
    apply congrArg List.sum
    rw [List.map_map]
    apply List.map_congr_left
    intro argument member
    exact inductionHypothesis argument member currentDepth
  · intro binder body inductionHypothesis currentDepth
    simp only [openBVar, patternNodeCount]
    rw [inductionHypothesis (currentDepth + 1)]
  · intro arity binders body inductionHypothesis currentDepth
    simp only [openBVar, patternNodeCount]
    rw [inductionHypothesis (currentDepth + arity)]
  · intro body replacement bodyHypothesis replacementHypothesis currentDepth
    simp only [openBVar, patternNodeCount]
    rw [bodyHypothesis (currentDepth + 1), replacementHypothesis currentDepth]
  · intro collectionType elements rest inductionHypothesis currentDepth
    simp only [openBVar, patternNodeCount]
    congr 1
    apply congrArg List.sum
    rw [List.map_map]
    apply List.map_congr_left
    intro element member
    exact inductionHypothesis element member currentDepth

/-- Executable strict elaboration.  A binder body is opened before recursive
descent, so any surviving bound variable is necessarily dangling. -/
def elaborateRegularPatternWith : {n : Nat} →
    (policy : BinderPolicy) → (depth : Nat) → (environment : QuoteEnv n) →
    Pattern → Except RegularPatternSyntaxError (RegularPatternTerm n)
  | _, _, _, _, .bvar index =>
      throw (.danglingBoundVariable index)
  | _, _, _, environment, .fvar name =>
      match resolveQuoteName environment name with
      | none => throw (.unknownFreeVariable name)
      | some index => pure ⟨.var index, .var index⟩
  | _, _, _, _, .apply "U0" [] =>
      pure ⟨.u0, .u0⟩
  | _, _, _, _, .apply "U1" [] =>
      pure ⟨.u1, .u1⟩
  | _, policy, depth, environment,
      .apply "Pi" [domain, .lambda none body] => do
      let domainTerm <- elaborateRegularPatternWith policy depth environment domain
      let name := policy.name depth
      if fresh : isFresh name body = true then
        let bodyTerm <- elaborateRegularPatternWith policy (depth + 1)
          (envCons name environment) (openBVar 0 (.fvar name) body)
        pure ⟨.pi domainTerm.term bodyTerm.term,
          .pi domainTerm.constantFree bodyTerm.constantFree⟩
      else
        throw (.binderNameCollision name)
  | _, policy, depth, environment,
      .apply "Sigma" [domain, .lambda none body] => do
      let domainTerm <- elaborateRegularPatternWith policy depth environment domain
      let name := policy.name depth
      if fresh : isFresh name body = true then
        let bodyTerm <- elaborateRegularPatternWith policy (depth + 1)
          (envCons name environment) (openBVar 0 (.fvar name) body)
        pure ⟨.sigma domainTerm.term bodyTerm.term,
          .sigma domainTerm.constantFree bodyTerm.constantFree⟩
      else
        throw (.binderNameCollision name)
  | _, policy, depth, environment, .apply "Id" [carrier, left, right] => do
      let carrierTerm <- elaborateRegularPatternWith policy depth environment carrier
      let leftTerm <- elaborateRegularPatternWith policy depth environment left
      let rightTerm <- elaborateRegularPatternWith policy depth environment right
      pure ⟨.id carrierTerm.term leftTerm.term rightTerm.term,
        .id carrierTerm.constantFree leftTerm.constantFree rightTerm.constantFree⟩
  | _, policy, depth, environment, .apply "Lam" [.lambda none body] => do
      let name := policy.name depth
      if fresh : isFresh name body = true then
        let bodyTerm <- elaborateRegularPatternWith policy (depth + 1)
          (envCons name environment) (openBVar 0 (.fvar name) body)
        pure ⟨.lam bodyTerm.term, .lam bodyTerm.constantFree⟩
      else
        throw (.binderNameCollision name)
  | _, policy, depth, environment, .apply "App" [function, argument] => do
      let functionTerm <- elaborateRegularPatternWith policy depth environment function
      let argumentTerm <- elaborateRegularPatternWith policy depth environment argument
      pure ⟨.app functionTerm.term argumentTerm.term,
        .app functionTerm.constantFree argumentTerm.constantFree⟩
  | _, policy, depth, environment, .apply "Pair" [first, second] => do
      let firstTerm <- elaborateRegularPatternWith policy depth environment first
      let secondTerm <- elaborateRegularPatternWith policy depth environment second
      pure ⟨.pair firstTerm.term secondTerm.term,
        .pair firstTerm.constantFree secondTerm.constantFree⟩
  | _, policy, depth, environment, .apply "Fst" [pair] => do
      let pairTerm <- elaborateRegularPatternWith policy depth environment pair
      pure ⟨.fst pairTerm.term, .fst pairTerm.constantFree⟩
  | _, policy, depth, environment, .apply "Snd" [pair] => do
      let pairTerm <- elaborateRegularPatternWith policy depth environment pair
      pure ⟨.snd pairTerm.term, .snd pairTerm.constantFree⟩
  | _, policy, depth, environment, .apply "Refl" [term] => do
      let elaborated <- elaborateRegularPatternWith policy depth environment term
      pure ⟨.refl elaborated.term, .refl elaborated.constantFree⟩
  | _, _, _, _, .apply name arguments =>
      throw (.malformedConstructor name arguments.length)
  | _, _, _, _, .lambda _ _ => throw .unexpectedBinder
  | _, _, _, _, .multiLambda _ _ _ => throw .unsupportedMultiBinder
  | _, _, _, _, .subst _ _ => throw .unsupportedExplicitSubstitution
  | _, _, _, _, .collection _ _ _ => throw .unsupportedCollection
termination_by _ _ _ _ pattern => patternNodeCount pattern
decreasing_by
  all_goals simp [patternNodeCount, patternNodeCount_openBVar_fvar] <;> omega

/-- Public strict syntax boundary at quotation depth zero. -/
def elaborateRegularPattern (policy : BinderPolicy) (environment : QuoteEnv n)
    (pattern : Pattern) : Except RegularPatternSyntaxError (RegularPatternTerm n) :=
  elaborateRegularPatternWith policy 0 environment pattern

/-! ## Formation-directed checking boundary -/

/-- The four diagnostic phases are kept disjoint so a malformed expected type
is reported before term syntax or term typing is consulted. -/
inductive RegularPatternCheckError where
  | expectedSyntax (error : RegularPatternSyntaxError)
  | expectedFormation (error : RegularCheckError)
  | termSyntax (error : RegularPatternSyntaxError)
  | termTyping (error : RegularCheckError)
  deriving DecidableEq, Repr

/-- Prepared expected types distinguish the upper-sort boundary from ordinary
formed types. -/
inductive RegularExpectedStatus {Γ : Ctx n} : PureTm n → Type where
  | top (equal : expected = .u1) : RegularExpectedStatus expected
  | formed (typing : RegularHasType Γ expected .u1) :
      RegularExpectedStatus expected

/-- Formation is synthesized before the subject term is inspected. -/
def prepareRegularExpected {Γ : Ctx n} (context : RegularCtx Γ)
    (expected : PureTm n) :
    Except RegularCheckError (RegularExpectedStatus (Γ := Γ) expected) :=
  if top : expected = .u1 then
    pure (.top top)
  else do
    let inferred <- inferRegularType context expected
    let formed <- inferred.asFormedType? context
    pure (.formed formed.down)

/-- Consume a prepared expected type without repeating formation. -/
def checkPreparedRegularExpected {Γ : Ctx n} (context : RegularCtx Γ)
    (term expected : PureTm n) (status : RegularExpectedStatus (Γ := Γ) expected) :
    Except RegularCheckError (RegularChecked (Γ := Γ) term expected) :=
  match status with
  | .top equal => equal ▸ checkRegularTop context term
  | .formed typing => checkRegularFormed context term expected typing

/-- Successful Pattern admission contains the two strict elaborations and the
intrinsic regular typing derivation returned by the exact checker. -/
structure RegularPatternAdmission {Γ : Ctx n} (context : RegularCtx Γ)
    (policy : BinderPolicy) (environment : QuoteEnv n)
    (termPattern expectedPattern : Pattern) where
  term : RegularPatternTerm n
  expected : RegularPatternTerm n
  termComputed : elaborateRegularPattern policy environment termPattern = .ok term
  expectedComputed : elaborateRegularPattern policy environment expectedPattern = .ok expected
  checked : RegularChecked (Γ := Γ) term.term expected.term

/-- Production Pattern query.  Expected syntax and formation are processed
before term syntax and typing, yielding stable early diagnostics. -/
def elaborateAndCheckRegularPattern {Γ : Ctx n} (context : RegularCtx Γ)
    (policy : BinderPolicy) (environment : QuoteEnv n)
    (termPattern expectedPattern : Pattern) :
    Except RegularPatternCheckError
      (RegularPatternAdmission context policy environment termPattern expectedPattern) :=
  match expectedComputed : elaborateRegularPattern policy environment expectedPattern with
  | .error syntaxError => .error (.expectedSyntax syntaxError)
  | .ok expected =>
      match _formationComputed : prepareRegularExpected context expected.term with
      | .error formationError => .error (.expectedFormation formationError)
      | .ok expectedStatus =>
          match termComputed : elaborateRegularPattern policy environment termPattern with
          | .error syntaxError => .error (.termSyntax syntaxError)
          | .ok term =>
              match _typingComputed : checkPreparedRegularExpected context term.term
                  expected.term expectedStatus with
              | .error typingError => .error (.termTyping typingError)
              | .ok checked =>
                  .ok ⟨term, expected, termComputed, expectedComputed, checked⟩

/-- Every admitted Pattern query is a genuine regular intrinsic judgment. -/
def RegularPatternAdmission.regularJudgment
    {Γ : Ctx n} {context : RegularCtx Γ} {policy : BinderPolicy}
    {environment : QuoteEnv n} {termPattern expectedPattern : Pattern}
    (admission : RegularPatternAdmission context policy environment
      termPattern expectedPattern) :
    RegularJudgment Γ admission.term.term admission.expected.term :=
  ⟨context, admission.checked.typing⟩

/-! ## Quotation completeness -/

/-- Successful strict elaboration is reflected by the established contextual
quotation. -/
theorem elaborateRegularPatternWith_reflects
    {policy : BinderPolicy} {depth : Nat} {environment : QuoteEnv n}
    (good : QuoteEnvGood policy depth environment) {pattern : Pattern}
    {result : RegularPatternTerm n}
    (computed : elaborateRegularPatternWith policy depth environment pattern =
      .ok result) :
    quoteTmWith policy.name depth environment result.term = pattern := by
  fun_induction elaborateRegularPatternWith policy depth environment pattern
  case case3 =>
    have named := resolveQuoteName_sound (computed := by assumption)
    have resultEq := Except.ok.inj (show Except.ok _ = Except.ok result from computed)
    subst result
    simpa [quoteTmWith] using named
  case case4 =>
    have resultEq := Except.ok.inj (show Except.ok _ = Except.ok result from computed)
    subst result
    rfl
  case case5 =>
    have resultEq := Except.ok.inj (show Except.ok _ = Except.ok result from computed)
    subst result
    rfl
  case case6 =>
    rename_i _ policy depth domain body environment ihDomain ihBody
    cases domainComputed : elaborateRegularPatternWith policy depth environment domain with
    | error error =>
        simp [domainComputed, Bind.bind, Except.bind] at computed
    | ok domainTerm =>
        rw [domainComputed] at computed
        dsimp [Bind.bind, Except.instMonad, Except.bind] at computed
        split at computed
        next fresh =>
          cases bodyComputed : elaborateRegularPatternWith policy (depth + 1)
              (envCons (policy.name depth) environment)
              (openBVar 0 (.fvar (policy.name depth)) body) with
          | error error =>
              simp [bodyComputed] at computed
          | ok bodyTerm =>
              simp [bodyComputed] at computed
              change Except.ok _ = Except.ok result at computed
              injection computed with resultEq
              subst result
              have domainQuoted := ihDomain good domainComputed
              have bodyQuoted := ihBody fresh good.envCons bodyComputed
              have closeOpen :
                  closeFVar 0 (policy.name depth)
                      (openBVar 0 (.fvar (policy.name depth)) body) = body := by
                simpa [Mettapedia.Languages.MeTTa.Pure.BinderOps.closeBVar] using
                  (Mettapedia.Languages.MeTTa.Pure.BinderOps.closeBVar_openBVar_cancel
                    (k := 0) fresh)
              simp [quoteTmWith, mkPi, domainQuoted, bodyQuoted, closeOpen]
        next notFresh =>
          simp at computed
  case case7 =>
    rename_i _ policy depth domain body environment ihDomain ihBody
    cases domainComputed : elaborateRegularPatternWith policy depth environment domain with
    | error error =>
        simp [domainComputed, Bind.bind, Except.bind] at computed
    | ok domainTerm =>
        rw [domainComputed] at computed
        dsimp [Bind.bind, Except.instMonad, Except.bind] at computed
        split at computed
        next fresh =>
          cases bodyComputed : elaborateRegularPatternWith policy (depth + 1)
              (envCons (policy.name depth) environment)
              (openBVar 0 (.fvar (policy.name depth)) body) with
          | error error =>
              simp [bodyComputed] at computed
          | ok bodyTerm =>
              simp [bodyComputed] at computed
              change Except.ok _ = Except.ok result at computed
              injection computed with resultEq
              subst result
              have domainQuoted := ihDomain good domainComputed
              have bodyQuoted := ihBody fresh good.envCons bodyComputed
              have closeOpen :
                  closeFVar 0 (policy.name depth)
                      (openBVar 0 (.fvar (policy.name depth)) body) = body := by
                simpa [Mettapedia.Languages.MeTTa.Pure.BinderOps.closeBVar] using
                  (Mettapedia.Languages.MeTTa.Pure.BinderOps.closeBVar_openBVar_cancel
                    (k := 0) fresh)
              simp [quoteTmWith, mkSigma, domainQuoted, bodyQuoted, closeOpen]
        next notFresh =>
          simp at computed
  case case8 =>
    rename_i _ policy depth carrier left right environment ihCarrier ihLeft ihRight
    cases carrierComputed : elaborateRegularPatternWith policy depth environment carrier with
    | error error =>
        simp [carrierComputed, Bind.bind, Except.bind] at computed
    | ok carrierTerm =>
        cases leftComputed : elaborateRegularPatternWith policy depth environment left with
        | error error =>
            simp [carrierComputed, leftComputed, Bind.bind, Except.bind] at computed
        | ok leftTerm =>
            cases rightComputed : elaborateRegularPatternWith policy depth environment right with
            | error error =>
                simp [carrierComputed, leftComputed, rightComputed, Bind.bind,
                  Except.bind] at computed
            | ok rightTerm =>
                simp [carrierComputed, leftComputed, rightComputed, Bind.bind,
                  Except.bind] at computed
                change Except.ok _ = Except.ok result at computed
                injection computed with resultEq
                subst result
                simp [quoteTmWith, mkId, ihCarrier good carrierComputed,
                  ihLeft good leftComputed, ihRight good rightComputed]
  case case9 =>
    rename_i _ policy depth body name fresh environment ihBody
    cases bodyComputed : elaborateRegularPatternWith policy (depth + 1)
        (envCons name environment) (openBVar 0 (.fvar name) body) with
    | error error =>
        simp [bodyComputed, Bind.bind, Except.bind] at computed
    | ok bodyTerm =>
        simp [bodyComputed, Bind.bind, Except.bind] at computed
        change Except.ok _ = Except.ok result at computed
        injection computed with resultEq
        subst result
        have bodyQuoted := ihBody good.envCons bodyComputed
        have closeOpen : closeFVar 0 name (openBVar 0 (.fvar name) body) = body := by
          simpa [Mettapedia.Languages.MeTTa.Pure.BinderOps.closeBVar] using
            (Mettapedia.Languages.MeTTa.Pure.BinderOps.closeBVar_openBVar_cancel
              (k := 0) fresh)
        simp [quoteTmWith, mkLam, name, bodyQuoted, closeOpen]
  case case11 =>
    rename_i _ policy depth function argument environment ihFunction ihArgument
    cases functionComputed : elaborateRegularPatternWith policy depth environment function with
    | error error =>
        simp [functionComputed, Bind.bind, Except.bind] at computed
    | ok functionTerm =>
        cases argumentComputed : elaborateRegularPatternWith policy depth environment argument with
        | error error =>
            simp [functionComputed, argumentComputed, Bind.bind, Except.bind] at computed
        | ok argumentTerm =>
            simp [functionComputed, argumentComputed, Bind.bind,
              Except.bind] at computed
            change Except.ok _ = Except.ok result at computed
            injection computed with resultEq
            subst result
            simp [quoteTmWith, mkApp, ihFunction good functionComputed,
              ihArgument good argumentComputed]
  case case12 =>
    rename_i _ policy depth first second environment ihFirst ihSecond
    cases firstComputed : elaborateRegularPatternWith policy depth environment first with
    | error error =>
        simp [firstComputed, Bind.bind, Except.bind] at computed
    | ok firstTerm =>
        cases secondComputed : elaborateRegularPatternWith policy depth environment second with
        | error error =>
            simp [firstComputed, secondComputed, Bind.bind, Except.bind] at computed
        | ok secondTerm =>
            simp [firstComputed, secondComputed, Bind.bind, Except.bind] at computed
            change Except.ok _ = Except.ok result at computed
            injection computed with resultEq
            subst result
            simp [quoteTmWith, mkPair, ihFirst good firstComputed,
              ihSecond good secondComputed]
  case case13 =>
    rename_i _ policy depth pair environment ihPair
    cases pairComputed : elaborateRegularPatternWith policy depth environment pair with
    | error error =>
        simp [pairComputed, Bind.bind, Except.bind] at computed
    | ok pairTerm =>
        simp [pairComputed, Bind.bind, Except.bind] at computed
        change Except.ok _ = Except.ok result at computed
        injection computed with resultEq
        subst result
        simp [quoteTmWith, mkFst, ihPair good pairComputed]
  case case14 =>
    rename_i _ policy depth pair environment ihPair
    cases pairComputed : elaborateRegularPatternWith policy depth environment pair with
    | error error =>
        simp [pairComputed, Bind.bind, Except.bind] at computed
    | ok pairTerm =>
        simp [pairComputed, Bind.bind, Except.bind] at computed
        change Except.ok _ = Except.ok result at computed
        injection computed with resultEq
        subst result
        simp [quoteTmWith, mkSnd, ihPair good pairComputed]
  case case15 =>
    rename_i _ policy depth term environment ihTerm
    cases termComputed : elaborateRegularPatternWith policy depth environment term with
    | error error =>
        simp [termComputed, Bind.bind, Except.bind] at computed
    | ok elaborated =>
        simp [termComputed, Bind.bind, Except.bind] at computed
        change Except.ok _ = Except.ok result at computed
        injection computed with resultEq
        subst result
        simp [quoteTmWith, mkRefl, ihTerm good termComputed]
  all_goals simp_all

/-- Depth-zero reflection for the public elaborator. -/
theorem elaborateRegularPattern_reflects
    {policy : BinderPolicy} {environment : QuoteEnv n}
    (good : QuoteEnvGood policy 0 environment) {pattern : Pattern}
    {result : RegularPatternTerm n}
    (computed : elaborateRegularPattern policy environment pattern = .ok result) :
    quoteTmWith policy.name 0 environment result.term = pattern :=
  elaborateRegularPatternWith_reflects good computed

/-- Every declaration-free intrinsic term is admitted by the strict syntax
boundary after contextual quotation.  Together with successful reflection,
this makes elaboration and quotation an exact partial isomorphism on the
regular Pattern grammar. -/
theorem elaborateRegularPatternWith_quote_complete
    {policy : BinderPolicy} {depth : Nat} {environment : QuoteEnv n}
    (good : QuoteEnvGood policy depth environment) {term : PureTm n}
    (constantFree : ConstantFree term) :
    ∃ elaborated,
      elaborateRegularPatternWith policy depth environment
          (quoteTmWith policy.name depth environment term) = .ok elaborated ∧
        elaborated.term = term := by
  induction constantFree generalizing depth with
  | var index =>
      simp only [quoteTmWith]
      rw [elaborateRegularPatternWith.eq_2]
      split
      · rename_i noResolution
        have resolved := resolveQuoteName_self good.env_inj index
        rw [resolved] at noResolution
        cases noResolution
      · rename_i resolvedIndex resolution
        have self := resolveQuoteName_self good.env_inj index
        have indexEq : resolvedIndex = index := by
          exact Option.some.inj (resolution.symm.trans self)
        subst resolvedIndex
        exact ⟨_, rfl, rfl⟩
  | u0 =>
      simp only [quoteTmWith, u0]
      rw [elaborateRegularPatternWith.eq_3]
      exact ⟨_, rfl, rfl⟩
  | u1 =>
      simp only [quoteTmWith, u1]
      rw [elaborateRegularPatternWith.eq_4]
      exact ⟨_, rfl, rfl⟩
  | pi domainFree bodyFree domainInduction bodyInduction =>
      rename_i arity domain body
      rcases domainInduction good with ⟨domainTerm, domainComputed, domainEq⟩
      rcases bodyInduction good.envCons with ⟨bodyTerm, bodyComputed, bodyEq⟩
      simp only [quoteTmWith, mkPi]
      rw [elaborateRegularPatternWith.eq_5, domainComputed]
      dsimp [Bind.bind, Except.instMonad, Except.bind]
      rw [dif_pos (isFresh_closeFVar_self 0 (policy.name depth)
        (quoteTmWith policy.name (depth + 1)
          (envCons (policy.name depth) environment) body))]
      have openClose :
          openBVar 0 (.fvar (policy.name depth))
              (closeFVar 0 (policy.name depth)
                  (quoteTmWith policy.name (depth + 1)
                  (envCons (policy.name depth) environment) body)) =
            quoteTmWith policy.name (depth + 1)
              (envCons (policy.name depth) environment) body := by
        simpa [Mettapedia.Languages.MeTTa.Pure.BinderOps.closeBVar] using
          (Mettapedia.Languages.MeTTa.Pure.BinderOps.openBVar_closeBVar_cancel
            (k := 0) (x := policy.name depth)
            (p := quoteTmWith policy.name (depth + 1)
              (envCons (policy.name depth) environment) body)
            (lc_quoteTmWith policy.name (depth + 1)
              (envCons (policy.name depth) environment) body))
      rw [openClose, bodyComputed]
      exact ⟨_, rfl, congrArg₂ PureTm.pi domainEq bodyEq⟩
  | sigma domainFree bodyFree domainInduction bodyInduction =>
      rename_i arity domain body
      rcases domainInduction good with ⟨domainTerm, domainComputed, domainEq⟩
      rcases bodyInduction good.envCons with ⟨bodyTerm, bodyComputed, bodyEq⟩
      simp only [quoteTmWith, mkSigma]
      rw [elaborateRegularPatternWith.eq_6, domainComputed]
      dsimp [Bind.bind, Except.instMonad, Except.bind]
      rw [dif_pos (isFresh_closeFVar_self 0 (policy.name depth)
        (quoteTmWith policy.name (depth + 1)
          (envCons (policy.name depth) environment) body))]
      have openClose :
          openBVar 0 (.fvar (policy.name depth))
              (closeFVar 0 (policy.name depth)
                (quoteTmWith policy.name (depth + 1)
                  (envCons (policy.name depth) environment) body)) =
            quoteTmWith policy.name (depth + 1)
              (envCons (policy.name depth) environment) body := by
        simpa [Mettapedia.Languages.MeTTa.Pure.BinderOps.closeBVar] using
          (Mettapedia.Languages.MeTTa.Pure.BinderOps.openBVar_closeBVar_cancel
            (k := 0) (x := policy.name depth)
            (p := quoteTmWith policy.name (depth + 1)
              (envCons (policy.name depth) environment) body)
            (lc_quoteTmWith policy.name (depth + 1)
              (envCons (policy.name depth) environment) body))
      rw [openClose, bodyComputed]
      exact ⟨_, rfl, congrArg₂ PureTm.sigma domainEq bodyEq⟩
  | id carrierFree leftFree rightFree carrierInduction leftInduction rightInduction =>
      rcases carrierInduction good with ⟨carrierTerm, carrierComputed, carrierEq⟩
      rcases leftInduction good with ⟨leftTerm, leftComputed, leftEq⟩
      rcases rightInduction good with ⟨rightTerm, rightComputed, rightEq⟩
      simp only [quoteTmWith, mkId]
      rw [elaborateRegularPatternWith.eq_7, carrierComputed]
      dsimp [Bind.bind, Except.instMonad, Except.bind]
      rw [leftComputed]
      dsimp [Bind.bind, Except.instMonad, Except.bind]
      rw [rightComputed]
      refine ⟨_, rfl, ?_⟩
      change PureTm.id carrierTerm.term leftTerm.term rightTerm.term =
        PureTm.id _ _ _
      rw [carrierEq, leftEq, rightEq]
  | lam bodyFree bodyInduction =>
      rename_i arity body
      rcases bodyInduction good.envCons with ⟨bodyTerm, bodyComputed, bodyEq⟩
      simp only [quoteTmWith, mkLam]
      rw [elaborateRegularPatternWith.eq_8]
      rw [dif_pos (isFresh_closeFVar_self 0 (policy.name depth)
        (quoteTmWith policy.name (depth + 1)
          (envCons (policy.name depth) environment) body))]
      dsimp [Bind.bind, Except.instMonad, Except.bind]
      have openClose :
          openBVar 0 (.fvar (policy.name depth))
              (closeFVar 0 (policy.name depth)
                (quoteTmWith policy.name (depth + 1)
                  (envCons (policy.name depth) environment) body)) =
            quoteTmWith policy.name (depth + 1)
              (envCons (policy.name depth) environment) body := by
        simpa [Mettapedia.Languages.MeTTa.Pure.BinderOps.closeBVar] using
          (Mettapedia.Languages.MeTTa.Pure.BinderOps.openBVar_closeBVar_cancel
            (k := 0) (x := policy.name depth)
            (p := quoteTmWith policy.name (depth + 1)
              (envCons (policy.name depth) environment) body)
            (lc_quoteTmWith policy.name (depth + 1)
              (envCons (policy.name depth) environment) body))
      rw [openClose, bodyComputed]
      exact ⟨_, rfl, congrArg PureTm.lam bodyEq⟩
  | app functionFree argumentFree functionInduction argumentInduction =>
      rcases functionInduction good with ⟨functionTerm, functionComputed, functionEq⟩
      rcases argumentInduction good with ⟨argumentTerm, argumentComputed, argumentEq⟩
      simp only [quoteTmWith, mkApp]
      rw [elaborateRegularPatternWith.eq_9, functionComputed]
      dsimp [Bind.bind, Except.instMonad, Except.bind]
      rw [argumentComputed]
      exact ⟨_, rfl, congrArg₂ PureTm.app functionEq argumentEq⟩
  | pair firstFree secondFree firstInduction secondInduction =>
      rcases firstInduction good with ⟨firstTerm, firstComputed, firstEq⟩
      rcases secondInduction good with ⟨secondTerm, secondComputed, secondEq⟩
      simp only [quoteTmWith, mkPair]
      rw [elaborateRegularPatternWith.eq_10, firstComputed]
      dsimp [Bind.bind, Except.instMonad, Except.bind]
      rw [secondComputed]
      exact ⟨_, rfl, congrArg₂ PureTm.pair firstEq secondEq⟩
  | fst pairFree pairInduction =>
      rcases pairInduction good with ⟨pairTerm, pairComputed, pairEq⟩
      simp only [quoteTmWith, mkFst]
      rw [elaborateRegularPatternWith.eq_11, pairComputed]
      exact ⟨_, rfl, congrArg PureTm.fst pairEq⟩
  | snd pairFree pairInduction =>
      rcases pairInduction good with ⟨pairTerm, pairComputed, pairEq⟩
      simp only [quoteTmWith, mkSnd]
      rw [elaborateRegularPatternWith.eq_12, pairComputed]
      exact ⟨_, rfl, congrArg PureTm.snd pairEq⟩
  | refl termFree termInduction =>
      rcases termInduction good with ⟨elaborated, termComputed, termEq⟩
      simp only [quoteTmWith, mkRefl]
      rw [elaborateRegularPatternWith.eq_13, termComputed]
      exact ⟨_, rfl, congrArg PureTm.refl termEq⟩

/-- Depth-zero completeness for the public elaborator. -/
theorem elaborateRegularPattern_quote_complete
    {policy : BinderPolicy} {environment : QuoteEnv n}
    (good : QuoteEnvGood policy 0 environment) {term : PureTm n}
    (constantFree : ConstantFree term) :
    ∃ elaborated,
      elaborateRegularPattern policy environment
          (quoteTmWith policy.name 0 environment term) = .ok elaborated ∧
        elaborated.term = term :=
  elaborateRegularPatternWith_quote_complete good constantFree

/-! ## Exact certificate-free Pattern authority -/

/-- Independent meaning of a strict Pattern typing query: both Pattern terms
are contextual quotations of declaration-free intrinsic terms, and the
independent regular bidirectional calculus accepts those terms. -/
def RegularPatternPublicChecks {Γ : Ctx n} (context : RegularCtx Γ)
    (policy : BinderPolicy) (environment : QuoteEnv n)
    (termPattern expectedPattern : Pattern) : Prop :=
  ∃ term expected : PureTm n,
    ConstantFree term ∧ ConstantFree expected ∧
    quoteTmWith policy.name 0 environment term = termPattern ∧
    quoteTmWith policy.name 0 environment expected = expectedPattern ∧
    RegularPublicChecks context term expected

/-- The ordinary authority bit contains neither elaboration nor typing
certificates.  Expected syntax is inspected first, matching the diagnostic
boundary's stable phase order. -/
def regularPatternCheckBool {Γ : Ctx n} (context : RegularCtx Γ)
    (policy : BinderPolicy) (environment : QuoteEnv n)
    (termPattern expectedPattern : Pattern) : Bool :=
  match elaborateRegularPattern policy environment expectedPattern with
  | .error _ => false
  | .ok expected =>
      match elaborateRegularPattern policy environment termPattern with
      | .error _ => false
      | .ok term => regularCheckBool context term.term expected.term

/-- Boolean acceptance reflects the independently stated Pattern meaning. -/
theorem regularPatternCheckBool_reflects {Γ : Ctx n} (context : RegularCtx Γ)
    (policy : BinderPolicy) (environment : QuoteEnv n)
    (good : QuoteEnvGood policy 0 environment)
    (termPattern expectedPattern : Pattern)
    (accepted : regularPatternCheckBool context policy environment
      termPattern expectedPattern = true) :
    RegularPatternPublicChecks context policy environment
      termPattern expectedPattern := by
  unfold regularPatternCheckBool at accepted
  cases expectedComputed : elaborateRegularPattern policy environment expectedPattern with
  | error error => simp [expectedComputed] at accepted
  | ok expected =>
      cases termComputed : elaborateRegularPattern policy environment termPattern with
      | error error => simp [expectedComputed, termComputed] at accepted
      | ok term =>
          rw [expectedComputed, termComputed] at accepted
          exact ⟨term.term, expected.term, term.constantFree, expected.constantFree,
            elaborateRegularPattern_reflects good termComputed,
            elaborateRegularPattern_reflects good expectedComputed,
            regularCheckBool_reflects context term.term expected.term accepted⟩

/-- Every independently meaningful strict Pattern query is accepted. -/
theorem regularPatternCheckBool_complete {Γ : Ctx n} (context : RegularCtx Γ)
    (policy : BinderPolicy) (environment : QuoteEnv n)
    (good : QuoteEnvGood policy 0 environment)
    (termPattern expectedPattern : Pattern)
    (meaning : RegularPatternPublicChecks context policy environment
      termPattern expectedPattern) :
    regularPatternCheckBool context policy environment
      termPattern expectedPattern = true := by
  rcases meaning with ⟨term, expected, termFree, expectedFree,
    termQuoted, expectedQuoted, publicChecks⟩
  rcases elaborateRegularPattern_quote_complete good expectedFree with
    ⟨expectedResult, expectedComputed, expectedTerm⟩
  rcases elaborateRegularPattern_quote_complete good termFree with
    ⟨termResult, termComputed, termTerm⟩
  have expectedComputed' :
      elaborateRegularPattern policy environment expectedPattern =
        .ok expectedResult := by
    rw [← expectedQuoted]
    exact expectedComputed
  have termComputed' :
      elaborateRegularPattern policy environment termPattern = .ok termResult := by
    rw [← termQuoted]
    exact termComputed
  unfold regularPatternCheckBool
  rw [expectedComputed', termComputed']
  change regularCheckBool context termResult.term expectedResult.term = true
  rw [expectedTerm, termTerm]
  exact regularCheckBool_complete publicChecks

/-- Exact agreement between the direct Pattern bit and its quotation-plus-
typing meaning. -/
theorem regularPatternCheckBool_correct {Γ : Ctx n} (context : RegularCtx Γ)
    (policy : BinderPolicy) (environment : QuoteEnv n)
    (good : QuoteEnvGood policy 0 environment)
    (termPattern expectedPattern : Pattern) :
    regularPatternCheckBool context policy environment
        termPattern expectedPattern = true ↔
      RegularPatternPublicChecks context policy environment
        termPattern expectedPattern := by
  constructor
  · exact regularPatternCheckBool_reflects context policy environment good
      termPattern expectedPattern
  · exact regularPatternCheckBool_complete context policy environment good
      termPattern expectedPattern

/-- Packaged input for the strict Pattern authority.  Environment hygiene is
part of the trusted input description; the decision itself remains a direct
Boolean computation. -/
structure RegularPatternTypingClaim where
  arity : Nat
  contextSyntax : Ctx arity
  context : RegularCtx contextSyntax
  policy : BinderPolicy
  environment : QuoteEnv arity
  environmentGood : QuoteEnvGood policy 0 environment
  termPattern : Pattern
  expectedPattern : Pattern

/-- Independent meaning of a packaged strict Pattern query. -/
def RegularPatternTypingClaim.Meaning
    (claim : RegularPatternTypingClaim) : Prop :=
  RegularPatternPublicChecks claim.context claim.policy claim.environment
    claim.termPattern claim.expectedPattern

/-- The Pattern checker is a generic NIK direct-decision authority. -/
def regularPatternTypingDecisionKernel :
    Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker.DecisionKernel
      RegularPatternTypingClaim RegularPatternTypingClaim.Meaning where
  decide := fun claim =>
    regularPatternCheckBool claim.context claim.policy claim.environment
      claim.termPattern claim.expectedPattern
  correct := fun claim =>
    regularPatternCheckBool_correct claim.context claim.policy claim.environment
      claim.environmentGood claim.termPattern claim.expectedPattern

/-! ## Diagnostic quotations and executable witnesses -/

/-- Admitted subject syntax quotes back to exactly the submitted Pattern. -/
theorem RegularPatternAdmission.term_quotation
    {Γ : Ctx n} {context : RegularCtx Γ} {policy : BinderPolicy}
    {environment : QuoteEnv n} {termPattern expectedPattern : Pattern}
    (good : QuoteEnvGood policy 0 environment)
    (admission : RegularPatternAdmission context policy environment
      termPattern expectedPattern) :
    quoteTmWith policy.name 0 environment admission.term.term = termPattern :=
  elaborateRegularPattern_reflects good admission.termComputed

/-- Admitted expected syntax quotes back to exactly the submitted Pattern. -/
theorem RegularPatternAdmission.expected_quotation
    {Γ : Ctx n} {context : RegularCtx Γ} {policy : BinderPolicy}
    {environment : QuoteEnv n} {termPattern expectedPattern : Pattern}
    (good : QuoteEnvGood policy 0 environment)
    (admission : RegularPatternAdmission context policy environment
      termPattern expectedPattern) :
    quoteTmWith policy.name 0 environment admission.expected.term = expectedPattern :=
  elaborateRegularPattern_reflects good admission.expectedComputed

/-- Closed quotation environments satisfy the strict hygiene invariant. -/
def defaultEmptyQuoteEnvGood :
    QuoteEnvGood defaultBinderPolicy 0 emptyEnv :=
  QuoteEnvGood.empty defaultBinderPolicy 0

/-- Positive Pattern witness: `U0 : U1`. -/
def regularPatternPositiveClaim : RegularPatternTypingClaim where
  arity := 0
  contextSyntax := .nil
  context := .nil
  policy := defaultBinderPolicy
  environment := emptyEnv
  environmentGood := defaultEmptyQuoteEnvGood
  termPattern := quoteClosedTm .u0
  expectedPattern := quoteClosedTm .u1

theorem regularPatternTypingDecisionKernel_accepts_positive :
    regularPatternTypingDecisionKernel.decide regularPatternPositiveClaim = true := by
  apply (regularPatternTypingDecisionKernel.correct regularPatternPositiveClaim).2
  exact ⟨.u0, .u1, .u0, .u1, rfl, rfl, regularPublic_u0_u1⟩

/-- Contextual quotation is injective on declaration-free intrinsic terms
under a good environment.  This is derived from strict elaboration
determinism, rather than assumed as a separate encoding postulate. -/
theorem quoteTmWith_injective_on_constantFree
    {policy : BinderPolicy} {environment : QuoteEnv n}
    (good : QuoteEnvGood policy 0 environment)
    {left right : PureTm n} (leftFree : ConstantFree left)
    (rightFree : ConstantFree right)
    (quoted : quoteTmWith policy.name 0 environment left =
      quoteTmWith policy.name 0 environment right) :
    left = right := by
  rcases elaborateRegularPattern_quote_complete good leftFree with
    ⟨leftResult, leftComputed, leftTerm⟩
  rcases elaborateRegularPattern_quote_complete good rightFree with
    ⟨rightResult, rightComputed, rightTerm⟩
  rw [quoted] at leftComputed
  have resultEq : leftResult = rightResult :=
    Except.ok.inj (leftComputed.symm.trans rightComputed)
  calc
    left = leftResult.term := leftTerm.symm
    _ = rightResult.term := congrArg RegularPatternTerm.term resultEq
    _ = right := rightTerm

/-- Negative Pattern witness: `U1 : U1` is impossible. -/
def regularPatternNegativeClaim : RegularPatternTypingClaim where
  arity := 0
  contextSyntax := .nil
  context := .nil
  policy := defaultBinderPolicy
  environment := emptyEnv
  environmentGood := defaultEmptyQuoteEnvGood
  termPattern := quoteClosedTm .u1
  expectedPattern := quoteClosedTm .u1

theorem regularPatternTypingDecisionKernel_rejects_negative :
    regularPatternTypingDecisionKernel.decide regularPatternNegativeClaim = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  rcases (regularPatternTypingDecisionKernel.correct
      regularPatternNegativeClaim).1 accepted with
    ⟨term, expected, termFree, expectedFree, termQuoted, expectedQuoted,
      publicChecks⟩
  have termEq : term = .u1 := quoteTmWith_injective_on_constantFree
    defaultEmptyQuoteEnvGood termFree (.u1)
    (by simpa [regularPatternNegativeClaim, quoteClosedTm, quoteTm,
      defaultBinderPolicy] using termQuoted)
  have expectedEq : expected = .u1 := quoteTmWith_injective_on_constantFree
    defaultEmptyQuoteEnvGood expectedFree (.u1)
    (by simpa [regularPatternNegativeClaim, quoteClosedTm, quoteTm,
      defaultBinderPolicy] using expectedQuoted)
  subst term
  subst expected
  exact regularPublic_u1_rejected publicChecks

/-- Negative syntax witness: an unbound Pattern name is rejected, rather than
being reinterpreted as a global declaration. -/
theorem elaborateRegularPattern_rejects_unknown_name :
    elaborateRegularPattern defaultBinderPolicy emptyEnv (.fvar "unbound") =
      .error (.unknownFreeVariable "unbound") := by
  simp [elaborateRegularPattern, elaborateRegularPatternWith, resolveQuoteName]
  change Except.error (RegularPatternSyntaxError.unknownFreeVariable "unbound") =
    Except.error (RegularPatternSyntaxError.unknownFreeVariable "unbound")
  rfl

/-- Negative hygiene witness: the canonical binder name may not already occur
free in its submitted body. -/
theorem elaborateRegularPattern_rejects_binder_collision :
    elaborateRegularPattern defaultBinderPolicy emptyEnv
        (mkLam (.fvar (defaultBinderPolicy.name 0))) =
      .error (.binderNameCollision (defaultBinderPolicy.name 0)) := by
  simp [elaborateRegularPattern, elaborateRegularPatternWith, mkLam,
    defaultBinderPolicy, defaultBinderName, isFresh, freeVars]
  change Except.error
      (RegularPatternSyntaxError.binderNameCollision ("__pk_" ++ Nat.repr 0)) =
    Except.error
      (RegularPatternSyntaxError.binderNameCollision ("__pk_" ++ Nat.repr 0))
  rfl

#print axioms elaborateRegularPatternWith_reflects
#print axioms elaborateRegularPatternWith_quote_complete
#print axioms regularPatternCheckBool_correct
#print axioms regularPatternTypingDecisionKernel
#print axioms regularPatternTypingDecisionKernel_accepts_positive
#print axioms regularPatternTypingDecisionKernel_rejects_negative

end Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary
