import Algorithms.MeTTa.Simple.Semantics.Dispatch
import Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaSound
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# PeTTa Compat-Head Runtime Boundary

This file states the **correct theorem boundary** for PeTTa compat-head lowering
without extending the formal MORK model.

The intended execution story is staged:

1. a certified external witness phase on the PeTTa side
2. a residual source-rule firing phase on actual MORK as it exists

Positive example:
- tuple membership / generator-style heads can first obtain witnesses through a
  grounded-host or oracle-certified lane, then feed those bindings into the
  residual MORK rule application

Negative example:
- this file does **not** claim that current MORK natively evaluates generator
  expressions inside compat-head matching
-/

namespace Mettapedia.Conformance.PeTTaCompatHeadBoundary

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.Translation

abbrev PeTTaPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
abbrev HEAtom := Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-- Local tuple/list view for OSLF PeTTa patterns, matching the runtime list
convention used by the current PeTTa implementation. -/
private def tupleElems : PeTTaPattern → List PeTTaPattern
  | .apply "()" [] => []
  | .apply "Expr" elems => elems
  | .apply ctor args => (.apply ctor []) :: args
  | p => [p]

/-- Canonical symbolic true pattern used by the current PeTTa grounded/control
lane. -/
private def truePattern : PeTTaPattern := .apply "True" []

private theorem applyBindings_fvar_of_find
    {bs : Bindings} {x : String} {v : PeTTaPattern}
    (hfind : bs.find? (·.1 == x) = some (x, v)) :
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs (.fvar x) = v := by
  simp [Mettapedia.OSLF.MeTTaIL.Match.applyBindings, hfind]

/-- Phase 1 of compat-head lowering: a certified external witness-producing
evaluation on the PeTTa side. -/
structure ExternalWitnessPhase
    (oracle : GroundedOracle) (space : PeTTaSpace)
    (generatorHead : String) (rawArgs : List PeTTaPattern) (ty : PeTTaPattern)
    (bindings finalBindings : Bindings)
    (evaledArgs witnessResults : List PeTTaPattern) : Prop where
  executable : oracle.isExecutable generatorHead
  argsEvaluated : InterpretArgs space bindings rawArgs evaledArgs finalBindings
  oracleCall : oracle.call generatorHead evaledArgs witnessResults

/-- Phase 2 of compat-head lowering: after witness selection, the residual
instantiated source rule fires in actual MORK. -/
structure ResidualMorkPhase
    (workspace : Space) (sourceRule : SourceExecRule) (σ : Subst) : Prop where
  fires : applySinks workspace σ sourceRule.tmpl ∈ fireSourceRule workspace sourceRule

/-- The staged compat-head lowering contract: external witness production first,
then residual MORK source firing. This is the theorem surface Rust should
follow, rather than inventing a separate unification semantics. -/
structure CompatHeadTwoPhaseLowering
    (oracle : GroundedOracle) (space : PeTTaSpace) (workspace : Space)
    (generatorHead : String) (rawArgs : List PeTTaPattern) (ty : PeTTaPattern)
    (bindings finalBindings : Bindings)
    (evaledArgs witnessResults : List PeTTaPattern)
    (sourceRule : SourceExecRule) (σ : Subst) : Prop where
  witnessPhase :
    ExternalWitnessPhase oracle space generatorHead rawArgs ty
      bindings finalBindings evaledArgs witnessResults
  residualPhase :
    ResidualMorkPhase workspace sourceRule σ

/-- The binding-flow seam between an external witness phase and the residual
actual-MORK phase.

This is the key compat-head obligation: the witness bindings chosen outside
MORK must instantiate the residual body the same way that the translated MORK
substitution does. -/
structure WitnessResidualBindingFlow
    (witnessBindings : Bindings) (residualBody residualInstantiated : PeTTaPattern)
    (σ : Subst) : Prop where
  substEq : σ = bindingsToSubst witnessBindings
  instantiated :
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings witnessBindings residualBody =
      residualInstantiated

/-- The external witness phase gives a genuine grounded PeTTa evaluation step.

This is the first half of the staged compat-head boundary. -/
theorem externalWitnessPhase_to_meTTaEvalG
    {oracle : GroundedOracle} {space : PeTTaSpace}
    {generatorHead : String} {rawArgs : List PeTTaPattern} {ty : PeTTaPattern}
    {bindings finalBindings : Bindings}
    {evaledArgs witnessResults : List PeTTaPattern}
    (h :
      ExternalWitnessPhase oracle space generatorHead rawArgs ty
        bindings finalBindings evaledArgs witnessResults) :
    MeTTaEvalG oracle space (.apply generatorHead rawArgs) ty bindings
      (witnessResults.map (·, finalBindings)) := by
  exact meTTaEvalG_groundedCall_mk
    h.executable h.argsEvaluated h.oracleCall

/-- Assemble the staged compat-head runtime boundary from its two validated
phases. -/
theorem compatHeadTwoPhaseLowering_mk
    {oracle : GroundedOracle} {space : PeTTaSpace} {workspace : Space}
    {generatorHead : String} {rawArgs : List PeTTaPattern} {ty : PeTTaPattern}
    {bindings finalBindings : Bindings}
    {evaledArgs witnessResults : List PeTTaPattern}
    {sourceRule : SourceExecRule} {σ : Subst}
    (hw :
      ExternalWitnessPhase oracle space generatorHead rawArgs ty
        bindings finalBindings evaledArgs witnessResults)
    (hr : ResidualMorkPhase workspace sourceRule σ) :
    CompatHeadTwoPhaseLowering oracle space workspace
      generatorHead rawArgs ty
      bindings finalBindings evaledArgs witnessResults
      sourceRule σ := by
  exact ⟨hw, hr⟩

/-- Unpack the staged boundary into the concrete PeTTa grounded evaluation and
actual MORK firing facts it guarantees. -/
theorem compatHeadTwoPhaseLowering_sound
    {oracle : GroundedOracle} {space : PeTTaSpace} {workspace : Space}
    {generatorHead : String} {rawArgs : List PeTTaPattern} {ty : PeTTaPattern}
    {bindings finalBindings : Bindings}
    {evaledArgs witnessResults : List PeTTaPattern}
    {sourceRule : SourceExecRule} {σ : Subst}
    (h :
      CompatHeadTwoPhaseLowering oracle space workspace
        generatorHead rawArgs ty
        bindings finalBindings evaledArgs witnessResults
        sourceRule σ) :
    MeTTaEvalG oracle space (.apply generatorHead rawArgs) ty bindings
        (witnessResults.map (·, finalBindings)) ∧
      applySinks workspace σ sourceRule.tmpl ∈ fireSourceRule workspace sourceRule := by
  refine ⟨externalWitnessPhase_to_meTTaEvalG h.witnessPhase, h.residualPhase.fires⟩

/-- The residual binding-flow seam is exactly the algebraic MORK bridge:
applying witness bindings on the PeTTa side agrees with applying the translated
substitution on the MORK side, provided the residual body is in the current
actual-MORK fragment. -/
theorem witnessResidualBindingFlow_sound
    {witnessBindings : Bindings}
    {residualBody residualInstantiated : PeTTaPattern}
    {σ : Subst}
    (hflow :
      WitnessResidualBindingFlow witnessBindings residualBody residualInstantiated σ)
    (htrans : morkTranslatable residualBody = true) :
    applySubst σ (morkPatternToAtom residualBody) =
      morkPatternToAtom residualInstantiated := by
  rcases hflow with ⟨rfl, hinst⟩
  simpa [hinst, translateBindings_eq_bindingsToSubst] using
    applySubst_commutes witnessBindings residualBody htrans

/-- Contract for the current grounded-host `is-member` generator lane.

This does not claim any MORK behavior. It only characterizes the external
witness-producing phase. -/
structure TupleMembershipOracleContract (oracle : GroundedOracle) : Prop where
  executable : oracle.isExecutable "is-member"
  call_true_of_member :
    ∀ {x xs : PeTTaPattern},
      x ∈ tupleElems xs →
        oracle.call "is-member" [x, xs] [truePattern]

/-- First concrete compat-head witness fragment:
if the arguments have already evaluated to `[x, xs]` and the oracle contract
certifies that `x` is a member of `xs`, then the staged boundary has a valid
external witness phase for `is-member`. -/
theorem tupleMembership_externalWitnessPhase_of_member
    {oracle : GroundedOracle} {space : PeTTaSpace}
    (horacle : TupleMembershipOracleContract oracle)
    {rawArgs : List PeTTaPattern} {ty : PeTTaPattern}
    {bindings finalBindings : Bindings}
    {x xs : PeTTaPattern}
    (hargs : InterpretArgs space bindings rawArgs [x, xs] finalBindings)
    (hmem : x ∈ tupleElems xs) :
    ExternalWitnessPhase oracle space "is-member" rawArgs ty
      bindings finalBindings [x, xs] [truePattern] := by
  refine ⟨horacle.executable, hargs, ?_⟩
  exact horacle.call_true_of_member hmem

/-- First concrete staged compat-head theorem:
tuple-membership witness production on the PeTTa side followed by any validated
actual-MORK residual source firing. This is the theorem surface the runtime
should follow for the current `in`/`is-member` fragment. -/
theorem tupleMembership_twoPhaseLowering_of_member
    {oracle : GroundedOracle} {space : PeTTaSpace} {workspace : Space}
    (horacle : TupleMembershipOracleContract oracle)
    {rawArgs : List PeTTaPattern} {ty : PeTTaPattern}
    {bindings finalBindings : Bindings}
    {x xs : PeTTaPattern}
    {sourceRule : SourceExecRule} {σ : Subst}
    (hargs : InterpretArgs space bindings rawArgs [x, xs] finalBindings)
    (hmem : x ∈ tupleElems xs)
    (hr : ResidualMorkPhase workspace sourceRule σ) :
    CompatHeadTwoPhaseLowering oracle space workspace
      "is-member" rawArgs ty
      bindings finalBindings [x, xs] [truePattern]
      sourceRule σ := by
  refine compatHeadTwoPhaseLowering_mk ?_ hr
  exact tupleMembership_externalWitnessPhase_of_member horacle hargs hmem

/-- The concrete tuple-membership staged theorem immediately yields a real
grounded PeTTa evaluation fact together with actual MORK firing. -/
theorem tupleMembership_twoPhaseLowering_sound_of_member
    {oracle : GroundedOracle} {space : PeTTaSpace} {workspace : Space}
    (horacle : TupleMembershipOracleContract oracle)
    {rawArgs : List PeTTaPattern} {ty : PeTTaPattern}
    {bindings finalBindings : Bindings}
    {x xs : PeTTaPattern}
    {sourceRule : SourceExecRule} {σ : Subst}
    (hargs : InterpretArgs space bindings rawArgs [x, xs] finalBindings)
    (hmem : x ∈ tupleElems xs)
    (hr : ResidualMorkPhase workspace sourceRule σ) :
    MeTTaEvalG oracle space (.apply "is-member" rawArgs) ty bindings
        [(.apply "True" [], finalBindings)] ∧
      applySinks workspace σ sourceRule.tmpl ∈ fireSourceRule workspace sourceRule := by
  exact compatHeadTwoPhaseLowering_sound
    (tupleMembership_twoPhaseLowering_of_member horacle hargs hmem hr)

/-- First concrete binding-flow theorem for the live compat-head fragment:
after an `is-member` witness is certified externally, a singleton witness
binding can instantiate the residual body in exactly the way actual MORK sees
through `bindingsToSubst`. -/
theorem tupleMembership_singleWitness_residual_sound_of_member
    {oracle : GroundedOracle} {space : PeTTaSpace} {workspace : Space}
    (horacle : TupleMembershipOracleContract oracle)
    {rawArgs : List PeTTaPattern} {ty : PeTTaPattern}
    {bindings finalBindings : Bindings}
    {x xs : PeTTaPattern}
    {var : String} {residualBody residualInstantiated : PeTTaPattern}
    {sourceRule : SourceExecRule}
    (hargs : InterpretArgs space bindings rawArgs [x, xs] finalBindings)
    (hmem : x ∈ tupleElems xs)
    (htrans : morkTranslatable residualBody = true)
    (hinst :
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings [(var, x)] residualBody =
        residualInstantiated)
    (hr :
      ResidualMorkPhase workspace sourceRule (bindingsToSubst [(var, x)])) :
    MeTTaEvalG oracle space (.apply "is-member" rawArgs) ty bindings
        [(.apply "True" [], finalBindings)] ∧
      applySubst (bindingsToSubst [(var, x)]) (morkPatternToAtom residualBody) =
        morkPatternToAtom residualInstantiated ∧
      applySinks workspace (bindingsToSubst [(var, x)]) sourceRule.tmpl ∈
        fireSourceRule workspace sourceRule := by
  refine ⟨?_, ?_, hr.fires⟩
  · exact (tupleMembership_twoPhaseLowering_sound_of_member
      (workspace := workspace) horacle hargs hmem hr).1
  · exact witnessResidualBindingFlow_sound
      ⟨rfl, hinst⟩ htrans

/-- If two singleton witness bindings merge successfully, the merged binding set
still maps both witness variables to the witnessed values. -/
theorem mergedSingletonWitnessBindings_preserve
    {varX varY : String} {x y : PeTTaPattern}
    {mergedWitnessBindings : Bindings}
    (hmerge :
      mergeBindings [(varX, x)] [(varY, y)] = some mergedWitnessBindings) :
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings mergedWitnessBindings (.fvar varX) = x ∧
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings mergedWitnessBindings (.fvar varY) = y := by
  refine ⟨?_, ?_⟩
  · apply applyBindings_fvar_of_find
    exact Mettapedia.OSLF.MeTTaIL.MatchSpec.mergeBindings_subsumed_left hmerge (by simp)
  · apply applyBindings_fvar_of_find
    exact Mettapedia.OSLF.MeTTaIL.MatchSpec.mergeBindings_subsumed_right hmerge (by simp)

/-- Two concrete tuple-membership witness phases compose into one residual
binding flow.

This is the first honest `X/Y`-shaped theorem toward `functionhead3`: two
certified external witnesses, one merged witness environment, one residual body,
and one actual-MORK residual phase. -/
theorem tupleMembership_twoWitness_residual_sound_of_member
    {oracle : GroundedOracle} {space : PeTTaSpace} {workspace : Space}
    (horacle : TupleMembershipOracleContract oracle)
    {rawArgsX rawArgsY : List PeTTaPattern} {tyX tyY : PeTTaPattern}
    {bindingsX finalBindingsX : Bindings}
    {bindingsY finalBindingsY : Bindings}
    {x xs y ys : PeTTaPattern}
    {varX varY : String}
    {mergedWitnessBindings : Bindings}
    {residualBody residualInstantiated : PeTTaPattern}
    {sourceRule : SourceExecRule}
    (hargsX : InterpretArgs space bindingsX rawArgsX [x, xs] finalBindingsX)
    (hmemX : x ∈ tupleElems xs)
    (hargsY : InterpretArgs space bindingsY rawArgsY [y, ys] finalBindingsY)
    (hmemY : y ∈ tupleElems ys)
    (hmerge :
      mergeBindings [(varX, x)] [(varY, y)] = some mergedWitnessBindings)
    (htrans : morkTranslatable residualBody = true)
    (hinst :
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings mergedWitnessBindings residualBody =
        residualInstantiated)
    (hr :
      ResidualMorkPhase workspace sourceRule
        (bindingsToSubst mergedWitnessBindings)) :
    MeTTaEvalG oracle space (.apply "is-member" rawArgsX) tyX bindingsX
        [(.apply "True" [], finalBindingsX)] ∧
      MeTTaEvalG oracle space (.apply "is-member" rawArgsY) tyY bindingsY
        [(.apply "True" [], finalBindingsY)] ∧
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings mergedWitnessBindings (.fvar varX) = x ∧
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings mergedWitnessBindings (.fvar varY) = y ∧
      applySubst (bindingsToSubst mergedWitnessBindings) (morkPatternToAtom residualBody) =
        morkPatternToAtom residualInstantiated ∧
      applySinks workspace (bindingsToSubst mergedWitnessBindings) sourceRule.tmpl ∈
        fireSourceRule workspace sourceRule := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hr.fires⟩
  · exact (externalWitnessPhase_to_meTTaEvalG
      (tupleMembership_externalWitnessPhase_of_member horacle hargsX hmemX))
  · exact (externalWitnessPhase_to_meTTaEvalG
      (tupleMembership_externalWitnessPhase_of_member horacle hargsY hmemY))
  · exact (mergedSingletonWitnessBindings_preserve hmerge).1
  · exact (mergedSingletonWitnessBindings_preserve hmerge).2
  · exact witnessResidualBindingFlow_sound
      ⟨rfl, hinst⟩ htrans

private def specToCoreCollType :
    Mettapedia.OSLF.MeTTaIL.Syntax.CollType → MeTTailCore.MeTTaIL.Syntax.CollType
  | .vec => .vec
  | .hashBag => .hashBag
  | .hashSet => .hashSet

private def specToCorePattern : PeTTaPattern → MeTTailCore.MeTTaIL.Syntax.Pattern
  | .bvar n => .bvar n
  | .fvar x => .fvar x
  | .apply ctor args => .apply ctor (args.map specToCorePattern)
  | .lambda _ body => .lambda (specToCorePattern body)
  | .multiLambda n _ body => .multiLambda n (specToCorePattern body)
  | .subst body repl => .subst (specToCorePattern body) (specToCorePattern repl)
  | .collection ct elems rest =>
      .collection (specToCoreCollType ct) (elems.map specToCorePattern) rest

/-- Core rewrite-rule shape corresponding to the `functionhead3` compat-head
fragment:
`(= (ctor (in $X xs) (in $Y ys)) rhs)`.

This theorem target is structural: the Dispatch classifier should see this as a
compat-head rule regardless of the concrete rhs. -/
private def functionhead3LikeCoreRule
    (ctor varX varY : String) (xs ys rhs : PeTTaPattern) :
    MeTTailCore.MeTTaIL.Syntax.RewriteRule :=
  { name := s!"{ctor}_functionhead3_shape"
    typeContext := []
    premises := []
    left := MeTTailCore.MeTTaIL.Syntax.Pattern.apply ctor
      [ MeTTailCore.MeTTaIL.Syntax.Pattern.apply "in"
          [MeTTailCore.MeTTaIL.Syntax.Pattern.fvar varX, specToCorePattern xs]
      , MeTTailCore.MeTTaIL.Syntax.Pattern.apply "in"
          [MeTTailCore.MeTTaIL.Syntax.Pattern.fvar varY, specToCorePattern ys]
      ]
    right := specToCorePattern rhs }

private def functionhead3LikeRawArgs
    (varX varY : String) (xs ys : PeTTaPattern) :
    List MeTTailCore.MeTTaIL.Syntax.Pattern :=
  [ MeTTailCore.MeTTaIL.Syntax.Pattern.apply "in"
      [MeTTailCore.MeTTaIL.Syntax.Pattern.fvar varX, specToCorePattern xs]
  , MeTTailCore.MeTTaIL.Syntax.Pattern.apply "in"
      [MeTTailCore.MeTTaIL.Syntax.Pattern.fvar varY, specToCorePattern ys]
  ]

/-- Minimal Dispatch interface used only for the structural compat-head
classifier. Only `rewrites` matters for `hasCompatHeadConstraintRule`; the
other fields are inert placeholders so we can state the theorem against the
real classifier from `Dispatch.lean`. -/
private def rewriteOnlyDispatchInterface
    (rules : List MeTTailCore.MeTTaIL.Syntax.RewriteRule) :
    Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Unit where
  rewrites := fun _ => rules
  premiseFreeRulesForHeadArity := fun _ ctor arity =>
    rules.filter fun rule =>
      match rule.left with
      | .apply lCtor pArgs =>
          rule.premises.isEmpty && lCtor == ctor && pArgs.length == arity
      | _ => false
  eval := fun s _ => (s, [])
  evalForRuleEnumeration := fun s _ => (s, [])
  applyBindings := fun bs pat => MeTTailCore.MeTTaIL.Match.applyBindings bs pat
  matchPattern := fun pat term => MeTTailCore.MeTTaIL.Match.matchPattern pat term
  normalizePattern := fun pat => pat
  dedupBindings := fun bs => bs

/-- The actual structural compat-head classifier from `Dispatch.lean` recognizes
the `functionhead3` rule shape. This pins the next runtime work to rule
structure rather than example-by-example guessing. -/
theorem functionhead3Like_ruleShape_hasCompatHeadConstraintRule
    {ctor varX varY : String} {xs ys rhs : PeTTaPattern} :
    Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule
      (rewriteOnlyDispatchInterface
        [functionhead3LikeCoreRule ctor varX varY xs ys rhs]) () ctor 2 = true := by
  simp [Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule,
    rewriteOnlyDispatchInterface, functionhead3LikeCoreRule]
  left
  rfl

/-- For the deterministic singleton `functionhead3`-like compat-head fragment,
the public Dispatch singleton bridge theorem applies directly on the
rewrite-only interface. This is the first theorem in this file that connects
the structural compat-head target to the owner-layer operational projection
seam. -/
theorem functionhead3Like_singleton_bridge
    {ctor varX varY : String} {xs ys rhs : PeTTaPattern}
    (hNoDollar : ctor.startsWith "$" = false) :
    let valsState :=
      Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
        (rewriteOnlyDispatchInterface
          [functionhead3LikeCoreRule ctor varX varY xs ys rhs])
        ()
        (.apply ctor (functionhead3LikeRawArgs varX varY xs ys))
    let pairState :=
      Algorithms.MeTTa.Simple.Semantics.Dispatch.constrainedCallBindingsAndValues
        (rewriteOnlyDispatchInterface
          [functionhead3LikeCoreRule ctor varX varY xs ys rhs])
        ()
        (.apply ctor (functionhead3LikeRawArgs varX varY xs ys))
    valsState.1 = pairState.1 ∧ valsState.2 = pairState.2.map Prod.snd := by
  let rule := functionhead3LikeCoreRule ctor varX varY xs ys rhs
  let ruleArgs := functionhead3LikeRawArgs varX varY xs ys
  have hEvalEq :
      ∀ (s : Unit) (rhsPat : MeTTailCore.MeTTaIL.Syntax.Pattern),
        (rewriteOnlyDispatchInterface [rule]).evalForRuleEnumeration s rhsPat =
          (rewriteOnlyDispatchInterface [rule]).eval s rhsPat := by
    intro s rhsPat
    rfl
  have hRules :
      (rewriteOnlyDispatchInterface [rule]).premiseFreeRulesForHeadArity () ctor
        ruleArgs.length = [rule] := by
    simp [rewriteOnlyDispatchInterface, rule, ruleArgs, functionhead3LikeCoreRule,
      functionhead3LikeRawArgs]
  have hRuleLeft : rule.left = .apply ctor ruleArgs := by
    rfl
  have hLen : ruleArgs.length == ruleArgs.length := by
    rfl
  simpa [rule, ruleArgs] using
    Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite_singleton_bridge
      (rewriteOnlyDispatchInterface [rule])
      hEvalEq
      ()
      ctor
      ruleArgs
      rule
      ruleArgs
      hRules
      hNoDollar
      hRuleLeft
      hLen
      (by
        simpa [Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule,
          rewriteOnlyDispatchInterface, rule, ruleArgs, functionhead3LikeCoreRule,
          functionhead3LikeRawArgs] using
          (functionhead3Like_ruleShape_hasCompatHeadConstraintRule
            (ctor := ctor) (varX := varX) (varY := varY) (xs := xs) (ys := ys)
            (rhs := rhs)))

/-- Rule-shape instantiation of the two-witness boundary theorem for the
`functionhead3` compat-head fragment.

This does not yet prove the full runtime behavior of `functionhead3`; it proves
that the rule shape selected by the actual Dispatch classifier is exactly the
shape for which the already-proved two-witness boundary theorem applies. -/
theorem functionhead3Like_ruleShape_twoWitnessBoundary_sound_of_member
    {oracle : GroundedOracle} {space : PeTTaSpace} {workspace : Space}
    (horacle : TupleMembershipOracleContract oracle)
    {ctor : String}
    {rawArgsX rawArgsY : List PeTTaPattern} {tyX tyY : PeTTaPattern}
    {bindingsX finalBindingsX : Bindings}
    {bindingsY finalBindingsY : Bindings}
    {x xs y ys : PeTTaPattern}
    {varX varY : String}
    {mergedWitnessBindings : Bindings}
    {residualBody residualInstantiated : PeTTaPattern}
    {sourceRule : SourceExecRule}
    (hargsX : InterpretArgs space bindingsX rawArgsX [x, xs] finalBindingsX)
    (hmemX : x ∈ tupleElems xs)
    (hargsY : InterpretArgs space bindingsY rawArgsY [y, ys] finalBindingsY)
    (hmemY : y ∈ tupleElems ys)
    (hmerge :
      mergeBindings [(varX, x)] [(varY, y)] = some mergedWitnessBindings)
    (htrans : morkTranslatable residualBody = true)
    (hinst :
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings mergedWitnessBindings residualBody =
        residualInstantiated)
    (hr :
      ResidualMorkPhase workspace sourceRule
        (bindingsToSubst mergedWitnessBindings)) :
    Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule
        (rewriteOnlyDispatchInterface
          [functionhead3LikeCoreRule ctor varX varY xs ys residualBody]) () ctor 2 = true ∧
      MeTTaEvalG oracle space (.apply "is-member" rawArgsX) tyX bindingsX
        [(.apply "True" [], finalBindingsX)] ∧
      MeTTaEvalG oracle space (.apply "is-member" rawArgsY) tyY bindingsY
        [(.apply "True" [], finalBindingsY)] ∧
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings mergedWitnessBindings (.fvar varX) = x ∧
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings mergedWitnessBindings (.fvar varY) = y ∧
      applySubst (bindingsToSubst mergedWitnessBindings) (morkPatternToAtom residualBody) =
        morkPatternToAtom residualInstantiated ∧
      applySinks workspace (bindingsToSubst mergedWitnessBindings) sourceRule.tmpl ∈
        fireSourceRule workspace sourceRule := by
  refine ⟨functionhead3Like_ruleShape_hasCompatHeadConstraintRule, ?_⟩
  exact tupleMembership_twoWitness_residual_sound_of_member
    (workspace := workspace) horacle hargsX hmemX hargsY hmemY hmerge htrans hinst hr

/-- Clean statement of the exact `Dispatch` seam the current deterministic
`functionhead3` fragment is meant to feed.

At the current conformance layer, the honest statement is still the structural
one: the real `Dispatch` classifier selects the compat-head branch for this
rule shape. The stronger operational singleton-projection seam belongs on the
`Dispatch` side, not here. -/

def Functionhead3LikeDispatchBridgeTarget
    (ctor varX varY : String) (xs ys rhs : PeTTaPattern)
    (_tArg0 _tArg1 : MeTTailCore.MeTTaIL.Syntax.Pattern) : Prop :=
  Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule
    (rewriteOnlyDispatchInterface
      [functionhead3LikeCoreRule ctor varX varY xs ys rhs]) () ctor 2 = true

/-- The deterministic singleton `functionhead3` fragment lands exactly on the
real `Dispatch` compat-head branch described by
`Functionhead3LikeDispatchBridgeTarget`. -/
theorem functionhead3Like_dispatchBridgeTarget
    {ctor varX varY : String} {xs ys rhs : PeTTaPattern}
    {_tArg0 _tArg1 : MeTTailCore.MeTTaIL.Syntax.Pattern}
    (_hPlainCtor : ¬ ctor.startsWith "$") :
    Functionhead3LikeDispatchBridgeTarget ctor varX varY xs ys rhs _tArg0 _tArg1 := by
  dsimp [Functionhead3LikeDispatchBridgeTarget]
  simpa using
    functionhead3Like_ruleShape_hasCompatHeadConstraintRule
      (ctor := ctor) (varX := varX) (varY := varY) (xs := xs) (ys := ys) (rhs := rhs)

/-- Exact deterministic contract that downstream runtimes are allowed to rely
on for the current singleton `functionhead3`-like compat-head fragment.

This contract is intentionally narrow:
- the rule set is a singleton;
- the rule head is compat-head by the real Dispatch classifier;
- the constructor is a plain user head (not `$...`);
- the observable compat-head outputs are exactly the `Prod.snd` projection of
  the binding-carrying constrained-call outputs.

It does not claim multiset/nondeterministic behavior, and it does not claim
general compat-head support beyond this deterministic singleton slice. -/
structure DeterministicFunctionhead3CompatContract
    (ctor varX varY : String) (xs ys rhs : PeTTaPattern) : Prop where
  noDollar : ctor.startsWith "$" = false
  branchTarget :
    Functionhead3LikeDispatchBridgeTarget ctor varX varY xs ys rhs
      (specToCorePattern (.apply "in" [.fvar varX, xs]))
      (specToCorePattern (.apply "in" [.fvar varY, ys]))
  singletonProjection :
    let valsState :=
      Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
        (rewriteOnlyDispatchInterface
          [functionhead3LikeCoreRule ctor varX varY xs ys rhs])
        ()
        (.apply ctor (functionhead3LikeRawArgs varX varY xs ys))
    let pairState :=
      Algorithms.MeTTa.Simple.Semantics.Dispatch.constrainedCallBindingsAndValues
        (rewriteOnlyDispatchInterface
          [functionhead3LikeCoreRule ctor varX varY xs ys rhs])
        ()
        (.apply ctor (functionhead3LikeRawArgs varX varY xs ys))
    valsState.1 = pairState.1 ∧ valsState.2 = pairState.2.map Prod.snd

/-- The deterministic singleton `functionhead3`-like fragment satisfies the
exact compat-head contract downstream runtimes are allowed to consume. -/
theorem functionhead3Like_deterministicCompatContract
    {ctor varX varY : String} {xs ys rhs : PeTTaPattern}
    (hNoDollar : ctor.startsWith "$" = false) :
    DeterministicFunctionhead3CompatContract ctor varX varY xs ys rhs := by
  refine ⟨hNoDollar, ?_, ?_⟩
  · simpa using
      (functionhead3Like_dispatchBridgeTarget
        (ctor := ctor) (varX := varX) (varY := varY) (xs := xs) (ys := ys) (rhs := rhs)
        (by simpa using hNoDollar))
  · exact functionhead3Like_singleton_bridge
      (ctor := ctor) (varX := varX) (varY := varY) (xs := xs) (ys := ys) (rhs := rhs)
      hNoDollar

/-! ## Finite existence-only once/match boundary

This is the narrow portable fragment behind source families such as:

- positive example: `if (== () (collapse (once (match S P P)))) Then Else`
- positive example: `if (== () (collapse (once (match S P True)))) Then Else`
- negative example: witness-returning `once` forms whose selected witness value
  must remain observable outside the goal itself

The contract here is intentionally about the canonical translated HE shape:
an emptiness check over the portable `once` lowering. -/

/-- Canonical HE-core emptiness check over a translated `once` surface. -/
def buildFiniteExistsMatchCondition (translatedOnce : HEAtom) : HEAtom :=
  .expression
    [.symbol "==",
     .symbol "()",
     .expression [.symbol "collapse", translatedOnce]]

/-- The existence-only once/match fragment is pure whenever the translated
`once` surface itself is pure. -/
theorem buildFiniteExistsMatchCondition_pureTranslatable
    {translatedOnce : HEAtom}
    (honce : PureTranslatable translatedOnce) :
    PureTranslatable (buildFiniteExistsMatchCondition translatedOnce) := by
  simp [buildFiniteExistsMatchCondition]
  have hcollapse :
      PureTranslatable (.expression [.symbol "collapse", translatedOnce]) := by
    exact pureTranslatable_expr "collapse" [translatedOnce]
      (by decide) (by decide) (by
        intro a ha
        simp at ha
        rcases ha with rfl
        exact honce)
  have hempty : PureTranslatable (.symbol "()") := pureTranslatable_symbol "()"
  exact pureTranslatable_expr "=="
    [.symbol "()", .expression [.symbol "collapse", translatedOnce]]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact hempty
      · exact hcollapse)

/-- Conformance contract for the existence-only `once(match ...)` fragment. The
observable result is just emptiness/non-emptiness, not the identity of a chosen
witness. -/
structure PureFiniteExistsMatchContract (translatedOnce : HEAtom) : Prop where
  translatedPure :
    PureTranslatable (buildFiniteExistsMatchCondition translatedOnce)

/-- Package an existing pure translated `once` surface as a finite-exists
compatibility witness. -/
theorem pureFiniteExistsMatchContract_of_pureOnce
    {translatedOnce : HEAtom}
    (honce : PureTranslatable translatedOnce) :
    PureFiniteExistsMatchContract translatedOnce := by
  exact ⟨buildFiniteExistsMatchCondition_pureTranslatable honce⟩

/-! ## Singleton visible witness boundary

This is the narrow portable fragment where the observable result of `once` is a
single visible witness together with its recovered bindings, independent of
visible result order.

- positive example: `(once (= $x 42))`
- positive example: a unique truth-value witness whose body binds exactly one
  translated result tuple
- negative example: ordered committed choice over multiple visible witnesses

At the current conformance layer, the dedicated
`singleton-visible-witness` surface is the honest portable contract. We keep it
explicit rather than pretending it has already been lowered to a more generic
HE-core form. -/

/-- Canonical HE surface for the unique visible-witness fragment. -/
def buildSingletonVisibleWitnessSurface (translatedWitness : HEAtom) : HEAtom :=
  .expression
    [.symbol "singleton-visible-witness",
     translatedWitness]

/-- The dedicated singleton visible-witness surface is pure whenever its inner
translated witness expression is pure. -/
theorem buildSingletonVisibleWitnessSurface_pureTranslatable
    {translatedWitness : HEAtom}
    (hwitness : PureTranslatable translatedWitness) :
    PureTranslatable (buildSingletonVisibleWitnessSurface translatedWitness) := by
  simp [buildSingletonVisibleWitnessSurface]
  exact pureTranslatable_expr "singleton-visible-witness"
    [translatedWitness]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl
      exact hwitness)

/-- Conformance contract for the unique visible-witness fragment. The
translated HE surface keeps the binding-carrying singleton witness explicit,
and does not widen the fragment into ordered first-witness selection. -/
structure PureSingletonVisibleWitnessContract
    (translatedWitness : HEAtom) : Prop where
  translatedPure :
    PureTranslatable
      (buildSingletonVisibleWitnessSurface translatedWitness)

/-- Package an existing pure translated witness surface as a singleton
visible-witness compatibility witness. -/
theorem pureSingletonVisibleWitnessContract_of_pureWitness
    {translatedWitness : HEAtom}
    (hwitness : PureTranslatable translatedWitness) :
    PureSingletonVisibleWitnessContract translatedWitness := by
  exact ⟨buildSingletonVisibleWitnessSurface_pureTranslatable hwitness⟩

/-! ## Core portable surface contracts

These rows are already covered executably in the HE profile suite. The
conformance layer keeps the proof-facing part honest by recording the portable
surface shape the translator/runtime are allowed to rely on, without pretending
this file is a full evaluator proof for every operational detail. -/

/-- Opaque user or runtime-added public heads stay explicit HE expressions. -/
def buildOpaqueHeadSurface (head : String) (args : List HEAtom) : HEAtom :=
  .expression (.symbol head :: args)

/-- The opaque-head surface is pure whenever all arguments are pure. -/
theorem buildOpaqueHeadSurface_pureTranslatable
    {head : String} {args : List HEAtom}
    (hnotLam : head ≠ "λ")
    (hnotSubst : head ≠ "subst")
    (hargs : ∀ a ∈ args, PureTranslatable a) :
    PureTranslatable (buildOpaqueHeadSurface head args) := by
  simp [buildOpaqueHeadSurface]
  exact pureTranslatable_expr head args hnotLam hnotSubst hargs

/-- Conformance contract for the "unknown heads remain data" fragment. -/
structure PureUnknownHeadDataContract
    (head : String) (args : List HEAtom) : Prop where
  headNotLambda : head ≠ "λ"
  headNotSubst : head ≠ "subst"
  translatedPure :
    PureTranslatable (buildOpaqueHeadSurface head args)

/-- Package a pure opaque-head expression as an unknown-head data witness. -/
theorem pureUnknownHeadDataContract_of_pureArgs
    {head : String} {args : List HEAtom}
    (hnotLam : head ≠ "λ")
    (hnotSubst : head ≠ "subst")
    (hargs : ∀ a ∈ args, PureTranslatable a) :
    PureUnknownHeadDataContract head args := by
  exact ⟨hnotLam, hnotSubst,
    buildOpaqueHeadSurface_pureTranslatable hnotLam hnotSubst hargs⟩

/-- Explicit `call` surface for known callable heads. -/
def buildExplicitCallSurface (body : HEAtom) : HEAtom :=
  .expression [.symbol "call", body]

/-- Explicit `eval` surface for known callable heads. -/
def buildExplicitEvalSurface (body : HEAtom) : HEAtom :=
  .expression [.symbol "eval", body]

theorem buildExplicitCallSurface_pureTranslatable
    {body : HEAtom}
    (hbody : PureTranslatable body) :
    PureTranslatable (buildExplicitCallSurface body) := by
  simp [buildExplicitCallSurface]
  exact pureTranslatable_expr "call" [body]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl
      exact hbody)

theorem buildExplicitEvalSurface_pureTranslatable
    {body : HEAtom}
    (hbody : PureTranslatable body) :
    PureTranslatable (buildExplicitEvalSurface body) := by
  simp [buildExplicitEvalSurface]
  exact pureTranslatable_expr "eval" [body]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl
      exact hbody)

/-- Conformance contract for the explicit known-callable `call`/`eval` surface. -/
structure PureKnownCallableHeadsReduceContract
    (body : HEAtom) : Prop where
  callPure :
    PureTranslatable (buildExplicitCallSurface body)
  evalPure :
    PureTranslatable (buildExplicitEvalSurface body)

/-- Package a pure body as an explicit known-callable surface witness. -/
theorem pureKnownCallableHeadsReduceContract_of_pureBody
    {body : HEAtom}
    (hbody : PureTranslatable body) :
    PureKnownCallableHeadsReduceContract body := by
  exact ⟨buildExplicitCallSurface_pureTranslatable hbody,
    buildExplicitEvalSurface_pureTranslatable hbody⟩

/-- Explicit quoted-data surface. -/
def buildQuotedDataSurface (body : HEAtom) : HEAtom :=
  .expression [.symbol "quote", body]

theorem buildQuotedDataSurface_pureTranslatable
    {body : HEAtom}
    (hbody : PureTranslatable body) :
    PureTranslatable (buildQuotedDataSurface body) := by
  simp [buildQuotedDataSurface]
  exact pureTranslatable_expr "quote" [body]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl
      exact hbody)

/-- Conformance contract for quoted/data positions that must stay explicit at
the portable surface. -/
structure PureQuotedAndDataPositionsContract
    (quotedBody evalBody : HEAtom) : Prop where
  quotedPure :
    PureTranslatable (buildQuotedDataSurface quotedBody)
  evalPure :
    PureTranslatable (buildExplicitEvalSurface evalBody)

/-- Package pure quoted/eval bodies as a portable quoted/data witness. -/
theorem pureQuotedAndDataPositionsContract_of_pureBodies
    {quotedBody evalBody : HEAtom}
    (hquoted : PureTranslatable quotedBody)
    (heval : PureTranslatable evalBody) :
    PureQuotedAndDataPositionsContract quotedBody evalBody := by
  exact ⟨buildQuotedDataSurface_pureTranslatable hquoted,
    buildExplicitEvalSurface_pureTranslatable heval⟩

/-- Conformance contract for the pure lowered shape of PeTTa partial-callable
idioms. The portable boundary keeps the callable body explicit and routes use
through ordinary `call` / `eval` surfaces instead of any PeTTa-internal partial
representation. -/
structure PurePartialCallableLoweringContract
    (callableBody : HEAtom) : Prop where
  bodyPure : PureTranslatable callableBody
  callPure : PureTranslatable (buildExplicitCallSurface callableBody)
  evalPure : PureTranslatable (buildExplicitEvalSurface callableBody)

/-- Package a pure lowered callable body as a partial-callable witness. -/
theorem purePartialCallableLoweringContract_of_pureBody
    {callableBody : HEAtom}
    (hbody : PureTranslatable callableBody) :
    PurePartialCallableLoweringContract callableBody := by
  exact ⟨hbody,
    buildExplicitCallSurface_pureTranslatable hbody,
    buildExplicitEvalSurface_pureTranslatable hbody⟩

/-- Conformance contract for the variable-head boundary.

For the negative/data branch, an unbound head stays an explicit variable plus
pure data arguments at the portable boundary. For the positive/callable branch,
the resolved callable body is lowered through ordinary `call` / `eval`
surfaces rather than through ambient variable-headed search. -/
structure PureVariableHeadDataAndCallableBindingContract
    (headVar : String) (dataArgs : List HEAtom) (callableBody : HEAtom) : Prop where
  variablePure : PureTranslatable (.var headVar)
  dataArgsPure : ∀ a ∈ dataArgs, PureTranslatable a
  callableCallPure : PureTranslatable (buildExplicitCallSurface callableBody)
  callableEvalPure : PureTranslatable (buildExplicitEvalSurface callableBody)

/-- Package pure variable-head data arguments together with a pure lowered
callable body as the portable variable-head witness. -/
theorem pureVariableHeadDataAndCallableBindingContract_of_pureArgsAndBody
    {headVar : String} {dataArgs : List HEAtom} {callableBody : HEAtom}
    (hargs : ∀ a ∈ dataArgs, PureTranslatable a)
    (hbody : PureTranslatable callableBody) :
    PureVariableHeadDataAndCallableBindingContract
      headVar dataArgs callableBody := by
  exact ⟨pureTranslatable_var headVar, hargs,
    buildExplicitCallSurface_pureTranslatable hbody,
    buildExplicitEvalSurface_pureTranslatable hbody⟩

/-- Conformance contract for runtime-added equations that remain callable under
their public head names. -/
structure PureRuntimeAddedEquationPublicHeadContract
    (head : String) (args : List HEAtom) : Prop where
  headNotLambda : head ≠ "λ"
  headNotSubst : head ≠ "subst"
  translatedPure :
    PureTranslatable (buildOpaqueHeadSurface head args)

/-- Package a pure opaque-head expression as a runtime-added public-head
callability witness. -/
theorem pureRuntimeAddedEquationPublicHeadContract_of_pureArgs
    {head : String} {args : List HEAtom}
    (hnotLam : head ≠ "λ")
    (hnotSubst : head ≠ "subst")
    (hargs : ∀ a ∈ args, PureTranslatable a) :
    PureRuntimeAddedEquationPublicHeadContract head args := by
  exact ⟨hnotLam, hnotSubst,
    buildOpaqueHeadSurface_pureTranslatable hnotLam hnotSubst hargs⟩

/-- Portable singleton-space pattern surface. -/
def buildSpacePatternMatchSurface
    (space pat body : HEAtom) : HEAtom :=
  .expression [.symbol "match", space, pat, body]

theorem buildSpacePatternMatchSurface_pureTranslatable
    {space pat body : HEAtom}
    (hspace : PureTranslatable space)
    (hpat : PureTranslatable pat)
    (hbody : PureTranslatable body) :
    PureTranslatable (buildSpacePatternMatchSurface space pat body) := by
  simp [buildSpacePatternMatchSurface]
  exact pureTranslatable_expr "match" [space, pat, body]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl | rfl
      · exact hspace
      · exact hpat
      · exact hbody)

/-- Conformance contract for singleton-space expression-pattern matching. -/
structure PureSpaceSingletonExpressionPatternContract
    (space pat body : HEAtom) : Prop where
  translatedPure :
    PureTranslatable (buildSpacePatternMatchSurface space pat body)

/-- Package a pure singleton-space pattern surface as a conformance witness. -/
theorem pureSpaceSingletonExpressionPatternContract_of_pureSurface
    {space pat body : HEAtom}
    (hspace : PureTranslatable space)
    (hpat : PureTranslatable pat)
    (hbody : PureTranslatable body) :
    PureSpaceSingletonExpressionPatternContract space pat body := by
  exact ⟨buildSpacePatternMatchSurface_pureTranslatable hspace hpat hbody⟩

/-- Explicit error payload surface. -/
def buildErrorSurface (term payload : HEAtom) : HEAtom :=
  .expression [.symbol "Error", term, payload]

theorem buildErrorSurface_pureTranslatable
    {term payload : HEAtom}
    (hterm : PureTranslatable term)
    (hpayload : PureTranslatable payload) :
    PureTranslatable (buildErrorSurface term payload) := by
  simp [buildErrorSurface]
  exact pureTranslatable_expr "Error" [term, payload]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact hterm
      · exact hpayload)

/-- Conformance contract for explicit portable type/error surfaces. -/
structure PureTypeAndErrorContract
    (term payload : HEAtom) : Prop where
  translatedPure :
    PureTranslatable (buildErrorSurface term payload)

/-- Package a pure explicit error payload as a type/error witness. -/
theorem pureTypeAndErrorContract_of_purePayload
    {term payload : HEAtom}
    (hterm : PureTranslatable term)
    (hpayload : PureTranslatable payload) :
    PureTypeAndErrorContract term payload := by
  exact ⟨buildErrorSurface_pureTranslatable hterm hpayload⟩

/-- Explicit `assertEqualToEval` portable surface used by the source test/helper
policy. -/
def buildAssertEqualToEvalSurface (lhs rhs : HEAtom) : HEAtom :=
  .expression [.symbol "assertEqualToEval", lhs, rhs]

theorem buildAssertEqualToEvalSurface_pureTranslatable
    {lhs rhs : HEAtom}
    (hlhs : PureTranslatable lhs)
    (hrhs : PureTranslatable rhs) :
    PureTranslatable (buildAssertEqualToEvalSurface lhs rhs) := by
  simp [buildAssertEqualToEvalSurface]
  exact pureTranslatable_expr "assertEqualToEval" [lhs, rhs]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact hlhs
      · exact hrhs)

/-- Conformance contract for the pure source-test helper surface. -/
structure PureSourceTestHelperPolicyContract
    (lhs rhs : HEAtom) : Prop where
  translatedPure :
    PureTranslatable (buildAssertEqualToEvalSurface lhs rhs)

/-- Package a pure `assertEqualToEval` surface as a helper-policy witness. -/
theorem pureSourceTestHelperPolicyContract_of_pureSurface
    {lhs rhs : HEAtom}
    (hlhs : PureTranslatable lhs)
    (hrhs : PureTranslatable rhs) :
    PureSourceTestHelperPolicyContract lhs rhs := by
  exact ⟨buildAssertEqualToEvalSurface_pureTranslatable hlhs hrhs⟩

/-! ## Backend-native HE-profile surface contracts

These rows are profile-lane contracts rather than pure-core claims. The
conformance layer records the narrow recognized HE surfaces and how larger
backend-native families decompose into already-named subcontracts, without
pretending this file proves the backend operational equivalence itself. -/

/-- Supported count consumers in the current counted-match and count-eval
profile contracts. -/
def IsCountConsumerName (counter : String) : Prop :=
  counter = "length" ∨ counter = "size-atom"

theorem countConsumer_notLambda
    {counter : String}
    (hcounter : IsCountConsumerName counter) :
    counter ≠ "λ" := by
  rcases hcounter with rfl | rfl <;> decide

theorem countConsumer_notSubst
    {counter : String}
    (hcounter : IsCountConsumerName counter) :
    counter ≠ "subst" := by
  rcases hcounter with rfl | rfl <;> decide

/-- Explicit `collapse` wrapper surface. -/
def buildCollapseSurface (body : HEAtom) : HEAtom :=
  .expression [.symbol "collapse", body]

theorem buildCollapseSurface_pureTranslatable
    {body : HEAtom}
    (hbody : PureTranslatable body) :
    PureTranslatable (buildCollapseSurface body) := by
  simp [buildCollapseSurface]
  exact pureTranslatable_expr "collapse" [body]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl
      exact hbody)

/-- Explicit `once` wrapper surface. -/
def buildOnceSurface (body : HEAtom) : HEAtom :=
  .expression [.symbol "once", body]

theorem buildOnceSurface_pureTranslatable
    {body : HEAtom}
    (hbody : PureTranslatable body) :
    PureTranslatable (buildOnceSurface body) := by
  simp [buildOnceSurface]
  exact pureTranslatable_expr "once" [body]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl
      exact hbody)

/-- Explicit `select` wrapper surface. -/
def buildSelectSurface (body : HEAtom) : HEAtom :=
  .expression [.symbol "select", body]

theorem buildSelectSurface_pureTranslatable
    {body : HEAtom}
    (hbody : PureTranslatable body) :
    PureTranslatable (buildSelectSurface body) := by
  simp [buildSelectSurface]
  exact pureTranslatable_expr "select" [body]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl
      exact hbody)

/-- Explicit equality surface used by recursive numeric/profile rows. -/
def buildEqualitySurface (lhs rhs : HEAtom) : HEAtom :=
  .expression [.symbol "==", lhs, rhs]

theorem buildEqualitySurface_pureTranslatable
    {lhs rhs : HEAtom}
    (hlhs : PureTranslatable lhs)
    (hrhs : PureTranslatable rhs) :
    PureTranslatable (buildEqualitySurface lhs rhs) := by
  simp [buildEqualitySurface]
  exact pureTranslatable_expr "==" [lhs, rhs]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact hlhs
      · exact hrhs)

/-- Explicit unused-binding `let` surface used by the effect-only branching
profile contract. -/
def buildUnusedBindingSurface
    (binder : String) (value body : HEAtom) : HEAtom :=
  .expression [.symbol "let", .var binder, value, body]

theorem buildUnusedBindingSurface_pureTranslatable
    {binder : String} {value body : HEAtom}
    (hvalue : PureTranslatable value)
    (hbody : PureTranslatable body) :
    PureTranslatable (buildUnusedBindingSurface binder value body) := by
  simp [buildUnusedBindingSurface]
  exact pureTranslatable_expr "let" [.var binder, value, body]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl | rfl
      · exact pureTranslatable_var binder
      · exact hvalue
      · exact hbody)

/-- Conformance contract for deterministic compiled-call surfaces where
`collapse`, `once`, and `select` observe the same pure underlying body. -/
structure ProfileDeterministicCompiledCallContract
    (body : HEAtom) : Prop where
  collapsePure : PureTranslatable (buildCollapseSurface body)
  oncePure : PureTranslatable (buildOnceSurface body)
  selectPure : PureTranslatable (buildSelectSurface body)

/-- Package a pure compiled-call body as the deterministic first-visible
surface witness. -/
theorem profileDeterministicCompiledCallContract_of_pureBody
    {body : HEAtom}
    (hbody : PureTranslatable body) :
    ProfileDeterministicCompiledCallContract body := by
  exact ⟨buildCollapseSurface_pureTranslatable hbody,
    buildOnceSurface_pureTranslatable hbody,
    buildSelectSurface_pureTranslatable hbody⟩

/-- Canonical counted visible-match surface: a count/size consumer over a
collapsed visible `match` result. -/
def buildCountedVisibleMatchSurface
    (counter : String) (space pat body : HEAtom) : HEAtom :=
  .expression
    [.symbol counter,
     buildCollapseSurface (buildSpacePatternMatchSurface space pat body)]

theorem buildCountedVisibleMatchSurface_pureTranslatable
    {counter : String} {space pat body : HEAtom}
    (hcounter : IsCountConsumerName counter)
    (hspace : PureTranslatable space)
    (hpat : PureTranslatable pat)
    (hbody : PureTranslatable body) :
    PureTranslatable (buildCountedVisibleMatchSurface counter space pat body) := by
  have hmatch :
      PureTranslatable (buildSpacePatternMatchSurface space pat body) := by
    exact buildSpacePatternMatchSurface_pureTranslatable hspace hpat hbody
  have hcollapse :
      PureTranslatable
        (buildCollapseSurface (buildSpacePatternMatchSurface space pat body)) := by
    exact buildCollapseSurface_pureTranslatable hmatch
  simp [buildCountedVisibleMatchSurface]
  exact pureTranslatable_expr counter
    [buildCollapseSurface (buildSpacePatternMatchSurface space pat body)]
    (countConsumer_notLambda hcounter)
    (countConsumer_notSubst hcounter)
    (by
      intro a ha
      simp at ha
      rcases ha with rfl
      exact hcollapse)

/-- Surface predicate for the current counted visible-match family. -/
def CountedVisibleMatchSurface (expr : HEAtom) : Prop :=
  ∃ counter space pat body,
    IsCountConsumerName counter ∧
    expr = buildCountedVisibleMatchSurface counter space pat body

/-- Conformance contract for counted visible-match profile surfaces. -/
structure ProfileCountedVisibleMatchContract
    (counter : String) (space pat body : HEAtom) : Prop where
  counterAllowed : IsCountConsumerName counter
  translatedPure :
    PureTranslatable (buildCountedVisibleMatchSurface counter space pat body)

/-- Package a pure counted visible-match surface as a profile witness. -/
theorem profileCountedVisibleMatchContract_of_pureSurface
    {counter : String} {space pat body : HEAtom}
    (hcounter : IsCountConsumerName counter)
    (hspace : PureTranslatable space)
    (hpat : PureTranslatable pat)
    (hbody : PureTranslatable body) :
    ProfileCountedVisibleMatchContract counter space pat body := by
  exact ⟨hcounter,
    buildCountedVisibleMatchSurface_pureTranslatable hcounter hspace hpat hbody⟩

/-- Canonical `count(eval(...))` profile surface. -/
def buildCountEvalSurface (counter : String) (body : HEAtom) : HEAtom :=
  .expression [.symbol counter, buildExplicitEvalSurface body]

theorem buildCountEvalSurface_pureTranslatable
    {counter : String} {body : HEAtom}
    (hcounter : IsCountConsumerName counter)
    (hbody : PureTranslatable body) :
    PureTranslatable (buildCountEvalSurface counter body) := by
  have heval : PureTranslatable (buildExplicitEvalSurface body) := by
    exact buildExplicitEvalSurface_pureTranslatable hbody
  simp [buildCountEvalSurface]
  exact pureTranslatable_expr counter [buildExplicitEvalSurface body]
    (countConsumer_notLambda hcounter)
    (countConsumer_notSubst hcounter)
    (by
      intro a ha
      simp at ha
      rcases ha with rfl
      exact heval)

/-- Conformance contract for the explicit count-eval profile surface. -/
structure ProfileCountEvalContract
    (counter : String) (body : HEAtom) : Prop where
  counterAllowed : IsCountConsumerName counter
  translatedPure :
    PureTranslatable (buildCountEvalSurface counter body)

/-- Package a pure count-eval surface as a profile witness. -/
theorem profileCountEvalContract_of_pureBody
    {counter : String} {body : HEAtom}
    (hcounter : IsCountConsumerName counter)
    (hbody : PureTranslatable body) :
    ProfileCountEvalContract counter body := by
  exact ⟨hcounter, buildCountEvalSurface_pureTranslatable hcounter hbody⟩

/-- Conformance contract for unused-binding effect-only branching surfaces. -/
structure ProfileEffectOnlyBranchingContract
    (binder : String) (value body : HEAtom) : Prop where
  translatedPure :
    PureTranslatable (buildUnusedBindingSurface binder value body)

/-- Package a pure unused-binding branch surface as the effect-only witness. -/
theorem profileEffectOnlyBranchingContract_of_pureSurface
    {binder : String} {value body : HEAtom}
    (hvalue : PureTranslatable value)
    (hbody : PureTranslatable body) :
    ProfileEffectOnlyBranchingContract binder value body := by
  exact ⟨buildUnusedBindingSurface_pureTranslatable hvalue hbody⟩

/-- Conformance contract for ground recursive memo families. The portable
surface keeps the recursive result under explicit `eval`, while dynamic helper
heads still obey the public runtime-added-equation head contract. -/
structure ProfileGroundRecursiveMemoContract
    (recursiveBody : HEAtom) (mutableHead : String) (mutableArgs : List HEAtom) : Prop where
  recursiveEvalPure :
    PureTranslatable (buildExplicitEvalSurface recursiveBody)
  mutablePublicHead :
    PureRuntimeAddedEquationPublicHeadContract mutableHead mutableArgs

/-- Package a pure recursive body plus a pure mutable public head as the ground
recursive memo witness. -/
theorem profileGroundRecursiveMemoContract_of_pureSurface
    {recursiveBody : HEAtom} {mutableHead : String} {mutableArgs : List HEAtom}
    (hbody : PureTranslatable recursiveBody)
    (hnotLam : mutableHead ≠ "λ")
    (hnotSubst : mutableHead ≠ "subst")
    (hargs : ∀ a ∈ mutableArgs, PureTranslatable a) :
    ProfileGroundRecursiveMemoContract recursiveBody mutableHead mutableArgs := by
  exact ⟨buildExplicitEvalSurface_pureTranslatable hbody,
    pureRuntimeAddedEquationPublicHeadContract_of_pureArgs
      hnotLam hnotSubst hargs⟩

/-- Conformance contract for equality over recursive numeric-call results. -/
structure ProfileNumericRecursionContract
    (lhs rhs : HEAtom) : Prop where
  translatedPure :
    PureTranslatable (buildEqualitySurface lhs rhs)

/-- Package pure equality sides as the recursive numeric-call witness. -/
theorem profileNumericRecursionContract_of_pureSides
    {lhs rhs : HEAtom}
    (hlhs : PureTranslatable lhs)
    (hrhs : PureTranslatable rhs) :
    ProfileNumericRecursionContract lhs rhs := by
  exact ⟨buildEqualitySurface_pureTranslatable hlhs hrhs⟩

/-- Canonical queue-search contract surface used by the current backend-native
family. -/
def buildQueueSearchContractSurface
    (space seedMode statePlan neighborPlan : HEAtom) : HEAtom :=
  .expression
    [.symbol "queue_search_contract", space, seedMode, statePlan, neighborPlan]

theorem buildQueueSearchContractSurface_pureTranslatable
    {space seedMode statePlan neighborPlan : HEAtom}
    (hspace : PureTranslatable space)
    (hseedMode : PureTranslatable seedMode)
    (hstatePlan : PureTranslatable statePlan)
    (hneighborPlan : PureTranslatable neighborPlan) :
    PureTranslatable
      (buildQueueSearchContractSurface space seedMode statePlan neighborPlan) := by
  simp [buildQueueSearchContractSurface]
  exact pureTranslatable_expr "queue_search_contract"
    [space, seedMode, statePlan, neighborPlan]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact hspace
      · exact hseedMode
      · exact hstatePlan
      · exact hneighborPlan)

/-- Conformance contract for the explicit queue-search wrapper surface. -/
structure ProfileQueueSearchContract
    (space seedMode statePlan neighborPlan : HEAtom) : Prop where
  translatedPure :
    PureTranslatable
      (buildQueueSearchContractSurface space seedMode statePlan neighborPlan)

/-- Package a pure explicit queue-search wrapper as a profile witness. -/
theorem profileQueueSearchContract_of_pureSurface
    {space seedMode statePlan neighborPlan : HEAtom}
    (hspace : PureTranslatable space)
    (hseedMode : PureTranslatable seedMode)
    (hstatePlan : PureTranslatable statePlan)
    (hneighborPlan : PureTranslatable neighborPlan) :
    ProfileQueueSearchContract space seedMode statePlan neighborPlan := by
  exact ⟨buildQueueSearchContractSurface_pureTranslatable
    hspace hseedMode hstatePlan hneighborPlan⟩

/-- Explicit unique-add profile surface. -/
def buildExactUniqueAddSurface (space atom : HEAtom) : HEAtom :=
  .expression [.symbol "add-unique-or-fail", space, atom]

theorem buildExactUniqueAddSurface_pureTranslatable
    {space atom : HEAtom}
    (hspace : PureTranslatable space)
    (hatom : PureTranslatable atom) :
    PureTranslatable (buildExactUniqueAddSurface space atom) := by
  simp [buildExactUniqueAddSurface]
  exact pureTranslatable_expr "add-unique-or-fail" [space, atom]
    (by decide) (by decide) (by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact hspace
      · exact hatom)

/-- Conformance contract for the exact-membership/public-unique-add surface. -/
structure ProfileExactUniqueAddContract
    (space atom : HEAtom) : Prop where
  translatedPure :
    PureTranslatable (buildExactUniqueAddSurface space atom)

/-- Package a pure unique-add surface as a profile witness. -/
theorem profileExactUniqueAddContract_of_pureSurface
    {space atom : HEAtom}
    (hspace : PureTranslatable space)
    (hatom : PureTranslatable atom) :
    ProfileExactUniqueAddContract space atom := by
  exact ⟨buildExactUniqueAddSurface_pureTranslatable hspace hatom⟩

/-- Conformance contract for the indexed-count wrapper family. At this layer we
record that a pure producer is paired with five counted visible-match
observations, one for each reported count channel. -/
structure ProfileIndexedCountContract
    (producer allQuery firstQuery secondQuery relQuery bothQuery : HEAtom) :
    Prop where
  producerPure : PureTranslatable producer
  allObserved : CountedVisibleMatchSurface allQuery
  firstObserved : CountedVisibleMatchSurface firstQuery
  secondObserved : CountedVisibleMatchSurface secondQuery
  relObserved : CountedVisibleMatchSurface relQuery
  bothObserved : CountedVisibleMatchSurface bothQuery

/-- Package the indexed-count family from its pure producer and observed
count-query surfaces. -/
theorem profileIndexedCountContract_of_surfaces
    {producer allQuery firstQuery secondQuery relQuery bothQuery : HEAtom}
    (hproducer : PureTranslatable producer)
    (hall : CountedVisibleMatchSurface allQuery)
    (hfirst : CountedVisibleMatchSurface firstQuery)
    (hsecond : CountedVisibleMatchSurface secondQuery)
    (hrel : CountedVisibleMatchSurface relQuery)
    (hboth : CountedVisibleMatchSurface bothQuery) :
    ProfileIndexedCountContract
      producer allQuery firstQuery secondQuery relQuery bothQuery := by
  exact ⟨hproducer, hall, hfirst, hsecond, hrel, hboth⟩

/-- Conformance contract for the seeded unary successor-closure family. At this
layer the profile-native story is recorded as the combination of:
- a public seed insertion surface
- an existence-only once/match expansion fragment
- a counted visible-match observation over the public `num(...)` facts -/
structure ProfileSeededUnarySuccessorClosureContract
    (seedSurface translatedOnce countQuery : HEAtom) : Prop where
  seedPure : PureTranslatable seedSurface
  existsObserved : PureFiniteExistsMatchContract translatedOnce
  countObserved : CountedVisibleMatchSurface countQuery

/-- Package the seeded successor-closure family from its explicit seed,
existence-only expansion, and counted observation surfaces. -/
theorem profileSeededUnarySuccessorClosureContract_of_surfaces
    {seedSurface translatedOnce countQuery : HEAtom}
    (hseed : PureTranslatable seedSurface)
    (hexists : PureFiniteExistsMatchContract translatedOnce)
    (hcount : CountedVisibleMatchSurface countQuery) :
    ProfileSeededUnarySuccessorClosureContract
      seedSurface translatedOnce countQuery := by
  exact ⟨hseed, hexists, hcount⟩

/-- Explicit lane split for function-call inversion.

`pureAppendSuffix` is the fully structural fragment already mirrored in the
HE translation proofs. `extendedWitness` is the oracle-backed fragment used
when structural inversion alone is not enough. -/
inductive FunctionCallInversionLane where
  | pureAppendSuffix
  | extendedWitness
deriving DecidableEq, Repr

/-- Pure function-call inversion contract: the append-suffix lowering itself lives in
the existing `PureTranslatable` HE fragment. This is the lane for structural
families such as the recovered-tail `functionhead` form. -/
structure PureFunctionCallInversionContract
    (prefixElems : List HEAtom) (actual : HEAtom)
    (binders : List (HEAtom × HEAtom)) (tailVar applyArg : HEAtom) : Prop where
  translatedPure :
    PureTranslatable
      (buildAppendSuffixHeadExtension prefixElems actual binders tailVar applyArg)

/-- Package an existing pure append-suffix proof as a function-call-inversion
contract witness. -/
theorem pureFunctionCallInversionContract_of_pureTranslatable
    {prefixElems : List HEAtom} {actual : HEAtom}
    {binders : List (HEAtom × HEAtom)} {tailVar applyArg : HEAtom}
    (hpure :
      PureTranslatable
        (buildAppendSuffixHeadExtension prefixElems actual binders tailVar applyArg)) :
    PureFunctionCallInversionContract prefixElems actual binders tailVar applyArg := by
  exact ⟨hpure⟩

/-!
## Function-Call Inversion Oracle Contract (functionhead.metta)

The `functionhead` pattern requires *symbolic inversion*: given an observed
output and a rule head containing a function call `(f known_args $B)`, the
runtime must enumerate input bindings `$B` such that `f(known_args, $B)`
evaluates to the observed output.

Example rule: `(= (h (myfunc (10) $B) $C) ($B $C))`
Query: `(h (42 10 40) 42000)` — must find `$B = (40)` via inverting `myfunc`.

This is strictly harder than tuple membership: the oracle must evaluate a
user-defined function and solve for its free arguments.
-/

/-- Oracle contract for callable-argument inversion in compat-head position.

Given a function head `funcHead`, the oracle can:
1. Evaluate `(funcHead evaluatedArgs)` to produce witness results.
2. The runtime unifies each witness result with the observed output to recover
   bindings for free arguments (e.g., `$B` in `(myfunc (10) $B)`).

This reuses `ExternalWitnessPhase` — function-call inversion IS a witness phase
where the generator is the user-defined function itself. -/
structure FunctionCallInversionOracleContract
    (oracle : GroundedOracle) (funcHead : String) : Prop where
  /-- The function head is evaluable by the oracle. -/
  evaluable : oracle.isExecutable funcHead

/-- Conformance obligation for a chosen function-call-inversion lane. -/
def functionCallInversionLaneObligation
    (oracle : GroundedOracle) (funcHead : String) :
    FunctionCallInversionLane → Prop
  | .pureAppendSuffix =>
      ∃ prefixElems actual binders tailVar applyArg,
        PureFunctionCallInversionContract prefixElems actual binders tailVar applyArg
  | .extendedWitness =>
      FunctionCallInversionOracleContract oracle funcHead

/-- The pure append-suffix lane is discharged by an explicit pure-translation
contract, independent of any ffi-token phase. -/
theorem functionCallInversionLaneObligation_of_pureAppendSuffix
    {oracle : GroundedOracle} {funcHead : String}
    {prefixElems : List HEAtom} {actual : HEAtom}
    {binders : List (HEAtom × HEAtom)} {tailVar applyArg : HEAtom}
    (h :
      PureFunctionCallInversionContract prefixElems actual binders tailVar applyArg) :
    functionCallInversionLaneObligation oracle funcHead .pureAppendSuffix := by
  exact ⟨prefixElems, actual, binders, tailVar, applyArg, h⟩

/-- The witness lane is exactly the existing oracle-backed function-call inversion
contract. -/
theorem functionCallInversionLaneObligation_of_extendedWitness
    {oracle : GroundedOracle} {funcHead : String}
    (h : FunctionCallInversionOracleContract oracle funcHead) :
    functionCallInversionLaneObligation oracle funcHead .extendedWitness := by
  exact h

/-- Arithmetic inversion is witness-lane only.

This deliberately does **not** promise a unique concrete answer: a certified
oracle may return residual or symbolic witness results, exactly as the current
PeTTa CLP-backed substrate does for non-singleton inverse families. -/
structure ArithmeticInversionWitnessContract
    (oracle : GroundedOracle) (funcHead : String) : Prop where
  functionCallWitness : FunctionCallInversionOracleContract oracle funcHead

/-- Any certified arithmetic-inversion witness contract discharges the generic
function-call-inversion witness lane. -/
theorem functionCallInversionLaneObligation_of_arithmeticWitness
    {oracle : GroundedOracle} {funcHead : String}
    (h : ArithmeticInversionWitnessContract oracle funcHead) :
    functionCallInversionLaneObligation oracle funcHead .extendedWitness := by
  exact h.functionCallWitness

/-- Witness phase for function-call inversion: the oracle evaluates `(funcHead args)`
and the runtime unifies the result with the observed output to recover bindings
for free arguments. -/
theorem functionCallInversion_externalWitnessPhase
    {oracle : GroundedOracle} {space : PeTTaSpace}
    {funcHead : String}
    (horacle : FunctionCallInversionOracleContract oracle funcHead)
    {rawArgs : List PeTTaPattern} {ty : PeTTaPattern}
    {bindings finalBindings : Bindings}
    {evaledArgs witnessResults : List PeTTaPattern}
    (hargs : InterpretArgs space bindings rawArgs evaledArgs finalBindings)
    (hcall : oracle.call funcHead evaledArgs witnessResults) :
    ExternalWitnessPhase oracle space funcHead rawArgs ty
      bindings finalBindings evaledArgs witnessResults := by
  exact ⟨horacle.evaluable, hargs, hcall⟩

/-- Core rule shape for `functionhead.metta`:
`(= (ctor (funcHead knownArg $freeVar) $otherVar) rhs)`.
Models e.g. `(= (h (myfunc (10) $B) $C) ($B $C))`. -/
private def functionheadLikeCoreRule
    (ctor funcHead freeVar otherVar : String)
    (knownArg : PeTTaPattern) (rhs : PeTTaPattern) :
    MeTTailCore.MeTTaIL.Syntax.RewriteRule :=
  { name := s!"{ctor}_functionhead_shape"
    typeContext := []
    premises := []
    left := MeTTailCore.MeTTaIL.Syntax.Pattern.apply ctor
      [ MeTTailCore.MeTTaIL.Syntax.Pattern.apply funcHead
          [specToCorePattern knownArg, .fvar freeVar]
      , .fvar otherVar
      ]
    right := specToCorePattern rhs }

/-- The actual structural compat-head classifier from `Dispatch.lean` recognizes
the `functionhead` rule shape — any rule where a function call appears in an
argument position is a compat-head rule. -/
theorem functionheadLike_ruleShape_hasCompatHeadConstraintRule
    {ctor funcHead freeVar otherVar : String}
    {knownArg : PeTTaPattern} {rhs : PeTTaPattern} :
    Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule
      (rewriteOnlyDispatchInterface
        [functionheadLikeCoreRule ctor funcHead freeVar otherVar knownArg rhs]) () ctor 2 = true := by
  simp [Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule,
    rewriteOnlyDispatchInterface, functionheadLikeCoreRule]
  left
  rfl

/-- Full staged lowering for the function-call-inversion fragment: external witness
production via function-call inversion followed by residual MORK source firing. -/
theorem functionCallInversion_twoPhaseLowering
    {oracle : GroundedOracle} {space : PeTTaSpace} {workspace : Space}
    {funcHead : String}
    (horacle : FunctionCallInversionOracleContract oracle funcHead)
    {rawArgs : List PeTTaPattern} {ty : PeTTaPattern}
    {bindings finalBindings : Bindings}
    {evaledArgs witnessResults : List PeTTaPattern}
    {sourceRule : SourceExecRule} {σ : Subst}
    (hargs : InterpretArgs space bindings rawArgs evaledArgs finalBindings)
    (hcall : oracle.call funcHead evaledArgs witnessResults)
    (hr : ResidualMorkPhase workspace sourceRule σ) :
    CompatHeadTwoPhaseLowering oracle space workspace
      funcHead rawArgs ty
      bindings finalBindings evaledArgs witnessResults
      sourceRule σ := by
  exact ⟨functionCallInversion_externalWitnessPhase horacle hargs hcall, hr⟩

/-!
## Nested Generator Composition Contract (functionhead2.metta)

The `functionhead2` pattern chains generators: `(cat (animal $X))` where
`(animal $X)` is itself a generator-style function producing results via
constraint composition (e.g., `(only ((living $X) (being $X)) $X)`).

The compat-head probe must: (1) evaluate the inner generator `(animal $X)` to
collect witness bindings for `$X`, then (2) use those bindings to constrain the
outer rule's arguments.

Example rules:
```
(= (animal $X) (only ((living $X) (being $X)) $X))
(= (cat (animal $X)) (only (small $X) $X))
```
Query: `(cat $X)` → expects `(cat42 garfield)`.

This is strictly harder than function-call inversion: the inner generator itself
uses constraint composition, requiring recursive witness evaluation.
-/

/-- Oracle contract for nested generator composition in compat-head position.

When a compat-head argument is itself a generator call `(innerHead args)`, the
witness phase must evaluate the inner generator to collect witness bindings,
then use those bindings to constrain the outer rule. -/
structure NestedGeneratorCompositionContract
    (oracle : GroundedOracle) (outerHead innerHead : String) : Prop where
  /-- Both heads are evaluable by the oracle. -/
  outerEvaluable : oracle.isExecutable outerHead
  innerEvaluable : oracle.isExecutable innerHead

/-- Core rule shape for `functionhead2.metta`:
`(= (ctor (innerHead $freeVar)) rhs)`. -/
private def functionhead2LikeCoreRule
    (ctor innerHead freeVar : String) (rhs : PeTTaPattern) :
    MeTTailCore.MeTTaIL.Syntax.RewriteRule :=
  { name := s!"{ctor}_functionhead2_shape"
    typeContext := []
    premises := []
    left := MeTTailCore.MeTTaIL.Syntax.Pattern.apply ctor
      [ MeTTailCore.MeTTaIL.Syntax.Pattern.apply innerHead [.fvar freeVar] ]
    right := specToCorePattern rhs }

/-- The structural compat-head classifier recognizes the `functionhead2` rule
shape — a nested function call in argument position. -/
theorem functionhead2Like_ruleShape_hasCompatHeadConstraintRule
    {ctor innerHead freeVar : String} {rhs : PeTTaPattern} :
    Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule
      (rewriteOnlyDispatchInterface
        [functionhead2LikeCoreRule ctor innerHead freeVar rhs]) () ctor 1 = true := by
  simp [Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule,
    rewriteOnlyDispatchInterface, functionhead2LikeCoreRule]
  rfl

/-- Witness phase for nested generator composition: the oracle evaluates the
inner generator to collect witness bindings. -/
theorem nestedGenerator_externalWitnessPhase
    {oracle : GroundedOracle} {space : PeTTaSpace}
    {outerHead innerHead : String}
    (horacle : NestedGeneratorCompositionContract oracle outerHead innerHead)
    {rawArgs : List PeTTaPattern} {ty : PeTTaPattern}
    {bindings finalBindings : Bindings}
    {evaledArgs witnessResults : List PeTTaPattern}
    (hargs : InterpretArgs space bindings rawArgs evaledArgs finalBindings)
    (hcall : oracle.call innerHead evaledArgs witnessResults) :
    ExternalWitnessPhase oracle space innerHead rawArgs ty
      bindings finalBindings evaledArgs witnessResults := by
  exact ⟨horacle.innerEvaluable, hargs, hcall⟩

/-- Full staged lowering for nested generator composition: inner generator
witness production followed by residual MORK source firing. -/
theorem nestedGenerator_twoPhaseLowering
    {oracle : GroundedOracle} {space : PeTTaSpace} {workspace : Space}
    {outerHead innerHead : String}
    (horacle : NestedGeneratorCompositionContract oracle outerHead innerHead)
    {rawArgs : List PeTTaPattern} {ty : PeTTaPattern}
    {bindings finalBindings : Bindings}
    {evaledArgs witnessResults : List PeTTaPattern}
    {sourceRule : SourceExecRule} {σ : Subst}
    (hargs : InterpretArgs space bindings rawArgs evaledArgs finalBindings)
    (hcall : oracle.call innerHead evaledArgs witnessResults)
    (hr : ResidualMorkPhase workspace sourceRule σ) :
    CompatHeadTwoPhaseLowering oracle space workspace
      innerHead rawArgs ty
      bindings finalBindings evaledArgs witnessResults
      sourceRule σ := by
  exact ⟨nestedGenerator_externalWitnessPhase horacle hargs hcall, hr⟩

section Canaries

#check @ExternalWitnessPhase
#check @ResidualMorkPhase
#check @CompatHeadTwoPhaseLowering
#check @WitnessResidualBindingFlow
#check @externalWitnessPhase_to_meTTaEvalG
#check @compatHeadTwoPhaseLowering_mk
#check @compatHeadTwoPhaseLowering_sound
#check @witnessResidualBindingFlow_sound
#check @TupleMembershipOracleContract
#check @tupleMembership_externalWitnessPhase_of_member
#check @tupleMembership_twoPhaseLowering_of_member
#check @tupleMembership_twoPhaseLowering_sound_of_member
#check @tupleMembership_singleWitness_residual_sound_of_member
#check @mergedSingletonWitnessBindings_preserve
#check @tupleMembership_twoWitness_residual_sound_of_member
#check @Algorithms.MeTTa.Simple.Semantics.Dispatch.compatMatchedBs_projection
#check @Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite_singleton_bridge
#check @functionhead3Like_ruleShape_hasCompatHeadConstraintRule
#check @functionhead3Like_singleton_bridge
#check @DeterministicFunctionhead3CompatContract
#check @functionhead3Like_deterministicCompatContract
#check @functionhead3Like_ruleShape_twoWitnessBoundary_sound_of_member
#check @FunctionCallInversionOracleContract
#check @functionCallInversion_externalWitnessPhase
#check @functionCallInversion_twoPhaseLowering
#check @functionheadLike_ruleShape_hasCompatHeadConstraintRule
#check @NestedGeneratorCompositionContract
#check @nestedGenerator_externalWitnessPhase
#check @nestedGenerator_twoPhaseLowering
#check @functionhead2Like_ruleShape_hasCompatHeadConstraintRule

end Canaries

section AxiomAudit

#print axioms externalWitnessPhase_to_meTTaEvalG
#print axioms compatHeadTwoPhaseLowering_sound
#print axioms witnessResidualBindingFlow_sound
#print axioms tupleMembership_externalWitnessPhase_of_member
#print axioms tupleMembership_twoPhaseLowering_sound_of_member
#print axioms tupleMembership_singleWitness_residual_sound_of_member
#print axioms mergedSingletonWitnessBindings_preserve
#print axioms tupleMembership_twoWitness_residual_sound_of_member
#print axioms functionhead3Like_ruleShape_hasCompatHeadConstraintRule
#print axioms functionhead3Like_ruleShape_twoWitnessBoundary_sound_of_member
#print axioms functionCallInversion_externalWitnessPhase
#print axioms functionCallInversion_twoPhaseLowering
#print axioms functionheadLike_ruleShape_hasCompatHeadConstraintRule
#print axioms nestedGenerator_externalWitnessPhase
#print axioms nestedGenerator_twoPhaseLowering
#print axioms functionhead2Like_ruleShape_hasCompatHeadConstraintRule

end AxiomAudit

end Mettapedia.Conformance.PeTTaCompatHeadBoundary
