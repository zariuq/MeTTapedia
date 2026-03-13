import Algorithms.MeTTa.Simple.Semantics.Dispatch
import Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary
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

abbrev PeTTaPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

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
  simpa [hinst] using applySubst_commutes witnessBindings residualBody htrans

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
  | .lambda body => .lambda (specToCorePattern body)
  | .multiLambda n body => .multiLambda n (specToCorePattern body)
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

/-- Operational singleton compat-head seam for the minimal rewrite-only
`functionhead3` interface: the plain compat-head outputs are exactly the
projection of the binding-carrying outputs.

This is the concrete theorem Rust should mirror for the single-rule compat-head
case once the external witness phase has already produced the generator-side
bindings. -/
theorem functionhead3Like_singleton_projection
    {ctor varX varY : String} {xs ys rhs : PeTTaPattern}
    {tArg0 tArg1 : MeTTailCore.MeTTaIL.Syntax.Pattern} :
    let rule := functionhead3LikeCoreRule ctor varX varY xs ys rhs
    let I := rewriteOnlyDispatchInterface [rule]
    let term := MeTTailCore.MeTTaIL.Syntax.Pattern.apply ctor [tArg0, tArg1]
    let valsState :=
      Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite I () term
    let pairState :=
      Algorithms.MeTTa.Simple.Semantics.Dispatch.constrainedCallBindingsAndValues I () term
    valsState.1 = pairState.1 ∧ valsState.2 = pairState.2.map Prod.snd := by
  dsimp
  let rule := functionhead3LikeCoreRule ctor varX varY xs ys rhs
  let I := rewriteOnlyDispatchInterface [rule]
  let pArgs :=
    match
        MeTTailCore.MeTTaIL.Syntax.renameFVarsWith
          (Algorithms.MeTTa.Simple.Semantics.Dispatch.scopedRuleTag rule.name [tArg0, tArg1])
          rule.left with
    | .apply _ pArgs => pArgs
    | _ => []
  have hEvalEq :
      ∀ (s : Unit) (rhs0 : MeTTailCore.MeTTaIL.Syntax.Pattern),
        I.evalForRuleEnumeration s rhs0 = I.eval s rhs0 := by
    intro _ _
    rfl
  have hRules :
      I.premiseFreeRulesForHeadArity () ctor [tArg0, tArg1].length = [rule] := by
    simp [I, rewriteOnlyDispatchInterface, rule, functionhead3LikeCoreRule]
  have hLeft :
      MeTTailCore.MeTTaIL.Syntax.renameFVarsWith
          (Algorithms.MeTTa.Simple.Semantics.Dispatch.scopedRuleTag rule.name [tArg0, tArg1])
          rule.left =
        .apply ctor pArgs := by
    simp [pArgs, rule, functionhead3LikeCoreRule]
  have hLen : pArgs.length == [tArg0, tArg1].length := by
    simp [pArgs, rule, functionhead3LikeCoreRule]
  have hCompat :
      pArgs.any Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintArg = true := by
    simp [pArgs, rule, functionhead3LikeCoreRule]
  simpa [I, rule] using
    Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite_eq_constrained_projection_singleton
      I hEvalEq () ctor [tArg0, tArg1] rule pArgs hRules hLeft hLen hCompat

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
#check @functionhead3Like_ruleShape_hasCompatHeadConstraintRule
#check @functionhead3Like_ruleShape_twoWitnessBoundary_sound_of_member

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

end AxiomAudit

end Mettapedia.Conformance.PeTTaCompatHeadBoundary
