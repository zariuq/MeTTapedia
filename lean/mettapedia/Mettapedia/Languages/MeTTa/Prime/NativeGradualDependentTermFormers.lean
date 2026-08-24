import Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability
import Mettapedia.Languages.MeTTa.PureKernel.Universe.SyntacticJudgmentalSigmaId
import Mettapedia.Languages.MeTTa.PureKernel.Universe.TypingGeneration

/-!
# Constructional gradual lifting of native dependent term formers

Prime does not place a checker between already typed native constructors.
The raw term remains available, while exact evidence for a constructor is
built directly from exact evidence for its premises.  This file connects the
generic gradual capability layer to the actual declaration-aware Pi, Sigma,
and identity judgments of the cumulative syntactic natural model.

Independent premises use products of displayed capabilities.  A dependent
Sigma premise uses their dependent sum: the expected type of the second term
is indexed by the first raw term.  Thus graduality does not flatten dependent
typing into flags, and native construction does not replay typing derivations
inside an execution loop.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentTermFormers

open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticContextual
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalPi
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalSigmaId

/-! ## Raw judgments and fixed expected types -/

/-- A raw candidate judgment retains its term and proposed type code.  The
type code is intentionally not required to be formed: unsupported raw syntax
remains representable, while the displayed exact fibre names the authoritative
typing judgment. -/
structure RawJudgment {rules : Rules Head}
    (context : FormedContext rules) where
  term : Tm Head context.arity
  type : Tm Head context.arity

@[ext] theorem RawJudgment.ext {rules : Rules Head}
    {context : FormedContext rules} {left right : RawJudgment context}
    (termEquality : left.term = right.term)
    (typeEquality : left.type = right.type) : left = right := by
  cases left
  cases right
  cases termEquality
  cases typeEquality
  rfl

/-- The declaration-aware typing judgment displayed over raw candidates. -/
def judgmentFibre {rules : Rules Head}
    (context : FormedContext rules) : Fibre where
  Raw := RawJudgment context
  Exact := fun candidate =>
    PLift (HasType rules context.context candidate.term candidate.type)

/-- Raw terms at one expected type code, with exact typing as the optional
native capability. -/
def termAtCodeFibre {rules : Rules Head}
    (context : FormedContext rules) (expected : Tm Head context.arity) :
    Fibre where
  Raw := Tm Head context.arity
  Exact := fun term => PLift (HasType rules context.context term expected)

/-- The fixed-type specialization used by intrinsic formed types. -/
def termFibre {rules : Rules Head} {context : FormedContext rules}
    (expected : TypeOver context) : Fibre :=
  termAtCodeFibre context expected.code

/-- Forget the fixed formed type into the general raw-judgment carrier. -/
def includeTermMap {rules : Rules Head} {context : FormedContext rules}
    (expected : TypeOver context) :
    ExactMap (termFibre expected) (judgmentFibre context) where
  mapRaw := fun term => ⟨term, expected.code⟩
  mapExact := fun evidence => evidence

/-! ## Native Pi construction -/

/-- Lambda introduction constructs the result judgment from its body
judgment, with no interior checker. -/
def lambdaMap {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (product : DependentProduct domain codomain) :
    ExactMap (termFibre codomain) (termFibre product.type) where
  mapRaw := Tm.lam
  mapExact := fun evidence => ⟨HasType.lamIntro evidence.down⟩

/-- Application consumes independent exact function and argument evidence,
then constructs the dependent result judgment. -/
def applicationMap {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (product : DependentProduct domain codomain) :
    ExactMap
      (Fibre.product (termFibre product.type) (termFibre domain))
      (judgmentFibre context) where
  mapRaw := fun input =>
    ⟨.app input.1 input.2, inst0 input.2 codomain.code⟩
  mapExact := fun evidence =>
    ⟨HasType.appElim evidence.1.down evidence.2.down⟩

/-- Gradual application is the common product-combination law followed by
the native application map. -/
def applicationState {rules : Rules Head}
    {context : FormedContext rules} {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (product : DependentProduct domain codomain)
    {functionRaw : Tm Head context.arity}
    {argumentRaw : Tm Head context.arity} :
    State (termFibre product.type) functionRaw ->
      State (termFibre domain) argumentRaw ->
      State (judgmentFibre context)
        ((applicationMap product).mapRaw (functionRaw, argumentRaw))
  | functionState, argumentState =>
      mapSafe (applicationMap product)
        (State.combine functionState argumentState)

theorem applicationState_mono {rules : Rules Head}
    {context : FormedContext rules} {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (product : DependentProduct domain codomain)
    {functionRaw argumentRaw : Tm Head context.arity}
    {functionRefined functionCoarse :
      State (termFibre product.type) functionRaw}
    {argumentRefined argumentCoarse :
      State (termFibre domain) argumentRaw}
    (functionPrecision : Refines functionRefined functionCoarse)
    (argumentPrecision : Refines argumentRefined argumentCoarse) :
    Refines
      (applicationState product functionRefined argumentRefined)
      (applicationState product functionCoarse argumentCoarse) :=
  Refines.mapSafe (State.combine_mono functionPrecision argumentPrecision)

/-! ## Native Sigma construction -/

/-- Pair premises form a genuinely dependent capability: the second term is
checked in the codomain instantiated by the first raw term. -/
def pairInputFibre {rules : Rules Head}
    {context : FormedContext rules} {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (_sum : DependentSum domain codomain) : Fibre :=
  Fibre.sigma (termFibre domain) (fun first =>
    termAtCodeFibre context (inst0 first codomain.code))

/-- Dependent pair introduction constructs the native Sigma term directly. -/
def pairMap {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain) :
    ExactMap (pairInputFibre sum) (termFibre sum.type) where
  mapRaw := fun input => .pair input.1 input.2
  mapExact := fun evidence =>
    ⟨HasType.pairIntro evidence.1.down evidence.2.down⟩

/-- Gradual dependent pairing combines premises in their true indexed fibre
before applying the native constructor. -/
def pairState {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain)
    {firstRaw secondRaw : Tm Head context.arity} :
    State (termFibre domain) firstRaw ->
      State (termAtCodeFibre context (inst0 firstRaw codomain.code))
        secondRaw ->
      State (termFibre sum.type) (.pair firstRaw secondRaw)
  | firstState, secondState =>
      mapSafe (pairMap sum)
        (State.combineDependent firstState secondState)

theorem pairState_mono {rules : Rules Head}
    {context : FormedContext rules} {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain)
    {firstRaw secondRaw : Tm Head context.arity}
    {firstRefined firstCoarse : State (termFibre domain) firstRaw}
    {secondRefined secondCoarse :
      State (termAtCodeFibre context (inst0 firstRaw codomain.code))
        secondRaw}
    (firstPrecision : Refines firstRefined firstCoarse)
    (secondPrecision : Refines secondRefined secondCoarse) :
    Refines (pairState sum firstRefined secondRefined)
      (pairState sum firstCoarse secondCoarse) :=
  Refines.mapSafe
    (State.combineDependent_mono firstPrecision secondPrecision)

/-! ## Native identity construction -/

/-- Identity formation uses exact evidence for both endpoints and retains the
carrier's universe level as the proposed result type. -/
def identityTypeMap {rules : Rules Head}
    {context : FormedContext rules} (carrier : TypeOver context) :
    ExactMap
      (Fibre.product (termFibre carrier) (termFibre carrier))
      (judgmentFibre context) where
  mapRaw := fun endpoints =>
    ⟨.id carrier.code endpoints.1 endpoints.2, .head carrier.level⟩
  mapExact := fun evidence =>
    ⟨HasType.idForm carrier.formed carrier.isUniverse
      evidence.1.down evidence.2.down⟩

/-- Reflexivity maps a typed term to the diagonal identity judgment. -/
def reflexivityMap {rules : Rules Head}
    {context : FormedContext rules} (carrier : TypeOver context) :
    ExactMap (termFibre carrier) (judgmentFibre context) where
  mapRaw := fun term => ⟨.refl term, .id carrier.code term term⟩
  mapExact := fun evidence => ⟨HasType.reflIntro evidence.down⟩

/-! ## Nondegenerate Tower controls -/

namespace Canary

open SyntacticContextual.TowerExamples

abbrev identityCodomain :=
  SyntacticJudgmentalPi.TowerExamples.identityCodomain
abbrev identityBody := SyntacticJudgmentalPi.TowerExamples.identityBody
abbrev identityProduct :=
  SyntacticJudgmentalPi.TowerExamples.identityProduct
abbrev identityFunction :=
  SyntacticJudgmentalPi.TowerExamples.identityFunction
abbrev identityApplication :=
  SyntacticJudgmentalPi.TowerExamples.identityApplication

abbrev dependentSum :=
  SyntacticJudgmentalSigmaId.TowerExamples.dependentSum
abbrev groundAtUniverseZero :=
  SyntacticJudgmentalSigmaId.TowerExamples.groundAtUniverseZero
abbrev dependentPair :=
  SyntacticJudgmentalSigmaId.TowerExamples.dependentPair
abbrev diagonalUniverseIdentity :=
  SyntacticJudgmentalSigmaId.TowerExamples.diagonalUniverseIdentity
abbrev mixedUniverseIdentity :=
  SyntacticJudgmentalSigmaId.TowerExamples.mixedUniverseIdentity

def identityBodyState :
    State (termFibre identityCodomain) identityBody.code :=
  .exact ⟨identityBody.typed⟩

/-- Positive Pi control: direct gradual lifting constructs the same lambda
syntax as the intrinsic native product. -/
@[simp] theorem lambda_constructs_identity_code :
    (lambdaMap identityProduct).mapRaw identityBody.code =
      identityFunction.code :=
  rfl

def identityLambdaTyping :
    (termFibre identityProduct.type).Exact identityFunction.code :=
  (lambdaMap identityProduct).mapExact ⟨identityBody.typed⟩

def identityApplicationEvidence :
    (Fibre.product
      (termFibre identityProduct.type)
      (termFibre universeOne)).Exact
      (identityFunction.code, universeZero.code) :=
  (⟨identityFunction.typed⟩, ⟨universeZero.typed⟩)

/-- Positive application control: both the term and its dependent result type
are exactly the intrinsic native application. -/
theorem application_constructs_identity_judgment :
    (applicationMap identityProduct).mapRaw
        (identityFunction.code, universeZero.code) =
      { term := identityApplication.code
        type := (instantiateType identityCodomain universeZero).code } :=
  rfl

def identityApplicationTyping :
    (judgmentFibre empty).Exact
      ((applicationMap identityProduct).mapRaw
        (identityFunction.code, universeZero.code)) :=
  (applicationMap identityProduct).mapExact
    identityApplicationEvidence

def dependentPairInput : (pairInputFibre dependentSum).Raw :=
  ⟨universeZero.code, groundAtUniverseZero.code⟩

def dependentPairEvidence :
    (pairInputFibre dependentSum).Exact dependentPairInput :=
  (⟨universeZero.typed⟩, ⟨groundAtUniverseZero.typed⟩)

/-- Positive Sigma control: the dependent capability constructs the same
nontrivial native pair. -/
@[simp] theorem pair_constructs_dependent_pair_code :
    (pairMap dependentSum).mapRaw dependentPairInput = dependentPair.code :=
  rfl

def dependentPairTyping :
    (termFibre dependentSum.type).Exact dependentPair.code :=
  (pairMap dependentSum).mapExact dependentPairEvidence

def universeZeroReflexivityTyping :
    (judgmentFibre empty).Exact
      ((reflexivityMap universeOne).mapRaw universeZero.code) :=
  (reflexivityMap universeOne).mapExact ⟨universeZero.typed⟩

def mixedIdentityEvidence :
    (Fibre.product (termFibre universeOne) (termFibre universeOne)).Exact
      (universeZero.code, legacyGround.code) :=
  (⟨universeZero.typed⟩, ⟨legacyGround.typed⟩)

def mixedIdentityTyping :
    (judgmentFibre empty).Exact
      ((identityTypeMap universeOne).mapRaw
        (universeZero.code, legacyGround.code)) :=
  (identityTypeMap universeOne).mapExact mixedIdentityEvidence

def missingBodyName : DeclName := `prime.gradual.missingBody

def missingBody : Tm Tower.Head (empty.arity + 1) :=
  .const missingBodyName

/-- The negative source is not merely unknown: the declaration inventory
proves that the body constant is absent at every proposed type. -/
theorem missingBody_has_no_exact :
    IsEmpty
      ((termFibre identityCodomain).Exact missingBody) := by
  constructor
  intro evidence
  exact HasType.constantImpossibleWhenMissing (rules := Tower.rules)
    (context := (extendContext empty universeOne).context)
    (displayedType := identityCodomain.code)
    (name := missingBodyName) rfl evidence.down

def missingBodyBlame :
    Refutation (termFibre identityCodomain) missingBody where
  path := [0]
  refutes := fun evidence => missingBody_has_no_exact.false evidence

/-- Negative Pi control: a refuted raw body cannot manufacture a typed
lambda.  Its raw lambda remains representable and the output capability is
suspended. -/
theorem refuted_lambda_does_not_become_exact :
    mapSafe (lambdaMap identityProduct)
        (.refuted missingBodyBlame) =
      (.suspended : State (termFibre identityProduct.type)
        (.lam missingBody)) :=
  rfl

/-- Negative identity control inherited from the native kernel: diagonal
reflexivity cannot inhabit the mixed-endpoint identity fibre. -/
theorem reflexivity_does_not_collapse_endpoints :
    diagonalUniverseIdentity ≠ mixedUniverseIdentity :=
  SyntacticJudgmentalSigmaId.TowerExamples.diagonalIdentity_ne_mixedIdentity

end Canary

#print axioms applicationState_mono
#print axioms pairState_mono
#print axioms Canary.identityLambdaTyping
#print axioms Canary.identityApplicationTyping
#print axioms Canary.dependentPairTyping
#print axioms Canary.mixedIdentityTyping
#print axioms Canary.missingBody_has_no_exact
#print axioms Canary.refuted_lambda_does_not_become_exact
#print axioms Canary.reflexivity_does_not_collapse_endpoints

end Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentTermFormers
