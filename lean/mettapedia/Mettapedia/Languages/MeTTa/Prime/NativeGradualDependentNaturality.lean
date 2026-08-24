import Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentTermFormers
import Mettapedia.Languages.MeTTa.PureKernel.Universe.SyntacticJudgmentalIdentityEliminator

/-!
# Naturality of constructional gradual dependent typing

The intrinsic Prime kernel already proves that Pi, Sigma, and identity
formation, introduction, and elimination commute with every typed context
substitution.  This module lifts those laws to the displayed gradual layer.

Each square has two parts:

* raw syntax commutes with substitution;
* transported exact evidence is heterogeneously equal along that raw square.

Consequently safe gradual transport commutes for suspended, exact, and
refuted inputs.  Stable blame is intentionally invalidated on both paths
unless a separate reflection theorem is supplied.  Naturality therefore
preserves raw execution without turning an old negative decision into a new
one in a reindexed dependent fibre.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentNaturality

open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State
open Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentTermFormers
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticContextual
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalPi
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalSigmaId
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.ProofRelevantStructuralComputation

private theorem pliftProp_subsingleton (proposition : Prop) :
    Subsingleton (PLift proposition) where
  allEq left right := by
    cases left
    cases right
    congr

private theorem exact_heq_of_index_eq
    (fibre : Fibre) (thin : ∀ raw, Subsingleton (fibre.Exact raw))
    {leftRaw rightRaw : fibre.Raw} (rawEquality : leftRaw = rightRaw)
    (left : fibre.Exact leftRaw) (right : fibre.Exact rightRaw) :
    HEq left right := by
  subst rightRaw
  exact heq_of_eq ((thin _).elim left right)

/-! ## Reindexing maps for displayed typing fibres -/

/-- Typed context substitution as a constructional map on raw candidate
judgments. -/
def reindexJudgmentMap {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target) :
    ExactMap (judgmentFibre target) (judgmentFibre source) where
  mapRaw := fun candidate =>
    { term := subst morphism.substitution candidate.term
      type := subst morphism.substitution candidate.type }
  mapExact := fun evidence => ⟨evidence.down.substitute morphism.typed⟩

/-- Reindex a raw term at an arbitrary expected type code. -/
def reindexTermAtCodeMap {rules : Rules Head}
    {source target : FormedContext rules}
    (expected : Tm Head target.arity) (morphism : source ⟶ target) :
    ExactMap (termAtCodeFibre target expected)
      (termAtCodeFibre source (subst morphism.substitution expected)) where
  mapRaw := subst morphism.substitution
  mapExact := fun evidence => ⟨evidence.down.substitute morphism.typed⟩

/-- Reindex a term at an intrinsically formed type. -/
def reindexTermMap {rules : Rules Head}
    {source target : FormedContext rules} (expected : TypeOver target)
    (morphism : source ⟶ target) :
    ExactMap (termFibre expected) (termFibre (expected.reindex morphism)) :=
  reindexTermAtCodeMap expected.code morphism

/-- Change only the retained formed-type record along a proved equality. -/
def castTermMap {rules : Rules Head} {context : FormedContext rules}
    {source target : TypeOver context} (equalTypes : source = target) :
    ExactMap (termFibre source) (termFibre target) := by
  cases equalTypes
  exact ExactMap.id _

@[simp] theorem castTermMap_mapRaw {rules : Rules Head}
    {context : FormedContext rules} {source target : TypeOver context}
    (equalTypes : source = target) (term : Tm Head context.arity) :
    (castTermMap equalTypes).mapRaw term = term := by
  cases equalTypes
  rfl

/-- Pointwise product of two constructional maps. -/
def productMap {first second firstTarget secondTarget : Fibre}
    (left : ExactMap first firstTarget)
    (right : ExactMap second secondTarget) :
    ExactMap (Fibre.product first second)
      (Fibre.product firstTarget secondTarget) where
  mapRaw := fun input => (left.mapRaw input.1, right.mapRaw input.2)
  mapExact := fun evidence =>
    (left.mapExact evidence.1, right.mapExact evidence.2)

/-! ## Pi naturality -/

def reindexProductTermMap {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) :
    ExactMap (termFibre product.type)
      (termFibre (product.reindex morphism).type) :=
  (castTermMap (product.type_reindex morphism)).comp
    (reindexTermMap product.type morphism)

@[simp] theorem reindexProductTermMap_mapRaw {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) (term : Tm Head target.arity) :
    (reindexProductTermMap product morphism).mapRaw term =
      subst morphism.substitution term := by
  simp [reindexProductTermMap, ExactMap.comp, reindexTermMap,
    reindexTermAtCodeMap]

theorem lambda_raw_natural {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) (body : Tm Head (target.arity + 1)) :
    (reindexProductTermMap product morphism).mapRaw
        ((lambdaMap product).mapRaw body) =
      (lambdaMap (product.reindex morphism)).mapRaw
        ((reindexTermMap codomain
          (liftContextHom morphism domain)).mapRaw body) := by
  simp [reindexTermMap, reindexTermAtCodeMap, lambdaMap,
    liftContextHom_substitution, subst]
  rfl

/-- Lambda introduction is a natural constructional capability map. -/
def lambdaNaturalitySquare {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) :
    ExactMap.Square (lambdaMap product)
      (reindexTermMap codomain (liftContextHom morphism domain))
      (reindexProductTermMap product morphism)
      (lambdaMap (product.reindex morphism)) where
  raw_commutes := lambda_raw_natural product morphism
  exact_commutes := fun {raw} _evidence =>
    exact_heq_of_index_eq (termFibre (product.reindex morphism).type)
      (fun _ => pliftProp_subsingleton _)
      (lambda_raw_natural product morphism raw) _ _

def reindexApplicationInputMap {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) :
    ExactMap
      (Fibre.product (termFibre product.type) (termFibre domain))
      (Fibre.product (termFibre (product.reindex morphism).type)
        (termFibre (domain.reindex morphism))) :=
  productMap (reindexProductTermMap product morphism)
    (reindexTermMap domain morphism)

theorem application_raw_natural {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target)
    (input : Tm Head target.arity × Tm Head target.arity) :
    (reindexJudgmentMap morphism).mapRaw
        ((applicationMap product).mapRaw input) =
      (applicationMap (product.reindex morphism)).mapRaw
        ((reindexApplicationInputMap product morphism).mapRaw input) := by
  cases input with
  | mk function argument =>
      apply RawJudgment.ext <;>
        simp [reindexJudgmentMap, applicationMap,
          reindexApplicationInputMap, productMap, reindexTermMap,
          reindexTermAtCodeMap, TypeOver.reindex,
          liftContextHom_substitution, subst, subst_inst0]
      all_goals rfl

/-- Dependent application satisfies the Beck--Chevalley square at the
displayed gradual level. -/
def applicationNaturalitySquare {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) :
    ExactMap.Square (applicationMap product)
      (reindexApplicationInputMap product morphism)
      (reindexJudgmentMap morphism)
      (applicationMap (product.reindex morphism)) where
  raw_commutes := application_raw_natural product morphism
  exact_commutes := fun {raw} _evidence =>
    exact_heq_of_index_eq (judgmentFibre source)
      (fun _ => pliftProp_subsingleton _)
      (application_raw_natural product morphism raw) _ _

/-! ## Sigma naturality and eliminators -/

def reindexSumTermMap {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target) :
    ExactMap (termFibre sum.type)
      (termFibre (sum.reindex morphism).type) :=
  (castTermMap (sum.type_reindex morphism)).comp
    (reindexTermMap sum.type morphism)

/-- Reindex both components of a genuinely dependent pair input. -/
def reindexPairInputMap {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target) :
    ExactMap (pairInputFibre sum) (pairInputFibre (sum.reindex morphism)) where
  mapRaw := fun input =>
    ⟨subst morphism.substitution input.1,
      subst morphism.substitution input.2⟩
  mapExact := fun {raw} evidence => by
    refine (⟨evidence.1.down.substitute morphism.typed⟩, ⟨?_⟩)
    let first : Term target domain :=
      { code := raw.1
        typed := evidence.1.down }
    let second : Term target (instantiateType codomain first) :=
      { code := raw.2
        typed := evidence.2.down }
    change HasType rules source.context
      (subst morphism.substitution raw.2)
      (instantiateType
        (codomain.reindex (liftContextHom morphism domain))
        (first.reindex morphism)).code
    have codeEquality :
        (Term.cast (instantiateType_reindex codomain first morphism)
          (second.reindex morphism)).code =
            subst morphism.substitution raw.2 := by
      show
        (Term.cast (instantiateType_reindex codomain first morphism)
          (second.reindex morphism)).code = _
      rw [Term.cast_code]
      rfl
    rw [← codeEquality]
    exact (Term.cast (instantiateType_reindex codomain first morphism)
      (second.reindex morphism)).typed

@[simp] theorem reindexSumTermMap_mapRaw {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target)
    (term : Tm Head target.arity) :
    (reindexSumTermMap sum morphism).mapRaw term =
      subst morphism.substitution term := by
  simp [reindexSumTermMap, ExactMap.comp, reindexTermMap,
    reindexTermAtCodeMap]

theorem pair_raw_natural {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target)
    (input : (pairInputFibre sum).Raw) :
    (reindexSumTermMap sum morphism).mapRaw ((pairMap sum).mapRaw input) =
      (pairMap (sum.reindex morphism)).mapRaw
        ((reindexPairInputMap sum morphism).mapRaw input) := by
  cases input with
  | mk first second =>
      simp [pairMap, reindexPairInputMap, subst]

/-- Dependent pair introduction is natural in its ambient formed context. -/
def pairNaturalitySquare {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target) :
    ExactMap.Square (pairMap sum) (reindexPairInputMap sum morphism)
      (reindexSumTermMap sum morphism) (pairMap (sum.reindex morphism)) where
  raw_commutes := pair_raw_natural sum morphism
  exact_commutes := fun {raw} _evidence =>
    exact_heq_of_index_eq (termFibre (sum.reindex morphism).type)
      (fun _ => pliftProp_subsingleton _)
      (pair_raw_natural sum morphism raw) _ _

/-- First projection is a native eliminator map, not a boundary check. -/
def firstProjectionMap {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain) :
    ExactMap (termFibre sum.type) (termFibre domain) where
  mapRaw := Tm.fst
  mapExact := fun evidence => ⟨HasType.fstElim evidence.down⟩

/-- Second projection returns a dependent raw judgment whose proposed type
mentions the first projection of the same pair. -/
def secondProjectionMap {rules : Rules Head}
    {context : FormedContext rules} {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain) :
    ExactMap (termFibre sum.type) (judgmentFibre context) where
  mapRaw := fun pair =>
    { term := .snd pair
      type := inst0 (.fst pair) codomain.code }
  mapExact := fun evidence => ⟨HasType.sndElim evidence.down⟩

theorem firstProjection_raw_natural {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target)
    (pair : Tm Head target.arity) :
    (reindexTermMap domain morphism).mapRaw
        ((firstProjectionMap sum).mapRaw pair) =
      (firstProjectionMap (sum.reindex morphism)).mapRaw
        ((reindexSumTermMap sum morphism).mapRaw pair) := by
  simp [reindexTermMap, reindexTermAtCodeMap, firstProjectionMap, subst]

def firstProjectionNaturalitySquare {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target) :
    ExactMap.Square (firstProjectionMap sum)
      (reindexSumTermMap sum morphism) (reindexTermMap domain morphism)
      (firstProjectionMap (sum.reindex morphism)) where
  raw_commutes := firstProjection_raw_natural sum morphism
  exact_commutes := fun {raw} _evidence =>
    exact_heq_of_index_eq (termFibre (domain.reindex morphism))
      (fun _ => pliftProp_subsingleton _)
      (firstProjection_raw_natural sum morphism raw) _ _

theorem secondProjection_raw_natural {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target)
    (pair : Tm Head target.arity) :
    (reindexJudgmentMap morphism).mapRaw
        ((secondProjectionMap sum).mapRaw pair) =
      (secondProjectionMap (sum.reindex morphism)).mapRaw
        ((reindexSumTermMap sum morphism).mapRaw pair) := by
  apply RawJudgment.ext <;>
    simp [reindexJudgmentMap, secondProjectionMap, TypeOver.reindex,
      liftContextHom_substitution, subst, subst_inst0]
  all_goals rfl

def secondProjectionNaturalitySquare {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target) :
    ExactMap.Square (secondProjectionMap sum)
      (reindexSumTermMap sum morphism) (reindexJudgmentMap morphism)
      (secondProjectionMap (sum.reindex morphism)) where
  raw_commutes := secondProjection_raw_natural sum morphism
  exact_commutes := fun {raw} _evidence =>
    exact_heq_of_index_eq (judgmentFibre source)
      (fun _ => pliftProp_subsingleton _)
      (secondProjection_raw_natural sum morphism raw) _ _

/-! ## Identity naturality -/

theorem identityType_raw_natural {rules : Rules Head}
    {source target : FormedContext rules} (carrier : TypeOver target)
    (morphism : source ⟶ target)
    (endpoints : Tm Head target.arity × Tm Head target.arity) :
    (reindexJudgmentMap morphism).mapRaw
        ((identityTypeMap carrier).mapRaw endpoints) =
      (identityTypeMap (carrier.reindex morphism)).mapRaw
        ((productMap (reindexTermMap carrier morphism)
          (reindexTermMap carrier morphism)).mapRaw endpoints) := by
  cases endpoints
  rfl

def identityTypeNaturalitySquare {rules : Rules Head}
    {source target : FormedContext rules} (carrier : TypeOver target)
    (morphism : source ⟶ target) :
    ExactMap.Square (identityTypeMap carrier)
      (productMap (reindexTermMap carrier morphism)
        (reindexTermMap carrier morphism))
      (reindexJudgmentMap morphism)
      (identityTypeMap (carrier.reindex morphism)) where
  raw_commutes := identityType_raw_natural carrier morphism
  exact_commutes := fun {raw} _evidence =>
    exact_heq_of_index_eq (judgmentFibre source)
      (fun _ => pliftProp_subsingleton _)
      (identityType_raw_natural carrier morphism raw) _ _

theorem reflexivity_raw_natural {rules : Rules Head}
    {source target : FormedContext rules} (carrier : TypeOver target)
    (morphism : source ⟶ target) (term : Tm Head target.arity) :
    (reindexJudgmentMap morphism).mapRaw
        ((reflexivityMap carrier).mapRaw term) =
      (reflexivityMap (carrier.reindex morphism)).mapRaw
        ((reindexTermMap carrier morphism).mapRaw term) :=
  rfl

def reflexivityNaturalitySquare {rules : Rules Head}
    {source target : FormedContext rules} (carrier : TypeOver target)
    (morphism : source ⟶ target) :
    ExactMap.Square (reflexivityMap carrier)
      (reindexTermMap carrier morphism) (reindexJudgmentMap morphism)
      (reflexivityMap (carrier.reindex morphism)) where
  raw_commutes := reflexivity_raw_natural carrier morphism
  exact_commutes := fun {raw} _evidence =>
    exact_heq_of_index_eq (judgmentFibre source)
      (fun _ => pliftProp_subsingleton _)
      (reflexivity_raw_natural carrier morphism raw) _ _

/-! ## Proof-relevant computation receipts -/

/-- A proposed homogeneous judgmental step.  Raw syntax names the common
type and both endpoints; exactness supplies both typings and the retained
structural rule that connects them. -/
structure RawHomogeneousStep {rules : Rules Head}
    (context : FormedContext rules) where
  type : Tm Head context.arity
  source : Tm Head context.arity
  target : Tm Head context.arity

@[ext] theorem RawHomogeneousStep.ext {rules : Rules Head}
    {context : FormedContext rules}
    {left right : RawHomogeneousStep context}
    (typeEquality : left.type = right.type)
    (sourceEquality : left.source = right.source)
    (targetEquality : left.target = right.target) : left = right := by
  cases left
  cases right
  cases typeEquality
  cases sourceEquality
  cases targetEquality
  rfl

/-- Displayed exact evidence for a typed, proof-relevant homogeneous step. -/
structure HomogeneousStepEvidence {rules : Rules Head}
    (retained : RetainedRoot rules) (context : FormedContext rules)
    (candidate : RawHomogeneousStep context) where
  sourceTyping : HasType rules context.context candidate.source candidate.type
  targetTyping : HasType rules context.context candidate.target candidate.type
  receipt : StructuralStepReceipt retained.computation rules.headEq
    candidate.source candidate.target

private theorem homogeneousStepEvidence_heq {rules : Rules Head}
    {retained : RetainedRoot rules} {context : FormedContext rules}
    {leftCandidate rightCandidate : RawHomogeneousStep context}
    (candidateEquality : leftCandidate = rightCandidate)
    (left : HomogeneousStepEvidence retained context leftCandidate)
    (right : HomogeneousStepEvidence retained context rightCandidate)
    (receiptEquality : HEq left.receipt right.receipt) : HEq left right := by
  subst rightCandidate
  have equalReceipt : left.receipt = right.receipt := eq_of_heq receiptEquality
  cases left
  cases right
  cases equalReceipt
  rfl

def homogeneousStepFibre {rules : Rules Head}
    (retained : RetainedRoot rules) (context : FormedContext rules) : Fibre where
  Raw := RawHomogeneousStep context
  Exact := HomogeneousStepEvidence retained context

/-- Reindex a typed homogeneous step, retaining its complete structural
receipt rather than reconstructing a conversion from its endpoints. -/
def reindexHomogeneousStepMap {rules : Rules Head}
    (retained : RetainedRoot rules) {source target : FormedContext rules}
    (morphism : source ⟶ target) :
    ExactMap (homogeneousStepFibre retained target)
      (homogeneousStepFibre retained source) where
  mapRaw := fun candidate =>
    { type := subst morphism.substitution candidate.type
      source := subst morphism.substitution candidate.source
      target := subst morphism.substitution candidate.target }
  mapExact := fun evidence =>
    { sourceTyping := evidence.sourceTyping.substitute morphism.typed
      targetTyping := evidence.targetTyping.substitute morphism.typed
      receipt := evidence.receipt.substitute morphism.substitution }

/-- Pi beta becomes a constructional capability: exact body and argument
evidence directly construct both endpoint typings and the retained beta
receipt. -/
def piBetaMap {rules : Rules Head} {context : FormedContext rules}
    (retained : RetainedRoot rules) {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (product : DependentProduct domain codomain) :
    ExactMap (Fibre.product (termFibre codomain) (termFibre domain))
      (homogeneousStepFibre retained context) where
  mapRaw := fun input =>
    { type := inst0 input.2 codomain.code
      source := .app (.lam input.1) input.2
      target := inst0 input.2 input.1 }
  mapExact := fun {raw} evidence => by
    let body : Term (extendContext context domain) codomain :=
      { code := raw.1
        typed := evidence.1.down }
    let argument : Term context domain :=
      { code := raw.2
        typed := evidence.2.down }
    exact
      { sourceTyping :=
          (product.application (product.lambda body) argument).typed
        targetTyping := (instantiateTerm body argument).typed
        receipt := product.betaReceipt retained body argument }

def reindexPiBetaInputMap {rules : Rules Head}
    {source target : FormedContext rules} {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (morphism : source ⟶ target) :
    ExactMap (Fibre.product (termFibre codomain) (termFibre domain))
      (Fibre.product
        (termFibre (codomain.reindex (liftContextHom morphism domain)))
        (termFibre (domain.reindex morphism))) :=
  productMap
    (reindexTermMap codomain (liftContextHom morphism domain))
    (reindexTermMap domain morphism)

/-- Direct beta receipts are strictly stable under substitution.  This is
stronger than endpoint preservation: the transported receipt is the same
proof-relevant beta constructor with the substituted body and argument. -/
theorem piBetaReceipt_reindex {rules : Rules Head}
    (retained : RetainedRoot rules) {source target : FormedContext rules}
    (domain : TypeOver target)
    (morphism : source ⟶ target)
    (body : Tm Head (target.arity + 1))
    (argument : Tm Head target.arity) :
    HEq
      ((StructuralStepReceipt.betaPi
          (computation := retained.computation) (headEq := rules.headEq)
          body argument).substitute morphism.substitution)
      (StructuralStepReceipt.betaPi
        (computation := retained.computation) (headEq := rules.headEq)
        (subst (liftContextHom morphism domain).substitution body)
        (subst morphism.substitution argument)) := by
  rw [liftContextHom_substitution]
  simp only [StructuralStepReceipt.substitute]
  apply cast_heq

theorem piBeta_raw_natural {rules : Rules Head}
    (retained : RetainedRoot rules) {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target)
    (input : Tm Head (target.arity + 1) × Tm Head target.arity) :
    (reindexHomogeneousStepMap retained morphism).mapRaw
        ((piBetaMap retained product).mapRaw input) =
      (piBetaMap retained (product.reindex morphism)).mapRaw
        ((reindexPiBetaInputMap morphism).mapRaw input) := by
  cases input
  apply RawHomogeneousStep.ext <;>
    simp [reindexHomogeneousStepMap, piBetaMap, reindexPiBetaInputMap,
      productMap, reindexTermMap, reindexTermAtCodeMap,
      TypeOver.reindex, liftContextHom_substitution, subst, subst_inst0]
  all_goals rfl

/-- Pi beta receipts commute with every typed context substitution. -/
def piBetaNaturalitySquare {rules : Rules Head}
    (retained : RetainedRoot rules) {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) :
    ExactMap.Square (piBetaMap retained product)
      (reindexPiBetaInputMap morphism)
      (reindexHomogeneousStepMap retained morphism)
      (piBetaMap retained (product.reindex morphism)) where
  raw_commutes := piBeta_raw_natural retained product morphism
  exact_commutes := fun {raw} evidence =>
    by
      rcases raw with ⟨body, argument⟩
      rcases evidence with ⟨⟨bodyTyping⟩, ⟨argumentTyping⟩⟩
      apply homogeneousStepEvidence_heq
        (piBeta_raw_natural retained product morphism (body, argument))
      dsimp [reindexHomogeneousStepMap, piBetaMap, reindexPiBetaInputMap,
        productMap, reindexTermMap, reindexTermAtCodeMap,
        DependentProduct.betaReceipt]
      convert piBetaReceipt_reindex retained domain morphism body argument
        using 1 <;> rfl

/-- First-projection beta is another homogeneous constructional receipt. -/
def sigmaFirstBetaMap {rules : Rules Head}
    (retained : RetainedRoot rules) {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain) :
    ExactMap (pairInputFibre sum) (homogeneousStepFibre retained context) where
  mapRaw := fun input =>
    { type := domain.code
      source := .fst (.pair input.1 input.2)
      target := input.1 }
  mapExact := fun {raw} evidence => by
    let first : Term context domain :=
      { code := raw.1
        typed := evidence.1.down }
    let second : Term context (instantiateType codomain first) :=
      { code := raw.2
        typed := evidence.2.down }
    exact
      { sourceTyping := (sum.firstProjection (sum.pair first second)).typed
        targetTyping := first.typed
        receipt := sum.firstBetaReceipt retained first second }

theorem sigmaFirstBeta_raw_natural {rules : Rules Head}
    (retained : RetainedRoot rules) {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target)
    (input : (pairInputFibre sum).Raw) :
    (reindexHomogeneousStepMap retained morphism).mapRaw
        ((sigmaFirstBetaMap retained sum).mapRaw input) =
      (sigmaFirstBetaMap retained (sum.reindex morphism)).mapRaw
        ((reindexPairInputMap sum morphism).mapRaw input) := by
  cases input
  apply RawHomogeneousStep.ext <;>
    simp [reindexHomogeneousStepMap, sigmaFirstBetaMap,
      reindexPairInputMap, TypeOver.reindex, subst]

def sigmaFirstBetaNaturalitySquare {rules : Rules Head}
    (retained : RetainedRoot rules) {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target) :
    ExactMap.Square (sigmaFirstBetaMap retained sum)
      (reindexPairInputMap sum morphism)
      (reindexHomogeneousStepMap retained morphism)
      (sigmaFirstBetaMap retained (sum.reindex morphism)) where
  raw_commutes := sigmaFirstBeta_raw_natural retained sum morphism
  exact_commutes := fun {raw} _evidence =>
    by
      cases raw
      rfl

/-- A dependent computation step retains distinct source and target type
codes, their conversion receipt, and the term-level step.  This is the
correct carrier for second-projection beta: raw equality of the fibres is
neither assumed nor generally true. -/
structure RawDependentStep {rules : Rules Head}
    (context : FormedContext rules) where
  sourceType : Tm Head context.arity
  targetType : Tm Head context.arity
  source : Tm Head context.arity
  target : Tm Head context.arity

@[ext] theorem RawDependentStep.ext {rules : Rules Head}
    {context : FormedContext rules} {left right : RawDependentStep context}
    (sourceTypeEquality : left.sourceType = right.sourceType)
    (targetTypeEquality : left.targetType = right.targetType)
    (sourceEquality : left.source = right.source)
    (targetEquality : left.target = right.target) : left = right := by
  cases left
  cases right
  cases sourceTypeEquality
  cases targetTypeEquality
  cases sourceEquality
  cases targetEquality
  rfl

structure DependentStepEvidence {rules : Rules Head}
    (retained : RetainedRoot rules) (context : FormedContext rules)
    (candidate : RawDependentStep context) where
  sourceTyping :
    HasType rules context.context candidate.source candidate.sourceType
  targetTyping :
    HasType rules context.context candidate.target candidate.targetType
  typeReceipt : StructuralConversionReceipt retained.computation rules.headEq
    candidate.sourceType candidate.targetType
  termReceipt : StructuralStepReceipt retained.computation rules.headEq
    candidate.source candidate.target

def dependentStepFibre {rules : Rules Head}
    (retained : RetainedRoot rules) (context : FormedContext rules) : Fibre where
  Raw := RawDependentStep context
  Exact := DependentStepEvidence retained context

def reindexDependentStepMap {rules : Rules Head}
    (retained : RetainedRoot rules) {source target : FormedContext rules}
    (morphism : source ⟶ target) :
    ExactMap (dependentStepFibre retained target)
      (dependentStepFibre retained source) where
  mapRaw := fun candidate =>
    { sourceType := subst morphism.substitution candidate.sourceType
      targetType := subst morphism.substitution candidate.targetType
      source := subst morphism.substitution candidate.source
      target := subst morphism.substitution candidate.target }
  mapExact := fun evidence =>
    { sourceTyping := evidence.sourceTyping.substitute morphism.typed
      targetTyping := evidence.targetTyping.substitute morphism.typed
      typeReceipt := evidence.typeReceipt.substitute morphism.substitution
      termReceipt := evidence.termReceipt.substitute morphism.substitution }

/-- Second-projection beta constructs its essential two-dimensional receipt:
type transport and term computation remain separate pieces of evidence. -/
def sigmaSecondBetaMap {rules : Rules Head}
    (retained : RetainedRoot rules) {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain) :
    ExactMap (pairInputFibre sum) (dependentStepFibre retained context) where
  mapRaw := fun input =>
    { sourceType := inst0 (.fst (.pair input.1 input.2)) codomain.code
      targetType := inst0 input.1 codomain.code
      source := .snd (.pair input.1 input.2)
      target := input.2 }
  mapExact := fun {raw} evidence => by
    let first : Term context domain :=
      { code := raw.1
        typed := evidence.1.down }
    let second : Term context (instantiateType codomain first) :=
      { code := raw.2
        typed := evidence.2.down }
    exact
      { sourceTyping := (sum.secondProjection (sum.pair first second)).typed
        targetTyping := second.typed
        typeReceipt :=
          (sum.secondBetaTypeConversion retained first second).receipt
        termReceipt := sum.secondBetaReceipt retained first second }

theorem sigmaSecondBeta_raw_natural {rules : Rules Head}
    (retained : RetainedRoot rules) {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target)
    (input : (pairInputFibre sum).Raw) :
    (reindexDependentStepMap retained morphism).mapRaw
        ((sigmaSecondBetaMap retained sum).mapRaw input) =
      (sigmaSecondBetaMap retained (sum.reindex morphism)).mapRaw
        ((reindexPairInputMap sum morphism).mapRaw input) := by
  cases input
  apply RawDependentStep.ext <;>
    simp [reindexDependentStepMap, sigmaSecondBetaMap,
      reindexPairInputMap, TypeOver.reindex, liftContextHom_substitution,
      subst, subst_inst0]
  all_goals rfl

/-- The term-level second-beta receipt is strictly stable under ambient
substitution. -/
theorem sigmaSecondBetaTermReceipt_reindex {rules : Rules Head}
    (retained : RetainedRoot rules) {source target : FormedContext rules}
    (morphism : source ⟶ target) (first second : Tm Head target.arity) :
    HEq
      ((StructuralStepReceipt.betaSigmaSnd
          (computation := retained.computation) (headEq := rules.headEq)
          first second).substitute morphism.substitution)
      (StructuralStepReceipt.betaSigmaSnd
        (computation := retained.computation) (headEq := rules.headEq)
        (subst morphism.substitution first)
        (subst morphism.substitution second)) := by
  simp only [StructuralStepReceipt.substitute]
  rfl

/-- The strongest currently justified naturality boundary for dependent
second beta.  Raw endpoints commute and the term computation receipt is
strictly stable.  Both type-conversion receipts remain present in `left`
and `right`; they are deliberately not identified here.  Substitution can
expand a variable into syntax with several occurrences, so pointwise
conversion may acquire a different proof tree.  Comparing those trees
requires an explicit higher coherence cell, not proof irrelevance. -/
structure DependentStepNaturalityBoundary {rules : Rules Head}
    {retained : RetainedRoot rules} {context : FormedContext rules}
    {leftCandidate rightCandidate : RawDependentStep context}
    (left : DependentStepEvidence retained context leftCandidate)
    (right : DependentStepEvidence retained context rightCandidate) where
  raw_commutes : leftCandidate = rightCandidate
  termReceipt_commutes : HEq left.termReceipt right.termReceipt

def sigmaSecondBetaNaturalityBoundary {rules : Rules Head}
    (retained : RetainedRoot rules) {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target)
    {raw : (pairInputFibre sum).Raw}
    (evidence : (pairInputFibre sum).Exact raw) :
    DependentStepNaturalityBoundary
      ((reindexDependentStepMap retained morphism).mapExact
        ((sigmaSecondBetaMap retained sum).mapExact evidence))
      ((sigmaSecondBetaMap retained (sum.reindex morphism)).mapExact
        ((reindexPairInputMap sum morphism).mapExact evidence)) := by
  rcases raw with ⟨first, second⟩
  rcases evidence with ⟨⟨firstTyping⟩, ⟨secondTyping⟩⟩
  refine
    { raw_commutes :=
        sigmaSecondBeta_raw_natural retained sum morphism ⟨first, second⟩
      termReceipt_commutes := ?_ }
  dsimp [reindexDependentStepMap, sigmaSecondBetaMap,
    reindexPairInputMap, DependentSum.secondBetaReceipt]
  exact sigmaSecondBetaTermReceipt_reindex retained morphism first second

/-! ### Native identity iota as a gradual root capability -/

namespace IdentityIota

abbrev identityRules : Rules Tower.Head :=
  Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeIndexedFamilies.Intrinsic.rules

/-- A raw candidate for one native indexed-family root computation. -/
structure RawRootStep (context : FormedContext identityRules) where
  type : Tower.Tm context.arity
  source : Tower.Tm context.arity
  target : Tower.Tm context.arity

structure RootStepEvidence (context : FormedContext identityRules)
    (candidate : RawRootStep context) where
  sourceTyping :
    @Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.HasType
      Tower.Head identityRules context.arity
      context.context candidate.source candidate.type
  targetTyping :
    @Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.HasType
      Tower.Head identityRules context.arity
      context.context candidate.target candidate.type
  receipt :
    Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeIndexedFamilies.Intrinsic.IotaEvidence
      context.arity candidate.source candidate.target

def rootStepFibre (context : FormedContext identityRules) : Fibre where
  Raw := RawRootStep context
  Exact := RootStepEvidence context

def candidateOfCell {context : FormedContext identityRules}
    (cell :
      Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalIdentityEliminator.NativeIotaCell
        context) : RawRootStep context :=
  { type := cell.resultType.code
    source := cell.source.code
    target := cell.target.code }

/-- Any intrinsically constructed iota cell supplies the corresponding exact
gradual root capability without a checker replay. -/
def exactOfCell {context : FormedContext identityRules}
    (cell :
      Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalIdentityEliminator.NativeIotaCell
        context) :
    (rootStepFibre context).Exact (candidateOfCell cell) :=
  { sourceTyping := cell.source.typed
    targetTyping := cell.target.typed
    receipt := cell.evidence }

def wrongIdentityCandidate : RawRootStep
    Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalIdentityEliminator.formedIdentityContext :=
  { type :=
      Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeIndexedFamilies.Intrinsic.identityIotaResultType
    source :=
      Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeIndexedFamilies.Intrinsic.identityIotaLeft
    target := .var ⟨1, by decide⟩ }

/-- Negative identity-elimination control: changing the authored iota target
cannot manufacture an exact native-root capability. -/
theorem wrongIdentityCandidate_has_no_exact :
    IsEmpty ((rootStepFibre
      Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalIdentityEliminator.formedIdentityContext).Exact
        wrongIdentityCandidate) := by
  constructor
  intro evidence
  exact
    Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalIdentityEliminator.wrongIdentityTarget_has_noEvidence.false
      evidence.receipt

end IdentityIota

/-! ## Nondegenerate receipt controls -/

namespace Canary

open Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentTermFormers.Canary
open SyntacticContextual.TowerExamples

abbrev piRetainedTower :=
  SyntacticJudgmentalPi.TowerExamples.retainedTower
abbrev sigmaRetainedTower :=
  SyntacticJudgmentalSigmaId.TowerExamples.retainedTower

def identityPiBetaInputEvidence :
    (Fibre.product (termFibre identityCodomain)
      (termFibre universeOne)).Exact
      (identityBody.code, universeZero.code) :=
  (⟨identityBody.typed⟩, ⟨universeZero.typed⟩)

/-- Positive Pi-beta control: construction returns typed endpoints together
with the exact beta receipt; no checker reconstruction is involved. -/
def identityPiBetaEvidence :
    (homogeneousStepFibre piRetainedTower empty).Exact
      ((piBetaMap piRetainedTower identityProduct).mapRaw
        (identityBody.code, universeZero.code)) :=
  (piBetaMap piRetainedTower identityProduct).mapExact
    identityPiBetaInputEvidence

/-- Positive dependent Sigma-beta control: both the conversion between
result fibres and the term computation remain first-class evidence. -/
def dependentSigmaSecondBetaEvidence :
    (dependentStepFibre sigmaRetainedTower empty).Exact
      ((sigmaSecondBetaMap sigmaRetainedTower dependentSum).mapRaw
        dependentPairInput) :=
  (sigmaSecondBetaMap sigmaRetainedTower dependentSum).mapExact
    dependentPairEvidence

/-- Negative/elegance control: dependent second beta really crosses two
distinct raw type codes.  Collapsing it to equality would discard the
conversion dimension that the receipt records. -/
theorem dependentSigmaSecondBeta_sourceType_ne_targetType :
    ((sigmaSecondBetaMap sigmaRetainedTower dependentSum).mapRaw
        dependentPairInput).sourceType ≠
      ((sigmaSecondBetaMap sigmaRetainedTower dependentSum).mapRaw
        dependentPairInput).targetType := by
  intro equality
  dsimp [sigmaSecondBetaMap,
    Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentTermFormers.Canary.dependentPairInput]
    at equality
  change
    Tm.fst (Tm.pair (sortTm Tower.zero) (Tm.head .legacyGround)) =
      sortTm Tower.zero at equality
  cases equality

/-- Positive identity-iota control at the authored native declaration. -/
def identityIotaEvidence :
    (IdentityIota.rootStepFibre
      Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalIdentityEliminator.formedIdentityContext).Exact
      (IdentityIota.candidateOfCell
        Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalIdentityEliminator.identityIotaCell) :=
  IdentityIota.exactOfCell
    Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalIdentityEliminator.identityIotaCell

end Canary

/-! ## State-level consequence -/

/-- Every naturality square above commutes on all safe gradual states. -/
theorem lambdaState_reindex {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) {body : Tm Head (target.arity + 1)}
    (state : State (termFibre codomain) body) :
    HEq
      (mapSafe (reindexProductTermMap product morphism)
        (mapSafe (lambdaMap product) state))
      (mapSafe (lambdaMap (product.reindex morphism))
        (mapSafe (reindexTermMap codomain
          (liftContextHom morphism domain)) state)) :=
  (lambdaNaturalitySquare product morphism).mapSafe_commutes state

/-! ## Axiom audit -/

#print axioms lambdaNaturalitySquare
#print axioms applicationNaturalitySquare
#print axioms pairNaturalitySquare
#print axioms firstProjectionNaturalitySquare
#print axioms secondProjectionNaturalitySquare
#print axioms identityTypeNaturalitySquare
#print axioms reflexivityNaturalitySquare
#print axioms piBetaNaturalitySquare
#print axioms sigmaFirstBetaNaturalitySquare
#print axioms sigmaSecondBetaNaturalityBoundary
#print axioms IdentityIota.exactOfCell
#print axioms IdentityIota.wrongIdentityCandidate_has_no_exact
#print axioms Canary.identityPiBetaEvidence
#print axioms Canary.dependentSigmaSecondBetaEvidence
#print axioms Canary.dependentSigmaSecondBeta_sourceType_ne_targetType
#print axioms Canary.identityIotaEvidence
#print axioms lambdaState_reindex

end Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentNaturality
