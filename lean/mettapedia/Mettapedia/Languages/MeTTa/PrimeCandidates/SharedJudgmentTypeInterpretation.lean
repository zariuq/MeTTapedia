import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentInterpretation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveBasedIdentity
import Mettapedia.TypeTheory.ContextualBasedIdentityOperations

/-!
# Native dependent constructors on the same interpretation

Raw Pi, Sigma, identity, reflexivity and based-J operations use the CwF of
the supplied assembly interpretation. Native context extensions are compared
by explicit maps with independent inverse and variable laws, not identified
by equality of context objects. Constructor agreement and coverage concern
the actual refined native judgments and their declared motives.

The interface is not a common model. In particular, native-motive coverage
does not require every ambient semantic family to be represented by syntax,
and the semantic beta/substitution clauses are restricted to the admitted
meanings named below. No full-versus-based J comparison, identity policy,
unbounded universe construction or evaluation profile is selected.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentTypeInterpretation

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.FormationSensitive SharedJudgmentFragment
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

open Mettapedia.TypeTheory

universe u v w w'

/-- The endpoint/path context and its reflexivity section do not presuppose
an eliminator on every semantic motive. Their formation and boundary laws
can therefore be qualified independently of total J. -/
structure FrameOperations (C : Cwf.{u, v, w, w'}) where
  identity : ContextualTypeOperations.IdentityFormationOperations C
  reflexivity : ContextualTypeOperations.IdentityReflexivityOperations identity
  reflSection : {context : C.Ctx} → {type : C.Ty context} →
    (left : C.Tm context type) →
      C.Sub context (ContextualBasedIdentityOperations.basedContext identity left)

structure Operations (C : Cwf.{u, v, w, w'}) where
  products : ContextualTypeOperations.PiOperations C
  sums : ContextualTypeOperations.SigmaOperations C
  identity : ContextualTypeOperations.IdentityFormationOperations C
  reflexivity : ContextualTypeOperations.IdentityReflexivityOperations identity
  based : ContextualBasedIdentityOperations.Operations identity

/-- The full operation class supplies the weaker frame data without changing
any of its fields or adding motive-coverage assumptions. -/
@[reducible] def Operations.frames {C : Cwf.{u, v, w, w'}}
    (operations : Operations C) : FrameOperations C where
  identity := operations.identity
  reflexivity := operations.reflexivity
  reflSection := operations.based.elimination.reflSection

variable {assembly : Assembly} {C : Cwf.{u, v, w, w'}}

/-- Maps only; inverse equations are not hidden in raw comparison data. -/
structure ContextComparison (C : Cwf.{u, v, w, w'}) (source target : C.Ctx) where
  forward : C.Sub source target
  backward : C.Sub target source

def ContextComparison.Inverse {source target : C.Ctx}
    (comparison : ContextComparison C source target) : Prop :=
  C.compS comparison.forward comparison.backward = C.idS target ∧
    C.compS comparison.backward comparison.forward = C.idS source

def ComprehensionMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    {n : Nat} (context : SharedJudgmentInterpretation.Context assembly n) (type : Tower.Tm n)
    (extendedFormed : ContextFormation assembly.rules (.snoc context.raw type))
    (semanticType : C.Ty (interpretation.ctx context))
    (comparison : ContextComparison C (interpretation.ctx ⟨.snoc context.raw type, extendedFormed⟩)
      (C.ext (interpretation.ctx context) semanticType)) : Prop :=
  let extended : SharedJudgmentInterpretation.Context assembly (n + 1) :=
    ⟨.snoc context.raw type, extendedFormed⟩
  comparison.Inverse ∧
    interpretation.sub context extended (renSub wk)
      (C.compS (C.wk semanticType) comparison.forward) ∧
    interpretation.ty extended (rename wk type)
      (C.tySub (C.tySub semanticType (C.wk semanticType)) comparison.forward) ∧
    interpretation.term extended (.var 0) (rename wk type)
      (C.tySub (C.tySub semanticType (C.wk semanticType)) comparison.forward)
      (C.tmSub (C.vz semanticType) comparison.forward)

def ComprehensionCoverage (interpretation : SharedJudgmentInterpretation.Data assembly C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (type : Tower.Tm n) (universeHead : Tower.Head)
    (semanticType : C.Ty (interpretation.ctx context))
    (admitted : Judgment assembly.rules context type (.head universeHead))
    (universeWitness : assembly.rules.isUniverse universeHead),
    interpretation.ty context type semanticType →
      ∃ comparison, ComprehensionMeaning interpretation context type
        (.snoc context.formed admitted.typing universeWitness) semanticType comparison

/-- Semantic family data retain the real dependent comprehension fibre. -/
structure Family (interpretation : SharedJudgmentInterpretation.Data assembly C) {n : Nat}
    (context : SharedJudgmentInterpretation.Context assembly n) (domain : Tower.Tm n) (_codomain : Tower.Tm (n + 1)) where
  contextFormation : ContextFormation assembly.rules (.snoc context.raw domain)
  semanticDomain : C.Ty (interpretation.ctx context)
  semanticCodomain : C.Ty (C.ext (interpretation.ctx context) semanticDomain)
  comparison : ContextComparison C
    (interpretation.ctx ⟨.snoc context.raw domain, contextFormation⟩)
    (C.ext (interpretation.ctx context) semanticDomain)

abbrev Family.context {interpretation : SharedJudgmentInterpretation.Data assembly C} {n : Nat}
    {context : SharedJudgmentInterpretation.Context assembly n}
    {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    (family : Family interpretation context domain codomain) :
    SharedJudgmentInterpretation.Context assembly (n + 1) :=
  ⟨.snoc context.raw domain, family.contextFormation⟩

def FamilyMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C) {n : Nat}
    {context : SharedJudgmentInterpretation.Context assembly n} {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    (family : Family interpretation context domain codomain) : Prop :=
  interpretation.ty context domain family.semanticDomain ∧
    ComprehensionMeaning interpretation context domain family.contextFormation
      family.semanticDomain family.comparison ∧
    interpretation.ty family.context codomain
      (C.tySub family.semanticCodomain family.comparison.forward)

/-- These are exactly the independent formation premises of native Pi and
Sigma. The join is native data, not a semantic universe assumption. -/
def FamilyAdmitted (assembly : Assembly) {n : Nat} (context : Tower.Ctx n)
    (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1)) : Prop :=
  ∃ lower upper result : Tower.Head,
    Judgment assembly.rules context domain (.head lower) ∧ assembly.rules.isUniverse lower ∧
    Judgment assembly.rules (.snoc context domain) codomain (.head upper) ∧
    assembly.rules.isUniverse upper ∧ assembly.rules.join lower upper result

/-- Product clauses require only product operations. A separate identity
eliminator is not a premise of their component-level qualification. -/
def PiFormationMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : ContextualTypeOperations.PiOperations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1))
    (family : Family interpretation context domain codomain),
    FamilyAdmitted assembly context domain codomain → FamilyMeaning interpretation family →
      interpretation.ty context (.pi domain codomain)
        (operations.pi family.semanticDomain family.semanticCodomain)

def PiIntroductionMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : ContextualTypeOperations.PiOperations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (domain : Tower.Tm n) (codomain body : Tower.Tm (n + 1))
    (family : Family interpretation context domain codomain)
    (semanticBody : C.Tm (C.ext (interpretation.ctx context) family.semanticDomain)
      family.semanticCodomain),
    FamilyAdmitted assembly context domain codomain → FamilyMeaning interpretation family →
    Judgment assembly.rules (.snoc context domain) body codomain →
    interpretation.term family.context body codomain
      (C.tySub family.semanticCodomain family.comparison.forward)
      (C.tmSub semanticBody family.comparison.forward) →
      interpretation.term context (.lam body) (.pi domain codomain)
        (operations.pi family.semanticDomain family.semanticCodomain)
        (operations.lam semanticBody)

def PiEliminationMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : ContextualTypeOperations.PiOperations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (domain function argument : Tower.Tm n)
    (codomain : Tower.Tm (n + 1)) (family : Family interpretation context domain codomain)
    (semanticFunction : C.Tm (interpretation.ctx context)
      (operations.pi family.semanticDomain family.semanticCodomain))
    (semanticArgument : C.Tm (interpretation.ctx context) family.semanticDomain),
    FamilyAdmitted assembly context domain codomain → FamilyMeaning interpretation family →
    Judgment assembly.rules context function (.pi domain codomain) →
    Judgment assembly.rules context argument domain →
    interpretation.term context function (.pi domain codomain)
      (operations.pi family.semanticDomain family.semanticCodomain) semanticFunction →
    interpretation.term context argument domain family.semanticDomain semanticArgument →
      interpretation.ty context (inst0 argument codomain)
        (C.tySub family.semanticCodomain (selfExtend C semanticArgument)) ∧
      interpretation.term context (.app function argument) (inst0 argument codomain)
        (C.tySub family.semanticCodomain (selfExtend C semanticArgument))
        (operations.app semanticFunction semanticArgument)

def SigmaFormationMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : ContextualTypeOperations.SigmaOperations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1))
    (family : Family interpretation context domain codomain),
    FamilyAdmitted assembly context domain codomain → FamilyMeaning interpretation family →
      interpretation.ty context (.sigma domain codomain)
        (operations.sigma family.semanticDomain family.semanticCodomain)

def SigmaIntroductionMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : ContextualTypeOperations.SigmaOperations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (domain first second : Tower.Tm n)
    (codomain : Tower.Tm (n + 1)) (family : Family interpretation context domain codomain)
    (semanticFirst : C.Tm (interpretation.ctx context) family.semanticDomain)
    (semanticSecond : C.Tm (interpretation.ctx context)
      (C.tySub family.semanticCodomain (selfExtend C semanticFirst))),
    FamilyAdmitted assembly context domain codomain → FamilyMeaning interpretation family →
    Judgment assembly.rules context first domain →
    Judgment assembly.rules context second (inst0 first codomain) →
    interpretation.term context first domain family.semanticDomain semanticFirst →
    interpretation.term context second (inst0 first codomain)
      (C.tySub family.semanticCodomain (selfExtend C semanticFirst)) semanticSecond →
      interpretation.term context (.pair first second) (.sigma domain codomain)
        (operations.sigma family.semanticDomain family.semanticCodomain)
        (operations.pair semanticFirst semanticSecond)

def SigmaEliminationMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : ContextualTypeOperations.SigmaOperations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (domain pair : Tower.Tm n)
    (codomain : Tower.Tm (n + 1)) (family : Family interpretation context domain codomain)
    (semanticPair : C.Tm (interpretation.ctx context)
      (operations.sigma family.semanticDomain family.semanticCodomain)),
    FamilyAdmitted assembly context domain codomain → FamilyMeaning interpretation family →
    Judgment assembly.rules context pair (.sigma domain codomain) →
    interpretation.term context pair (.sigma domain codomain)
      (operations.sigma family.semanticDomain family.semanticCodomain) semanticPair →
      interpretation.term context (.fst pair) domain family.semanticDomain
        (operations.fst semanticPair) ∧
      interpretation.ty context (inst0 (.fst pair) codomain)
        (C.tySub family.semanticCodomain (selfExtend C (operations.fst semanticPair))) ∧
      interpretation.term context (.snd pair) (inst0 (.fst pair) codomain)
        (C.tySub family.semanticCodomain (selfExtend C (operations.fst semanticPair)))
        (operations.snd semanticPair)

def IdentityFormationMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : ContextualTypeOperations.IdentityFormationOperations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (type left right : Tower.Tm n) (level : Tower.Head)
    (semanticType : C.Ty (interpretation.ctx context))
    (semanticLeft semanticRight : C.Tm (interpretation.ctx context) semanticType),
    Judgment assembly.rules context type (.head level) → assembly.rules.isUniverse level →
    Judgment assembly.rules context left type → Judgment assembly.rules context right type →
    interpretation.ty context type semanticType →
    interpretation.term context left type semanticType semanticLeft →
    interpretation.term context right type semanticType semanticRight →
      interpretation.ty context (.id type left right)
        (operations.idTy semanticType semanticLeft semanticRight)

def ReflexivityMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    {identity : ContextualTypeOperations.IdentityFormationOperations C}
    (operations : ContextualTypeOperations.IdentityReflexivityOperations identity) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (type left : Tower.Tm n)
    (semanticType : C.Ty (interpretation.ctx context))
    (semanticLeft : C.Tm (interpretation.ctx context) semanticType),
    Judgment assembly.rules context left type → interpretation.ty context type semanticType →
    interpretation.term context left type semanticType semanticLeft →
      interpretation.term context (.refl left) (.id type left left)
        (identity.idTy semanticType semanticLeft semanticLeft)
        (operations.refl semanticLeft)

/-- Coverage is separate from the implication-shaped constructor clauses.
It includes every native formed family, not every ambient semantic family. -/
def FamilyCoverage (interpretation : SharedJudgmentInterpretation.Data assembly C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1)),
    FamilyAdmitted assembly context domain codomain →
      ∃ family : Family interpretation context domain codomain, FamilyMeaning interpretation family

/-! ## The actual fixed-left-endpoint J motive -/

/-- Raw semantic data for one native parameter tuple. In particular, the
motive is over the based context, and the method lives in the original
context. The based telescope carries only its independent context formation;
no native motive admission, constructor meaning or comparison law occurs in
this record. -/
structure JFrame (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C) {n : Nat} (context : SharedJudgmentInterpretation.Context assembly n)
    (type left _motive _method : Tower.Tm n) where
  contextFormation : ContextFormation assembly.rules
    (FormationSensitiveBasedIdentity.basedContext context.raw type left)
  semanticType : C.Ty (interpretation.ctx context)
  semanticLeft : C.Tm (interpretation.ctx context) semanticType
  motive : C.Ty (ContextualBasedIdentityOperations.basedContext operations.identity semanticLeft)
  base : C.Tm (interpretation.ctx context)
    (C.tySub motive (operations.reflSection semanticLeft))
  comparison : ContextComparison C
    (interpretation.ctx
      ⟨FormationSensitiveBasedIdentity.basedContext context.raw type left, contextFormation⟩)
    (ContextualBasedIdentityOperations.basedContext operations.identity semanticLeft)
  reflexivityMap : C.Sub (interpretation.ctx context)
    (interpretation.ctx
      ⟨FormationSensitiveBasedIdentity.basedContext context.raw type left, contextFormation⟩)

abbrev JFrame.context {interpretation : SharedJudgmentInterpretation.Data assembly C}
    {operations : FrameOperations C} {n : Nat}
    {context : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    (frame : JFrame interpretation operations context type left motive method) :
    SharedJudgmentInterpretation.Context assembly (n + 2) :=
  ⟨FormationSensitiveBasedIdentity.basedContext context.raw type left, frame.contextFormation⟩

/-- These primitive clauses bind actual native context variables, motive
body, method and reflexivity substitution to the same semantic data. None
asserts the meaning of a J expression or its computed result. -/
structure JFrameMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C) {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    (frame : JFrame interpretation operations context type left motive method) : Prop where
  typeMeaning : interpretation.ty context type frame.semanticType
  leftMeaning : interpretation.term context left type frame.semanticType frame.semanticLeft
  inverse : frame.comparison.Inverse
  projection : interpretation.sub context
    frame.context
    (renSub (fun index => index.succ.succ))
    (C.compS (ContextualBasedIdentityOperations.baseProjection operations.identity frame.semanticLeft)
      frame.comparison.forward)
  rightMeaning : interpretation.term
    frame.context (.var 1)
    (FormationSensitiveBasedIdentity.doubleWeaken type)
    (C.tySub
      (C.tySub (C.tySub frame.semanticType (C.wk frame.semanticType))
        (C.wk (ContextualBasedIdentityOperations.witnessType operations.identity frame.semanticLeft)))
      frame.comparison.forward)
    (C.tmSub (ContextualBasedIdentityOperations.rightEndpoint operations.identity frame.semanticLeft)
      frame.comparison.forward)
  witnessMeaning : interpretation.term
    frame.context (.var 0)
    (.id (FormationSensitiveBasedIdentity.doubleWeaken type)
      (FormationSensitiveBasedIdentity.doubleWeaken left) (.var 1))
    (C.tySub
      (C.tySub (ContextualBasedIdentityOperations.witnessType operations.identity frame.semanticLeft)
        (C.wk (ContextualBasedIdentityOperations.witnessType operations.identity frame.semanticLeft)))
      frame.comparison.forward)
    (C.tmSub (C.vz (ContextualBasedIdentityOperations.witnessType operations.identity frame.semanticLeft))
      frame.comparison.forward)
  reflexivityMeaning : interpretation.sub
    frame.context context
    (FormationSensitiveBasedIdentity.reflexivitySub left) frame.reflexivityMap
  reflexivitySquare : C.compS frame.comparison.forward frame.reflexivityMap =
    operations.reflSection frame.semanticLeft
  motiveMeaning : interpretation.ty
    frame.context
    (FormationSensitiveBasedIdentity.motiveBody motive)
    (C.tySub frame.motive frame.comparison.forward)
  methodTypeMeaning : interpretation.ty context (FormationSensitiveBasedIdentity.methodType left motive)
    (C.tySub frame.motive (operations.reflSection frame.semanticLeft))
  methodMeaning : interpretation.term context method (FormationSensitiveBasedIdentity.methodType left motive)
    (C.tySub frame.motive (operations.reflSection frame.semanticLeft)) frame.base

/-- Every motive and method admitted at the authored declaration telescope
must have a based semantic comparison. The quantification includes arbitrary
formed extension contexts; it neither restricts motives to constants nor
requires syntactic names for all ambient semantic families. -/
def BasedMotiveCoverage (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (type left motive method : Tower.Tm n),
    FormationSensitiveBasedIdentity.Parameters assembly.declarations context type left motive method →
      ∃ frame : JFrame interpretation operations context type left motive method,
        JFrameMeaning interpretation operations frame

/-- Constructor agreement is at the generic right endpoint and retained
identity witness. The reflexivity case is derived below by actual native
substitution, rather than stored as a qualification field. -/
def BasedJMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (type left motive method : Tower.Tm n)
    (frame : JFrame interpretation operations.frames context type left motive method),
    FormationSensitiveBasedIdentity.Parameters assembly.declarations context type left motive method →
    JFrameMeaning interpretation operations.frames frame →
      interpretation.term frame.context
        (FormationSensitiveBasedIdentity.genericTerm type left motive method)
        (FormationSensitiveBasedIdentity.motiveBody motive)
        (C.tySub frame.motive frame.comparison.forward)
        (C.tmSub (operations.based.elimination.j frame.semanticLeft frame.motive frame.base)
          frame.comparison.forward)

def AdmittedBasedBeta (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (type left motive method : Tower.Tm n)
    (frame : JFrame interpretation operations.frames context type left motive method),
    FormationSensitiveBasedIdentity.Parameters assembly.declarations context type left motive method →
    JFrameMeaning interpretation operations.frames frame →
      C.tmSub (operations.based.elimination.j frame.semanticLeft frame.motive frame.base)
        (operations.based.elimination.reflSection frame.semanticLeft) = frame.base

/-- The semantic section denotes the fixed left endpoint and the supplied
reflexivity constructor on every required native frame. This is distinct
from both its comparison with a native substitution and J's beta law. -/
def AdmittedBasedBoundary (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (type left motive method : Tower.Tm n)
    (frame : JFrame interpretation operations context type left motive method),
    FormationSensitiveBasedIdentity.Parameters assembly.declarations context type left motive method →
    JFrameMeaning interpretation operations frame →
      C.compS (C.wk (ContextualBasedIdentityOperations.witnessType operations.identity frame.semanticLeft))
        (operations.reflSection frame.semanticLeft) = selfExtend C frame.semanticLeft ∧
      HEq (C.tmSub (C.vz (ContextualBasedIdentityOperations.witnessType operations.identity frame.semanticLeft))
        (operations.reflSection frame.semanticLeft))
        (operations.reflexivity.refl frame.semanticLeft)

theorem admittedBasedBoundary_of_full (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C)
    (boundary : ContextualBasedIdentityOperations.Boundary operations.reflexivity operations.based.elimination) :
    AdmittedBasedBoundary interpretation operations.frames := by
  intro n context type left motive method frame _ _
  exact ⟨boundary.1 frame.semanticLeft, boundary.2 frame.semanticLeft⟩

/-- Full semantic beta is a sufficient comparison class; only its
restriction to actual admitted native motive meanings is required above. -/
theorem admittedBasedBeta_of_full (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (beta : ContextualBasedIdentityOperations.Beta operations.based.elimination) :
    AdmittedBasedBeta interpretation operations := by
  intro n context type left motive method frame _ _
  exact beta frame.semanticLeft frame.motive frame.base

theorem termMeaning_transport (interpretation : SharedJudgmentInterpretation.Data assembly C)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {term type : Tower.Tm n}
    {first second : C.Ty (interpretation.ctx context)}
    {firstValue : C.Tm (interpretation.ctx context) first}
    {secondValue : C.Tm (interpretation.ctx context) second}
    (typesEqual : first = second) (valuesEqual : HEq firstValue secondValue)
    (meaning : interpretation.term context term type first firstValue) :
    interpretation.term context term type second secondValue := by
  cases typesEqual
  have equal := eq_of_heq valuesEqual
  cases equal
  exact meaning

/-- Any admitted native J application, not just an iota redex, has its
principal-result meaning. Native argument recovery supplies the complete
declared motive scope. Independent coverage supplies the semantic based
frame and the actual endpoint/witness substitution. The semantic value is
the supplied J operation pulled along that substitution, not a decoder.

The observed annotation may have been changed by native conversion or
cumulativity. Meaning at that changed annotation remains the separate
annotation/universe interface; this theorem names the principal `P y q`
result and does not silently equate differently interpreted universes. -/
theorem native_j_application_meaning
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : Operations C)
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    (coverage : BasedMotiveCoverage interpretation operations.frames)
    (subTotal : SharedJudgmentInterpretation.AdmittedSubstitutionsTotal interpretation)
    (stable : SharedJudgmentInterpretation.SubstitutionStable interpretation)
    (constructor : BasedJMeaning interpretation operations)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {type left motive method right witness displayed : Tower.Tm n}
    (admitted : Judgment assembly.rules context
      (NativeIndexedFamilies.Intrinsic.identityEliminateApp type left motive method right witness) displayed) :
    ∃ (frame : JFrame interpretation operations.frames context type left motive method)
      (semantic : C.Sub (interpretation.ctx context)
        (interpretation.ctx frame.context)),
      JFrameMeaning interpretation operations.frames frame ∧
      interpretation.sub frame.context context
        (FormationSensitiveBasedIdentity.pointSub right witness) semantic ∧
      Judgment assembly.rules context
        (NativeIndexedFamilies.Intrinsic.identityEliminateApp type left motive method right witness)
        (.app (.app motive right) witness) ∧
      interpretation.ty context (.app (.app motive right) witness)
        (C.tySub frame.motive (C.compS frame.comparison.forward semantic)) ∧
      interpretation.term context
        (NativeIndexedFamilies.Intrinsic.identityEliminateApp type left motive method right witness)
        (.app (.app motive right) witness)
        (C.tySub frame.motive (C.compS frame.comparison.forward semantic))
        (C.tmSub (operations.based.elimination.j frame.semanticLeft frame.motive frame.base)
          (C.compS frame.comparison.forward semantic)) := by
  obtain ⟨parameters, rightTyped, witnessTyped, _⟩ :=
    FormationSensitiveBasedIdentity.arguments_of_judgment opacity admitted
  obtain ⟨frame, meaning⟩ := coverage n context type left motive method parameters
  have pointTyped := FormationSensitiveBasedIdentity.pointSub_typed parameters rightTyped witnessTyped
  obtain ⟨semantic, subMeaning⟩ := subTotal (n + 2) n
    frame.context context
    (FormationSensitiveBasedIdentity.pointSub right witness) parameters.1 pointTyped
  have typeMeaning := stable.1 (n + 2) n
    frame.context context
    (FormationSensitiveBasedIdentity.pointSub right witness) semantic _ _
    parameters.1 pointTyped subMeaning meaning.motiveMeaning
  have termMeaning := stable.2 (n + 2) n
    frame.context context
    (FormationSensitiveBasedIdentity.pointSub right witness) semantic _ _ _ _
    parameters.1 pointTyped (FormationSensitiveBasedIdentity.generic_judgment parameters)
    subMeaning meaning.motiveMeaning
    (constructor n context type left motive method frame parameters meaning)
  simp only [FormationSensitiveBasedIdentity.pointSub_genericTerm,
    FormationSensitiveBasedIdentity.pointSub_motiveBody] at typeMeaning termMeaning
  rw [← C.tySub_comp] at typeMeaning
  exact ⟨frame, semantic, meaning, subMeaning,
    FormationSensitiveBasedIdentity.point_judgment parameters rightTyped witnessTyped, typeMeaning,
    termMeaning_transport interpretation (C.tySub_comp _ _ _).symm
      (TypeOver.tmSub_comp_heq _ _ _).symm termMeaning⟩

/-- The native reflexivity redex has the method's meaning. Its judgment,
substitution and computation root come from the actual authored declaration;
its semantic value follows from generic-variable constructor agreement,
the section square, CwF composition and the scoped operation beta law. -/
theorem native_j_beta_meaning
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : Operations C)
    (stable : SharedJudgmentInterpretation.TermSubstitutionStable interpretation)
    (constructor : BasedJMeaning interpretation operations)
    (beta : AdmittedBasedBeta interpretation operations)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      context type left motive method)
    (frame : JFrame interpretation operations.frames context type left motive method)
    (meaning : JFrameMeaning interpretation operations.frames frame) :
    interpretation.term context
      (NativeIndexedFamilies.Intrinsic.identityEliminateApp type left motive method left (.refl left))
      (FormationSensitiveBasedIdentity.methodType left motive)
      (C.tySub frame.motive (operations.based.elimination.reflSection frame.semanticLeft)) frame.base := by
  have generic := constructor n context type left motive method frame parameters meaning
  have substituted := stable (n + 2) n
    frame.context context
    (FormationSensitiveBasedIdentity.reflexivitySub left) frame.reflexivityMap
    (FormationSensitiveBasedIdentity.genericTerm type left motive method)
    (FormationSensitiveBasedIdentity.motiveBody motive)
    (C.tySub frame.motive frame.comparison.forward)
    (C.tmSub (operations.based.elimination.j frame.semanticLeft frame.motive frame.base)
      frame.comparison.forward)
    parameters.1 (FormationSensitiveBasedIdentity.reflexivitySub_typed parameters)
    (FormationSensitiveBasedIdentity.generic_judgment parameters)
    meaning.reflexivityMeaning meaning.motiveMeaning generic
  simp only [FormationSensitiveBasedIdentity.reflexivitySub_genericTerm,
    FormationSensitiveBasedIdentity.reflexivitySub_motiveBody] at substituted
  have typesEqual : C.tySub (C.tySub frame.motive frame.comparison.forward) frame.reflexivityMap =
      C.tySub frame.motive (operations.based.elimination.reflSection frame.semanticLeft) := by
    rw [← C.tySub_comp, meaning.reflexivitySquare]
  have valuesEqual : HEq
      (C.tmSub (C.tmSub (operations.based.elimination.j frame.semanticLeft frame.motive frame.base)
        frame.comparison.forward) frame.reflexivityMap) frame.base := by
    apply (TypeOver.tmSub_comp_heq _ _ _).symm.trans
    rw [meaning.reflexivitySquare]
    exact heq_of_eq (beta n context type left motive method frame parameters meaning)
  exact termMeaning_transport interpretation typesEqual valuesEqual substituted

/-- Actual typed native substitution preserves both sides of the derived
computation square, including the dependent type annotation and value. -/
theorem native_j_beta_substitution
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : Operations C)
    (stable : SharedJudgmentInterpretation.TermSubstitutionStable interpretation)
    (constructor : BasedJMeaning interpretation operations)
    (beta : AdmittedBasedBeta interpretation operations)
    {n m : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {target : SharedJudgmentInterpretation.Context assembly m}
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      context type left motive method)
    (frame : JFrame interpretation operations.frames context type left motive method)
    (meaning : JFrameMeaning interpretation operations.frames frame)
    (sigma : Sub Tower.Head n m) (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx context))
    (formed : ContextFormation assembly.rules target.raw)
    (typed : FormationSensitive.CtxMor assembly.rules context target sigma)
    (substitutionMeaning : interpretation.sub context target sigma semantic) :
    let redex := NativeIndexedFamilies.Intrinsic.identityEliminateApp
      type left motive method left (.refl left)
    let nativeType := FormationSensitiveBasedIdentity.methodType left motive
    let semanticType := C.tySub frame.motive (operations.based.elimination.reflSection frame.semanticLeft)
    Judgment assembly.rules target (subst sigma redex) (subst sigma nativeType) ∧
    Judgment assembly.rules target (subst sigma method) (subst sigma nativeType) ∧
    assembly.rules.computation.step (subst sigma redex) (subst sigma method) ∧
    interpretation.term target (subst sigma redex) (subst sigma nativeType)
      (C.tySub semanticType semantic) (C.tmSub frame.base semantic) ∧
    interpretation.term target (subst sigma method) (subst sigma nativeType)
      (C.tySub semanticType semantic) (C.tmSub frame.base semantic) := by
  dsimp only
  have source := FormationSensitiveBasedIdentity.reflexivity_judgment parameters
  have result := FormationSensitiveBasedIdentity.method_judgment parameters
  refine ⟨source.substitute formed typed, result.substitute formed typed, ?_, ?_, ?_⟩
  · simpa only [Assembly.rules, NativeIndexedFamilies.Intrinsic.subst_identityEliminateApp, subst] using
      FormationSensitiveBasedIdentity.authored_beta assembly.declarations
        (subst sigma type) (subst sigma left) (subst sigma motive) (subst sigma method)
  · exact stable n m context target sigma semantic _ _ _ frame.base formed typed source
      substitutionMeaning meaning.methodTypeMeaning
      (native_j_beta_meaning interpretation operations stable constructor beta parameters frame meaning)
  · exact stable n m context target sigma semantic _ _ _ frame.base formed typed result
      substitutionMeaning meaning.methodTypeMeaning meaning.methodMeaning

/-! ## Operation laws restricted to admitted native meanings -/

def AdmittedPiBeta (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : ContextualTypeOperations.PiOperations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (domain argument : Tower.Tm n)
    (codomain body : Tower.Tm (n + 1)) (family : Family interpretation context domain codomain)
    (semanticBody : C.Tm (C.ext (interpretation.ctx context) family.semanticDomain) family.semanticCodomain)
    (semanticArgument : C.Tm (interpretation.ctx context) family.semanticDomain),
    FamilyAdmitted assembly context domain codomain → FamilyMeaning interpretation family →
    Judgment assembly.rules (.snoc context domain) body codomain →
    Judgment assembly.rules context argument domain →
    interpretation.term family.context body codomain
      (C.tySub family.semanticCodomain family.comparison.forward)
      (C.tmSub semanticBody family.comparison.forward) →
    interpretation.term context argument domain family.semanticDomain semanticArgument →
      operations.app (operations.lam semanticBody) semanticArgument =
        C.tmSub semanticBody (selfExtend C semanticArgument)

def AdmittedSigmaBeta (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : ContextualTypeOperations.SigmaOperations C) : Prop :=
  ∀ (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (domain first second : Tower.Tm n)
    (codomain : Tower.Tm (n + 1)) (family : Family interpretation context domain codomain)
    (semanticFirst : C.Tm (interpretation.ctx context) family.semanticDomain)
    (semanticSecond : C.Tm (interpretation.ctx context)
      (C.tySub family.semanticCodomain (selfExtend C semanticFirst))),
    FamilyAdmitted assembly context domain codomain → FamilyMeaning interpretation family →
    Judgment assembly.rules context first domain →
    Judgment assembly.rules context second (inst0 first codomain) →
    interpretation.term context first domain family.semanticDomain semanticFirst →
    interpretation.term context second (inst0 first codomain)
      (C.tySub family.semanticCodomain (selfExtend C semanticFirst)) semanticSecond →
      operations.fst (operations.pair semanticFirst semanticSecond) = semanticFirst ∧
      HEq (operations.snd (operations.pair semanticFirst semanticSecond)) semanticSecond

/-- Equality/HEq comparison at admitted native substitutions only. This
does not quantify over unnamed ambient motives or impose context equality. -/
def AdmittedBasedSubstitution (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) : Prop :=
  ∀ (n m : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (target : SharedJudgmentInterpretation.Context assembly m)
    (type left motive method : Tower.Tm n)
    (frame : JFrame interpretation operations.frames context type left motive method)
    (sigma : Sub Tower.Head n m)
    (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx context)),
    FormationSensitiveBasedIdentity.Parameters assembly.declarations context type left motive method →
    JFrameMeaning interpretation operations.frames frame → ContextFormation assembly.rules target.raw →
    FormationSensitive.CtxMor assembly.rules context target sigma →
    interpretation.sub context target sigma semantic →
      C.compS (operations.based.reindexing.map semantic frame.semanticLeft)
          (operations.based.elimination.reflSection (C.tmSub frame.semanticLeft semantic)) =
        C.compS (operations.based.elimination.reflSection frame.semanticLeft) semantic ∧
      ∀ reindexedBase : C.Tm (interpretation.ctx target)
          (C.tySub (C.tySub frame.motive (operations.based.reindexing.map semantic frame.semanticLeft))
            (operations.based.elimination.reflSection (C.tmSub frame.semanticLeft semantic))),
        HEq (C.tmSub frame.base semantic) reindexedBase →
        HEq (C.tmSub (operations.based.elimination.j frame.semanticLeft frame.motive frame.base)
          (operations.based.reindexing.map semantic frame.semanticLeft))
          (operations.based.elimination.j (C.tmSub frame.semanticLeft semantic)
            (C.tySub frame.motive (operations.based.reindexing.map semantic frame.semanticLeft)) reindexedBase)

theorem admittedPiBeta_of_full (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : ContextualTypeOperations.PiOperations C) (beta : ContextualTypeOperations.PiBeta operations) :
    AdmittedPiBeta interpretation operations := by
  intro n context domain argument codomain body family semanticBody semanticArgument _ _ _ _ _ _
  exact beta semanticBody semanticArgument

theorem admittedSigmaBeta_of_full (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : ContextualTypeOperations.SigmaOperations C) (beta : ContextualTypeOperations.SigmaBeta operations) :
    AdmittedSigmaBeta interpretation operations := by
  intro n context domain first second codomain family semanticFirst semanticSecond _ _ _ _ _ _
  exact ⟨beta.1 semanticFirst semanticSecond, beta.2 semanticFirst semanticSecond⟩

theorem admittedBasedSubstitution_of_full (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C)
    (square : ContextualBasedIdentityOperations.ReflexivitySquare
      operations.based.elimination operations.based.reindexing)
    (stable : ContextualBasedIdentityOperations.StrictJSubstitution
      operations.based.elimination operations.based.reindexing) :
    AdmittedBasedSubstitution interpretation operations := by
  intro n m context target type left motive method frame sigma semantic _ _ _ _ _
  exact ⟨square semantic frame.semanticLeft,
    fun reindexedBase same => stable semantic frame.semanticLeft frame.motive frame.base reindexedBase same⟩

/-- On the same admitted native substitution as the semantic computation
theorem, reindexing the based context and then taking its reflexivity section
also computes the transported method. This square follows from CwF
composition and the two independently scoped operation laws. -/
theorem admitted_j_reindex_beta
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : Operations C)
    (beta : AdmittedBasedBeta interpretation operations)
    (stable : AdmittedBasedSubstitution interpretation operations)
    {n m : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {target : SharedJudgmentInterpretation.Context assembly m}
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations context type left motive method)
    (frame : JFrame interpretation operations.frames context type left motive method)
    (meaning : JFrameMeaning interpretation operations.frames frame)
    (sigma : Sub Tower.Head n m) (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx context))
    (formed : ContextFormation assembly.rules target.raw)
    (typed : FormationSensitive.CtxMor assembly.rules context target sigma)
    (substitutionMeaning : interpretation.sub context target sigma semantic) :
    HEq (C.tmSub
      (C.tmSub (operations.based.elimination.j frame.semanticLeft frame.motive frame.base)
        (operations.based.reindexing.map semantic frame.semanticLeft))
      (operations.based.elimination.reflSection (C.tmSub frame.semanticLeft semantic)))
      (C.tmSub frame.base semantic) := by
  obtain ⟨square, _⟩ := stable n m context target type left motive method frame sigma semantic
    parameters meaning formed typed substitutionMeaning
  apply (TypeOver.tmSub_comp_heq _ _ _).symm.trans
  rw [square]
  apply (TypeOver.tmSub_comp_heq _ _ _).trans
  rw [beta n context type left motive method frame parameters meaning]

/-! ## Connected admitted-source controls -/

namespace Controls

open NativeIndexedFamilies NativeIndexedFamilies.Intrinsic RussellTarski

def source : Tower.Ctx 4 := contextAXPD

def target : Tower.Ctx 5 := .snoc source (.id (.var 3) (.var 2) (.var 2))

def substitution : Sub Tower.Head 4 5 := renSub wk

theorem parameters (assembly : Assembly) :
    FormationSensitiveBasedIdentity.Parameters assembly.declarations source
      (.var 3) (.var 2) (.var 1) (.var 0) :=
  FormationSensitiveBasedIdentity.canonical_parameters assembly.declarations

theorem target_formed (assembly : Assembly) : ContextFormation assembly.rules target :=
  .snoc (parameters assembly).1
    (.idForm (.var 3) (.sort elementLevel) (.var 2) (.var 2)) (.sort elementLevel)

def sourceContext (assembly : Assembly) : SharedJudgmentInterpretation.Context assembly 4 :=
  ⟨source, (parameters assembly).1⟩

def targetContext (assembly : Assembly) : SharedJudgmentInterpretation.Context assembly 5 :=
  ⟨target, target_formed assembly⟩

theorem substitution_typed (assembly : Assembly) :
    FormationSensitive.CtxMor assembly.rules source target substitution := by
  intro index
  simpa only [target, substitution, subst_renSub, renSub, rename] using
    (Typing.weaken (extension := .id (.var 3) (.var 2) (.var 2))
      (Typing.var (R := assembly.rules) (Γ := source) index))

/-- The family is the actual identity-witness fibre over a variable right
endpoint. Its Pi and Sigma formations use the same admitted family. -/
theorem family_admitted (assembly : Assembly) :
    FamilyAdmitted assembly source (.var 3) (.id (.var 4) (.var 3) (.var 0)) := by
  refine ⟨.sort elementLevel, .sort elementLevel, .sort (.max elementLevel elementLevel),
    ⟨(parameters assembly).1, .var 3⟩, .sort elementLevel, ?_, .sort elementLevel,
    .sorts elementLevel elementLevel⟩
  exact ⟨.snoc (parameters assembly).1 (.var 3) (.sort elementLevel),
    .idForm (.var 4) (.sort elementLevel) (.var 3) (.var 0)⟩

theorem pi_sigma_j_admitted (assembly : Assembly) :
    Judgment assembly.rules source (.pi (.var 3) (.id (.var 4) (.var 3) (.var 0)))
      (sortTm (.max elementLevel elementLevel)) ∧
    Judgment assembly.rules source (.sigma (.var 3) (.id (.var 4) (.var 3) (.var 0)))
      (sortTm (.max elementLevel elementLevel)) ∧
    Judgment assembly.rules
      (FormationSensitiveBasedIdentity.basedContext source (.var 3) (.var 2))
      (FormationSensitiveBasedIdentity.genericTerm (.var 3) (.var 2) (.var 1) (.var 0))
      (FormationSensitiveBasedIdentity.motiveBody (.var 1)) := by
  refine ⟨⟨(parameters assembly).1, ?_⟩, ⟨(parameters assembly).1, ?_⟩,
    FormationSensitiveBasedIdentity.generic_judgment (parameters assembly)⟩
  · exact .piForm (.var 3) (.sort elementLevel)
      (.idForm (.var 4) (.sort elementLevel) (.var 3) (.var 0)) (.sort elementLevel)
      (.sorts elementLevel elementLevel)
  · exact .sigmaForm (.var 3) (.sort elementLevel)
      (.idForm (.var 4) (.sort elementLevel) (.var 3) (.var 0)) (.sort elementLevel)
      (.sorts elementLevel elementLevel)

/-- The admitted generic motive retains its proof argument. Replacing it
by a reflexivity witness changes syntax; no semantic nonconvertibility or
identity principle follows from this syntactic control. -/
theorem motive_retains_path :
    FormationSensitiveBasedIdentity.motiveBody (.var 1 : Tower.Tm 4) ≠
      (.app (.app (.var 3) (.var 1)) (.refl (.var 4)) : Tower.Tm 6) :=
  FormationSensitiveNativeIdentity.endpoint_and_path_remain_in_result

theorem shifted_method_not_newest :
    subst substitution (.var 0 : Tower.Tm 4) = (.var 1 : Tower.Tm 5) ∧
      subst substitution (.var 0 : Tower.Tm 4) ≠ (.var 0 : Tower.Tm 5) :=
  ⟨rfl, by decide⟩

/-- Under the explicitly opaque package, the actual admitted weakened
redex cannot compute to the newly inserted witness instead of its method.
This is an authored-root statement, not nonconvertibility. -/
theorem newest_is_not_method_root (opacity : OpaqueRelatorExtension.Opacity assembly.declarations) :
    ¬ assembly.rules.computation.step (subst substitution identityIotaLeft) (.var 0 : Tower.Tm 5) := by
  intro root
  have inherited := (OpaqueRelatorExtension.root_iff opacity).mp root
  have selected := (FormationSensitiveNativeIdentity.identity_root_iff.mp inherited).2.2
  cases selected

/-- Coverage is used to obtain one shared semantic family, then both
native constructors are interpreted using that same witness. -/
theorem pi_sigma_meanings (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C) (coverage : FamilyCoverage interpretation)
    (products : PiFormationMeaning interpretation operations.products)
    (sums : SigmaFormationMeaning interpretation operations.sums) :
    ∃ family : Family interpretation (sourceContext assembly) (.var 3) (.id (.var 4) (.var 3) (.var 0)),
      FamilyMeaning interpretation family ∧
      interpretation.ty (sourceContext assembly) (.pi (.var 3) (.id (.var 4) (.var 3) (.var 0)))
        (operations.products.pi family.semanticDomain family.semanticCodomain) ∧
      interpretation.ty (sourceContext assembly) (.sigma (.var 3) (.id (.var 4) (.var 3) (.var 0)))
        (operations.sums.sigma family.semanticDomain family.semanticCodomain) := by
  obtain ⟨family, meaning⟩ := coverage 4 (sourceContext assembly) _ _ (family_admitted assembly)
  exact ⟨family, meaning, products 4 (sourceContext assembly) _ _ family (family_admitted assembly) meaning,
    sums 4 (sourceContext assembly) _ _ family (family_admitted assembly) meaning⟩

/-- Independent native-motive and substitution coverage supply the
witnesses. The complete semantic/native square is then derived. The
nonidentity substitution shifts every parameter past a newly admitted
identity witness; neither a closed context nor a constant motive is used.
This is conditional qualification of an inhabited source, not existence
of a common model satisfying the supplied requirements. -/
theorem semantic_control
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : Operations C)
    (coverage : BasedMotiveCoverage interpretation operations.frames)
    (subTotal : SharedJudgmentInterpretation.AdmittedSubstitutionsTotal interpretation)
    (stable : SharedJudgmentInterpretation.SubstitutionStable interpretation)
    (constructor : BasedJMeaning interpretation operations)
    (beta : AdmittedBasedBeta interpretation operations)
    (reindex : AdmittedBasedSubstitution interpretation operations) :
    ∃ (frame : JFrame interpretation operations.frames (sourceContext assembly) (.var 3) (.var 2) (.var 1) (.var 0))
      (semantic : C.Sub (interpretation.ctx (targetContext assembly))
        (interpretation.ctx (sourceContext assembly))),
      JFrameMeaning interpretation operations.frames frame ∧
      interpretation.sub (sourceContext assembly) (targetContext assembly) substitution semantic ∧
      let nativeType := subst substitution (FormationSensitiveBasedIdentity.methodType (.var 2) (.var 1))
      let semanticType := C.tySub frame.motive (operations.based.elimination.reflSection frame.semanticLeft)
      Judgment assembly.rules target (subst substitution identityIotaLeft) nativeType ∧
      Judgment assembly.rules target (.var 1) nativeType ∧
      assembly.rules.computation.step (subst substitution identityIotaLeft) (.var 1) ∧
      interpretation.ty (targetContext assembly) nativeType (C.tySub semanticType semantic) ∧
      interpretation.term (targetContext assembly) (subst substitution identityIotaLeft) nativeType
        (C.tySub semanticType semantic) (C.tmSub frame.base semantic) ∧
      interpretation.term (targetContext assembly) (.var 1) nativeType (C.tySub semanticType semantic)
        (C.tmSub frame.base semantic) ∧
      HEq (C.tmSub
        (C.tmSub (operations.based.elimination.j frame.semanticLeft frame.motive frame.base)
          (operations.based.reindexing.map semantic frame.semanticLeft))
        (operations.based.elimination.reflSection (C.tmSub frame.semanticLeft semantic)))
        (C.tmSub frame.base semantic) := by
  obtain ⟨frame, meaning⟩ := coverage 4 (sourceContext assembly) _ _ _ _ (parameters assembly)
  obtain ⟨semantic, subMeaning⟩ := subTotal 4 5 (sourceContext assembly) (targetContext assembly) substitution
    (target_formed assembly) (substitution_typed assembly)
  obtain ⟨sourceJudgment, methodJudgment, computation, sourceMeaning, methodMeaning⟩ :=
    native_j_beta_substitution interpretation operations stable.2 constructor beta
      (parameters assembly) frame meaning substitution semantic
      (target_formed assembly) (substitution_typed assembly) subMeaning
  exact ⟨frame, semantic, meaning, subMeaning, sourceJudgment, methodJudgment, computation,
    stable.1 4 5 (sourceContext assembly) (targetContext assembly) substitution semantic _ _
      (target_formed assembly) (substitution_typed assembly) subMeaning meaning.methodTypeMeaning,
    sourceMeaning, methodMeaning,
    admitted_j_reindex_beta interpretation operations beta reindex (parameters assembly) frame meaning
      substitution semantic (target_formed assembly) (substitution_typed assembly) subMeaning⟩

/-- The existing empty raw relations satisfy implication-shaped agreement
but fail coverage at the actual admitted native J telescope. They are a
negative control, not a model or a positive qualification witness. -/
theorem empty_raw_agreement_without_coverage (context : C.Ctx) (operations : Operations C) :
    BasedJMeaning (SharedJudgmentInterpretation.emptyRaw assembly C context) operations ∧
      AdmittedBasedBeta (SharedJudgmentInterpretation.emptyRaw assembly C context) operations ∧
      ¬ BasedMotiveCoverage (SharedJudgmentInterpretation.emptyRaw assembly C context) operations.frames := by
  refine ⟨?_, ?_, ?_⟩
  · intro n source type left motive method frame _ meaning
    exact meaning.typeMeaning.elim
  · intro n source type left motive method frame _ meaning
    exact meaning.typeMeaning.elim
  · intro coverage
    obtain ⟨frame, meaning⟩ := coverage 4 (sourceContext assembly) _ _ _ _ (parameters assembly)
    exact meaning.typeMeaning.elim

end Controls

/-- The independently constructed full set-family operations provide the
raw attachment, without asserting any native interpretation relation. -/
def familiesOperations : Operations (familiesCwf.{w}) where
  products := ContextualTypeOperations.Families.products
  sums := ContextualTypeOperations.Families.sums
  identity := ContextualTypeOperations.Families.formation
  reflexivity := ContextualTypeOperations.Families.reflexivity
  based := ContextualBasedIdentityOperations.Families.operations

/-- Full set-family laws imply each scoped operation requirement. Native
constructor agreement, admitted coverage and unbounded universes are not
consequences of this operation-side instance. -/
theorem families_operation_laws (interpretation : SharedJudgmentInterpretation.Data assembly (familiesCwf.{w})) :
    AdmittedPiBeta interpretation familiesOperations.products ∧
    AdmittedSigmaBeta interpretation familiesOperations.sums ∧
    AdmittedBasedBoundary interpretation familiesOperations.frames ∧
    AdmittedBasedBeta interpretation familiesOperations ∧
    AdmittedBasedSubstitution interpretation familiesOperations :=
  ⟨admittedPiBeta_of_full interpretation familiesOperations.products
      ContextualTypeOperations.Families.beta_laws.1,
    admittedSigmaBeta_of_full interpretation familiesOperations.sums
      ContextualTypeOperations.Families.beta_laws.2.1,
    admittedBasedBoundary_of_full interpretation familiesOperations
      ContextualBasedIdentityOperations.Families.boundary,
    admittedBasedBeta_of_full interpretation familiesOperations ContextualBasedIdentityOperations.Families.beta,
    admittedBasedSubstitution_of_full interpretation familiesOperations
      ContextualBasedIdentityOperations.Families.reindexing_laws.2.2
      ContextualBasedIdentityOperations.Families.substitution⟩

#print axioms native_j_beta_meaning
#print axioms native_j_application_meaning
#print axioms native_j_beta_substitution
#print axioms admitted_j_reindex_beta
#print axioms Controls.pi_sigma_j_admitted
#print axioms Controls.semantic_control
#print axioms Controls.empty_raw_agreement_without_coverage
#print axioms Controls.newest_is_not_method_root
#print axioms families_operation_laws

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentTypeInterpretation
