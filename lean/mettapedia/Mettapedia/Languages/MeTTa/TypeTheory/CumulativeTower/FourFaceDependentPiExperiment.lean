import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceBetaExperiment
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareErasureNaturality
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationSignature

/-!
# One genuinely dependent Pi beta law across four faces

This experiment strengthens `FourFaceBetaExperiment` at the first point where
simple arrows are insufficient.  Its intrinsically scoped telescope contains

```text
B : A -> U,  g : (x : A) -> B x,  a : A.
```

The selected redex `(fun x => g x) a` has the instantiated result type `B a`.
Both the contractum and its type therefore require opening the newest binder.
The same two substitutions are checked by the declaration-aware deep GSLT and given an
independent interpretation by ordinary dependent functions and their
set-valued graphs.

The construction is intentionally one canonical dependent cell.  It does not
claim a model of the full cumulative tower or reflection of extensional
equality into judgmental equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FourFaceDependentPiExperiment

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Face 1: a formed intrinsically scoped dependent telescope -/

namespace ScopedDTT

/-- The distinguished ground type in any ambient telescope. -/
def base (arity : Nat) : Presentation.Tower.Tm arity :=
  .head .legacyGround

/-- `B : A -> U 0`. -/
def familyType : Presentation.Tower.Tm 0 :=
  .pi (base 0) (sortTm Presentation.Tower.zero)

def familyTypeLevel : LevelExpr :=
  .max Presentation.Tower.zero (.succ Presentation.Tower.zero)

/-- Telescope containing the dependent family `B`. -/
def contextB : Presentation.Tower.Ctx 1 :=
  .snoc .nil familyType

/-- In context `B`, the section type is `(x : A) -> B x`. -/
def sectionType : Presentation.Tower.Tm 1 :=
  .pi (base 1) (.app (.var 1) (.var 0))

def sectionTypeLevel : LevelExpr :=
  .max Presentation.Tower.zero Presentation.Tower.zero

/-- Telescope containing `B` and `g : (x : A) -> B x`. -/
def contextBG : Presentation.Tower.Ctx 2 :=
  .snoc contextB sectionType

/-- The canonical ambient telescope `B, g, a`. -/
def context : Presentation.Tower.Ctx 3 :=
  .snoc contextBG (base 2)

/-- Under one additional binder `x`, the codomain is `B x`. -/
def bodyType : Presentation.Tower.Tm 4 :=
  .app (.var 3) (.var 0)

/-- Under that binder, the body is `g x`. -/
def body : Presentation.Tower.Tm 4 :=
  .app (.var 2) (.var 0)

def argument : Presentation.Tower.Tm 3 := .var 0

def source : Presentation.Tower.Tm 3 :=
  .app (.lam body) argument

def target : Presentation.Tower.Tm 3 :=
  Presentation.inst0 argument body

def resultType : Presentation.Tower.Tm 3 :=
  Presentation.inst0 argument bodyType

theorem familyType_hasType :
    Presentation.Tower.HasType (.nil : Presentation.Tower.Ctx 0) familyType
      (sortTm familyTypeLevel) := by
  unfold familyType familyTypeLevel base
  exact .piForm
    (.headType .legacyGround) (.sort Presentation.Tower.zero)
    (.headType (.sort Presentation.Tower.zero))
      (.sort (.succ Presentation.Tower.zero))
    (.sorts Presentation.Tower.zero (.succ Presentation.Tower.zero))

def contextBWellFormed :
    ContextWellFormed Presentation.Tower.rules contextB :=
  .snoc .nil familyType_hasType (.sort familyTypeLevel)

theorem sectionType_hasType :
    Presentation.Tower.HasType contextB sectionType
      (sortTm sectionTypeLevel) := by
  unfold sectionType sectionTypeLevel
  apply Presentation.HasType.piForm
  · exact .headType .legacyGround
  · exact .sort Presentation.Tower.zero
  · have familyApplication := Presentation.HasType.appElim
      (Presentation.HasType.var (R := Presentation.Tower.rules)
        (Γ := .snoc contextB (base 1)) 1)
      (Presentation.HasType.var (R := Presentation.Tower.rules)
        (Γ := .snoc contextB (base 1)) 0)
    change Presentation.Tower.HasType (.snoc contextB (base 1))
      (.app (.var 1) (.var 0)) (sortTm Presentation.Tower.zero) at familyApplication
    exact familyApplication
  · exact .sort Presentation.Tower.zero
  · exact .sorts Presentation.Tower.zero Presentation.Tower.zero

def contextBGWellFormed :
    ContextWellFormed Presentation.Tower.rules contextBG :=
  .snoc contextBWellFormed sectionType_hasType (.sort sectionTypeLevel)

def contextWellFormed :
    ContextWellFormed Presentation.Tower.rules context := by
  apply ContextWellFormed.snoc
  · exact contextBGWellFormed
  · exact .headType .legacyGround
  · exact .sort Presentation.Tower.zero

theorem body_hasType :
    Presentation.Tower.HasType (.snoc context (base 3)) body bodyType := by
  have application := Presentation.HasType.appElim
    (Presentation.HasType.var (R := Presentation.Tower.rules)
      (Γ := .snoc context (base 3)) 2)
    (Presentation.HasType.var (R := Presentation.Tower.rules)
      (Γ := .snoc context (base 3)) 0)
  change Presentation.Tower.HasType (.snoc context (base 3)) body bodyType at application
  exact application

theorem argument_hasType :
    Presentation.Tower.HasType context argument (base 3) := by
  simpa [context, contextBG, contextB, sectionType, familyType, base,
    argument, Presentation.Ctx.lookup, Presentation.rename] using
      (Presentation.HasType.var (R := Presentation.Tower.rules)
        (Γ := context) 0)

/-- Scoped dependent beta and subject reduction instantiate the same
codomain `B x` with the same argument `a`. -/
theorem typedBeta :
    StepCore Presentation.Tower.rules.computation
        Presentation.Tower.rules.headEq source target ∧
      Presentation.Tower.HasType context source resultType ∧
      Presentation.Tower.HasType context target resultType := by
  exact Presentation.HasType.typedBeta body_hasType argument_hasType

@[simp] theorem target_eq_section_argument :
    target = .app (.var 1) (.var 0) :=
  rfl

@[simp] theorem resultType_eq_family_argument :
    resultType = .app (.var 2) (.var 0) :=
  rfl

/-- Dependency is syntactically visible: the opened result type mentions both
the family and the selected argument. -/
theorem resultType_is_not_closed_ground :
    resultType ≠ base 3 := by
  intro equality
  cases equality

/-- The computational event is not raw syntactic equality. -/
theorem source_ne_target : source ≠ target := by
  intro equality
  cases equality

end ScopedDTT

/-! ## Face 2: declaration-aware term and codomain substitution -/

namespace DeepGSLT

open ScopedDTT
open DeclarationAwarePatternCodec
open DeclarationAwareSubstitutionCompiler
open DeclarationAwareSubstitutionLanguage

def rawBody : DeclarationAwareSubstitutionCompiler.RawTerm :=
  DeclarationAwareSubstitutionSemantics.erase body

def rawBodyType : DeclarationAwareSubstitutionCompiler.RawTerm :=
  DeclarationAwareSubstitutionSemantics.erase bodyType

def rawArgument : DeclarationAwareSubstitutionCompiler.RawTerm :=
  DeclarationAwareSubstitutionSemantics.erase argument

def rawTarget : DeclarationAwareSubstitutionCompiler.RawTerm :=
  DeclarationAwareSubstitutionSemantics.erase target

def rawResultType : DeclarationAwareSubstitutionCompiler.RawTerm :=
  DeclarationAwareSubstitutionSemantics.erase resultType

/-- The independently defined raw substitution computes the scoped
contractum's erasure.  This is an instance of the generic erasure-naturality
theorem, rather than a reduction peculiar to this example. -/
@[simp] theorem term_substitution_commutes :
    substituteRaw 0 rawArgument rawBody = rawTarget := by
  exact
    (DeclarationAwareErasureNaturality.erase_inst0 argument body).symm

/-- Dependency is retained by a second commuting square: opening the body
type computes the erasure of `B a`.  The same generic theorem governs terms
and types because both are terms of the scoped tower syntax. -/
@[simp] theorem type_substitution_commutes :
    substituteRaw 0 rawArgument rawBodyType = rawResultType := by
  exact
    (DeclarationAwareErasureNaturality.erase_inst0 argument bodyType).symm

def targetPattern : Pattern := encodeRaw rawTarget

def resultTypePattern : Pattern := encodeRaw rawResultType

def termGoal (candidate : Pattern) : Pattern :=
  rootBeta
    (tmApp (tmLam (encodeRaw rawBody)) (encodeRaw rawArgument))
    candidate

def typeGoal (candidate : Pattern) : Pattern :=
  substitutesAt (encodeNat 0) (encodeRaw rawArgument)
    (encodeRaw rawBodyType) candidate

/-- The declaration-aware generic checker accepts the dependent contractum. -/
theorem term_checked :
    checkRaw DeclarationAwareSubstitutionLanguage.definition
      (termGoal targetPattern) (betaRawProof rawBody rawArgument) = true := by
  unfold termGoal targetPattern
  rw [← term_substitution_commutes]
  exact betaRawProof_accepts rawBody rawArgument

/-- The declaration-aware generic checker independently accepts the instantiated
codomain. -/
theorem type_checked :
    checkRaw DeclarationAwareSubstitutionLanguage.definition
      (typeGoal resultTypePattern)
      (substituteRawProof 0 rawArgument rawBodyType) = true := by
  unfold typeGoal resultTypePattern
  rw [← type_substitution_commutes]
  exact substituteRawProof_accepts 0 rawArgument rawBodyType

/-- Any accepted term certificate for this source names exactly the scoped
contractum's erasure. -/
theorem term_no_invention {candidate : Pattern} {proof : RawProof}
    (accepted : checkRaw DeclarationAwareSubstitutionLanguage.definition
      (termGoal candidate) proof = true) :
    candidate = targetPattern := by
  have reflected :=
    DeclarationAwareSubstitutionReflection.checkRaw_beta_reflects
      rawBody rawArgument accepted
  calc
    candidate = encodeRaw (substituteRaw 0 rawArgument rawBody) := reflected
    _ = targetPattern := by rw [term_substitution_commutes]; rfl

/-- Any accepted codomain certificate names exactly `B a`. -/
theorem type_no_invention {candidate : Pattern} {proof : RawProof}
    (accepted : checkRaw DeclarationAwareSubstitutionLanguage.definition
      (typeGoal candidate) proof = true) :
    candidate = resultTypePattern := by
  have reflected :=
    DeclarationAwareSubstitutionReflection.checkRaw_substitution_reflects
      0 rawArgument rawBodyType accepted
  calc
    candidate = encodeRaw (substituteRaw 0 rawArgument rawBodyType) := reflected
    _ = resultTypePattern := by rw [type_substitution_commutes]; rfl

def changedTermPattern : Pattern := encodeRaw (.lam rawBody)

def changedTypePattern : Pattern :=
  encodeRaw (.head (.sort Presentation.Tower.zero))

theorem changedTermPattern_ne : changedTermPattern ≠ targetPattern := by
  simp [changedTermPattern, targetPattern, rawBody, rawTarget, body, target,
    argument, Presentation.inst0, Presentation.subst,
    Presentation.subst0, DeclarationAwareSubstitutionSemantics.erase, encodeRaw,
    DeclarationAwareSubstitutionSemantics.encode]

theorem changedTypePattern_ne : changedTypePattern ≠ resultTypePattern := by
  unfold changedTypePattern resultTypePattern rawResultType
  rw [ScopedDTT.resultType_eq_family_argument]
  simp [DeclarationAwareSubstitutionSemantics.erase, encodeRaw,
    DeclarationAwareSubstitutionSemantics.encode]

theorem changed_term_rejected :
    checkRaw DeclarationAwareSubstitutionLanguage.definition
      (termGoal changedTermPattern) (betaRawProof rawBody rawArgument) =
        false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  exact changedTermPattern_ne
    (betaRawProof_no_invention rawBody rawArgument accepted)

theorem changed_type_rejected :
    checkRaw DeclarationAwareSubstitutionLanguage.definition
      (typeGoal changedTypePattern)
        (substituteRawProof 0 rawArgument rawBodyType) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  exact changedTypePattern_ne
    (substituteRawProof_no_invention 0 rawArgument rawBodyType accepted)

end DeepGSLT

/-! ## Faces 3 and 4: dependent functions and set-valued graphs -/

namespace ExtensionalFaces

universe u v

/-- An independent extensional interpretation of the selected telescope.
The family may genuinely vary with its base argument. -/
structure Model where
  Base : Type u
  Fiber : Base → Type v
  dependentFunction : (value : Base) → Fiber value

/-- The shallow interpretation of the lambda body. -/
def etaSection (model : Model.{u, v}) :
    (value : model.Base) → model.Fiber value :=
  fun value => model.dependentFunction value

def sourceAt (model : Model.{u, v}) (argument : model.Base) :
    model.Fiber argument :=
  etaSection model argument

def targetAt (model : Model.{u, v}) (argument : model.Base) :
    model.Fiber argument :=
  model.dependentFunction argument

/-- HOL-shaped shallow validity in every dependent-family interpretation. -/
def ShallowValid : Prop :=
  ∀ (model : Model.{u, v}) (argument : model.Base),
    sourceAt model argument = targetAt model argument

/-- The graph of a dependent section lives in the corresponding dependent
sum. -/
def sectionGraph (model : Model.{u, v})
    (candidate : (value : model.Base) → model.Fiber value) :
    Set (Sigma model.Fiber) :=
  { point | point.2 = candidate point.1 }

/-- Equality of dependent graphs is exactly pointwise equality of sections. -/
theorem sectionGraph_eq_iff (model : Model.{u, v})
    (left right : (value : model.Base) → model.Fiber value) :
    sectionGraph model left = sectionGraph model right ↔
      ∀ value, left value = right value := by
  constructor
  · intro graphsEqual value
    have member : (Sigma.mk value (left value)) ∈ sectionGraph model left := rfl
    rw [graphsEqual] at member
    exact member
  · intro pointwise
    ext point
    simp only [sectionGraph, Set.mem_setOf_eq]
    constructor
    · intro equalLeft
      exact equalLeft.trans (pointwise point.1)
    · intro equalRight
      exact equalRight.trans (pointwise point.1).symm

/-- Set/HOTG-shaped validity of the same dependent function. -/
def SetGraphValid : Prop :=
  ∀ model : Model.{u, v},
    sectionGraph model (etaSection model) =
      sectionGraph model model.dependentFunction

theorem shallow_iff_setGraph :
    ShallowValid.{u, v} ↔ SetGraphValid.{u, v} := by
  constructor
  · intro valid model
    apply (sectionGraph_eq_iff model _ _).2
    intro value
    simpa [sourceAt, targetAt] using valid model value
  · intro valid model
    have pointwise := (sectionGraph_eq_iff model _ _).1 (valid model)
    intro value
    simpa [sourceAt, targetAt] using pointwise value

theorem dependent_shallow_valid : ShallowValid.{u, v} :=
  fun _model _argument => rfl

theorem dependent_setGraph_valid : SetGraphValid.{u, v} :=
  shallow_iff_setGraph.mp dependent_shallow_valid

/-- A concrete model whose result family is not constant: the false fibre is
`Unit`, while the true fibre is `Bool`. -/
def varyingModel : Model where
  Base := Bool
  Fiber := fun flag => if flag then Bool else Unit
  dependentFunction := fun flag =>
    match flag with
    | false => ()
    | true => true

theorem varying_fibres_have_distinct_subsingleton_status :
    Subsingleton (varyingModel.Fiber false) ∧
      ¬ Subsingleton (varyingModel.Fiber true) := by
  constructor
  · change Subsingleton Unit
    infer_instance
  · change ¬ Subsingleton Bool
    intro singleton
    have impossible : true = false := @Subsingleton.elim Bool singleton true false
    cases impossible

theorem varying_model_graph_valid :
    sectionGraph varyingModel (etaSection varyingModel) =
      sectionGraph varyingModel varyingModel.dependentFunction :=
  dependent_setGraph_valid varyingModel

/-- Extensional validity does not identify raw intensional syntax: the beta
redex and contractum have equal meaning in every dependent-family model but
remain different syntax trees. -/
theorem extensional_validity_not_raw_reflection :
    ShallowValid.{u, v} ∧ ScopedDTT.source ≠ ScopedDTT.target :=
  ⟨dependent_shallow_valid, ScopedDTT.source_ne_target⟩

end ExtensionalFaces

/-! ## A NIK authority for the dependent cell -/

namespace NIKProfile

open ScopedDTT
open DeepGSLT
open ExtensionalFaces
open DeclarationAwareSubstitutionCompiler

/-- A dependent beta answer retains both the term and its instantiated type. -/
structure Candidate where
  term : Pattern
  type : Pattern
  deriving DecidableEq, Repr

/-- Replay requires separate source derivations for term opening and
codomain opening. -/
structure Certificate where
  termProof : RawProof
  typeProof : RawProof

def canonicalCandidate : Candidate where
  term := targetPattern
  type := resultTypePattern

def canonicalCertificate : Certificate where
  termProof := betaRawProof rawBody rawArgument
  typeProof := substituteRawProof 0 rawArgument rawBodyType

/-- Intrinsic scope retains exact target identity, a formed telescope, the
scoped computation step, and typing of both endpoints at the opened
codomain. -/
structure IntrinsicScope (candidate : Candidate) : Prop where
  term_exact : candidate.term = targetPattern
  type_exact : candidate.type = resultTypePattern
  formed : ContextWellFormed Presentation.Tower.rules context
  computation : StepCore Presentation.Tower.rules.computation
    Presentation.Tower.rules.headEq source target
  source_typed : Presentation.Tower.HasType context source resultType
  target_typed : Presentation.Tower.HasType context target resultType

def canonicalScope : IntrinsicScope canonicalCandidate where
  term_exact := rfl
  type_exact := rfl
  formed := contextWellFormed
  computation := typedBeta.1
  source_typed := typedBeta.2.1
  target_typed := typedBeta.2.2

/-- Independent meaning is extensional validity in every selected universe,
not possession of either source certificate. -/
def Meaning.{u, v} (candidate : Candidate) : Prop :=
  candidate = canonicalCandidate ∧
    ShallowValid.{u, v} ∧ SetGraphValid.{u, v}

def theory.{u, v} : TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _ => ()
  Claim := fun _ => Candidate
  Scope := fun _ => IntrinsicScope
  Meaning := fun _ => Meaning.{u, v}
  scope_sound := by
    intro _kind candidate intrinsic
    refine ⟨?_, dependent_shallow_valid, dependent_setGraph_valid⟩
    cases candidate
    simp only [canonicalCandidate, Candidate.mk.injEq]
    exact ⟨intrinsic.term_exact, intrinsic.type_exact⟩

/-- Both independently declared judgments must accept. -/
def checker : Checker Candidate Certificate where
  check candidate certificate :=
    checkRaw DeclarationAwareSubstitutionLanguage.definition
        (termGoal candidate.term) certificate.termProof &&
      checkRaw DeclarationAwareSubstitutionLanguage.definition
        (typeGoal candidate.type) certificate.typeProof

theorem checker_authority : checker.Authority IntrinsicScope where
  sound := by
    intro candidate certificate accepted
    have acceptedParts :
        checkRaw DeclarationAwareSubstitutionLanguage.definition
            (termGoal candidate.term) certificate.termProof = true ∧
          checkRaw DeclarationAwareSubstitutionLanguage.definition
            (typeGoal candidate.type) certificate.typeProof = true := by
      simpa only [checker, Bool.and_eq_true] using accepted
    exact
      { term_exact := term_no_invention acceptedParts.1
        type_exact := type_no_invention acceptedParts.2
        formed := contextWellFormed
        computation := typedBeta.1
        source_typed := typedBeta.2.1
        target_typed := typedBeta.2.2 }
  complete := by
    intro candidate intrinsic
    refine ⟨canonicalCertificate, ?_⟩
    simp only [checker, canonicalCertificate, Bool.and_eq_true]
    constructor
    · simpa only [intrinsic.term_exact] using term_checked
    · simpa only [intrinsic.type_exact] using type_checked

def contract.{u, v} : AuthorityContract theory.{u, v} where
  Certificate := fun _ => Certificate
  checker := fun _ => checker
  scopeAuthority := fun _ => checker_authority

/-- Accepted artifacts project through intrinsic typing to both independent
extensional faces. -/
theorem accepted_has_dependent_meaning.{u, v}
    (candidate : Candidate) (certificate : Certificate)
    (accepted : (contract.{u, v}.checker ()).check candidate certificate = true) :
    Meaning.{u, v} candidate :=
  (contract.{u, v}.projection ()).sound candidate certificate accepted

theorem canonical_certificate_replays :
    checker.check canonicalCandidate canonicalCertificate = true := by
  simpa only [checker, canonicalCandidate, canonicalCertificate,
    Bool.and_eq_true] using And.intro term_checked type_checked

def wrongTermCandidate : Candidate where
  term := changedTermPattern
  type := resultTypePattern

def wrongTypeCandidate : Candidate where
  term := targetPattern
  type := changedTypePattern

theorem wrongTermCandidate_outside_scope :
    ¬ IntrinsicScope wrongTermCandidate := by
  intro intrinsic
  exact changedTermPattern_ne intrinsic.term_exact

theorem wrongTypeCandidate_outside_scope :
    ¬ IntrinsicScope wrongTypeCandidate := by
  intro intrinsic
  exact changedTypePattern_ne intrinsic.type_exact

theorem wrongTermCandidate_not_meaning.{u, v} :
    ¬ Meaning.{u, v} wrongTermCandidate := by
  intro meaningful
  have exactCandidate := congrArg Candidate.term meaningful.1
  exact changedTermPattern_ne
    (by simpa [wrongTermCandidate, canonicalCandidate] using exactCandidate)

theorem wrongTypeCandidate_not_meaning.{u, v} :
    ¬ Meaning.{u, v} wrongTypeCandidate := by
  intro meaningful
  have exactCandidate := congrArg Candidate.type meaningful.1
  exact changedTypePattern_ne
    (by simpa [wrongTypeCandidate, canonicalCandidate] using exactCandidate)

/-- No choice of the second proof can compensate for a wrong term target. -/
theorem wrong_term_rejected (certificate : Certificate) :
    checker.check wrongTermCandidate certificate = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  exact wrongTermCandidate_outside_scope
    (checker_authority.sound wrongTermCandidate certificate accepted)

/-- No choice of the first proof can compensate for a wrong instantiated
codomain. -/
theorem wrong_type_rejected (certificate : Certificate) :
    checker.check wrongTypeCandidate certificate = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  exact wrongTypeCandidate_outside_scope
    (checker_authority.sound wrongTypeCandidate certificate accepted)

end NIKProfile

/-! ## Axiom audit -/

#print axioms ScopedDTT.familyType_hasType
#print axioms ScopedDTT.sectionType_hasType
#print axioms ScopedDTT.contextWellFormed
#print axioms ScopedDTT.body_hasType
#print axioms ScopedDTT.typedBeta
#print axioms ScopedDTT.resultType_is_not_closed_ground
#print axioms DeepGSLT.term_checked
#print axioms DeepGSLT.type_checked
#print axioms DeepGSLT.term_no_invention
#print axioms DeepGSLT.type_no_invention
#print axioms DeepGSLT.changed_term_rejected
#print axioms DeepGSLT.changed_type_rejected
#print axioms ExtensionalFaces.sectionGraph_eq_iff
#print axioms ExtensionalFaces.shallow_iff_setGraph
#print axioms ExtensionalFaces.varying_fibres_have_distinct_subsingleton_status
#print axioms ExtensionalFaces.varying_model_graph_valid
#print axioms ExtensionalFaces.extensional_validity_not_raw_reflection
#print axioms NIKProfile.checker_authority
#print axioms NIKProfile.accepted_has_dependent_meaning
#print axioms NIKProfile.canonical_certificate_replays
#print axioms NIKProfile.wrongTermCandidate_not_meaning
#print axioms NIKProfile.wrongTypeCandidate_not_meaning
#print axioms NIKProfile.wrong_term_rejected
#print axioms NIKProfile.wrong_type_rejected

end FourFaceDependentPiExperiment
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
