import Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
import Mettapedia.OSLF.Framework.WMCalculusCombinedPresentationSignature

/-!
# Relational model of the structural combined WM presentation

The directed and structural presentations share constructors but not their
operational rules. A structural intrinsic term is interpreted when transport
back to the directed constructor signature has a first-order interpretation
certificate. Keeping that certificate existential makes the result an honest
relation, not an asserted total function on generic lambda/collection forms.

Supported substitution preserves and reflects each model value through the
context-preserving same-terms signature map. This does not reflect support
without an initially supported source term or establish full equation-modulo
subject reduction.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralRelationalModel

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
open Mettapedia.OSLF.Framework.WMCalculusCombinedPresentationSignature
open Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralPresentation
open Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef

set_option autoImplicit false

private abbrev StructuralSignature := signatureOf combinedStructuralLanguageDef

private theorem congrArgThree {A B C D : Type} (function : A → B → C → D)
    {a a' : A} {b b' : B} {c c' : C}
    (first : a = a') (second : b = b') (third : c = c') :
    function a b c = function a' b' c' := by
  cases first
  cases second
  cases third
  rfl

/-- A structural-presentation term denotes a value only when its transported
constructor term carries an explicit interpretation certificate. This is a
proof-relevant *support* condition whose existential image is Prop-valued. -/
def Denotes {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature} {sort : TypeExpr}
    (term : Term StructuralSignature Γ sort)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (value : Carrier State Query Ev Ov Scope sort) : Prop :=
  ∃ certificate : FirstOrder
      (transportSameTerms same_authored_constructors.symm term),
    FirstOrder.denote reading environment certificate = value

/-- A supported structural term has at most one value in a fixed reading and
environment, independently of which first-order certificate establishes its
support. Generic binder and collection terms may remain unsupported. -/
theorem denotes_functional {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature} {sort : TypeExpr}
    (term : Term StructuralSignature Γ sort)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (firstValue secondValue : Carrier State Query Ev Ov Scope sort)
    (firstDenotes : Denotes reading term environment firstValue)
    (secondDenotes : Denotes reading term environment secondValue) :
    firstValue = secondValue := by
  obtain ⟨firstCertificate, firstCorrect⟩ := firstDenotes
  obtain ⟨secondCertificate, secondCorrect⟩ := secondDenotes
  exact firstCorrect.symm.trans
    ((denote_heq_of_erase_eq reading environment firstCertificate
      secondCertificate rfl).eq.trans secondCorrect)

/-- The domain of the structural model is exactly the existing first-order
support certificate. On that domain the relational value exists uniquely;
this is semantic functionality, not a decision procedure for support. -/
theorem denotes_existsUnique_iff_supported {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature} {sort : TypeExpr}
    (term : Term StructuralSignature Γ sort)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ) :
    (∃! value : Carrier State Query Ev Ov Scope sort,
      Denotes reading term environment value) ↔
      Nonempty (FirstOrder
        (transportSameTerms same_authored_constructors.symm term)) := by
  constructor
  · rintro ⟨_, ⟨certificate, _⟩, _⟩
    exact ⟨certificate⟩
  · rintro ⟨certificate⟩
    refine ⟨FirstOrder.denote reading environment certificate,
      ⟨certificate, rfl⟩, ?_⟩
    intro other otherDenotes
    exact (denotes_functional reading term environment _ _
      ⟨certificate, rfl⟩ otherDenotes).symm

/-- Once a structural evidence term has a first-order certificate, its
presentation-independent relational denotation is exactly the established
dependent evidence fibre of that certificate. The equivalence does not
select a canonical certificate or extend the interpretation domain. -/
theorem denotes_iff_evidenceFibre_of_certificate
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (term : Term StructuralSignature Γ (.base "BinaryEvidence"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (certificate : FirstOrder
      (transportSameTerms same_authored_constructors.symm term))
    (value : Ev) :
    Denotes reading term environment value ↔
      EvidenceFibre reading certificate value environment := by
  constructor
  · intro actual
    have chosen : Denotes reading term environment
        (FirstOrder.denote reading environment certificate) :=
      ⟨certificate, rfl⟩
    have equal := denotes_functional reading term environment value
      (FirstOrder.denote reading environment certificate) actual chosen
    exact equal.symm
  · intro equal
    exact ⟨certificate, equal⟩

/-- A common value is an all-value relational equivalence when each
supported term has certificate-independent denotation. -/
theorem denotes_iff_of_common_value {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature} {sort : TypeExpr}
    (first second : Term StructuralSignature Γ sort)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (common : ∃ witness : Carrier State Query Ev Ov Scope sort,
      Denotes reading first environment witness ∧
      Denotes reading second environment witness)
    (value : Carrier State Query Ev Ov Scope sort) :
    Denotes reading first environment value ↔
      Denotes reading second environment value := by
  obtain ⟨witness, firstDenotes, secondDenotes⟩ := common
  constructor
  · intro actual
    have equal := denotes_functional reading first environment value witness
      actual firstDenotes
    subst value
    exact secondDenotes
  · intro actual
    have equal := denotes_functional reading second environment value witness
      actual secondDenotes
    subst value
    exact firstDenotes

/-- Two supported intrinsic presentations of the same raw pattern have
exactly the same model answers. Both support certificates are essential: raw
erasure equality by itself does not interpret generic representation forms. -/
theorem denotes_iff_of_same_erasure_and_support
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature} {sort : TypeExpr}
    (first second : Term StructuralSignature Γ sort)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (sameErasure : erase first = erase second)
    (firstSupported : Nonempty (FirstOrder
      (transportSameTerms same_authored_constructors.symm first)))
    (secondSupported : Nonempty (FirstOrder
      (transportSameTerms same_authored_constructors.symm second)))
    (value : Carrier State Query Ev Ov Scope sort) :
    Denotes reading first environment value ↔
      Denotes reading second environment value := by
  obtain ⟨firstCertificate⟩ := firstSupported
  obtain ⟨secondCertificate⟩ := secondSupported
  have sameDirected :
      erase (transportSameTerms same_authored_constructors.symm first) =
        erase (transportSameTerms same_authored_constructors.symm second) := by
    simpa only [erase_transportSameTerms] using sameErasure
  have equalValues :=
    (denote_heq_of_erase_eq reading environment firstCertificate
      secondCertificate sameDirected).eq
  apply denotes_iff_of_common_value reading first second environment
    ⟨FirstOrder.denote reading environment firstCertificate,
      ⟨firstCertificate, rfl⟩, ⟨secondCertificate, equalValues.symm⟩⟩

/-- Structural substitutions are transported back to the directed signature
without changing either context or the result sort. -/
def directedSubstitution {Γ Δ : Ctx StructuralSignature}
    (sigma : Sub StructuralSignature Γ Δ) :
    Sub Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport.CombinedSignature
      Γ Δ :=
  fun sort position =>
    transportSameTerms same_authored_constructors.symm (sigma sort position)

/-- A target substitution is supported when every variable image is
interpretable after transport. This is the real extra hypothesis needed for
semantic reindexing; arbitrary signature terms need not satisfy it. -/
def SupportedSubstitution {Γ Δ : Ctx StructuralSignature}
    (sigma : Sub StructuralSignature Γ Δ) : Type :=
  ∀ (sort : TypeExpr) (position : Var Γ sort),
    FirstOrder (directedSubstitution sigma sort position)

/-- Forward substitution soundness on the exact supported image. It is not
an equivalence for arbitrary target terms or a compiler-extraction theorem. -/
theorem denotes_substitution_forward {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx StructuralSignature}
    (sigma : Sub StructuralSignature Γ Δ)
    (supported : SupportedSubstitution sigma)
    {sort : TypeExpr}
    (term : Term StructuralSignature Γ sort)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    (value : Carrier State Query Ev Ov Scope sort)
    (original : Denotes reading term
      (reindexEnvironment reading (directedSubstitution sigma) supported environment)
      value) :
    Denotes reading (bind sigma term) environment value := by
  obtain ⟨certificate, correct⟩ := original
  unfold Denotes
  rw [transportSameTerms_bind]
  refine ⟨FirstOrder.substitute (directedSubstitution sigma) supported
    certificate, ?_⟩
  exact (denote_substitute reading (directedSubstitution sigma)
    supported environment certificate).trans correct

/-- On a source term known to have an authored first-order interpretation,
structural substitution preserves and reflects the *exact* model value.
This is conditional on source support; it does not infer support for arbitrary
generic representation forms from a supported substituted term. -/
theorem denotes_substitution_iff_of_supported
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx StructuralSignature}
    (sigma : Sub StructuralSignature Γ Δ)
    (supported : SupportedSubstitution sigma)
    {sort : TypeExpr}
    (term : Term StructuralSignature Γ sort)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    (sourceSupported : ∃ sourceValue : Carrier State Query Ev Ov Scope sort,
      Denotes reading term
        (reindexEnvironment reading (directedSubstitution sigma)
          supported environment) sourceValue)
    (value : Carrier State Query Ev Ov Scope sort) :
    Denotes reading (bind sigma term) environment value ↔
      Denotes reading term
        (reindexEnvironment reading (directedSubstitution sigma)
          supported environment) value := by
  obtain ⟨sourceValue, sourceDenotes⟩ := sourceSupported
  have targetDenotes := denotes_substitution_forward reading sigma supported
    term environment sourceValue sourceDenotes
  constructor
  · intro actual
    have equal := denotes_functional reading (bind sigma term)
      environment value sourceValue actual targetDenotes
    subst value
    exact sourceDenotes
  · intro actual
    have equal := denotes_functional reading term
      (reindexEnvironment reading (directedSubstitution sigma)
        supported environment)
      value sourceValue actual sourceDenotes
    subst value
    exact targetDenotes

/-- Variables of declared sorts give actual witnesses; the relation is not
empty by definition. -/
theorem variable_denotes {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature} {sort : TypeExpr}
    (position : Var Γ sort)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ) :
    Denotes reading (.var position) environment (environment sort position) := by
  refine ⟨FirstOrder.variable position, rfl⟩

/-- An intrinsically typed structural variable has exactly the environment
value at its context position, regardless of its first-order certificate. -/
theorem variable_denotes_iff {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature} {sort : TypeExpr}
    (position : Var Γ sort)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (value : Carrier State Query Ev Ov Scope sort) :
    Denotes reading (.var position) environment value ↔
      value = environment sort position := by
  constructor
  · rintro ⟨certificate, correct⟩
    have shape : erase
        (transportSameTerms same_authored_constructors.symm
          (Term.var position : Term StructuralSignature Γ sort)) =
        .bvar (variableIndex position) := rfl
    exact correct.symm.trans
      (variable_erasure_denote reading environment position certificate shape).eq
  · intro equal
    subst value
    exact variable_denotes reading position environment

/-- The structural presentation contains a closed authored evidence term;
its denotation is not supplied merely by the variable case. -/
def evidenceZero {Γ : Ctx StructuralSignature} :
    Term StructuralSignature Γ (.base "BinaryEvidence") :=
  .op (Operator.ofSameTerms same_authored_constructors combinedZeroOperator) .nil

/-- A generic substitution former can have the authored evidence result
sort without being an authored WM constructor. -/
def genericEvidenceSubst :
    Term StructuralSignature [] (.base "BinaryEvidence") :=
  .op (.subst (.base "BinaryEvidence") (.base "BinaryEvidence"))
    (.cons (.var .zero) (.cons evidenceZero .nil))

theorem genericEvidenceSubst_not_denotes {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) [])
    (value : Ev) :
    ¬ Denotes reading genericEvidenceSubst environment value := by
  rintro ⟨certificate, _⟩
  have shape : erase
      (transportSameTerms same_authored_constructors.symm
        genericEvidenceSubst) = .subst (.bvar 0) pEvidenceZero := rfl
  exact subst_erasure_not_FirstOrder certificate _ _ shape

/-- The negative support boundary is non-vacuous in the concrete count
reading: natural-number evidence values exist, but this generic form has no
WM denotation there. -/
theorem counting_genericEvidenceSubst_not_denotes :
    ¬ Denotes countingCombined genericEvidenceSubst
      (fun _ position => nomatch position) (0 : Nat) := by
  exact genericEvidenceSubst_not_denotes countingCombined _ 0

/-- The structural constructor for combining two evidence terms. -/
def evidenceCombine {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "BinaryEvidence")) :
    Term StructuralSignature Γ (.base "BinaryEvidence") :=
  .op (Operator.ofSameTerms same_authored_constructors combinedCombineOperator)
    (.cons first (.cons second .nil))

def stateRevise {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "State")) :
    Term StructuralSignature Γ (.base "State") :=
  .op (Operator.ofSameTerms same_authored_constructors combinedReviseOperator)
    (.cons first (.cons second .nil))

def queryExtract {Γ : Ctx StructuralSignature}
    (world : Term StructuralSignature Γ (.base "State"))
    (query : Term StructuralSignature Γ (.base "Query")) :
    Term StructuralSignature Γ (.base "BinaryEvidence") :=
  .op (Operator.ofSameTerms same_authored_constructors combinedExtractOperator)
    (.cons world (.cons query .nil))

def stateOverlapMerge {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "State")) :
    Term StructuralSignature Γ (.base "State") :=
  .op (Operator.ofSameTerms same_authored_constructors overlapMergeOperator)
    (.cons first (.cons second .nil))

def queryOverlapFactor {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "State"))
    (query : Term StructuralSignature Γ (.base "Query")) :
    Term StructuralSignature Γ (.base "Overlap") :=
  .op (Operator.ofSameTerms same_authored_constructors overlapFactorOperator)
    (.cons first (.cons second (.cons query .nil)))

def evidenceOverlapCorrect {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "BinaryEvidence"))
    (factor : Term StructuralSignature Γ (.base "Overlap")) :
    Term StructuralSignature Γ (.base "BinaryEvidence") :=
  .op (Operator.ofSameTerms same_authored_constructors overlapCorrectOperator)
    (.cons first (.cons second (.cons factor .nil)))

def stateForget {Γ : Ctx StructuralSignature}
    (scope : Term StructuralSignature Γ (.base "Scope"))
    (world : Term StructuralSignature Γ (.base "State")) :
    Term StructuralSignature Γ (.base "State") :=
  .op (Operator.ofSameTerms same_authored_constructors forgetOperator)
    (.cons scope (.cons world .nil))

theorem evidenceZero_denotes {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ) :
    Denotes reading (evidenceZero (Γ := Γ)) environment reading.core.zero := by
  unfold Denotes
  change ∃ certificate : FirstOrder
      (WMCalculusCombinedIntrinsicTransport.zero (Γ := Γ)),
      FirstOrder.denote reading environment certificate = reading.core.zero
  exact ⟨.zero, rfl⟩

/-- The authored nullary evidence term has exactly one possible semantic
value in every combined reading, even when the interpretation certificate
is supplied existentially rather than chosen canonically. -/
theorem evidenceZero_denotes_iff {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (value : Ev) :
    Denotes reading (evidenceZero (Γ := Γ)) environment value ↔
      value = reading.core.zero := by
  constructor
  · rintro ⟨certificate, correct⟩
    change FirstOrder
      (WMCalculusCombinedIntrinsicTransport.zero (Γ := Γ)) at certificate
    exact correct.symm.trans
      (zero_certificate_denote reading environment certificate)
  · intro equal
    subst value
    exact evidenceZero_denotes reading environment

/-- The relational interpretation is closed under the authored evidence
combination constructor, for every combined reading. -/
theorem evidenceCombine_denotes {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "BinaryEvidence"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (firstValue secondValue : Ev)
    (firstDenotes : Denotes reading first environment firstValue)
    (secondDenotes : Denotes reading second environment secondValue) :
    Denotes reading (evidenceCombine first second) environment
      (reading.core.combine firstValue secondValue) := by
  obtain ⟨firstCertificate, firstCorrect⟩ := firstDenotes
  obtain ⟨secondCertificate, secondCorrect⟩ := secondDenotes
  unfold Denotes
  change ∃ certificate : FirstOrder
      (WMCalculusCombinedIntrinsicTransport.combine
        (transportSameTerms same_authored_constructors.symm first)
        (transportSameTerms same_authored_constructors.symm second)),
      FirstOrder.denote reading environment certificate =
        reading.core.combine firstValue secondValue
  refine ⟨.combine firstCertificate secondCertificate, ?_⟩
  exact congrArg₂ reading.core.combine firstCorrect secondCorrect

/-- The first non-nullary structural evidence term has a unique denotation,
independently of the certificate used to exhibit its first-order support. -/
theorem evidenceCombine_zero_zero_denotes_iff
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (value : Ev) :
    Denotes reading
        (evidenceCombine (evidenceZero (Γ := Γ)) evidenceZero)
        environment value ↔
      value = reading.core.combine reading.core.zero reading.core.zero := by
  constructor
  · rintro ⟨certificate, correct⟩
    change FirstOrder
      (WMCalculusCombinedIntrinsicTransport.combine
        (WMCalculusCombinedIntrinsicTransport.zero (Γ := Γ))
        (WMCalculusCombinedIntrinsicTransport.zero (Γ := Γ))) at certificate
    have shape : Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        (WMCalculusCombinedIntrinsicTransport.combine
          (WMCalculusCombinedIntrinsicTransport.zero (Γ := Γ))
          (WMCalculusCombinedIntrinsicTransport.zero (Γ := Γ))) =
        pCombine pEvidenceZero pEvidenceZero := rfl
    exact correct.symm.trans
      (combine_zero_zero_erasure_denote reading environment certificate shape).eq
  · intro equal
    subst value
    exact evidenceCombine_denotes reading _ _ environment _ _
      (evidenceZero_denotes reading environment)
      (evidenceZero_denotes reading environment)

theorem stateRevise_denotes {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "State"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (firstValue secondValue : State)
    (firstDenotes : Denotes reading first environment firstValue)
    (secondDenotes : Denotes reading second environment secondValue) :
    Denotes reading (stateRevise first second) environment
      (reading.core.revise firstValue secondValue) := by
  obtain ⟨firstCertificate, firstCorrect⟩ := firstDenotes
  obtain ⟨secondCertificate, secondCorrect⟩ := secondDenotes
  unfold Denotes
  change ∃ certificate : FirstOrder
      (WMCalculusCombinedIntrinsicTransport.revise
        (transportSameTerms same_authored_constructors.symm first)
        (transportSameTerms same_authored_constructors.symm second)),
      FirstOrder.denote reading environment certificate =
        reading.core.revise firstValue secondValue
  refine ⟨.revise firstCertificate secondCertificate, ?_⟩
  exact congrArg₂ reading.core.revise firstCorrect secondCorrect

theorem queryExtract_denotes {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (world : Term StructuralSignature Γ (.base "State"))
    (query : Term StructuralSignature Γ (.base "Query"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (worldValue : State) (queryValue : Query)
    (worldDenotes : Denotes reading world environment worldValue)
    (queryDenotes : Denotes reading query environment queryValue) :
    Denotes reading (queryExtract world query) environment
      (reading.core.extract worldValue queryValue) := by
  obtain ⟨worldCertificate, worldCorrect⟩ := worldDenotes
  obtain ⟨queryCertificate, queryCorrect⟩ := queryDenotes
  unfold Denotes
  change ∃ certificate : FirstOrder
      (WMCalculusCombinedIntrinsicTransport.extract
        (transportSameTerms same_authored_constructors.symm world)
        (transportSameTerms same_authored_constructors.symm query)),
      FirstOrder.denote reading environment certificate =
        reading.core.extract worldValue queryValue
  refine ⟨.extract worldCertificate queryCertificate, ?_⟩
  exact congrArg₂ reading.core.extract worldCorrect queryCorrect

theorem stateOverlapMerge_denotes {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "State"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (firstValue secondValue : State)
    (firstDenotes : Denotes reading first environment firstValue)
    (secondDenotes : Denotes reading second environment secondValue) :
    Denotes reading (stateOverlapMerge first second) environment
      (reading.overlapMerge firstValue secondValue) := by
  obtain ⟨firstCertificate, firstCorrect⟩ := firstDenotes
  obtain ⟨secondCertificate, secondCorrect⟩ := secondDenotes
  unfold Denotes
  change ∃ certificate : FirstOrder
      (WMCalculusCombinedIntrinsicTransport.overlapMerge
        (transportSameTerms same_authored_constructors.symm first)
        (transportSameTerms same_authored_constructors.symm second)),
      FirstOrder.denote reading environment certificate =
        reading.overlapMerge firstValue secondValue
  refine ⟨.overlapMerge firstCertificate secondCertificate, ?_⟩
  exact congrArg₂ reading.overlapMerge firstCorrect secondCorrect

theorem queryOverlapFactor_denotes {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "State"))
    (query : Term StructuralSignature Γ (.base "Query"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (firstValue secondValue : State) (queryValue : Query)
    (firstDenotes : Denotes reading first environment firstValue)
    (secondDenotes : Denotes reading second environment secondValue)
    (queryDenotes : Denotes reading query environment queryValue) :
    Denotes reading (queryOverlapFactor first second query) environment
      (reading.overlapFactor firstValue secondValue queryValue) := by
  obtain ⟨firstCertificate, firstCorrect⟩ := firstDenotes
  obtain ⟨secondCertificate, secondCorrect⟩ := secondDenotes
  obtain ⟨queryCertificate, queryCorrect⟩ := queryDenotes
  unfold Denotes
  change ∃ certificate : FirstOrder
      (WMCalculusCombinedIntrinsicTransport.overlapFactor
        (transportSameTerms same_authored_constructors.symm first)
        (transportSameTerms same_authored_constructors.symm second)
        (transportSameTerms same_authored_constructors.symm query)),
      FirstOrder.denote reading environment certificate =
        reading.overlapFactor firstValue secondValue queryValue
  refine ⟨.overlapFactor firstCertificate secondCertificate queryCertificate, ?_⟩
  exact congrArgThree reading.overlapFactor firstCorrect secondCorrect queryCorrect

theorem evidenceOverlapCorrect_denotes {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "BinaryEvidence"))
    (factor : Term StructuralSignature Γ (.base "Overlap"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (firstValue secondValue : Ev) (factorValue : Ov)
    (firstDenotes : Denotes reading first environment firstValue)
    (secondDenotes : Denotes reading second environment secondValue)
    (factorDenotes : Denotes reading factor environment factorValue) :
    Denotes reading (evidenceOverlapCorrect first second factor) environment
      (reading.overlapCorrect firstValue secondValue factorValue) := by
  obtain ⟨firstCertificate, firstCorrect⟩ := firstDenotes
  obtain ⟨secondCertificate, secondCorrect⟩ := secondDenotes
  obtain ⟨factorCertificate, factorCorrect⟩ := factorDenotes
  unfold Denotes
  change ∃ certificate : FirstOrder
      (WMCalculusCombinedIntrinsicTransport.overlapCorrect
        (transportSameTerms same_authored_constructors.symm first)
        (transportSameTerms same_authored_constructors.symm second)
        (transportSameTerms same_authored_constructors.symm factor)),
      FirstOrder.denote reading environment certificate =
        reading.overlapCorrect firstValue secondValue factorValue
  refine ⟨.overlapCorrect firstCertificate secondCertificate factorCertificate, ?_⟩
  exact congrArgThree reading.overlapCorrect firstCorrect secondCorrect factorCorrect

theorem stateForget_denotes {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (scope : Term StructuralSignature Γ (.base "Scope"))
    (world : Term StructuralSignature Γ (.base "State"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (scopeValue : Scope) (worldValue : State)
    (scopeDenotes : Denotes reading scope environment scopeValue)
    (worldDenotes : Denotes reading world environment worldValue) :
    Denotes reading (stateForget scope world) environment
      (reading.forget scopeValue worldValue) := by
  obtain ⟨scopeCertificate, scopeCorrect⟩ := scopeDenotes
  obtain ⟨worldCertificate, worldCorrect⟩ := worldDenotes
  unfold Denotes
  change ∃ certificate : FirstOrder
      (WMCalculusCombinedIntrinsicTransport.forget
        (transportSameTerms same_authored_constructors.symm scope)
        (transportSameTerms same_authored_constructors.symm world)),
      FirstOrder.denote reading environment certificate =
        reading.forget scopeValue worldValue
  refine ⟨.forget scopeCertificate worldCertificate, ?_⟩
  exact congrArg₂ reading.forget scopeCorrect worldCorrect

/-- Each pair of supported evidence terms supplies the same witness for
the two authored commutation sides. Functionality is proved separately;
generic representation forms may still be unsupported. -/
theorem evidenceCombine_comm_common_value {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "BinaryEvidence"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (firstValue secondValue : Ev)
    (firstDenotes : Denotes reading first environment firstValue)
    (secondDenotes : Denotes reading second environment secondValue) :
    ∃ value : Ev,
      Denotes reading (evidenceCombine first second) environment value ∧
      Denotes reading (evidenceCombine second first) environment value := by
  refine ⟨reading.core.combine firstValue secondValue,
    evidenceCombine_denotes reading first second environment firstValue secondValue
      firstDenotes secondDenotes, ?_⟩
  rw [reading.coreLaws.combine_comm firstValue secondValue]
  exact evidenceCombine_denotes reading second first environment secondValue firstValue
    secondDenotes firstDenotes

theorem evidenceCombine_assoc_common_value {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (first second third : Term StructuralSignature Γ (.base "BinaryEvidence"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (firstValue secondValue thirdValue : Ev)
    (firstDenotes : Denotes reading first environment firstValue)
    (secondDenotes : Denotes reading second environment secondValue)
    (thirdDenotes : Denotes reading third environment thirdValue) :
    ∃ value : Ev,
      Denotes reading
        (evidenceCombine (evidenceCombine first second) third) environment value ∧
      Denotes reading
        (evidenceCombine first (evidenceCombine second third)) environment value := by
  refine ⟨reading.core.combine
    (reading.core.combine firstValue secondValue) thirdValue, ?_, ?_⟩
  · exact evidenceCombine_denotes reading _ _ environment _ _
      (evidenceCombine_denotes reading first second environment firstValue secondValue
        firstDenotes secondDenotes) thirdDenotes
  · rw [reading.coreLaws.combine_assoc firstValue secondValue thirdValue]
    exact evidenceCombine_denotes reading _ _ environment _ _ firstDenotes
      (evidenceCombine_denotes reading second third environment secondValue thirdValue
        secondDenotes thirdDenotes)

theorem evidenceCombine_zero_common_value {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (term : Term StructuralSignature Γ (.base "BinaryEvidence"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (value : Ev) (supported : Denotes reading term environment value) :
    Denotes reading (evidenceCombine term evidenceZero) environment value ∧
    Denotes reading term environment value := by
  constructor
  · have combined := evidenceCombine_denotes reading term evidenceZero environment
      value reading.core.zero supported (evidenceZero_denotes reading environment)
    simpa only [reading.coreLaws.combine_zero value] using combined
  · exact supported

/-- Evidence commutation preserves and reflects every possible semantic
value of the supported structural terms, not merely one shared witness. -/
theorem evidenceCombine_comm_denotes_iff {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (first second : Term StructuralSignature Γ (.base "BinaryEvidence"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (firstValue secondValue value : Ev)
    (firstDenotes : Denotes reading first environment firstValue)
    (secondDenotes : Denotes reading second environment secondValue) :
    Denotes reading (evidenceCombine first second) environment value ↔
      Denotes reading (evidenceCombine second first) environment value := by
  exact denotes_iff_of_common_value (sort := .base "BinaryEvidence")
    reading _ _ environment
    (evidenceCombine_comm_common_value reading first second environment
      firstValue secondValue firstDenotes secondDenotes) value

/-- Evidence association preserves and reflects every possible value of
the supported structural terms. -/
theorem evidenceCombine_assoc_denotes_iff {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (first second third : Term StructuralSignature Γ (.base "BinaryEvidence"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (firstValue secondValue thirdValue value : Ev)
    (firstDenotes : Denotes reading first environment firstValue)
    (secondDenotes : Denotes reading second environment secondValue)
    (thirdDenotes : Denotes reading third environment thirdValue) :
    Denotes reading
        (evidenceCombine (evidenceCombine first second) third) environment value ↔
      Denotes reading
        (evidenceCombine first (evidenceCombine second third)) environment value := by
  exact denotes_iff_of_common_value (sort := .base "BinaryEvidence")
    reading _ _ environment
    (evidenceCombine_assoc_common_value reading first second third environment
      firstValue secondValue thirdValue firstDenotes secondDenotes thirdDenotes) value

/-- Right identity preserves and reflects every possible value of an
arbitrary supported evidence term. -/
theorem evidenceCombine_zero_denotes_iff {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx StructuralSignature}
    (term : Term StructuralSignature Γ (.base "BinaryEvidence"))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (knownValue value : Ev)
    (supported : Denotes reading term environment knownValue) :
    Denotes reading (evidenceCombine term evidenceZero) environment value ↔
      Denotes reading term environment value := by
  refine denotes_iff_of_common_value (sort := .base "BinaryEvidence")
    reading _ _ environment ?_ value
  exact ⟨knownValue,
    (evidenceCombine_zero_common_value reading term environment knownValue supported).1,
    supported⟩

#print axioms denotes_substitution_forward
#print axioms denotes_substitution_iff_of_supported
#print axioms denotes_functional
#print axioms denotes_existsUnique_iff_supported
#print axioms denotes_iff_evidenceFibre_of_certificate
#print axioms denotes_iff_of_common_value
#print axioms denotes_iff_of_same_erasure_and_support
#print axioms variable_denotes
#print axioms variable_denotes_iff
#print axioms evidenceZero_denotes
#print axioms genericEvidenceSubst_not_denotes
#print axioms counting_genericEvidenceSubst_not_denotes
#print axioms evidenceZero_denotes_iff
#print axioms evidenceCombine_denotes
#print axioms evidenceCombine_zero_zero_denotes_iff
#print axioms stateRevise_denotes
#print axioms queryExtract_denotes
#print axioms stateOverlapMerge_denotes
#print axioms queryOverlapFactor_denotes
#print axioms evidenceOverlapCorrect_denotes
#print axioms stateForget_denotes
#print axioms evidenceCombine_comm_common_value
#print axioms evidenceCombine_assoc_common_value
#print axioms evidenceCombine_zero_common_value
#print axioms evidenceCombine_comm_denotes_iff
#print axioms evidenceCombine_assoc_denotes_iff
#print axioms evidenceCombine_zero_denotes_iff

end Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralRelationalModel
