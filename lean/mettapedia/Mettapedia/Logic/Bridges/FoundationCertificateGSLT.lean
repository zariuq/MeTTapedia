import Foundation.Logic.Entailment
import Mettapedia.GSLT.LanguageDef.CompletenessSpectrum

/-!
# Foundation proof terms as CertificateGSLT authorities

Foundation distinguishes the proof type `Entailment.Prf system formula` from
its propositional truncation `Entailment.Provable system formula`.  CertificateGSLT
also has a proof-relevant derivation type.  This module gives the generic
bridge between those two proof carriers and then reuses Foundation's separate
soundness and completeness classes to obtain semantic CertificateGSLT authority.

No executable checker is inferred from an arbitrary Foundation proof type.
Executable replay enters only after a concrete CertificateGSLT presentation and a
two-sided proof-term translation have been supplied.
-/

namespace Mettapedia.Logic.Bridges.FoundationCertificateGSLT

open Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

universe uSystem uTargetSystem uFormula uModel

/-! ## Proof-relevant presentation -/

/-- A claim-indexed bridge from Foundation proof terms to CertificateGSLT.

Both the deductive system and the conclusion formula are selected by the
claim.  Thus a sequent-like claim can retain its context as `systemOf claim`
instead of silently encoding that context into an implication.  This
structure gives exactness only for the displayed Foundation judgment;
relating it to any independently intended claim semantics requires an
explicit `CalculusExact` argument below. -/
structure JudgmentProofTermPresentation
    {System : Type uSystem} {Formula : Type uFormula} {Claim : Type*}
    [LO.Entailment System Formula]
    (presentation : ValidatedPresentation) where
  systemOf : Claim -> System
  formulaOf : Claim -> Formula
  encode : Claim -> Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
  toDerivation : forall {claim},
    LO.Entailment.Prf (systemOf claim) (formulaOf claim) ->
      Derivation presentation (encode claim)
  fromDerivation : forall {claim},
    Derivation presentation (encode claim) ->
      LO.Entailment.Prf (systemOf claim) (formulaOf claim)

namespace JudgmentProofTermPresentation

variable {System : Type uSystem} {Formula : Type uFormula} {Claim : Type*}
    [LO.Entailment System Formula]
    {presentation : ValidatedPresentation}
    (bridge : JudgmentProofTermPresentation
      (System := System) (Formula := Formula)
      (Claim := Claim) presentation)

theorem provable_iff_derivable (claim : Claim) :
    LO.Entailment.Provable (bridge.systemOf claim) (bridge.formulaOf claim) <->
      Nonempty (Derivation presentation (bridge.encode claim)) := by
  constructor
  · rintro ⟨proof⟩
    exact ⟨bridge.toDerivation proof⟩
  · rintro ⟨derivation⟩
    exact ⟨bridge.fromDerivation derivation⟩

/-- Exactness for the Foundation derivability judgment named by each claim. -/
def exactForProvability :
    ExactJudgmentPresentation Claim
      (fun claim => LO.Entailment.Provable
        (bridge.systemOf claim) (bridge.formulaOf claim))
      presentation where
  encode := bridge.encode
  derivation_sound := by
    intro claim derivable
    exact (bridge.provable_iff_derivable claim).mpr derivable
  derivation_complete := by
    intro claim provable
    exact (bridge.provable_iff_derivable claim).mp provable

/-- Exact CertificateGSLT authority for an independently stated claim meaning.
The explicit two-sided premise is what prevents extra claim data from being
discarded by an ad hoc formula encoding. -/
def exactForMeaning {Meaning : Claim -> Prop}
    (calculus : CalculusExact
      (fun claim => LO.Entailment.Provable
        (bridge.systemOf claim) (bridge.formulaOf claim))
      Meaning) :
    ExactJudgmentPresentation Claim Meaning presentation where
  encode := bridge.encode
  derivation_sound := by
    intro claim derivable
    exact calculus.sound claim
      ((bridge.exactForProvability).derivation_sound claim derivable)
  derivation_complete := by
    intro claim meaningful
    exact (bridge.exactForProvability).derivation_complete claim
      (calculus.complete claim meaningful)

def semanticallyCompleteCertificateGSLT
    {Meaning : Claim -> Prop}
    (calculus : CalculusExact
      (fun claim => LO.Entailment.Provable
        (bridge.systemOf claim) (bridge.formulaOf claim))
      Meaning) :
    SemanticallyCompleteCertificateGSLT Claim Meaning where
  presentation := presentation
  adequacy := bridge.exactForMeaning calculus

end JudgmentProofTermPresentation

/-- A two-sided translation between one Foundation proof type and one
CertificateGSLT derivation family.  The maps retain proof objects; an equivalence of
mere provability propositions would be too weak for proof transformation,
cost, or provenance. -/
structure ProofTermPresentation
    {System : Type uSystem} {Formula : Type uFormula}
    [LO.Entailment System Formula]
    (system : System) (presentation : ValidatedPresentation) where
  encode : Formula -> Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
  toDerivation : forall {formula},
    LO.Entailment.Prf system formula ->
      Derivation presentation (encode formula)
  fromDerivation : forall {formula},
    Derivation presentation (encode formula) ->
      LO.Entailment.Prf system formula

namespace ProofTermPresentation

variable {System : Type uSystem} {Formula : Type uFormula}
    [LO.Entailment System Formula]
    {system : System} {presentation : ValidatedPresentation}
    (bridge : ProofTermPresentation system presentation)

/-- View the formula-specialized bridge as the general claim-indexed bridge. -/
def toJudgment : JudgmentProofTermPresentation
    (System := System) (Formula := Formula)
    (Claim := Formula) presentation where
  systemOf := fun _ => system
  formulaOf := id
  encode := bridge.encode
  toDerivation := bridge.toDerivation
  fromDerivation := bridge.fromDerivation

/-- Foundation provability and CertificateGSLT derivability agree after erasing the
particular proof object on each side. -/
theorem provable_iff_derivable (formula : Formula) :
    LO.Entailment.Provable system formula <->
      Nonempty (Derivation presentation (bridge.encode formula)) := by
  constructor
  · rintro ⟨proof⟩
    exact ⟨bridge.toDerivation proof⟩
  · rintro ⟨derivation⟩
    exact ⟨bridge.fromDerivation derivation⟩

/-- The proof-term bridge is exactly a complete CertificateGSLT presentation for
the independently defined Foundation provability predicate. -/
def exactForProvability :
    ExactJudgmentPresentation Formula
      (LO.Entailment.Provable system) presentation where
  encode := bridge.encode
  derivation_sound := by
    intro formula derivable
    exact (bridge.provable_iff_derivable formula).mpr derivable
  derivation_complete := by
    intro formula provable
    exact (bridge.provable_iff_derivable formula).mp provable

/-! ## Foundation semantics -/

/-- Foundation's independent soundness and completeness instances are the
generic two-sided calculus/semantics law expected by the NIK completeness
spectrum. -/
def foundationCalculusExact
    {Model : Type uModel} [LO.Semantics Model Formula] (model : Model)
    [LO.Sound system model] [LO.Complete system model] :
    CalculusExact (LO.Entailment.Provable system)
      (fun formula => LO.Semantics.Models model formula) where
  sound := by
    intro formula provable
    exact LO.Sound.sound provable
  complete := by
    intro formula meaningful
    exact LO.Complete.complete meaningful

/-- A proof-term presentation plus Foundation soundness/completeness gives a
semantic CertificateGSLT presentation for the chosen model or model class. -/
def exactForModel
    {Model : Type uModel} [LO.Semantics Model Formula] (model : Model)
    [LO.Sound system model] [LO.Complete system model] :
    ExactJudgmentPresentation Formula
      (fun formula => LO.Semantics.Models model formula) presentation where
  encode := bridge.encode
  derivation_sound := by
    intro formula derivable
    exact (foundationCalculusExact (system := system) model).sound formula
      ((bridge.exactForProvability).derivation_sound formula derivable)
  derivation_complete := by
    intro formula meaningful
    exact (bridge.exactForProvability).derivation_complete formula
      ((foundationCalculusExact (system := system) model).complete formula meaningful)

/-- The resulting semantic presentation is directly consumable by the
generic exact CertificateGSLT wire authority and dependent NIK family. -/
def semanticallyCompleteCertificateGSLT
    {Model : Type uModel} [LO.Semantics Model Formula] (model : Model)
    [LO.Sound system model] [LO.Complete system model] :
    SemanticallyCompleteCertificateGSLT Formula
      (fun formula => LO.Semantics.Models model formula) where
  presentation := presentation
  adequacy := bridge.exactForModel model

end ProofTermPresentation

/-! ## Proof translations between Foundation systems -/

/-- A theorem-preserving translation at the proof-relevant Foundation layer.
Unlike `WeakerThan`, this structure says how to transform the proof itself. -/
structure ProofTranslation
    {SourceSystem : Type uSystem} {TargetSystem : Type uTargetSystem}
    {Formula : Type uFormula}
    [LO.Entailment SourceSystem Formula]
    [LO.Entailment TargetSystem Formula]
    (source : SourceSystem) (target : TargetSystem) where
  map : forall {formula},
    LO.Entailment.Prf source formula -> LO.Entailment.Prf target formula

namespace ProofTranslation

variable {SourceSystem : Type uSystem}
    {TargetSystem : Type uTargetSystem} {Formula : Type uFormula}
    [LO.Entailment SourceSystem Formula]
    [LO.Entailment TargetSystem Formula]
    {source : SourceSystem} {target : TargetSystem}

/-- Proof-relevant translation implies theorem preservation after
propositional truncation. -/
theorem preservesProvability
    (translation : ProofTranslation source target) {formula : Formula} :
    LO.Entailment.Provable source formula ->
      LO.Entailment.Provable target formula := by
  rintro ⟨proof⟩
  exact ⟨ProofTranslation.map translation proof⟩

/-- When both Foundation systems have CertificateGSLT presentations, a Foundation
proof translation induces an actual CertificateGSLT derivation transformation. -/
def mapDerivation
    (translation : ProofTranslation source target)
    {sourcePresentation targetPresentation : ValidatedPresentation}
    (sourceBridge : ProofTermPresentation source sourcePresentation)
    (targetBridge : ProofTermPresentation target targetPresentation)
    {formula : Formula}
    (derivation : Derivation sourcePresentation
      (sourceBridge.encode formula)) :
    Derivation targetPresentation (targetBridge.encode formula) :=
  targetBridge.toDerivation
    (ProofTranslation.map translation
      (sourceBridge.fromDerivation derivation))

end ProofTranslation

/-! ## Information-loss canary -/

/-- Mere proof existence does not determine the original proof object.  Thus
Foundation's `Provable` view is sufficient for theorem sets but not for the
proof-relevant transformations, costs, or provenance carried by `Prf`. -/
theorem proof_identity_not_recoverable_from_provability :
    Not (Exists fun recover : Nonempty Bool -> Bool =>
      forall proof : Bool, recover ⟨proof⟩ = proof) := by
  rintro ⟨recover, recovers⟩
  have erasedEqual : (⟨false⟩ : Nonempty Bool) = ⟨true⟩ :=
    Subsingleton.elim _ _
  have recoveredEqual := congrArg recover erasedEqual
  have impossible : false = true :=
    (recovers false).symm.trans (recoveredEqual.trans (recovers true))
  exact Bool.false_ne_true impossible

end Mettapedia.Logic.Bridges.FoundationCertificateGSLT
