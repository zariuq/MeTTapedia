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
Executable replay enters only after a concrete CertificateGSLT definition and a
two-sided proof-term translation have been supplied.
-/

namespace Mettapedia.Logic.Bridges.FoundationCertificateGSLT

open Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef

universe uSystem uTargetSystem uFormula uModel

/-! ## Proof-relevant bridge -/

/-- A claim-indexed bridge from Foundation proof terms to CertificateGSLT.

Both the deductive system and the conclusion formula are selected by the
claim.  Thus a sequent-like claim can retain its context as `systemOf claim`
instead of silently encoding that context into an implication.  This
structure gives exactness only for the displayed Foundation judgment;
relating it to any independently intended claim semantics requires an
explicit `CalculusExact` argument below. -/
structure JudgmentProofTermBridge
    {System : Type uSystem} {Formula : Type uFormula} {Claim : Type*}
    [LO.Entailment System Formula]
    (definition : ValidatedCalculusLanguageDef) where
  systemOf : Claim -> System
  formulaOf : Claim -> Formula
  encode : Claim -> Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
  toDerivation : forall {claim},
    LO.Entailment.Prf (systemOf claim) (formulaOf claim) ->
      Derivation definition (encode claim)
  fromDerivation : forall {claim},
    Derivation definition (encode claim) ->
      LO.Entailment.Prf (systemOf claim) (formulaOf claim)

namespace JudgmentProofTermBridge

variable {System : Type uSystem} {Formula : Type uFormula} {Claim : Type*}
    [LO.Entailment System Formula]
    {definition : ValidatedCalculusLanguageDef}
    (bridge : JudgmentProofTermBridge
      (System := System) (Formula := Formula)
      (Claim := Claim) definition)

theorem provable_iff_derivable (claim : Claim) :
    LO.Entailment.Provable (bridge.systemOf claim) (bridge.formulaOf claim) <->
      Nonempty (Derivation definition (bridge.encode claim)) := by
  constructor
  · rintro ⟨proof⟩
    exact ⟨bridge.toDerivation proof⟩
  · rintro ⟨derivation⟩
    exact ⟨bridge.fromDerivation derivation⟩

/-- Exactness for the Foundation derivability judgment named by each claim. -/
def exactForProvability :
    ExactJudgmentEncoding Claim
      (fun claim => LO.Entailment.Provable
        (bridge.systemOf claim) (bridge.formulaOf claim))
      definition where
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
    ExactJudgmentEncoding Claim Meaning definition where
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
  definition := definition
  adequacy := bridge.exactForMeaning calculus

end JudgmentProofTermBridge

/-- A two-sided translation between one Foundation proof type and one
CertificateGSLT derivation family.  The maps retain proof objects; an equivalence of
mere provability propositions would be too weak for proof transformation,
cost, or provenance. -/
structure ProofTermBridge
    {System : Type uSystem} {Formula : Type uFormula}
    [LO.Entailment System Formula]
    (system : System) (definition : ValidatedCalculusLanguageDef) where
  encode : Formula -> Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
  toDerivation : forall {formula},
    LO.Entailment.Prf system formula ->
      Derivation definition (encode formula)
  fromDerivation : forall {formula},
    Derivation definition (encode formula) ->
      LO.Entailment.Prf system formula

namespace ProofTermBridge

variable {System : Type uSystem} {Formula : Type uFormula}
    [LO.Entailment System Formula]
    {system : System} {definition : ValidatedCalculusLanguageDef}
    (bridge : ProofTermBridge system definition)

/-- View the formula-specialized bridge as the general claim-indexed bridge. -/
def toJudgment : JudgmentProofTermBridge
    (System := System) (Formula := Formula)
    (Claim := Formula) definition where
  systemOf := fun _ => system
  formulaOf := id
  encode := bridge.encode
  toDerivation := bridge.toDerivation
  fromDerivation := bridge.fromDerivation

/-- Foundation provability and CertificateGSLT derivability agree after erasing the
particular proof object on each side. -/
theorem provable_iff_derivable (formula : Formula) :
    LO.Entailment.Provable system formula <->
      Nonempty (Derivation definition (bridge.encode formula)) := by
  constructor
  · rintro ⟨proof⟩
    exact ⟨bridge.toDerivation proof⟩
  · rintro ⟨derivation⟩
    exact ⟨bridge.fromDerivation derivation⟩

/-- The proof-term bridge is exactly a complete CertificateGSLT definition for
the independently defined Foundation provability predicate. -/
def exactForProvability :
    ExactJudgmentEncoding Formula
      (LO.Entailment.Provable system) definition where
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

/-- A proof-term bridge plus Foundation soundness/completeness gives a
semantic CertificateGSLT authority for the chosen model or model class. -/
def exactForModel
    {Model : Type uModel} [LO.Semantics Model Formula] (model : Model)
    [LO.Sound system model] [LO.Complete system model] :
    ExactJudgmentEncoding Formula
      (fun formula => LO.Semantics.Models model formula) definition where
  encode := bridge.encode
  derivation_sound := by
    intro formula derivable
    exact (foundationCalculusExact (system := system) model).sound formula
      ((bridge.exactForProvability).derivation_sound formula derivable)
  derivation_complete := by
    intro formula meaningful
    exact (bridge.exactForProvability).derivation_complete formula
      ((foundationCalculusExact (system := system) model).complete formula meaningful)

/-- The resulting semantic authority is directly consumable by the
generic exact CertificateGSLT wire authority and dependent NIK family. -/
def semanticallyCompleteCertificateGSLT
    {Model : Type uModel} [LO.Semantics Model Formula] (model : Model)
    [LO.Sound system model] [LO.Complete system model] :
    SemanticallyCompleteCertificateGSLT Formula
      (fun formula => LO.Semantics.Models model formula) where
  definition := definition
  adequacy := bridge.exactForModel model

end ProofTermBridge

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

/-- When both Foundation systems have CertificateGSLT definitions, a Foundation
proof translation induces an actual CertificateGSLT derivation transformation. -/
def mapDerivation
    (translation : ProofTranslation source target)
    {sourceDefinition targetDefinition : ValidatedCalculusLanguageDef}
    (sourceBridge : ProofTermBridge source sourceDefinition)
    (targetBridge : ProofTermBridge target targetDefinition)
    {formula : Formula}
    (derivation : Derivation sourceDefinition
      (sourceBridge.encode formula)) :
    Derivation targetDefinition (targetBridge.encode formula) :=
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
