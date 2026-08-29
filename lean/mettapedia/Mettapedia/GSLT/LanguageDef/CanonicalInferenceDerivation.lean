import Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure

/-!
# Canonically indexed inference derivations

An ordinary checked derivation is indexed by raw `Pattern` judgments.  That is
the correct carrier for relational search, including syntax outside any one
native calculus.  Correct-by-construction execution needs the stronger local
fact that every node lies in a declared intrinsic codec image.

`CanonicalDerivation` adds exactly that support witness at every proof node
without changing the authored rule instance, ordered children, or raw
erasure.  Positive rule semantics can therefore interpret it directly.  No
post-hoc checker appears inside the interpreted computation.

Canonical-premise closure is then characterized operationally: when a
definition has the closure law, a supported root is enough to lift every
ordinary derivation into a canonical derivation.  Without that law, the
nodewise carrier remains available and prevents a hidden noncanonical premise
from being smuggled beneath a canonical conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation

open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
open Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
open Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uCertificate uEvidence

mutual

/-- A checked derivation whose conclusion and every recursive premise are in
the exact image of the intrinsic judgment codec. -/
inductive CanonicalDerivation {Certificate : Type uCertificate}
    (definition : ValidatedCalculusLanguageDef)
    (codec : PartialCodec Certificate Pattern) : Pattern → Type uCertificate where
  | byRule (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern}
      (support : InImage codec conclusion)
      (application :
        RuleApplication definition ruleInstance premises conclusion)
      (children : CanonicalDerivationList definition codec premises) :
      CanonicalDerivation definition codec conclusion

/-- Ordered canonical children retain duplicate occurrences and their exact
premise slots. -/
inductive CanonicalDerivationList {Certificate : Type uCertificate}
    (definition : ValidatedCalculusLanguageDef)
    (codec : PartialCodec Certificate Pattern) :
    List Pattern → Type uCertificate where
  | nil : CanonicalDerivationList definition codec []
  | cons {premise : Pattern} {premises : List Pattern}
      (head : CanonicalDerivation definition codec premise)
      (tail : CanonicalDerivationList definition codec premises) :
      CanonicalDerivationList definition codec (premise :: premises)

end

namespace CanonicalDerivation

variable {Certificate : Type uCertificate}
    {definition : ValidatedCalculusLanguageDef}
    {codec : PartialCodec Certificate Pattern}

/-- The root support carried by a canonical derivation. -/
def support {goal : Pattern}
    (derivation : CanonicalDerivation definition codec goal) :
    InImage codec goal := by
  cases derivation with
  | byRule _ support _ _ => exact support

mutual

/-- Forget only canonical-image support, recovering the identical checked
derivation tree. -/
def toDerivation {goal : Pattern} :
    CanonicalDerivation definition codec goal → Derivation definition goal
  | .byRule ruleInstance _ application children =>
      .byRule ruleInstance application
        (toDerivationList children)

/-- Pointwise forgetting for ordered children. -/
def toDerivationList {premises : List Pattern} :
    CanonicalDerivationList definition codec premises →
      DerivationList definition premises
  | .nil => .nil
  | .cons head tail =>
      .cons head.toDerivation (toDerivationList tail)

end

/-- Raw erasure is inherited from the unchanged ordinary derivation. -/
def erase {goal : Pattern}
    (derivation : CanonicalDerivation definition codec goal) : RawProof :=
  derivation.toDerivation.erase

/-- Every canonical derivation is accepted by the original checker with its
exact raw erasure. -/
theorem checkRaw_erase {goal : Pattern}
    (derivation : CanonicalDerivation definition codec goal) :
    InferenceChecker.checkRaw definition goal derivation.erase = true :=
  InferenceChecker.checkRaw_erase derivation.toDerivation

/-- A goal outside the intrinsic image has no canonical derivation, even if a
raw definition happens to derive the same wire. -/
theorem false_of_not_inImage {goal : Pattern}
    (unsupported : ¬ InImage codec goal)
    (derivation : CanonicalDerivation definition codec goal) : False :=
  unsupported derivation.support

end CanonicalDerivation

/-! ## Executable check-once canonical ingress -/

mutual

/-- Check an untrusted raw tree while requiring every node goal to lie in the
exact codec image.  Successful checking is a boundary operation; native
interpretation below consumes the resulting canonical derivation instead of
calling this function again. -/
def checkCanonicalRaw {Certificate : Type uCertificate}
    (definition : ValidatedCalculusLanguageDef)
    (codec : PartialCodec Certificate Pattern) : Pattern → RawProof → Bool
  | goal, .node ruleInstance children =>
      match decodeCanonical? codec goal with
      | none => false
      | some _ =>
          match instantiateRule? definition ruleInstance with
          | none => false
          | some (premises, conclusion) =>
              decide (conclusion = goal) &&
                checkCanonicalRawChildren definition codec premises children
termination_by _ proof => sizeOf proof

/-- Ordered recursive canonical checking for premise occurrences. -/
def checkCanonicalRawChildren {Certificate : Type uCertificate}
    (definition : ValidatedCalculusLanguageDef)
    (codec : PartialCodec Certificate Pattern) :
    List Pattern → List RawProof → Bool
  | [], [] => true
  | premise :: premises, child :: children =>
      checkCanonicalRaw definition codec premise child &&
        checkCanonicalRawChildren definition codec premises children
  | _, _ => false
termination_by _ children => sizeOf children

end


mutual

/-- Soundness with exact raw identity: successful canonical ingress produces
a nodewise canonical derivation of the same goal and the same tree. -/
theorem checkCanonicalRaw_sound
    {Certificate : Type uCertificate}
    {definition : ValidatedCalculusLanguageDef}
    {codec : PartialCodec Certificate Pattern}
    {goal : Pattern} {raw : RawProof}
    (accepted : checkCanonicalRaw definition codec goal raw = true) :
    ∃ derivation : CanonicalDerivation definition codec goal,
      derivation.erase = raw := by
  cases raw with
  | node ruleInstance children =>
      simp only [checkCanonicalRaw] at accepted
      cases decoded : decodeCanonical? codec goal with
      | none => simp [decoded] at accepted
      | some certificate =>
          have support : InImage codec goal :=
            ⟨certificate,
              (decodeCanonical?_eq_some_iff codec goal certificate).1
                decoded |>.2⟩
          cases instantiated : instantiateRule? definition ruleInstance with
          | none => simp [decoded, instantiated] at accepted
          | some result =>
              rcases result with ⟨premises, conclusion⟩
              simp only [decoded, instantiated, Bool.and_eq_true,
                decide_eq_true_eq] at accepted
              rcases accepted with ⟨conclusionEquality, childrenAccepted⟩
              subst goal
              have application :
                  RuleApplication definition ruleInstance premises
                    conclusion :=
                instantiateRule?_eq_some_iff_application.mp instantiated
              rcases checkCanonicalRawChildren_sound childrenAccepted with
                ⟨canonicalChildren, childrenErase⟩
              refine
                ⟨.byRule ruleInstance support application canonicalChildren, ?_⟩
              simp [CanonicalDerivation.erase,
                CanonicalDerivation.toDerivation, Derivation.erase,
                childrenErase]
termination_by sizeOf raw

/-- Exact soundness for ordered children. -/
theorem checkCanonicalRawChildren_sound
    {Certificate : Type uCertificate}
    {definition : ValidatedCalculusLanguageDef}
    {codec : PartialCodec Certificate Pattern}
    {premises : List Pattern} {raw : List RawProof}
    (accepted :
      checkCanonicalRawChildren definition codec premises raw = true) :
    ∃ derivations : CanonicalDerivationList definition codec premises,
      (CanonicalDerivation.toDerivationList derivations).erase = raw := by
  cases premises with
  | nil =>
      cases raw with
      | nil => exact ⟨.nil, rfl⟩
      | cons proof proofs => simp [checkCanonicalRawChildren] at accepted
  | cons premise premises =>
      cases raw with
      | nil => simp [checkCanonicalRawChildren] at accepted
      | cons proof proofs =>
          simp only [checkCanonicalRawChildren, Bool.and_eq_true] at accepted
          rcases checkCanonicalRaw_sound accepted.1 with
            ⟨head, headErase⟩
          rcases checkCanonicalRawChildren_sound accepted.2 with
            ⟨tail, tailErase⟩
          have headErase' : head.toDerivation.erase = proof := by
            simpa [CanonicalDerivation.erase] using headErase
          exact ⟨.cons head tail, by
            simp [CanonicalDerivation.toDerivationList,
              DerivationList.erase, headErase', tailErase]⟩
termination_by sizeOf raw

end


mutual

/-- Completeness: erasing a canonical derivation and checking it at the raw
boundary always succeeds. -/
theorem CanonicalDerivation.checkCanonicalRaw_erase
    {Certificate : Type uCertificate}
    {definition : ValidatedCalculusLanguageDef}
    {codec : PartialCodec Certificate Pattern}
    {goal : Pattern}
    (derivation : CanonicalDerivation definition codec goal) :
    checkCanonicalRaw definition codec goal derivation.erase = true := by
  cases derivation with
  | byRule ruleInstance support application children =>
      have decodedSome : (decodeCanonical? codec goal).isSome = true :=
        (decodeCanonical?_isSome_iff_exists_encode_eq codec goal).2 support
      cases decoded : decodeCanonical? codec goal with
      | none => simp [decoded] at decodedSome
      | some certificate =>
          have instantiated :=
            instantiateRule?_eq_some_iff_application.mpr application
          simp only [CanonicalDerivation.erase,
            CanonicalDerivation.toDerivation, Derivation.erase,
            checkCanonicalRaw, decoded]
          rw [instantiated]
          simp only [decide_true]
          exact CanonicalDerivationList.checkCanonicalRawChildren_erase children

/-- Completeness for ordered child erasures. -/
theorem CanonicalDerivationList.checkCanonicalRawChildren_erase
    {Certificate : Type uCertificate}
    {definition : ValidatedCalculusLanguageDef}
    {codec : PartialCodec Certificate Pattern}
    {premises : List Pattern}
    (derivations : CanonicalDerivationList definition codec premises) :
    checkCanonicalRawChildren definition codec premises
        (CanonicalDerivation.toDerivationList derivations).erase = true := by
  cases derivations with
  | nil => simp [CanonicalDerivation.toDerivationList,
      DerivationList.erase, checkCanonicalRawChildren]
  | cons head tail =>
      simp only [CanonicalDerivation.toDerivationList,
        DerivationList.erase, checkCanonicalRawChildren, Bool.and_eq_true]
      exact ⟨head.checkCanonicalRaw_erase,
        tail.checkCanonicalRawChildren_erase⟩

end

/-- Exact admission theorem for the check-once boundary. -/
theorem checkCanonicalRaw_iff_exists_derivation_erases
    {Certificate : Type uCertificate}
    {definition : ValidatedCalculusLanguageDef}
    {codec : PartialCodec Certificate Pattern}
    (goal : Pattern) (raw : RawProof) :
    checkCanonicalRaw definition codec goal raw = true ↔
      ∃ derivation : CanonicalDerivation definition codec goal,
        derivation.erase = raw := by
  constructor
  · exact checkCanonicalRaw_sound
  · rintro ⟨derivation, rfl⟩
    exact derivation.checkCanonicalRaw_erase

/-! ## Direct positive interpretation -/

namespace PositiveCalculusLanguageSemantics

variable {Certificate : Type uCertificate}
    {definition : ValidatedCalculusLanguageDef}
    {codec : PartialCodec Certificate Pattern}
    {Evidence : Certificate → Type uEvidence}

mutual

/-- Interpret a nodewise canonical derivation directly into the positive
native fibre. -/
def interpretCanonical
    (semantics : PositiveCalculusLanguageSemantics definition codec Evidence) :
    {goal : Pattern} → CanonicalDerivation definition codec goal →
      PositiveFibre codec Evidence goal
  | _, .byRule _ support application children =>
      semantics.ruleMeaning application support
        (interpretCanonicalList semantics children)

/-- Ordered positive interpretation retains every premise occurrence. -/
def interpretCanonicalList
    (semantics : PositiveCalculusLanguageSemantics definition codec Evidence) :
    {premises : List Pattern} →
      CanonicalDerivationList definition codec premises →
      EvidenceList (PositiveFibre codec Evidence) premises
  | [], .nil => .nil
  | _ :: _, .cons head tail =>
      .cons (interpretCanonical semantics head)
        (interpretCanonicalList semantics tail)

end

end PositiveCalculusLanguageSemantics

/-! ## Closure lifts supported ordinary derivations -/

namespace CanonicalPremiseClosed

variable {Certificate : Type uCertificate}
    {definition : ValidatedCalculusLanguageDef}
    {codec : PartialCodec Certificate Pattern}

mutual

/-- Under canonical-premise closure, root support recursively supplies the
support field at every ordinary derivation node. -/
def liftDerivation
    (closed : CanonicalPremiseClosed definition codec) :
    {goal : Pattern} → InImage codec goal → Derivation definition goal →
      CanonicalDerivation definition codec goal
  | _, support, .byRule ruleInstance application children =>
      .byRule ruleInstance support application
        (liftDerivationList closed
          (closed ruleInstance _ _ application support) children)

/-- Ordered recursive lifting; support is selected by exact occurrence, not
by deduplicated membership. -/
def liftDerivationList
    (closed : CanonicalPremiseClosed definition codec) :
    {premises : List Pattern} → PremisesInImage codec premises →
      DerivationList definition premises →
      CanonicalDerivationList definition codec premises
  | [], _, .nil => .nil
  | premise :: premises, support, .cons head tail =>
      .cons
        (liftDerivation closed (support premise (by simp)) head)
        (liftDerivationList closed
          (fun candidate membership =>
            support candidate (by simp [membership])) tail)

end

mutual

@[simp] theorem liftDerivation_toDerivation
    (closed : CanonicalPremiseClosed definition codec)
    {goal : Pattern} (support : InImage codec goal)
    (derivation : Derivation definition goal) :
    (liftDerivation closed support derivation).toDerivation = derivation := by
  cases derivation with
  | byRule ruleInstance application children =>
      simp only [liftDerivation, CanonicalDerivation.toDerivation,
        liftDerivationList_toDerivationList closed
          (closed ruleInstance _ _ application support) children]

@[simp] theorem liftDerivationList_toDerivationList
    (closed : CanonicalPremiseClosed definition codec)
    {premises : List Pattern} (support : PremisesInImage codec premises)
    (derivations : DerivationList definition premises) :
    CanonicalDerivation.toDerivationList
        (liftDerivationList closed support derivations) =
      derivations := by
  cases derivations with
  | nil => rfl
  | @cons premise premises head tail =>
      simp only [liftDerivationList,
        CanonicalDerivation.toDerivationList,
        liftDerivation_toDerivation closed (support premise (by simp)) head,
        liftDerivationList_toDerivationList closed
          (fun candidate membership =>
            support candidate (by simp [membership])) tail]

end

/-- Closure lifting preserves the exact raw proof artifact. -/
@[simp] theorem liftDerivation_erase
    (closed : CanonicalPremiseClosed definition codec)
    {goal : Pattern} (support : InImage codec goal)
    (derivation : Derivation definition goal) :
    (liftDerivation closed support derivation).erase = derivation.erase := by
  simp [CanonicalDerivation.erase]

/-- Exact raw-checker characterization on a supported root of a
canonical-premise-closed definition. -/
theorem checkRaw_iff_exists_canonical_erases
    (closed : CanonicalPremiseClosed definition codec)
    {goal : Pattern} (support : InImage codec goal) (raw : RawProof) :
    InferenceChecker.checkRaw definition goal raw = true ↔
      ∃ derivation : CanonicalDerivation definition codec goal,
        derivation.erase = raw := by
  constructor
  · intro accepted
    rcases
        (G2_checkRaw_iff_exists_derivation_erases_to.mp accepted) with
      ⟨derivation, erases⟩
    exact ⟨liftDerivation closed support derivation, by
      simpa using erases⟩
  · rintro ⟨derivation, erases⟩
    rw [← erases]
    exact derivation.checkRaw_erase

end CanonicalPremiseClosed

/-! ## Negative control -/

namespace Canary

def boolPatternCodec : PartialCodec Bool Pattern where
  encode
    | false => .apply "canonical-false" []
    | true => .apply "canonical-true" []
  decode
    | .apply "canonical-false" [] => some false
    | .apply "canonical-true" [] => some true
    | _ => none
  decode_encode := by
    intro value
    cases value <;> rfl

def aliasPattern : Pattern := .apply "noncanonical-alias" []

theorem aliasPattern_not_inImage :
    ¬ InImage boolPatternCodec aliasPattern := by
  rintro ⟨certificate, equality⟩
  cases certificate <;> simp [boolPatternCodec, aliasPattern] at equality

theorem tolerantAlias_has_no_canonicalDerivation
    (definition : ValidatedCalculusLanguageDef) :
    CanonicalDerivation definition boolPatternCodec aliasPattern → False :=
  CanonicalDerivation.false_of_not_inImage aliasPattern_not_inImage

end Canary

#print axioms CanonicalDerivation.checkRaw_erase
#print axioms CanonicalDerivation.false_of_not_inImage
#print axioms checkCanonicalRaw_iff_exists_derivation_erases
#print axioms PositiveCalculusLanguageSemantics.interpretCanonical
#print axioms CanonicalPremiseClosed.liftDerivation_toDerivation
#print axioms CanonicalPremiseClosed.liftDerivation_erase
#print axioms CanonicalPremiseClosed.checkRaw_iff_exists_canonical_erases
#print axioms Canary.tolerantAlias_has_no_canonicalDerivation

end Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation
