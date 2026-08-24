import Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
import Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension

/-!
# Canonical premise closure for proof-relevant inference semantics

A partial codec separates an intrinsic judgment from its raw wire syntax.
There are then two natural semantic fibres over a wire:

* `UniversalFibre` says that every intrinsic judgment encoding to the wire has
  evidence.  It is inhabited vacuously outside the encoder image, so it gives
  a total semantics for unrestricted relational proof search.
* `PositiveFibre` retains an intrinsic judgment, its exact encoding equality,
  and its evidence.  It is empty outside the encoder image, so it is the
  appropriate carrier for native construction.

They are equivalent exactly on supported wires.  Consequently, a rule with a
canonical conclusion can be interpreted natively from universal premise
meanings exactly when canonicality of the conclusion forces canonicality of
every ordered premise.  `CanonicalPremiseClosed` states that condition for an
authored inference presentation.

The final lifting theorem is the useful architecture boundary: positive
rule semantics plus canonical-premise closure induces a total presentation
semantics.  Noncanonical raw conclusions remain relationally meaningful, but
they cannot be mistaken for native evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure

open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uCertificate uWire uEvidence

/-! ## Exact-image support and its two semantic fibres -/

/-- A wire is supported when it is the exact encoding of an intrinsic value. -/
def InImage {Certificate : Type uCertificate} {Wire : Type uWire}
    (codec : PartialCodec Certificate Wire) (wire : Wire) : Prop :=
  ∃ certificate, codec.encode certificate = wire

@[simp] theorem inImage_encode
    {Certificate : Type uCertificate} {Wire : Type uWire}
    (codec : PartialCodec Certificate Wire) (certificate : Certificate) :
    InImage codec (codec.encode certificate) :=
  ⟨certificate, rfl⟩

/-- Exact-image support can be reified constructively through the canonical
decoder.  The proposition proves that the `none` branch is impossible; the
decoder, rather than existential elimination or choice, supplies the value. -/
def witnessOfInImage
    {Certificate : Type uCertificate} {Wire : Type uWire}
    [DecidableEq Wire] (codec : PartialCodec Certificate Wire) (wire : Wire)
    (support : InImage codec wire) :
    { certificate : Certificate // codec.encode certificate = wire } := by
  cases decoded : CanonicalPartialCodec.decodeCanonical? codec wire with
  | none =>
      have accepted :
          (CanonicalPartialCodec.decodeCanonical? codec wire).isSome = true :=
        (CanonicalPartialCodec.decodeCanonical?_isSome_iff_exists_encode_eq
          codec wire).2 support
      simp [decoded] at accepted
  | some certificate =>
      exact ⟨certificate,
        (CanonicalPartialCodec.decodeCanonical?_eq_some_iff
          codec wire certificate).1 decoded |>.2⟩

/-- The implication-shaped semantic fibre used to interpret unrestricted raw
proofs.  It is intentionally vacuous away from the canonical image. -/
def UniversalFibre {Certificate : Type uCertificate} {Wire : Type uWire}
    (codec : PartialCodec Certificate Wire)
    (Evidence : Certificate → Type uEvidence) (wire : Wire) :
    Type (max uCertificate uEvidence) :=
  ∀ certificate, codec.encode certificate = wire → Evidence certificate

/-- A native semantic point positively retains its decoded certificate,
exact wire identity, and certificate-indexed evidence. -/
structure PositiveFibre {Certificate : Type uCertificate} {Wire : Type uWire}
    (codec : PartialCodec Certificate Wire)
    (Evidence : Certificate → Type uEvidence) (wire : Wire) :
    Type (max uCertificate uEvidence) where
  certificate : Certificate
  encodes : codec.encode certificate = wire
  evidence : Evidence certificate

namespace PositiveFibre

variable {Certificate : Type uCertificate} {Wire : Type uWire}
    {codec : PartialCodec Certificate Wire}
    {Evidence : Certificate → Type uEvidence} {wire : Wire}

/-- Positive evidence always supplies exact-image support. -/
def support (positive : PositiveFibre codec Evidence wire) :
    InImage codec wire :=
  ⟨positive.certificate, positive.encodes⟩

/-- Injectivity of a partial codec turns one positive point into the universal
meaning of the same wire. -/
def toUniversal (positive : PositiveFibre codec Evidence wire) :
    UniversalFibre codec Evidence wire := by
  intro certificate equality
  have certificateEquality : certificate = positive.certificate :=
    codec.encode_injective (equality.trans positive.encodes.symm)
  subst certificate
  exact positive.evidence

end PositiveFibre

namespace UniversalFibre

variable {Certificate : Type uCertificate} {Wire : Type uWire}
    {codec : PartialCodec Certificate Wire}
    {Evidence : Certificate → Type uEvidence} {wire : Wire}

/-- On a supported wire, universal evidence becomes a positive native point. -/
def toPositive [DecidableEq Wire] (support : InImage codec wire)
    (universal : UniversalFibre codec Evidence wire) :
    PositiveFibre codec Evidence wire := by
  let witness := witnessOfInImage codec wire support
  exact
    ⟨witness.1, witness.2, universal witness.1 witness.2⟩

end UniversalFibre

/-! ## Disjoint sums of proof-relevant fibres -/

/-- Evidence selected by a heterogeneous coproduct index. -/
def SumEvidence {Left Right : Type uCertificate}
    (LeftEvidence : Left → Type uEvidence)
    (RightEvidence : Right → Type uEvidence) :
    Left ⊕ Right → Type uEvidence
  | .inl left => LeftEvidence left
  | .inr right => RightEvidence right

/-- Universal proof-relevant semantics sends a disjoint coproduct of exact
judgment codecs to the product of the two independently usable semantic
views.  This is the generic extension law behind a multi-judgment hosted
calculus; no presentation-specific transport theorem is required. -/
def universalFibre_product_equiv_sumOfDisjoint
    {Left Right : Type uCertificate} {Wire : Type uWire}
    [DecidableEq Wire]
    (left : PartialCodec Left Wire) (right : PartialCodec Right Wire)
    (disjoint : CanonicalPartialCodec.EncoderImagesDisjoint left right)
    (LeftEvidence : Left → Type uEvidence)
    (RightEvidence : Right → Type uEvidence) (wire : Wire) :
    (UniversalFibre left LeftEvidence wire ×
        UniversalFibre right RightEvidence wire) ≃
      UniversalFibre
        (CanonicalPartialCodec.sumOfDisjoint left right disjoint)
        (SumEvidence LeftEvidence RightEvidence) wire where
  toFun meaning := by
    intro index equality
    cases index with
    | inl leftIndex =>
        exact meaning.1 leftIndex (by
          simpa [CanonicalPartialCodec.sumOfDisjoint] using equality)
    | inr rightIndex =>
        exact meaning.2 rightIndex (by
          simpa [CanonicalPartialCodec.sumOfDisjoint] using equality)
  invFun meaning :=
    ⟨fun leftIndex equality =>
        meaning (.inl leftIndex) (by
          simpa [CanonicalPartialCodec.sumOfDisjoint] using equality),
      fun rightIndex equality =>
        meaning (.inr rightIndex) (by
          simpa [CanonicalPartialCodec.sumOfDisjoint] using equality)⟩
  left_inv _ := rfl
  right_inv meaning := by
    funext index equality
    cases index <;> rfl

/-! ## Extending an existing semantics by a genuinely new judgment fibre -/

/-- No rule of a presentation concludes a canonical wire owned by the given
codec.  This is the semantic form of adding a genuinely new judgment family:
old rules cannot manufacture evidence in its fibre. -/
def PresentationConclusionsAvoid
    {Certificate : Type uCertificate}
    (presentation : ValidatedPresentation)
    (codec : PartialCodec Certificate Pattern) : Prop :=
  ∀ {ruleInstance premises conclusion},
    RuleApplication presentation ruleInstance premises conclusion →
      ∀ certificate, codec.encode certificate ≠ conclusion

/-- A wire outside an encoder image has a canonical vacuous universal
meaning.  This is valid for unrestricted relational semantics but does not
construct a positive native point. -/
def universalFibreOfAvoids
    {Certificate : Type uCertificate} {Wire : Type uWire}
    {codec : PartialCodec Certificate Wire}
    {Evidence : Certificate → Type uEvidence} {wire : Wire}
    (avoids : ∀ certificate, codec.encode certificate ≠ wire) :
    UniversalFibre codec Evidence wire := by
  intro certificate equality
  exact False.elim (avoids certificate equality)

namespace PresentationSemantics

/-- Enlarge an existing rule interpretation by a universal fibre whose
canonical image no retained rule can conclude.  Ordered premise evidence is
projected pointwise; no occurrence is dropped from the source derivation. -/
def productWithVacuousFibre
    {Certificate : Type uCertificate}
    {presentation : ValidatedPresentation}
    {LeftMeaning : Pattern → Type uEvidence}
    (semantics : PresentationSemantics presentation LeftMeaning)
    (codec : PartialCodec Certificate Pattern)
    (Evidence : Certificate → Type uEvidence)
    (avoids : PresentationConclusionsAvoid presentation codec) :
    PresentationSemantics presentation
      (fun wire => LeftMeaning wire × UniversalFibre codec Evidence wire) where
  ruleMeaning := by
    intro ruleInstance premises conclusion application premiseEvidence
    exact
      ⟨semantics.ruleMeaning application
          (premiseEvidence.map (fun _ evidence => evidence.1)),
        universalFibreOfAvoids (avoids application)⟩

end PresentationSemantics

/-- Negative control: one actual rule application at an encoded conclusion
refutes the avoidance premise.  A nonempty new judgment family therefore
cannot be smuggled in through the vacuous-fibre construction. -/
theorem no_presentationConclusionsAvoid_of_ruleApplication_encoding
    {Certificate : Type uCertificate}
    {presentation : ValidatedPresentation}
    {codec : PartialCodec Certificate Pattern}
    {ruleInstance premises conclusion}
    (application :
      RuleApplication presentation ruleInstance premises conclusion)
    (certificate : Certificate)
    (equality : codec.encode certificate = conclusion) :
    ¬ PresentationConclusionsAvoid presentation codec := by
  intro avoids
  exact avoids application certificate equality

/-- The universal and positive fibres are simultaneously inhabited on every
supported wire.  This is deliberately an image-local theorem. -/
theorem nonempty_positive_iff_nonempty_universal_of_inImage
    {Certificate : Type uCertificate} {Wire : Type uWire}
    {codec : PartialCodec Certificate Wire}
    {Evidence : Certificate → Type uEvidence} {wire : Wire}
    [DecidableEq Wire]
    (support : InImage codec wire) :
    Nonempty (PositiveFibre codec Evidence wire) ↔
      Nonempty (UniversalFibre codec Evidence wire) := by
  constructor
  · rintro ⟨positive⟩
    exact ⟨positive.toUniversal⟩
  · rintro ⟨universal⟩
    exact ⟨universal.toPositive support⟩

/-- Away from the canonical image, a positive fibre is genuinely empty. -/
theorem noPositiveFibre_of_not_inImage
    {Certificate : Type uCertificate} {Wire : Type uWire}
    {codec : PartialCodec Certificate Wire}
    {Evidence : Certificate → Type uEvidence} {wire : Wire}
    (unsupported : ¬ InImage codec wire) :
    PositiveFibre codec Evidence wire → False := by
  intro positive
  exact unsupported positive.support

/-! ## Canonical-premise closure -/

/-- Every occurrence in an ordered premise vector is in the canonical image.
Occurrence membership is retained; this is not a set quotient. -/
def PremisesInImage {Certificate : Type uCertificate} {Wire : Type uWire}
    (codec : PartialCodec Certificate Wire) (premises : List Wire) : Prop :=
  ∀ premise, premise ∈ premises → InImage codec premise

/-- The local surface property required of one instantiated rule. -/
def PremisesClosedAt {Certificate : Type uCertificate} {Wire : Type uWire}
    (codec : PartialCodec Certificate Wire) (premises : List Wire)
    (conclusion : Wire) : Prop :=
  InImage codec conclusion → PremisesInImage codec premises

/-- A validated presentation is canonical-premise closed when every
declarative rule application with a canonical conclusion has canonical
ordered premises.  It does not require arbitrary raw conclusions to decode. -/
def CanonicalPremiseClosed {Certificate : Type uCertificate}
    (presentation : ValidatedPresentation)
    (codec : PartialCodec Certificate Pattern) : Prop :=
  ∀ ruleInstance premises conclusion,
    RuleApplication presentation ruleInstance premises conclusion →
      PremisesClosedAt codec premises conclusion

namespace EvidenceList

/-- Canonical-premise support converts ordered universal evidence into
ordered positive evidence without dropping or deduplicating occurrences. -/
def toPositive {Certificate : Type uCertificate}
    {codec : PartialCodec Certificate Pattern}
    {Evidence : Certificate → Type uEvidence} :
    {premises : List Pattern} →
      EvidenceList (UniversalFibre codec Evidence) premises →
      PremisesInImage codec premises →
      EvidenceList (PositiveFibre codec Evidence) premises
  | [], .nil, _ => .nil
  | premise :: premises, .cons head tail, support =>
      .cons
        (head.toPositive (support premise (by simp)))
        (toPositive tail (fun candidate membership =>
          support candidate (by simp [membership])))

end EvidenceList

/-! ## Positive semantics induces total raw semantics -/

/-- Native rule semantics is stated only at canonical conclusions and consumes
positive premise evidence.  Closure is the separate surface theorem that
justifies this consumption. -/
structure PositivePresentationSemantics
    {Certificate : Type uCertificate}
    (presentation : ValidatedPresentation)
    (codec : PartialCodec Certificate Pattern)
    (Evidence : Certificate → Type uEvidence) where
  premiseClosed : CanonicalPremiseClosed presentation codec
  ruleMeaning : ∀ {ruleInstance premises conclusion},
    RuleApplication presentation ruleInstance premises conclusion →
      InImage codec conclusion →
      EvidenceList (PositiveFibre codec Evidence) premises →
      PositiveFibre codec Evidence conclusion

namespace PositivePresentationSemantics

variable {Certificate : Type uCertificate}
    {presentation : ValidatedPresentation}
    {codec : PartialCodec Certificate Pattern}
    {Evidence : Certificate → Type uEvidence}

/-- The total relational interpretation induced by positive native rule
semantics.  For a noncanonical conclusion the returned universal function has
no inputs; for a canonical conclusion, premise closure supplies every positive
child required by the rule. -/
def toPresentationSemantics
    (semantics : PositivePresentationSemantics presentation codec Evidence) :
    PresentationSemantics presentation (UniversalFibre codec Evidence) where
  ruleMeaning := by
    intro ruleInstance premises conclusion application premiseEvidence
      certificate equality
    let conclusionSupport : InImage codec conclusion :=
      ⟨certificate, equality⟩
    let premiseSupport : PremisesInImage codec premises :=
      semantics.premiseClosed ruleInstance premises conclusion application
        conclusionSupport
    let positivePremises :=
      Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure.EvidenceList.toPositive
        premiseEvidence premiseSupport
    let positiveConclusion :=
      semantics.ruleMeaning application conclusionSupport positivePremises
    exact PositiveFibre.toUniversal positiveConclusion certificate equality

/-- A checked derivation of a canonical wire therefore produces a positive
native point.  The derivation itself continues to retain exact raw proof
identity independently of this semantic projection. -/
def interpretPositive
    (semantics : PositivePresentationSemantics presentation codec Evidence)
    {goal : Pattern} (derivation : Derivation presentation goal)
    (support : InImage codec goal) : PositiveFibre codec Evidence goal :=
  (semantics.toPresentationSemantics.interpret derivation).toPositive support

end PositivePresentationSemantics

/-! ## Controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec.Canary

abbrev UnitEvidence (_ : Bool) := Unit

abbrev UnitChoiceEvidence (_ : Unit) := Unit

def zeroUnitUniversal :
    UniversalFibre zeroUnit UnitChoiceEvidence 0 := by
  intro _ _
  exact ()

def oneUnitUniversalAtZero :
    UniversalFibre oneUnit UnitChoiceEvidence 0 := by
  intro value equality
  cases value
  simp [oneUnit] at equality

/-- Positive control for the coproduct law: independently supplied meanings
interpret the left summand of the combined exact codec without inspecting or
coercing the right evidence family. -/
theorem unitChoice_product_interprets_left :
    (universalFibre_product_equiv_sumOfDisjoint zeroUnit oneUnit
      zero_one_disjoint UnitChoiceEvidence UnitChoiceEvidence 0).toFun
        ⟨zeroUnitUniversal, oneUnitUniversalAtZero⟩ (.inl ()) rfl = () :=
  rfl

/-- The tolerant alias has a vacuous universal meaning. -/
def aliasUniversal :
    UniversalFibre tolerantBool UnitEvidence 2 := by
  intro certificate equality
  exact False.elim (alias_is_not_in_encoder_image
    ⟨certificate, equality⟩)

/-- The same alias has no positive native meaning. -/
theorem aliasPositive_empty :
    PositiveFibre tolerantBool UnitEvidence 2 → False :=
  noPositiveFibre_of_not_inImage alias_is_not_in_encoder_image

/-- Therefore no unrestricted conversion from universal to positive evidence
can exist.  Canonical support is a necessary input, not an implementation
detail. -/
theorem no_global_universal_to_positive :
    ¬ Nonempty
      (UniversalFibre tolerantBool UnitEvidence 2 →
        PositiveFibre tolerantBool UnitEvidence 2) := by
  rintro ⟨conversion⟩
  exact aliasPositive_empty (conversion aliasUniversal)

def canonicalPremises : List Nat := [0, 1]

theorem canonicalPremises_inImage :
    PremisesInImage tolerantBool canonicalPremises := by
  intro premise membership
  simp [canonicalPremises] at membership
  rcases membership with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

/-- A canonical conclusion does not rescue a hidden noncanonical premise. -/
theorem hiddenAlias_not_closed :
    ¬ PremisesClosedAt tolerantBool [2] 0 := by
  intro closed
  have premiseSupported := closed ⟨false, rfl⟩ 2 (by simp)
  exact alias_is_not_in_encoder_image premiseSupported

end Canary

#print axioms nonempty_positive_iff_nonempty_universal_of_inImage
#print axioms universalFibre_product_equiv_sumOfDisjoint
#print axioms PresentationSemantics.productWithVacuousFibre
#print axioms no_presentationConclusionsAvoid_of_ruleApplication_encoding
#print axioms noPositiveFibre_of_not_inImage
#print axioms EvidenceList.toPositive
#print axioms PositivePresentationSemantics.toPresentationSemantics
#print axioms PositivePresentationSemantics.interpretPositive
#print axioms Canary.no_global_universal_to_positive
#print axioms Canary.hiddenAlias_not_closed
#print axioms Canary.unitChoice_product_interprets_left

end Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure
