import Mettapedia.TypeTheory.ContextualCode
import Mettapedia.TypeTheory.EqualityFamilyObserverFactorization

/-!
# Dependent observations of contextual code

A beta-correct quote/splice interface is a split readout from retained code to
its spliced body.  The generic dependent-family criterion therefore gives an
exact admission law for data indexed by code: the family may be observed at
the body level precisely when every code fibre is equivalent to the fibre at
its canonical quote-after-splice representative.

For ordinary source equality, this condition specializes further.  Equality
families factor through splicing exactly when the readout is exact, which is
exactly the quote/splice eta law.  Thus beta supports a canonical extensional
body view; eta is the additional price of claiming that no code identity was
lost.

No staging syntax, evaluator, demand policy, or concrete language calculus is
selected here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCodeObserverFactorization

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.ContextualCode
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.EqualityFamilyObserverFactorization
open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.SelectedModalIntroduction

universe u v w w' uFamily

variable {modes : ModeTheory} {cwf : ModalCwF modes}
variable {laws : ModalCwFLaws modes cwf}
variable {selection : WideSubtheory modes}
variable {quotation : SelectedQuotationTermStructure modes cwf laws selection}
variable {splicing : SelectedSpliceTermStructure modes cwf laws selection}

/-- A code-indexed dependent family factors through splicing exactly when it
is fibrewise equivalent to its value at canonical quote-after-splice code. -/
theorem familyFactorization_iff_quoteSpliceFibreEquivalences
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)}
    (family :
      cwf.Tm context (cwf.boxTy modality type) → Type uFamily) :
    Nonempty
        (FamilyFactorization
          (splicing.splice modality admitted) family) ↔
      Nonempty
        (∀ code,
          family code ≃
            family
              (quotation.introduce modality admitted
                (splicing.splice modality admitted code))) := by
  simpa [ContextualCode.SelectedQuoteSpliceBeta.readout,
    SplitReadout.canonicalize] using
      FamilyFactorization.nonempty_iff_canonicalFibreEquivalences
        (beta.readout modality admitted
          (context := context) (type := type)) family

/-- Ordinary code equality factors through splicing exactly when quote after
splice is eta-exact. -/
theorem equalityFamilyFactorization_iff_quoteSplice
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    Nonempty
        (EqualityFamilyFactorization
          (splicing.splice modality admitted :
            cwf.Tm context (cwf.boxTy modality type) →
              cwf.Tm (cwf.lock modality context) type)) ↔
      (∀ code : cwf.Tm context (cwf.boxTy modality type),
        quotation.introduce modality admitted
            (splicing.splice modality admitted code) = code) := by
  let codeReadout :=
    beta.readout modality admitted (context := context) (type := type)
  calc
    Nonempty
        (EqualityFamilyFactorization
          (splicing.splice modality admitted :
            cwf.Tm context (cwf.boxTy modality type) →
              cwf.Tm (cwf.lock modality context) type)) ↔
        codeReadout.Exact :=
      (splitReadout_exact_iff_equalityFamilyFactorization
        codeReadout).symm
    _ ↔ codeReadout.Faithful := codeReadout.exact_iff_faithful
    _ ↔ _ := beta.faithful_iff_quote_splice modality admitted

/-! ## Tagged-code controls -/

namespace Canary

/-- Code-indexed data which observes a retained Boolean code tag. -/
def tagSensitiveFamily : PUnit × Bool → Type
  | (_, false) => PUnit
  | (_, true) => Bool

/-- Body-constant data factors through the tagged code readout. -/
def constantTaggedFamilyFactors :
    FamilyFactorization
      (ContextualCode.FibreCanary.taggedReadout PUnit).observe
      (fun _ => PUnit) :=
  FamilyFactorization.constant
    (ContextualCode.FibreCanary.taggedReadout PUnit).observe PUnit

/-- Tag-sensitive dependent data cannot descend to the spliced body. -/
theorem tagSensitiveFamily_does_not_factor :
    ¬ Nonempty
      (FamilyFactorization
        (ContextualCode.FibreCanary.taggedReadout PUnit).observe
        tagSensitiveFamily) := by
  exact FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := (PUnit.unit, false)) (right := (PUnit.unit, true)) rfl
    DependentFamilyObserverFactorization.Canary.unit_not_equiv_bool

/-- The tagged readout cannot preserve source equality either, because its
retained code tag makes it non-exact. -/
theorem taggedEquality_does_not_factor :
    ¬ Nonempty
      (EqualityFamilyFactorization
        (ContextualCode.FibreCanary.taggedReadout PUnit).observe) := by
  rw [EqualityFamilyFactorization.nonempty_iff_injective]
  intro injective
  have impossible : (PUnit.unit, false) = (PUnit.unit, true) :=
    injective rfl
  exact Bool.false_ne_true (congrArg Prod.snd impossible)

/-- Paired boundary: body-constant families descend through beta, while
tag-sensitive data and source equality both require distinctions which the
tagged body readout does not retain. -/
theorem contextual_code_observer_boundary :
    Nonempty
        (FamilyFactorization
          (ContextualCode.FibreCanary.taggedReadout PUnit).observe
          (fun _ => PUnit)) ∧
      ¬ Nonempty
        (FamilyFactorization
          (ContextualCode.FibreCanary.taggedReadout PUnit).observe
          tagSensitiveFamily) ∧
      ¬ Nonempty
        (EqualityFamilyFactorization
          (ContextualCode.FibreCanary.taggedReadout PUnit).observe) :=
  ⟨⟨constantTaggedFamilyFactors⟩,
    tagSensitiveFamily_does_not_factor,
    taggedEquality_does_not_factor⟩

end Canary

#print axioms familyFactorization_iff_quoteSpliceFibreEquivalences
#print axioms equalityFamilyFactorization_iff_quoteSplice
#print axioms Canary.tagSensitiveFamily_does_not_factor
#print axioms Canary.taggedEquality_does_not_factor
#print axioms Canary.contextual_code_observer_boundary

end Mettapedia.TypeTheory.ContextualCodeObserverFactorization
