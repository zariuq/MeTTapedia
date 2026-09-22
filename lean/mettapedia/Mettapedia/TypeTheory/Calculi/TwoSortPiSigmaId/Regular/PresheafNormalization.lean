import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.PresheafSemantics

/-!
# Normalization and substitution of represented regular terms

The existing executable normalizer acts on regularly typed source terms and
therefore on their represented natural sections. It preserves typing and
decides the existing fragment conversion relation. Substitution can create a
new redex: normalization commutes with it after normalizing the substituted
term, not as an equality of unreduced syntax.

This normal-form observation retains the source type index. It is not a
quotient of the whole CwF's contexts and types by conversion.
-/

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SyntacticCwf

open Syntax Substitution Regular
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction
open Mettapedia.TypeTheory

/-- Coverage follows from the actual regular judgment of the source term. -/
def normalizationInput {Γ : Context} {A : Ty Γ} (term : Tm Γ A) :
    RegularNormalizationTerm Γ.length :=
  ⟨term.val, regularNormalizationSpecification.covers_subject
    ⟨Γ.regular, term.property⟩⟩

/-- The existing executable normalizer returns a term of the original type;
subject reduction supplies the typing proof. -/
def normalizeTerm {Γ : Context} {A : Ty Γ} (term : Tm Γ A) : Tm Γ A :=
  ⟨regularNormalizationSpecification.normalize term.val (normalizationInput term).property,
    term.property.subject_reduction_star Γ.regular
      (regularNormalizationSpecification.reduces term.val (normalizationInput term).property)⟩

theorem normalizeTerm_reduces {Γ : Context} {A : Ty Γ} (term : Tm Γ A) :
    RedStar term.val (normalizeTerm term).val :=
  regularNormalizationSpecification.reduces term.val (normalizationInput term).property

theorem normalizeTerm_normal {Γ : Context} {A : Ty Γ} (term : Tm Γ A) :
    RedNormal (normalizeTerm term).val :=
  regularNormalizationSpecification.irreducible term.val (normalizationInput term).property

theorem normalizeTerm_converts {Γ : Context} {A : Ty Γ} (term : Tm Γ A) :
    ConstantFreeConv term.val (normalizeTerm term).val :=
  ((term.property.constantFree_both Γ.regular.constantFreeCtx).1.redStar
    (normalizeTerm_reduces term)).1

/-- Equality of computed normal terms is exactly fragment conversion, not
equality of the original source terms. -/
theorem normalizeTerm_eq_iff {Γ : Context} {A : Ty Γ} (left right : Tm Γ A) :
    normalizeTerm left = normalizeTerm right ↔ ConstantFreeConv left.val right.val := by
  rw [Subtype.ext_iff]
  exact regularNormalizationSpecification.toNormalizationSpecification.normalize_eq_iff_converts
    (normalizationInput left) (normalizationInput right)

theorem normalizeTerm_idempotent {Γ : Context} {A : Ty Γ} (term : Tm Γ A) :
    normalizeTerm (normalizeTerm term) = normalizeTerm term :=
  Subtype.ext ((normalizeTerm_normal term).redStar_eq
    (normalizeTerm_reduces (normalizeTerm term)))

/-- The executable normalization/substitution law. Source normalization may
be performed before substitution provided the result is normalized again. -/
theorem normalizeTerm_substitution {Γ Δ : Context} {A : Ty Γ}
    (term : Tm Γ A) (σ : Hom Δ Γ) :
    normalizeTerm (termSub (normalizeTerm term) σ) =
      normalizeTerm (termSub term σ) := by
  apply (normalizeTerm_eq_iff _ _).2
  exact (normalizeTerm_converts term).symm.subst σ.val σ.property.constantFree

/-- Read a represented term, run the existing source normalizer, and retain
the resulting typed source term as a natural semantic section. -/
def normalizeSection {Γ : Context} {A : Ty Γ}
    (sectionValue : (representedFamily A).sections) : (representedFamily A).sections :=
  representedTermEquiv A (normalizeTerm ((representedTermEquiv A).symm sectionValue))

theorem normalizeSection_interpret {Γ : Context} {A : Ty Γ} (term : Tm Γ A) :
    normalizeSection (representedTermEquiv A term) =
      representedTermEquiv A (normalizeTerm term) := by
  simp only [normalizeSection, Equiv.symm_apply_apply]

/-- The normal-form observation identifies exactly convertible represented
source terms. The original representation still distinguishes their code. -/
theorem normalizeSection_eq_iff {Γ : Context} {A : Ty Γ} (left right : Tm Γ A) :
    normalizeSection (representedTermEquiv A left) =
        normalizeSection (representedTermEquiv A right) ↔
      ConstantFreeConv left.val right.val := by
  rw [normalizeSection_interpret, normalizeSection_interpret, Equiv.apply_eq_iff_eq]
  exact normalizeTerm_eq_iff left right

/-- The existing direct conversion decision decides equality of the
normal-form observations; it does not decide equality of retained code. -/
theorem decided_conversion_iff_normalized_sections {Γ : Context} {A : Ty Γ}
    (left right : Tm Γ A) :
    (regularDecidedConversion Γ.length).decide
        (normalizationInput left) (normalizationInput right) = true ↔
      normalizeSection (representedTermEquiv A left) =
        normalizeSection (representedTermEquiv A right) :=
  (regularDecidedConversion_correct (normalizationInput left)
    (normalizationInput right)).trans (normalizeSection_eq_iff left right).symm

theorem normalizeSection_substitution {Γ Δ : Context} {A : Ty Γ}
    (term : Tm Γ A) (σ : Hom Δ Γ) :
    normalizeSection (representedTermEquiv (typeSub A σ)
        (termSub (normalizeTerm term) σ)) =
      normalizeSection (representedTermEquiv (typeSub A σ) (termSub term σ)) := by
  rw [normalizeSection_interpret, normalizeSection_interpret,
    normalizeTerm_substitution]

/-- An actual accepted checker result enters the representation and its
normal-form observation. At every subsequent source substitution, executing
the observed program gives exactly the normal form of the substituted
checked program. The successful checker computation is retained. -/
theorem accepted_has_normalizing_representation {Γ : Context} (A : Ty Γ)
    (term : ScopedTerm Γ.length)
    (accepted : regularCheckBool Γ.regular term A.val = true) :
    ∃ checked : RegularChecked (Γ := Γ.raw) term A.val,
      checkRegularType Γ.regular term A.val = .ok checked ∧
      ∀ (Δ : Context) (σ : Hom Δ Γ),
        normalizeTerm (CwfYoneda.decodeTerm cwf A σ
          ((normalizeSection (representedTermEquiv A (termOfChecked checked))).val
            ⟨Opposite.op (CwfYoneda.context cwf Δ), σ⟩)) =
          normalizeTerm (termSub (termOfChecked checked) σ) := by
  obtain ⟨checked, computed, _⟩ := accepted_has_represented_term A term accepted
  refine ⟨checked, computed, ?_⟩
  intro Δ σ
  rw [normalizeSection_interpret, representedTerm_at]
  exact normalizeTerm_substitution (termOfChecked checked) σ

/-! ## Inhabited computation and substitution controls -/

theorem sampleTerm_normal : RedNormal sampleTerm.val := by
  intro target step
  change Red (.var (0 : Fin 1)) target at step
  cases step

theorem normalize_sampleTerm : normalizeTerm sampleTerm = sampleTerm :=
  Subtype.ext (sampleTerm_normal.redStar_eq (normalizeTerm_reduces sampleTerm))

theorem normalize_sampleBeta : normalizeTerm sampleBeta = sampleTerm := by
  rw [← normalize_sampleTerm]
  exact (normalizeTerm_eq_iff sampleBeta sampleTerm).2
    beta_conversion_does_not_collapse_sections.1

/-- Replace the only source variable by a regularly typed beta redex. -/
def betaSubstitution : Hom sampleContext sampleContext :=
  pair (toEmpty sampleContext) (smallSort empty) sampleBeta

theorem betaSubstitution_variable : termSub sampleTerm betaSubstitution = sampleBeta :=
  Subtype.ext rfl

/-- Substituting into a normal variable can introduce a redex. Consequently
the second normalization in `normalizeTerm_substitution` is indispensable. -/
theorem normalization_does_not_commute_with_raw_substitution :
    normalizeTerm (termSub sampleTerm betaSubstitution) ≠
      termSub (normalizeTerm sampleTerm) betaSubstitution := by
  rw [normalize_sampleTerm]
  change normalizeTerm sampleBeta ≠ sampleBeta
  rw [normalize_sampleBeta]
  intro equal
  have raw := congrArg Subtype.val equal
  cases raw

/-- Normal-form observation erases a real code distinction without changing
the equality of the syntax-retaining representation. -/
theorem normalized_sections_collapse_beta_only :
    normalizeSection (representedTermEquiv (smallSort sampleContext) sampleBeta) =
        normalizeSection (representedTermEquiv (smallSort sampleContext) sampleTerm) ∧
      representedTermEquiv (smallSort sampleContext) sampleBeta ≠
        representedTermEquiv (smallSort sampleContext) sampleTerm :=
  ⟨(normalizeSection_eq_iff sampleBeta sampleTerm).2
      beta_conversion_does_not_collapse_sections.1,
    beta_conversion_does_not_collapse_sections.2⟩

#print axioms normalizeTerm
#print axioms normalizeTerm_eq_iff
#print axioms normalizeTerm_substitution
#print axioms normalizeSection_eq_iff
#print axioms decided_conversion_iff_normalized_sections
#print axioms normalizeSection_substitution
#print axioms accepted_has_normalizing_representation
#print axioms normalization_does_not_commute_with_raw_substitution
#print axioms normalized_sections_collapse_beta_only

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SyntacticCwf
