import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualCategory
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualCategory
import Mettapedia.GSLT.Core.ContextualComprehension

/-!
# Categories with families from the actual dependent contexts

Both contextual presentations already provide formed types, typed terms,
substitution and comprehension. These adapters assemble their existing laws
into the common CwF interface without changing either judgment relation.
The formation-sensitive and typed-equality presentations remain distinct.
No equality of conversion theories is asserted by this construction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

namespace FormationSensitiveContextual

variable {Head : Type} {rules : Rules Head}

private theorem cast_term_heq {Γ : Context rules} {A B : TypeOver Γ}
    (same : A = B) (term : Term Γ A) : HEq (term.cast same) term := by
  cases same
  rfl

private theorem term_heq_of_type_code {Γ : Context rules} {A B : TypeOver Γ}
    (sameType : A = B) {first : Term Γ A} {second : Term Γ B}
    (sameCode : first.code = second.code) : HEq first second := by
  cases sameType
  exact heq_of_eq (Term.ext sameCode)

/-- The CwF of formation-sensitive contexts, using their actual syntax and judgments. -/
abbrev cwf (rules : Rules Head) : Cwf where
  Ctx := Context rules
  Sub Γ Δ := Γ ⟶ Δ
  idS Γ := 𝟙 Γ
  compS σ τ := τ ≫ σ
  id_comp σ := Category.comp_id σ
  comp_id σ := Category.id_comp σ
  comp_assoc σ τ ρ := (Category.assoc ρ τ σ).symm
  Ty := TypeOver
  tySub A σ := A.reindex σ
  tySub_id A := A.reindex_id
  tySub_comp A σ τ := A.reindex_comp τ σ
  Tm := Term
  tmSub term σ := term.reindex σ
  tmSub_id {Γ} {A} term := by
    have same : HEq (term.reindex (𝟙 Γ)) term :=
      (cast_term_heq A.reindex_id (term.reindex (𝟙 Γ))).symm.trans
        (heq_of_eq term.reindex_id)
    exact eq_of_heq (same.trans (cast_heq _ term).symm)
  tmSub_comp {Γ} {Δ} {Θ} {A} term σ τ := by
    have same : HEq (term.reindex (τ ≫ σ)) ((term.reindex σ).reindex τ) :=
      (cast_term_heq (A.reindex_comp τ σ) (term.reindex (τ ≫ σ))).symm.trans
        (heq_of_eq (term.reindex_comp τ σ))
    exact eq_of_heq (same.trans (cast_heq _ _).symm)
  ext := extend
  wk {Γ} A := projectionHom Γ A
  vz {Γ} A := newest Γ A
  pair σ _ term := pair σ term
  wk_pair σ _ term := pair_projection σ term
  vz_pair {Γ} {Δ} σ A term := by
    have sameType : (A.reindex (projectionHom Δ A)).reindex (pair σ term) = A.reindex σ := by
      rw [← TypeOver.reindex_comp, pair_projection]
    have same : HEq ((newest Δ A).reindex (pair σ term)) term :=
      term_heq_of_type_code sameType rfl
    exact eq_of_heq (same.trans (cast_heq _ term).symm)
  pair_eta A σ := by
    convert pair_eta σ using 1
    congr 1
    unfold pulledNewest
    exact eq_of_heq ((cast_heq _ _).trans (cast_term_heq _ _).symm)

theorem cwf_substitution_code {Γ Δ : Context rules} (σ : Δ ⟶ Γ)
    {A : TypeOver Γ} (term : Term Γ A) :
    ((cwf rules).tmSub term σ).code = subst σ.substitution term.code := rfl

theorem cwf_pair_code {Γ Δ : Context rules} (σ : Δ ⟶ Γ)
    (A : TypeOver Γ) (term : Term Δ (A.reindex σ)) :
    ((cwf rules).pair σ A term).substitution = consSub term.code σ.substitution := rfl

end FormationSensitiveContextual

namespace TypedContextual

variable {Head : Type} {rules : Rules Head}

private theorem cast_term_heq {Γ : Context rules} {A B : TypeOver Γ}
    (same : A = B) (term : Term Γ A) : HEq (term.cast same) term := by
  cases same
  rfl

private theorem term_heq_of_type_code {Γ : Context rules} {A B : TypeOver Γ}
    (sameType : A = B) {first : Term Γ A} {second : Term Γ B}
    (sameCode : first.code = second.code) : HEq first second := by
  cases sameType
  exact heq_of_eq (Term.ext sameCode)

/-- The CwF used by the typed-equality context family. This does not replace
typed equality by raw conversion or identify its terms with another model. -/
abbrev cwf (rules : Rules Head) : Cwf where
  Ctx := Context rules
  Sub Γ Δ := Γ ⟶ Δ
  idS Γ := 𝟙 Γ
  compS σ τ := τ ≫ σ
  id_comp σ := Category.comp_id σ
  comp_id σ := Category.id_comp σ
  comp_assoc σ τ ρ := (Category.assoc ρ τ σ).symm
  Ty := TypeOver
  tySub A σ := A.reindex σ
  tySub_id A := A.reindex_id
  tySub_comp A σ τ := A.reindex_comp τ σ
  Tm := Term
  tmSub term σ := term.reindex σ
  tmSub_id {Γ} {A} term := by
    have same : HEq (term.reindex (𝟙 Γ)) term :=
      (cast_term_heq A.reindex_id (term.reindex (𝟙 Γ))).symm.trans
        (heq_of_eq term.reindex_id)
    exact eq_of_heq (same.trans (cast_heq _ term).symm)
  tmSub_comp {Γ} {Δ} {Θ} {A} term σ τ := by
    have same : HEq (term.reindex (τ ≫ σ)) ((term.reindex σ).reindex τ) :=
      (cast_term_heq (A.reindex_comp τ σ) (term.reindex (τ ≫ σ))).symm.trans
        (heq_of_eq (term.reindex_comp τ σ))
    exact eq_of_heq (same.trans (cast_heq _ _).symm)
  ext := extend
  wk {Γ} A := projectionHom Γ A
  vz {Γ} A := newest Γ A
  pair σ _ term := pair σ term
  wk_pair σ _ term := pair_projection σ term
  vz_pair {Γ} {Δ} σ A term := by
    have sameType : (A.reindex (projectionHom Δ A)).reindex (pair σ term) = A.reindex σ := by
      rw [← TypeOver.reindex_comp, pair_projection]
    have same : HEq ((newest Δ A).reindex (pair σ term)) term :=
      term_heq_of_type_code sameType rfl
    exact eq_of_heq (same.trans (cast_heq _ term).symm)
  pair_eta A σ := by
    convert pair_eta σ using 1
    congr 1
    unfold pulledNewest
    exact eq_of_heq ((cast_heq _ _).trans (cast_term_heq _ _).symm)

theorem cwf_substitution_code {Γ Δ : Context rules} (σ : Δ ⟶ Γ)
    {A : TypeOver Γ} (term : Term Γ A) :
    ((cwf rules).tmSub term σ).code = subst σ.substitution term.code := rfl

theorem cwf_pair_code {Γ Δ : Context rules} (σ : Δ ⟶ Γ)
    (A : TypeOver Γ) (term : Term Δ (A.reindex σ)) :
    ((cwf rules).pair σ A term).substitution = consSub term.code σ.substitution := rfl

end TypedContextual

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
