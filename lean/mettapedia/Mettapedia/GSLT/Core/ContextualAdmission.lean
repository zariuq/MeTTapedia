import Mettapedia.GSLT.Core.ContextualLadderTerminal

/-!
# Restricting a contextual structure by retained derivations

A contextual structure supplies syntax and its strict substitution laws.
This construction restricts it to the support of Type-valued formation,
typing, and substitution families. The closure operations consume actual
derivations. Their support supplies admission, without selecting a derivation
from `Nonempty` or identifying two supplied derivations.

This is a conditional construction for any contextual structure. An instance
for a calculus must separately define its rules and prove their structural
admissibility. No functoriality law on derivation trees, initiality theorem,
conversion quotient, or checking algorithm is assumed or obtained here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

universe u v w w' e

/-- Retained judgments and the structural operations needed to restrict a
contextual structure. Evidence operations have no imposed proof-irrelevance
or identity/composition equations. -/
structure CwfDerivations (C : Cwf.{u, v, w, w'}) where
  context : C.Ctx → Type e
  type : (Γ : C.Ctx) → C.Ty Γ → Type e
  term : (Γ : C.Ctx) → (A : C.Ty Γ) → C.Tm Γ A → Type e
  substitution : (Γ Δ : C.Ctx) → C.Sub Γ Δ → Type e
  identityDerivation : ∀ Γ, context Γ → substitution Γ Γ (C.idS Γ)
  composeDerivation : ∀ {Γ Δ Θ} (σ : C.Sub Δ Θ) (τ : C.Sub Γ Δ),
    context Γ → context Δ → context Θ →
    substitution Δ Θ σ → substitution Γ Δ τ →
    substitution Γ Θ (C.compS σ τ)
  reindexType : ∀ {Γ Δ} (A : C.Ty Δ) (σ : C.Sub Γ Δ),
    context Γ → context Δ → type Δ A → substitution Γ Δ σ →
    type Γ (C.tySub A σ)
  reindexTerm : ∀ {Γ Δ} {A : C.Ty Δ} (t : C.Tm Δ A) (σ : C.Sub Γ Δ),
    context Γ → context Δ → type Δ A → term Δ A t →
    substitution Γ Δ σ → term Γ (C.tySub A σ) (C.tmSub t σ)
  extendDerivation : ∀ Γ (A : C.Ty Γ), context Γ → type Γ A → context (C.ext Γ A)
  projectionDerivation : ∀ Γ (A : C.Ty Γ), context Γ → type Γ A →
    substitution (C.ext Γ A) Γ (C.wk A)
  variableDerivation : ∀ Γ (A : C.Ty Γ), context Γ → type Γ A →
    term (C.ext Γ A) (C.tySub A (C.wk A)) (C.vz A)
  pairing : ∀ {Γ Δ} (σ : C.Sub Γ Δ) (A : C.Ty Δ)
    (t : C.Tm Γ (C.tySub A σ)),
    context Γ → context Δ → substitution Γ Δ σ → type Δ A →
    term Γ (C.tySub A σ) t → substitution Γ (C.ext Δ A) (C.pair σ A t)

namespace CwfDerivations

variable {C : Cwf.{u, v, w, w'}} (D : CwfDerivations.{u, v, w, w', e} C)

abbrev Context := { Γ : C.Ctx // Nonempty (D.context Γ) }
abbrev TypeOver (Γ : D.Context) := { A : C.Ty Γ.val // Nonempty (D.type Γ.val A) }
abbrev Term (Γ : D.Context) (A : D.TypeOver Γ) :=
  { t : C.Tm Γ.val A.val // Nonempty (D.term Γ.val A.val t) }
abbrev Substitution (Γ Δ : D.Context) :=
  { σ : C.Sub Γ.val Δ.val // Nonempty (D.substitution Γ.val Δ.val σ) }

def identity (Γ : D.Context) : D.Substitution Γ Γ :=
  ⟨C.idS Γ.val, by
    obtain ⟨formed⟩ := Γ.property
    exact ⟨D.identityDerivation Γ.val formed⟩⟩

def compose {Γ Δ Θ : D.Context} (σ : D.Substitution Δ Θ)
    (τ : D.Substitution Γ Δ) : D.Substitution Γ Θ :=
  ⟨C.compS σ.val τ.val, by
    obtain ⟨formedΓ⟩ := Γ.property
    obtain ⟨formedΔ⟩ := Δ.property
    obtain ⟨formedΘ⟩ := Θ.property
    obtain ⟨typedσ⟩ := σ.property
    obtain ⟨typedτ⟩ := τ.property
    exact ⟨D.composeDerivation σ.val τ.val formedΓ formedΔ formedΘ typedσ typedτ⟩⟩

def typeSubstitution {Γ Δ : D.Context} (A : D.TypeOver Δ)
    (σ : D.Substitution Γ Δ) : D.TypeOver Γ :=
  ⟨C.tySub A.val σ.val, by
    obtain ⟨formedΓ⟩ := Γ.property
    obtain ⟨formedΔ⟩ := Δ.property
    obtain ⟨formedA⟩ := A.property
    obtain ⟨typedσ⟩ := σ.property
    exact ⟨D.reindexType A.val σ.val formedΓ formedΔ formedA typedσ⟩⟩

def termSubstitution {Γ Δ : D.Context} {A : D.TypeOver Δ}
    (t : D.Term Δ A) (σ : D.Substitution Γ Δ) :
    D.Term Γ (D.typeSubstitution A σ) :=
  ⟨C.tmSub t.val σ.val, by
    obtain ⟨formedΓ⟩ := Γ.property
    obtain ⟨formedΔ⟩ := Δ.property
    obtain ⟨formedA⟩ := A.property
    obtain ⟨typed⟩ := t.property
    obtain ⟨typedσ⟩ := σ.property
    exact ⟨D.reindexTerm t.val σ.val formedΓ formedΔ formedA typed typedσ⟩⟩

def extend (Γ : D.Context) (A : D.TypeOver Γ) : D.Context :=
  ⟨C.ext Γ.val A.val, by
    obtain ⟨formedΓ⟩ := Γ.property
    obtain ⟨formedA⟩ := A.property
    exact ⟨D.extendDerivation Γ.val A.val formedΓ formedA⟩⟩

def projection {Γ : D.Context} (A : D.TypeOver Γ) :
    D.Substitution (D.extend Γ A) Γ :=
  ⟨C.wk A.val, by
    obtain ⟨formedΓ⟩ := Γ.property
    obtain ⟨formedA⟩ := A.property
    exact ⟨D.projectionDerivation Γ.val A.val formedΓ formedA⟩⟩

def newest {Γ : D.Context} (A : D.TypeOver Γ) :
    D.Term (D.extend Γ A) (D.typeSubstitution A (D.projection A)) :=
  ⟨C.vz A.val, by
    obtain ⟨formedΓ⟩ := Γ.property
    obtain ⟨formedA⟩ := A.property
    exact ⟨D.variableDerivation Γ.val A.val formedΓ formedA⟩⟩

def pair {Γ Δ : D.Context} (σ : D.Substitution Γ Δ) (A : D.TypeOver Δ)
    (t : D.Term Γ (D.typeSubstitution A σ)) : D.Substitution Γ (D.extend Δ A) :=
  ⟨C.pair σ.val A.val t.val, by
    obtain ⟨formedΓ⟩ := Γ.property
    obtain ⟨formedΔ⟩ := Δ.property
    obtain ⟨typedσ⟩ := σ.property
    obtain ⟨formedA⟩ := A.property
    obtain ⟨typed⟩ := t.property
    exact ⟨D.pairing σ.val A.val t.val formedΓ formedΔ typedσ formedA typed⟩⟩

theorem term_heq {Γ : D.Context} {A B : D.TypeOver Γ}
    (sameType : A.val = B.val) {t : D.Term Γ A} {u : D.Term Γ B}
    (sameTerm : HEq t.val u.val) : HEq t u := by
  have same : A = B := Subtype.ext sameType
  cases same
  exact heq_of_eq (Subtype.ext (eq_of_heq sameTerm))

theorem cast_term_val {Γ : D.Context} {A B : D.TypeOver Γ}
    (sameType : A = B) (equal : D.Term Γ A = D.Term Γ B) (t : D.Term Γ A) :
    HEq (cast equal t).val t.val := by
  cases sameType
  cases equal
  rfl

theorem cast_term_val_eq {Γ : D.Context} {A B : D.TypeOver Γ}
    (sameType : A = B) (equal : D.Term Γ A = D.Term Γ B) (t : D.Term Γ A) :
    (cast equal t).val =
      cast (congrArg (C.Tm Γ.val) (congrArg Subtype.val sameType)) t.val := by
  cases sameType
  cases equal
  rfl

theorem typeSubstitution_identity {Γ : D.Context} (A : D.TypeOver Γ) :
    D.typeSubstitution A (D.identity Γ) = A :=
  Subtype.ext (C.tySub_id A.val)

theorem typeSubstitution_compose {Γ Δ Θ : D.Context} (A : D.TypeOver Θ)
    (σ : D.Substitution Δ Θ) (τ : D.Substitution Γ Δ) :
    D.typeSubstitution A (D.compose σ τ) =
      D.typeSubstitution (D.typeSubstitution A σ) τ :=
  Subtype.ext (C.tySub_comp A.val σ.val τ.val)

theorem termSubstitution_identity {Γ : D.Context} {A : D.TypeOver Γ}
    (t : D.Term Γ A) : HEq (D.termSubstitution t (D.identity Γ)) t :=
  D.term_heq (C.tySub_id A.val)
    ((heq_of_eq (C.tmSub_id t.val)).trans (cast_heq _ t.val))

theorem termSubstitution_compose {Γ Δ Θ : D.Context} {A : D.TypeOver Θ}
    (t : D.Term Θ A) (σ : D.Substitution Δ Θ) (τ : D.Substitution Γ Δ) :
    HEq (D.termSubstitution t (D.compose σ τ))
      (D.termSubstitution (D.termSubstitution t σ) τ) :=
  D.term_heq (C.tySub_comp A.val σ.val τ.val)
    ((heq_of_eq (C.tmSub_comp t.val σ.val τ.val)).trans (cast_heq _ _))

/-- Restriction to admitted syntax is a strict contextual structure. Its
equalities concern the supported syntax, not the retained derivation fibres. -/
def admitted : Cwf.{u, v, w, w'} where
  Ctx := D.Context
  Sub := D.Substitution
  idS := D.identity
  compS := D.compose
  id_comp σ := Subtype.ext (C.id_comp σ.val)
  comp_id σ := Subtype.ext (C.comp_id σ.val)
  comp_assoc σ τ ρ := Subtype.ext (C.comp_assoc σ.val τ.val ρ.val)
  Ty := D.TypeOver
  tySub := D.typeSubstitution
  tySub_id := D.typeSubstitution_identity
  tySub_comp := D.typeSubstitution_compose
  Tm := D.Term
  tmSub := D.termSubstitution
  tmSub_id t := eq_of_heq ((D.termSubstitution_identity t).trans (cast_heq _ t).symm)
  tmSub_comp t σ τ := eq_of_heq
    ((D.termSubstitution_compose t σ τ).trans (cast_heq _ _).symm)
  ext := D.extend
  wk := D.projection
  vz := D.newest
  pair := D.pair
  wk_pair σ A t := Subtype.ext (C.wk_pair σ.val A.val t.val)
  vz_pair := by
    intro Γ Δ σ A t
    apply eq_of_heq
    refine (D.term_heq ?_ ?_).trans (cast_heq _ t).symm
    · exact (C.tySub_comp A.val (C.wk A.val) (C.pair σ.val A.val t.val)).symm.trans
        (congrArg (C.tySub A.val) (C.wk_pair σ.val A.val t.val))
    · exact (heq_of_eq (C.vz_pair σ.val A.val t.val)).trans (cast_heq _ t.val)
  pair_eta := by
    intro Γ Δ A σ
    apply Subtype.ext
    change C.pair (C.compS (C.wk A.val) σ.val) A.val
      (cast _ (D.termSubstitution (D.newest A) σ) :
        D.Term Γ (D.typeSubstitution A (D.compose (D.projection A) σ))).val = σ.val
    rw [D.cast_term_val_eq
      (D.typeSubstitution_compose A (D.projection A) σ).symm]
    exact C.pair_eta A.val σ.val

/-- Evidence over an admitted term remains the original Type-valued fibre. -/
abbrev TermEvidence {Γ : D.Context} {A : D.TypeOver Γ} (t : D.Term Γ A) :=
  D.term Γ.val A.val t.val

/-- Supply the admission view without discarding the accompanying tree. -/
def retainTerm {Γ : D.Context} {A : D.TypeOver Γ} {t : C.Tm Γ.val A.val}
    (evidence : D.term Γ.val A.val t) :
    Σ t : D.Term Γ A, D.TermEvidence t :=
  ⟨⟨t, ⟨evidence⟩⟩, evidence⟩

theorem retainTerm_injective {Γ : D.Context} {A : D.TypeOver Γ}
    {t : C.Tm Γ.val A.val} :
    Function.Injective (D.retainTerm (Γ := Γ) (A := A) (t := t)) := by
  intro first second equal
  exact eq_of_heq (Sigma.mk.inj equal).2

/-- Terminality requires actual evidence for the empty context and each
empty substitution, beyond the terminal-free closure operations. -/
def admittedWithTerminal (T : CwfWithTerminal.{u, v, w, w'})
    (D : CwfDerivations.{u, v, w, w', e} T.toCwf)
    (empty : D.context T.empty)
    (toEmpty : ∀ Γ, D.context Γ → D.substitution Γ T.empty (T.toEmpty Γ)) :
    CwfWithTerminal.{u, v, w, w'} where
  toCwf := D.admitted
  empty := ⟨T.empty, ⟨empty⟩⟩
  toEmpty Γ := ⟨T.toEmpty Γ.val, by
    obtain ⟨formed⟩ := Γ.property
    exact ⟨toEmpty Γ.val formed⟩⟩
  toEmpty_unique Γ σ := Subtype.ext (T.toEmpty_unique Γ.val σ.val)

end CwfDerivations

end Mettapedia.GSLT.Core.ContextualLadder
