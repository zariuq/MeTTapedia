import Mettapedia.TypeTheory.GeneratedFamilyUniverse

/-!
# Contextual operations of the generated enclosure

Generated codes can vary over an arbitrary context. Their decodings are actual
dependent families and their terms are actual sections. This module constructs
context extension and dependent code operations, and proves their substitution
laws together with abstraction/application and dependent equality elimination.

Identity is interpreted by the discrete equality fibres of the generated
grammar. The motive of J may depend on both endpoints and the witness. This
checks that particular model; no equality rule is transferred to another
calculus or to a richer observation without an interpretation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.GeneratedUniverseSubstitution

open GeneratedFamilyUniverse FamilyEnclosingUniverse

universe u v v' v''

variable {A : Type u} {B : A → Type u}
variable {Γ : Type v} {Δ : Type v'} {Θ : Type v''}

/-- Contextual codes retain a generated derivation at every context value. -/
abbrev Family (A : Type u) (B : A → Type u) (Γ : Type v) := Γ → Code A B

/-- Sections of the actual decoded family. -/
abbrev Section (C : Family A B Γ) := (γ : Γ) → (C γ).El

def reindex (C : Family A B Γ) (σ : Δ → Γ) : Family A B Δ := fun δ => C (σ δ)

@[simp] theorem reindex_id (C : Family A B Γ) : reindex C id = C := rfl

theorem reindex_comp (C : Family A B Γ) (σ : Δ → Γ) (τ : Θ → Δ) :
    reindex (reindex C σ) τ = reindex C (σ ∘ τ) := rfl

def sectionSub {C : Family A B Γ} (term : Section C) (σ : Δ → Γ) :
    Section (reindex C σ) := fun δ => term (σ δ)

@[simp] theorem sectionSub_id {C : Family A B Γ} (term : Section C) :
    sectionSub term id = term := rfl

theorem sectionSub_comp {C : Family A B Γ} (term : Section C)
    (σ : Δ → Γ) (τ : Θ → Δ) :
    sectionSub (sectionSub term σ) τ = sectionSub term (σ ∘ τ) := rfl

/-- Actual comprehension of the decoded family. -/
abbrev Ext (C : Family A B Γ) := Σ γ : Γ, (C γ).El

def liftSub (C : Family A B Γ) (σ : Δ → Γ) : Ext (reindex C σ) → Ext C :=
  fun value => ⟨σ value.1, value.2⟩

@[simp] theorem liftSub_id (C : Family A B Γ) : liftSub C id = id := rfl

theorem liftSub_comp (C : Family A B Γ) (σ : Δ → Γ) (τ : Θ → Δ) :
    liftSub C σ ∘ liftSub (reindex C σ) τ = liftSub C (σ ∘ τ) := rfl

def pi (C : Family A B Γ) (D : Family A B (Ext C)) : Family A B Γ :=
  fun γ => Code.pi (C γ) (fun value => D ⟨γ, value⟩)

def sigma (C : Family A B Γ) (D : Family A B (Ext C)) : Family A B Γ :=
  fun γ => Code.sigma (C γ) (fun value => D ⟨γ, value⟩)

def w (C : Family A B Γ) (D : Family A B (Ext C)) : Family A B Γ :=
  fun γ => Code.w (C γ) (fun value => D ⟨γ, value⟩)

/-- Substitution uses the actual comprehension map on a dependent codomain. -/
theorem pi_sub (C : Family A B Γ) (D : Family A B (Ext C)) (σ : Δ → Γ) :
    reindex (pi C D) σ = pi (reindex C σ) (reindex D (liftSub C σ)) := rfl

theorem sigma_sub (C : Family A B Γ) (D : Family A B (Ext C)) (σ : Δ → Γ) :
    reindex (sigma C D) σ = sigma (reindex C σ) (reindex D (liftSub C σ)) := rfl

theorem w_sub (C : Family A B Γ) (D : Family A B (Ext C)) (σ : Δ → Γ) :
    reindex (w C D) σ = w (reindex C σ) (reindex D (liftSub C σ)) := rfl

def lam {C : Family A B Γ} {D : Family A B (Ext C)}
    (term : Section D) : Section (pi C D) := fun γ value => term ⟨γ, value⟩

def app {C : Family A B Γ} {D : Family A B (Ext C)}
    (term : Section (pi C D)) : Section D := fun value => term value.1 value.2

@[simp] theorem app_lam {C : Family A B Γ} {D : Family A B (Ext C)}
    (term : Section D) : app (lam term) = term := rfl

@[simp] theorem lam_app {C : Family A B Γ} {D : Family A B (Ext C)}
    (term : Section (pi C D)) : lam (app term) = term := rfl

theorem lam_sub {C : Family A B Γ} {D : Family A B (Ext C)}
    (term : Section D) (σ : Δ → Γ) :
    sectionSub (lam term) σ = lam (sectionSub term (liftSub C σ)) := rfl

theorem app_sub {C : Family A B Γ} {D : Family A B (Ext C)}
    (term : Section (pi C D)) (σ : Δ → Γ) :
    sectionSub (app term) (liftSub C σ) = app (sectionSub term σ) := rfl

/-- The section adjunction has actual dependent functions as its two sides. -/
def sectionPiEquiv (C : Family A B Γ) (D : Family A B (Ext C)) :
    Section (pi C D) ≃ Section D where
  toFun := app
  invFun := lam
  left_inv := lam_app
  right_inv := app_lam

/-- Beck--Chevalley for sections: reindexing commutes with the constructed
adjunction, using the comprehension square rather than a constant codomain. -/
theorem sectionPiEquiv_natural (C : Family A B Γ) (D : Family A B (Ext C))
    (σ : Δ → Γ) (term : Section (pi C D)) :
    sectionSub (sectionPiEquiv C D term) (liftSub C σ) =
      sectionPiEquiv (reindex C σ) (reindex D (liftSub C σ))
        (sectionSub term σ) := rfl

def identity (C : Family A B Γ) (left right : Section C) : Family A B Γ :=
  fun γ => Code.identity (C γ) (left γ) (right γ)

def refl {C : Family A B Γ} (term : Section C) : Section (identity C term term) :=
  fun _ => ⟨⟨rfl⟩⟩

theorem identity_sub (C : Family A B Γ) (left right : Section C) (σ : Δ → Γ) :
    reindex (identity C left right) σ =
      identity (reindex C σ) (sectionSub left σ) (sectionSub right σ) := rfl

theorem refl_sub {C : Family A B Γ} (term : Section C) (σ : Δ → Γ) :
    sectionSub (refl term) σ = refl (sectionSub term σ) := rfl

/-- The full identity context retains both endpoints and its witness. -/
abbrev IdCtx (C : Family A B Γ) :=
  Σ γ : Γ, Σ left : (C γ).El, Σ right : (C γ).El,
    (Code.identity (C γ) left right).El

def diagonal (C : Family A B Γ) : Ext C → IdCtx C :=
  fun value => ⟨value.1, value.2, value.2, ⟨⟨rfl⟩⟩⟩

def identityLift (C : Family A B Γ) (σ : Δ → Γ) :
    IdCtx (reindex C σ) → IdCtx C :=
  fun value => ⟨σ value.1, value.2.1, value.2.2.1, value.2.2.2⟩

theorem identityLift_diagonal (C : Family A B Γ) (σ : Δ → Γ) :
    identityLift C σ ∘ diagonal (reindex C σ) = diagonal C ∘ liftSub C σ := rfl

/-- Dependent J for arbitrary generated motives over the full identity
context. Equality elimination, rather than an assumed eliminator, defines it. -/
def J {C : Family A B Γ} (motive : Family A B (IdCtx C))
    (atRefl : Section (reindex motive (diagonal C))) : Section motive
  | ⟨γ, left, right, ⟨⟨path⟩⟩⟩ => by
      cases path
      exact atRefl ⟨γ, left⟩

@[simp] theorem J_beta {C : Family A B Γ} (motive : Family A B (IdCtx C))
    (atRefl : Section (reindex motive (diagonal C))) :
    sectionSub (J motive atRefl) (diagonal C) = atRefl := rfl

/-- J commutes with arbitrary context substitution, including its
endpoint-and-witness-dependent motive. -/
theorem J_sub {C : Family A B Γ} (motive : Family A B (IdCtx C))
    (atRefl : Section (reindex motive (diagonal C))) (σ : Δ → Γ) :
    sectionSub (J motive atRefl) (identityLift C σ) =
      J (reindex motive (identityLift C σ))
        (sectionSub atRefl (liftSub C σ)) := by
  funext value
  rcases value with ⟨δ, left, right, ⟨⟨path⟩⟩⟩
  cases path
  rfl

theorem identityLift_comp (C : Family A B Γ) (σ : Δ → Γ) (τ : Θ → Δ) :
    identityLift C σ ∘ identityLift (reindex C σ) τ =
      identityLift C (σ ∘ τ) := rfl

#print axioms sectionPiEquiv
#print axioms sectionPiEquiv_natural
#print axioms J
#print axioms J_beta
#print axioms J_sub

end Mettapedia.TypeTheory.GeneratedUniverseSubstitution
