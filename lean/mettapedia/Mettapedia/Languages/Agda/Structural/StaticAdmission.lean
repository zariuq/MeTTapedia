import Mettapedia.Languages.Agda.Structural.StaticTypedSubstitution
import Mettapedia.GSLT.Core.ContextualAdmissionMorphism

/-!
# Formed contexts and typed substitutions from actual static derivations

This specializes the shared admission construction to structural rule trees.
Substitution evidence retains both context derivations and all variable-image
derivations. The category laws concern supported raw substitutions. Derivation
trees remain available in their original fibres and are not equated by those
laws. No conversion quotient, initiality, normalization, or checker is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Mettapedia.GSLT.Core.ContextualLadder

variable {D : Judgment → Type}

namespace TypedSubstitution

def identity
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    {n : Nat} {Γ : RawContext n} (formed : D (context Γ)) :
    TypedSubstitution D Γ Γ (Telescope.identity (S := sig) .term n) where
  source := formed
  target := formed
  image v :=
    (congrArg (fun A => D (typed Γ (.var v) A))
      (Telescope.bind_identity (ContextGeometry.lookup Γ v))).mpr
      (algebra.act () _ ⟨.variable Γ v, consEvidence D formed (noEvidence D)⟩)

def comp (substituteEvidence : ∀ {j : Judgment}, D j → SubstitutionAction D j)
    {n m p : Nat} {Γ : RawContext n} {Δ : RawContext m} {Θ : RawContext p}
    {σ : RawSub n m} {τ : RawSub m p}
    (first : TypedSubstitution D Γ Δ σ) (second : TypedSubstitution D Δ Θ τ) :
    TypedSubstitution D Γ Θ (Telescope.comp σ τ) where
  source := first.source
  target := second.target
  image v :=
    (congrArg (fun A => D (typed Θ (bind τ (σ .term v)) A))
      (Telescope.bind_compose σ τ (ContextGeometry.lookup Γ v))).mp
      (substituteEvidence (first.image v) Θ τ second)

def projection
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (formed : D (context Γ)) (domain : D (Statics.formed Γ A)) :
    TypedSubstitution D Γ (Γ.snoc A) (Telescope.projection (S := sig) .term n) := by
  let extended : D (context (Γ.snoc A)) := algebra.act () _
    ⟨.extend Γ A, consEvidence D formed (consEvidence D domain (noEvidence D))⟩
  refine ⟨formed, extended, fun v => ?_⟩
  exact (congrArg (fun T => D (typed (Γ.snoc A) (.var (.succ v)) T))
    (Telescope.lookup_projection Γ A v)).mp
    (algebra.act () _ ⟨.variable (Γ.snoc A) (.succ v), consEvidence D extended (noEvidence D)⟩)

def pair
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    {n m : Nat} {Γ : RawContext n} {Δ : RawContext m} {σ : RawSub n m}
    (prior : TypedSubstitution D Γ Δ σ) {A : RawTy n} {a : RawTm m}
    (domain : D (formed Γ A)) (argument : D (typed Δ a (bind σ A))) :
    TypedSubstitution D (Γ.snoc A) Δ (Telescope.pair σ a) where
  source := algebra.act () _ ⟨.extend Γ A, consEvidence D prior.source (consEvidence D domain (noEvidence D))⟩
  target := prior.target
  image v := by
    cases v with
    | zero => exact (congrArg (fun T => D (typed Δ a T))
        (Telescope.lookup_pair_newest Γ A σ a)).mpr argument
    | succ v => exact (congrArg (fun T => D (typed Δ (σ .term v) T))
        (Telescope.lookup_pair_older Γ A v σ a)).mpr (prior.image v)

def empty
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    {n : Nat} {Γ : RawContext n} (formed : D (context Γ)) :
    TypedSubstitution D .nil Γ (Telescope.emptySub (S := sig) .term n) where
  source := algebra.act () _ ⟨.empty, noEvidence D⟩
  target := formed
  image v := nomatch v

end TypedSubstitution

/-- The admission data require real structural closure operations on the chosen
evidence family. The canonical and combined presentations supply them by folds. -/
def admissionData
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    (substituteEvidence : ∀ {j : Judgment}, D j → SubstitutionAction D j) :
    CwfDerivations rawCwf where
  context Γ := D (context Γ.2)
  type Γ A := D (formed Γ.2 A)
  term Γ A t := D (typed Γ.2 t.code A)
  substitution Γ Δ σ := TypedSubstitution D Δ.2 Γ.2 σ
  identityDerivation _ formed := TypedSubstitution.identity algebra formed
  composeDerivation _ _ _ _ _ first second := TypedSubstitution.comp substituteEvidence first second
  reindexType A σ _ _ typed substitution := substituteEvidence typed _ σ substitution
  reindexTerm t σ _ _ _ typed substitution := substituteEvidence typed _ σ substitution
  extendDerivation Γ A formed type := algebra.act () _
    ⟨.extend Γ.2 A, consEvidence D formed (consEvidence D type (noEvidence D))⟩
  projectionDerivation _ _ formed type := TypedSubstitution.projection algebra formed type
  variableDerivation Γ A formed type := by
    let extended : D (context (Γ.2.snoc A)) := algebra.act () _
      ⟨.extend Γ.2 A, consEvidence D formed (consEvidence D type (noEvidence D))⟩
    exact (congrArg (fun T => D (typed (Γ.2.snoc A) (.var .zero) T))
      (Telescope.bind_projection (S := sig) (b := .term) A)).mpr
      (algebra.act () _ ⟨.variable (Γ.2.snoc A) .zero, consEvidence D extended (noEvidence D)⟩)
  pairing _ _ _ _ _ prior type term := TypedSubstitution.pair algebra prior type term

/-- The actual canonical rule-tree family supplies every admission obligation. -/
noncomputable def canonicalAdmission : CwfDerivations rawCwf :=
  admissionData (IndexedPolynomial.Algebra.initial presentation.polynomial) Derivation.substitution

/-- The formed canonical contexts constitute a category with families, including
its terminal empty context, on unquotiented structural syntax. -/
noncomputable def canonicalCwf : CwfWithTerminal :=
  CwfDerivations.admittedWithTerminal ContextGeometry.rawAgdaTelescopeCwfWithTerminal
    canonicalAdmission Derivation.empty
    (fun _ formed => TypedSubstitution.empty (IndexedPolynomial.Algebra.initial presentation.polynomial) formed)

end Mettapedia.Languages.Agda.Structural.Statics
