import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.ContextConversion
import Mettapedia.GSLT.Core.ContextualLadderTerminal

/-!
# The regular two-sort syntactic category with families

Contexts, types, terms, and substitutions carry the existing regular
judgments. The operations are actual de Bruijn substitution and telescope
extension. This packages their structural laws in the shared CwF interface;
it introduces no alternative typing judgment.

Equality in this CwF is equality of raw syntax. Fragment conversion remains
a separate relation. In particular, this structural construction does not
assert equality reflection, a classifying universal property, or a cumulative
universe tower.
-/

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SyntacticCwf

open Syntax Renaming Substitution Context Regular
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
open Mettapedia.GSLT.Core.ContextualLadder

/-- A telescope with its existing regular-context derivation. -/
structure Context where
  length : Nat
  raw : Ctx length
  regular : RegularCtx raw

/-- The formed types below the distinguished top sort. -/
abbrev Ty (Γ : Context) := {A : ScopedTerm Γ.length // RegularHasType Γ.raw A .u1}

/-- Actual source terms with the existing regular typing derivation. -/
abbrev Tm (Γ : Context) (A : Ty Γ) :=
  {t : ScopedTerm Γ.length // RegularHasType Γ.raw t A.val}

/-- A categorical arrow maps the target's variables into the source. -/
abbrev Hom (Γ Δ : Context) :=
  {σ : Sub Δ.length Γ.length // RegularCtxMor Δ.raw Γ.raw σ}

def identity (Γ : Context) : Hom Γ Γ :=
  ⟨ids, RegularCtxMor.identity Γ.raw⟩

def compose {Γ Δ Θ : Context} (σ : Hom Δ Θ) (τ : Hom Γ Δ) : Hom Γ Θ :=
  ⟨fun i => subst τ.val (σ.val i),
    σ.property.comp τ.property⟩

@[simp] theorem identity_compose {Γ Δ : Context} (σ : Hom Γ Δ) :
    compose (identity Δ) σ = σ := by
  apply Subtype.ext
  rfl

@[simp] theorem compose_identity {Γ Δ : Context} (σ : Hom Γ Δ) :
    compose σ (identity Γ) = σ := by
  apply Subtype.ext
  funext i
  exact subst_ids (σ.val i)

theorem compose_assoc {Γ Δ Θ Ξ : Context}
    (σ : Hom Θ Ξ) (τ : Hom Δ Θ) (ρ : Hom Γ Δ) :
    compose (compose σ τ) ρ = compose σ (compose τ ρ) := by
  apply Subtype.ext
  funext i
  exact subst_comp ρ.val τ.val (σ.val i)

def typeSub {Γ Δ : Context} (A : Ty Δ) (σ : Hom Γ Δ) : Ty Γ :=
  ⟨subst σ.val A.val, A.property.subst σ.property⟩

def termSub {Γ Δ : Context} {A : Ty Δ} (t : Tm Δ A) (σ : Hom Γ Δ) :
    Tm Γ (typeSub A σ) :=
  ⟨subst σ.val t.val, t.property.subst σ.property⟩

@[simp] theorem typeSub_identity {Γ : Context} (A : Ty Γ) :
    typeSub A (identity Γ) = A := Subtype.ext (subst_ids A.val)

theorem typeSub_compose {Γ Δ Θ : Context}
    (A : Ty Θ) (σ : Hom Δ Θ) (τ : Hom Γ Δ) :
    typeSub A (compose σ τ) = typeSub (typeSub A σ) τ :=
  Subtype.ext (subst_comp τ.val σ.val A.val).symm

/-- Transport between equal type indices does not change the source term. -/
@[simp] theorem cast_term_val {Γ : Context} {A B : Ty Γ}
    (equal : A = B) (t : Tm Γ A) :
    (cast (congrArg (Tm Γ) equal) t).val = t.val := by
  cases equal
  rfl

def extend (Γ : Context) (A : Ty Γ) : Context :=
  ⟨Γ.length + 1, .snoc Γ.raw A.val, .snoc Γ.regular A.property⟩

def weaken {Γ : Context} (A : Ty Γ) : Hom (extend Γ A) Γ :=
  ⟨renToSub wk, ⟨fun i => by
    simpa [renToSub, extend, wk] using
      (RegularHasType.var (Γ := .snoc Γ.raw A.val) i.succ),
    fun i => .var i.succ⟩⟩

def lastTerm {Γ : Context} (A : Ty Γ) :
    Tm (extend Γ A) (typeSub A (weaken A)) :=
  ⟨.var (0 : Fin (Γ.length + 1)), by
    simpa [typeSub, weaken, extend] using
      (RegularHasType.var (Γ := .snoc Γ.raw A.val) 0)⟩

def pair {Γ Δ : Context} (σ : Hom Γ Δ) (A : Ty Δ)
    (t : Tm Γ (typeSub A σ)) : Hom Γ (extend Δ A) :=
  ⟨Fin.cases t.val σ.val, ⟨by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [extend, typeSub, subst_rename, wk] using t.property
    · simpa [extend, subst_rename, wk] using σ.property.typing j,
    fun i => Fin.cases
      (t.property.constantFree_both Γ.regular.constantFreeCtx).1
      σ.property.constantFree i⟩⟩

@[simp] theorem weaken_pair {Γ Δ : Context} (σ : Hom Γ Δ)
    (A : Ty Δ) (t : Tm Γ (typeSub A σ)) :
    compose (weaken A) (pair σ A t) = σ := by
  apply Subtype.ext
  rfl

/-- The regular syntax supplies every substitution and comprehension law. -/
def cwf : Cwf where
  Ctx := Context
  Sub := Hom
  idS := identity
  compS := compose
  id_comp := identity_compose
  comp_id := compose_identity
  comp_assoc := compose_assoc
  Ty := Ty
  tySub := typeSub
  tySub_id := typeSub_identity
  tySub_comp := typeSub_compose
  Tm := Tm
  tmSub := termSub
  tmSub_id t := by
    apply Subtype.ext
    rw [cast_term_val (typeSub_identity _).symm]
    exact subst_ids t.val
  tmSub_comp t σ τ := by
    apply Subtype.ext
    rw [cast_term_val (typeSub_compose _ σ τ).symm]
    exact (subst_comp τ.val σ.val t.val).symm
  ext := extend
  wk := weaken
  vz := lastTerm
  pair := pair
  wk_pair := weaken_pair
  vz_pair σ A t := by
    apply Subtype.ext
    rw [cast_term_val (by rw [← typeSub_compose, weaken_pair])]
    rfl
  pair_eta A σ := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    simp only [pair, Fin.cases_zero]
    rw [cast_term_val (typeSub_compose A (weaken A) σ).symm]
    rfl

def empty : Context := ⟨0, .nil, .nil⟩

def toEmpty (Γ : Context) : Hom Γ empty :=
  ⟨Fin.elim0, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩

/-- The empty telescope is terminal, completing the structural CwF. -/
def cwfWithTerminal : CwfWithTerminal where
  toCwf := cwf
  empty := empty
  toEmpty := toEmpty
  toEmpty_unique Γ σ := by
    apply Subtype.ext
    funext i
    exact Fin.elim0 i

/-! ## Existing dependent formers on the structural CwF -/

def piType {Γ : Context} (A : Ty Γ) (B : Ty (extend Γ A)) : Ty Γ :=
  ⟨.pi A.val B.val, .pi_form A.property B.property⟩

def sigmaType {Γ : Context} (A : Ty Γ) (B : Ty (extend Γ A)) : Ty Γ :=
  ⟨.sigma A.val B.val, .sigma_form A.property B.property⟩

def lambdaTerm {Γ : Context} {A : Ty Γ} {B : Ty (extend Γ A)}
    (body : Tm (extend Γ A) B) : Tm Γ (piType A B) :=
  ⟨.lam body.val, .lam_intro A.property B.property body.property⟩

def instantiateType {Γ : Context} {A : Ty Γ}
    (B : Ty (extend Γ A)) (argument : Tm Γ A) : Ty Γ :=
  ⟨inst0 argument.val B.val,
    B.property.instantiate argument.property Γ.regular.constantFreeCtx⟩

def instantiateTerm {Γ : Context} {A : Ty Γ} {B : Ty (extend Γ A)}
    (body : Tm (extend Γ A) B) (argument : Tm Γ A) :
    Tm Γ (instantiateType B argument) :=
  ⟨inst0 argument.val body.val,
    body.property.instantiate argument.property Γ.regular.constantFreeCtx⟩

/-- Dependent application uses the same substitution as context pairing. -/
theorem instantiateType_eq_typeSub {Γ : Context} {A : Ty Γ}
    (B : Ty (extend Γ A)) (argument : Tm Γ A) :
    instantiateType B argument =
      typeSub B (pair (identity Γ) A
        (cast (congrArg (Tm Γ) (typeSub_identity A).symm) argument)) := by
  apply Subtype.ext
  change subst (subst0 argument.val) B.val = subst _ B.val
  apply congrArg (fun σ => subst σ B.val)
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  exact (cast_term_val (typeSub_identity A).symm argument).symm

def applyTerm {Γ : Context} {A : Ty Γ} {B : Ty (extend Γ A)}
    (function : Tm Γ (piType A B)) (argument : Tm Γ A) :
    Tm Γ (instantiateType B argument) :=
  ⟨.app function.val argument.val,
    .app_elim A.property function.property argument.property B.property⟩

def pairTerm {Γ : Context} {A : Ty Γ} {B : Ty (extend Γ A)}
    (first : Tm Γ A) (second : Tm Γ (instantiateType B first)) :
    Tm Γ (sigmaType A B) :=
  ⟨.pair first.val second.val,
    .pair_intro A.property first.property second.property B.property⟩

def firstTerm {Γ : Context} {A : Ty Γ} {B : Ty (extend Γ A)}
    (term : Tm Γ (sigmaType A B)) : Tm Γ A :=
  ⟨.fst term.val, .fst_elim A.property term.property B.property⟩

def secondTerm {Γ : Context} {A : Ty Γ} {B : Ty (extend Γ A)}
    (term : Tm Γ (sigmaType A B)) :
    Tm Γ (instantiateType B (firstTerm term)) :=
  ⟨.snd term.val, .snd_elim A.property term.property B.property⟩

def identityType {Γ : Context} (A : Ty Γ) (left right : Tm Γ A) : Ty Γ :=
  ⟨.id A.val left.val right.val, .id_form A.property left.property right.property⟩

def reflexivityTerm {Γ : Context} {A : Ty Γ} (term : Tm Γ A) :
    Tm Γ (identityType A term term) :=
  ⟨.refl term.val, .refl_intro A.property term.property⟩

/-- Source beta computation is conversion, not raw syntactic identity. -/
theorem apply_lambda_converts {Γ : Context} {A : Ty Γ} {B : Ty (extend Γ A)}
    (body : Tm (extend Γ A) B) (argument : Tm Γ A) :
    ConstantFreeConv (applyTerm (lambdaTerm body) argument).val
      (instantiateTerm body argument).val :=
  .rel ⟨.betaPi body.val argument.val,
    ((applyTerm (lambdaTerm body) argument).property.constantFree_both
      Γ.regular.constantFreeCtx).1,
    ((instantiateTerm body argument).property.constantFree_both
      Γ.regular.constantFreeCtx).1⟩

/-- The existing binder lift is a well-typed context substitution. -/
def lift {Γ Δ : Context} (σ : Hom Γ Δ) (A : Ty Δ) :
    Hom (extend Γ (typeSub A σ)) (extend Δ A) :=
  ⟨liftSub σ.val, σ.property.lift A.val⟩

theorem piType_substitution {Γ Δ : Context} (σ : Hom Γ Δ)
    (A : Ty Δ) (B : Ty (extend Δ A)) :
    typeSub (piType A B) σ =
      piType (typeSub A σ) (typeSub B (lift σ A)) := Subtype.ext rfl

theorem sigmaType_substitution {Γ Δ : Context} (σ : Hom Γ Δ)
    (A : Ty Δ) (B : Ty (extend Δ A)) :
    typeSub (sigmaType A B) σ =
      sigmaType (typeSub A σ) (typeSub B (lift σ A)) := Subtype.ext rfl

theorem identityType_substitution {Γ Δ : Context} (σ : Hom Γ Δ)
    (A : Ty Δ) (left right : Tm Δ A) :
    typeSub (identityType A left right) σ =
      identityType (typeSub A σ) (termSub left σ) (termSub right σ) :=
  Subtype.ext rfl

#print axioms cwf
#print axioms cwfWithTerminal
#print axioms instantiateType_eq_typeSub
#print axioms apply_lambda_converts
#print axioms piType_substitution
#print axioms sigmaType_substitution
#print axioms identityType_substitution

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SyntacticCwf
