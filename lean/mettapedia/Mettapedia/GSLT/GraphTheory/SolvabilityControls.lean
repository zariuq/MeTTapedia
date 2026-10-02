import Mettapedia.GSLT.GraphTheory.Solvability
import Mettapedia.GSLT.GraphTheory.ParallelReduction

/-! Positive and negative controls for solvability, head normalization and
semisensibility. -/

namespace Mettapedia.GSLT.GraphTheory.SolvabilityControls

open Mettapedia.GSLT.GraphTheory

/-! ### Solvable and unsolvable terms -/

theorem I_solvable : LambdaTerm.I.Solvable := LambdaTerm.solvable_of_isHNF rfl

theorem K_solvable : LambdaTerm.K.Solvable := LambdaTerm.solvable_of_isHNF rfl

/-- `λx. x Ω` is solvable although its argument is not. -/
theorem lam_var_Omega_solvable :
    (LambdaTerm.lam (.app (.var 0) LambdaTerm.Omega)).Solvable :=
  LambdaTerm.solvable_of_isHNF rfl

/-- `λx. Ω` is unsolvable. -/
theorem lam_Omega_unsolvable : (LambdaTerm.lam LambdaTerm.Omega).Unsolvable :=
  Omega_unsolvable.lam

/-- `Ω A` is unsolvable for every argument `A`. -/
theorem Omega_app_unsolvable (A : LambdaTerm) :
    (LambdaTerm.app LambdaTerm.Omega A).Unsolvable :=
  Omega_unsolvable.app A

/-! ### Head normalization -/

/-- A solvable term that is not yet a head normal form head-normalizes. -/
theorem identity_redex_headNormalizes :
    HeadNormalizes (.app LambdaTerm.I LambdaTerm.I) ∧
      (LambdaTerm.app LambdaTerm.I LambdaTerm.I).isHNF = false :=
  ⟨headNormalizes_of_solvable
    ⟨LambdaTerm.I, .single (ParRed.beta (ParRed.var 0) (ParRed.refl LambdaTerm.I)), rfl⟩, rfl⟩

theorem Omega_not_headNormalizes : ¬HeadNormalizes LambdaTerm.Omega :=
  fun h => Omega_unsolvable h.solvable

/-! ### The closure lemmas hold in one direction only -/

/-- Substitution can destroy solvability: `x x` is a head normal form, and
substituting `ω` for `x` gives `Ω`. Only the converse holds
(`solvable_of_solvable_subst`). -/
theorem subst_can_destroy_solvability :
    (LambdaTerm.app (.var 0) (.var 0)).Solvable ∧
      (LambdaTerm.subst 0 LambdaTerm.omega (.app (.var 0) (.var 0))).Unsolvable :=
  ⟨LambdaTerm.solvable_of_isHNF rfl, Omega_unsolvable⟩

/-- Application can destroy solvability: `ω` is solvable and `ω ω = Ω` is not.
Only the converse holds (`solvable_of_solvable_app`). -/
theorem app_can_destroy_solvability :
    LambdaTerm.omega.Solvable ∧ (LambdaTerm.app LambdaTerm.omega LambdaTerm.omega).Unsolvable :=
  ⟨LambdaTerm.solvable_of_isHNF rfl, Omega_unsolvable⟩

/-- The context lemma needs solvability: no context `(λ^q [·]) N₁ ⋯ Nₚ` sends
`Ω` to `I`. -/
theorem no_context_reduces_Omega_to_I (q : Nat) (args : List LambdaTerm) :
    ¬((args.foldl .app (LambdaTerm.lam^[q] LambdaTerm.Omega)) ⇛* LambdaTerm.I) :=
  fun h => (Omega_unsolvable.iterate_lam q).foldl_app args
    (LambdaTerm.solvable_of_reduces h I_solvable)

/-! ### Consistency cannot be dropped -/

/-- The theory equating all terms. -/
def totalTheory : LambdaTheory where
  equations := Set.univ
  refl _ := Set.mem_univ _
  symm _ := Set.mem_univ _
  trans _ _ := Set.mem_univ _
  beta _ _ := Set.mem_univ _
  congLam _ := Set.mem_univ _
  congAppLeft _ := Set.mem_univ _
  congAppRight _ := Set.mem_univ _

theorem totalTheory_equates_unsolvables : totalTheory.EquatesUnsolvables :=
  fun _ _ _ _ => Set.mem_univ _

theorem totalTheory_not_consistent : ¬totalTheory.Consistent := fun h => h (Set.mem_univ _)

theorem totalTheory_not_sensible : ¬totalTheory.Sensible :=
  fun h => totalTheory_not_consistent h.consistent

/-- Equating all unsolvables alone does not imply semisensibility. -/
theorem totalTheory_not_semisensible : ¬totalTheory.Semisensible :=
  fun h => h LambdaTerm.Omega LambdaTerm.I Omega_unsolvable (Set.mem_univ _) I_solvable

/-! ### A consistent theory that is not sensible

β-conversion is consistent and semisensible but does not equate `Ω` with
`λx. Ω`, so the sensibility hypothesis is not implied by consistency. -/

theorem eqvGen_parRed_map (f : LambdaTerm → LambdaTerm) (hf : ∀ a b, (a ⇛ b) → (f a ⇛ f b))
    {a b : LambdaTerm} (h : Relation.EqvGen ParRed a b) : Relation.EqvGen ParRed (f a) (f b) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (hf _ _ h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

/-- β-conversion, the equivalence closure of parallel reduction. -/
def betaTheory : LambdaTheory where
  equations := {e | Relation.EqvGen ParRed e.lhs e.rhs}
  refl t := Relation.EqvGen.refl t
  symm h := Relation.EqvGen.symm _ _ h
  trans h h' := Relation.EqvGen.trans _ _ _ h h'
  beta t s := Relation.EqvGen.rel _ _ (ParRed.beta (ParRed.refl t) (ParRed.refl s))
  congLam h := eqvGen_parRed_map LambdaTerm.lam (fun _ _ => ParRed.lam) h
  congAppLeft h :=
    eqvGen_parRed_map (fun x => .app x _) (fun _ _ hx => ParRed.app hx (ParRed.refl _)) h
  congAppRight h :=
    eqvGen_parRed_map (LambdaTerm.app _) (fun _ _ hx => ParRed.app (ParRed.refl _) hx) h

/-- β-convertible terms have a common reduct. -/
theorem join_of_eqvGen {a b : LambdaTerm} (h : Relation.EqvGen ParRed a b) :
    Relation.Join ParRedStar a b := by
  have hEquiv : Equivalence (Relation.Join (Relation.ReflTransGen ParRed)) :=
    Relation.equivalence_join_reflTransGen fun _ _ _ hb hc =>
      let ⟨d, hbd, hcd⟩ := parRed_diamond hb hc
      ⟨d, .single hbd, .single hcd⟩
  exact hEquiv.eqvGen_iff.mp (h.mono fun _ y hxy => ⟨y, .single hxy, .refl⟩)

theorem parRedStar_I_eq {result : LambdaTerm} (h : LambdaTerm.I ⇛* result) :
    result = LambdaTerm.I := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      subst ih
      cases hs with
      | lam hb => cases hb; rfl

theorem parRedStar_K_eq {result : LambdaTerm} (h : LambdaTerm.K ⇛* result) :
    result = LambdaTerm.K := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      subst ih
      cases hs with
      | lam hb =>
          cases hb with
          | lam hv => cases hv; rfl

theorem betaTheory_consistent : betaTheory.Consistent := fun h => by
  obtain ⟨c, hIc, hKc⟩ := join_of_eqvGen h
  exact absurd ((parRedStar_I_eq hIc).symm.trans (parRedStar_K_eq hKc)) (by decide)

/-- `Ω` weak-head-reduces only to itself. -/
theorem weakHeadStar_Omega_eq {result : LambdaTerm} (h : WeakHeadStar LambdaTerm.Omega result) :
    result = LambdaTerm.Omega := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      subst ih
      exact hs.deterministic (.beta (.app (.var 0) (.var 0)) LambdaTerm.omega)

/-- `Ω` and `λx. Ω` are not β-convertible: a common reduct is an abstraction,
and standardization turns `Ω ⇛* λ…` into a weak head reduction from `Ω` to an
abstraction. -/
theorem Omega_not_betaConv_lam_Omega :
    ¬Relation.EqvGen ParRed LambdaTerm.Omega (.lam LambdaTerm.Omega) := by
  intro h
  obtain ⟨c, hOc, hLc⟩ := join_of_eqvGen h
  obtain ⟨body, rfl, _⟩ := parRedStar_lam_inv hLc
  obtain ⟨body', hwh, _⟩ := (StandardRed.of_parRedStar hOc).lam_inv
  cases weakHeadStar_Omega_eq hwh

theorem betaTheory_not_sensible : ¬betaTheory.Sensible :=
  fun h => Omega_not_betaConv_lam_Omega
    (h.equates_unsolvables _ _ Omega_unsolvable lam_Omega_unsolvable)

/-- Semisensibility does not require sensibility. -/
theorem betaTheory_semisensible : betaTheory.Semisensible := fun _ _ ht hts hs => by
  obtain ⟨c, htc, hsc⟩ := join_of_eqvGen hts
  exact ht (LambdaTerm.solvable_of_reduces htc ((solvable_iff_of_parRedStar hsc).1 hs))

end Mettapedia.GSLT.GraphTheory.SolvabilityControls
