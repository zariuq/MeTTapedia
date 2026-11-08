import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaElimination

/-!
# Instantiating the newest metavariable keeps opened sides in the fragment

A solver answer for the newest metavariable `F` of `Γ, F` instantiates the store along
`instantiate Γ value : Γ ⟶ Γ, F`, the substitution `F ↦ value` that keeps every older
metavariable. When the value is a pattern solution `λ z̄. u` with one binder for each Π binder of
`F`'s declared type, and `u` is normal with Miller occurrences and the arities of the older
metavariables, then every opened side of every instantiated equation, normalized, is again in the
dynamic pattern fragment: its occurrences of `F` collapse to renamings of `u`.

Opening commutes with substitution, so the instantiated equation, opened, is the opened equation
instantiated under the local binders.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDynamicFragment

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin
open ContextualDependentGeneralPattern (liftFlexible)

variable {Head : Type}

/-! ## Substitution under binders, and opening -/

/-- A substitution lifted under `count` binders. -/
def liftSubK {n m : Nat} : (count : Nat) → Sub Head n m → Sub Head (n + count) (m + count)
  | 0, σ => σ
  | count + 1, σ => liftSub (liftSubK count σ)

theorem subst_liftSub_rename_wk {n m : Nat} (σ : Sub Head n m) (t : Tm Head n) :
    subst (liftSub σ) (rename wk t) = rename wk (subst σ t) := by
  rw [subst_rename, rename_subst]
  rfl

/-- **Opening commutes with substitution.** -/
theorem openCode_subst {n m : Nat} (σ : Sub Head n m) (t : Tm Head n) :
    ∀ count : Nat, openCode count (subst σ t) = subst (liftSubK count σ) (openCode count t)
  | 0 => rfl
  | count + 1 => by
      simp only [openCode, subst, liftSubK]
      rw [openCode_subst σ t count, subst_liftSub_rename_wk]
      rfl

theorem piCount_rename {n m : Nat} (ρ : Ren n m) : ∀ t : Tm Head n, piCount (rename ρ t) = piCount t
  | .pi _ body => by simp only [rename, piCount, piCount_rename (liftRen ρ) body]
  | .var _ => rfl
  | .const _ => rfl
  | .head _ => rfl
  | .sigma _ _ => rfl
  | .id _ _ _ => rfl
  | .lam _ => rfl
  | .app _ _ => rfl
  | .pair _ _ => rfl
  | .fst _ => rfl
  | .snd _ => rfl
  | .refl _ => rfl

theorem liftRenK_id {n : Nat} : ∀ (count : Nat) (index : Fin (n + count)), liftRenK count (idRen : Ren n n) index = index
  | 0, _ => rfl
  | count + 1, index => by
      rcases Fin.eq_zero_or_eq_succ index with rfl | ⟨prior, rfl⟩
      · rfl
      · exact congrArg Fin.succ (liftRenK_id count prior)

/-! ## Markings of opened contexts -/

/-- The opened marking is the body marking: `count` rigid binders over flexible metavariables. -/
theorem bodyFlexible_eq {o : Nat} : ∀ (count : Nat) (index : Fin (o + count)),
    bodyFlexible count index = openedFlexible count index
  | 0, index => by simp [bodyFlexible, openedFlexible]
  | count + 1, index => by
      rcases Fin.eq_zero_or_eq_succ index with rfl | ⟨prior, rfl⟩
      · simp [bodyFlexible, openedFlexible, liftFlexible]
      · change bodyFlexible count prior = _
        rw [bodyFlexible_eq count prior]
        simp [openedFlexible]

theorem liftArityK_eq {n : Nat} (context : Ctx Head n) : ∀ (count : Nat) (index : Fin (n + count)),
    liftArityK count (fun j => piCount (Ctx.lookup context j)) index = metaArity context count index
  | 0, index => by simp [liftArityK, metaArity]
  | count + 1, index => by
      rcases Fin.eq_zero_or_eq_succ index with rfl | ⟨prior, rfl⟩
      · simp [liftArityK, liftArity, metaArity]
      · change liftArityK count _ prior = _
        rw [liftArityK_eq context count prior]
        unfold metaArity
        by_cases h : count ≤ prior.val
        · rw [dif_pos h, dif_pos (by simp only [Fin.val_succ]; omega)]
          congr 2
          ext
          simp only [Fin.val_succ]
          omega
        · rw [dif_neg h, dif_neg (by simp only [Fin.val_succ]; omega)]

/-! ## The instantiation of the newest metavariable -/

variable {R : Rules Head}

/-- **The newest metavariable, instantiated by a pattern solution**, as a pattern instantiation of
the closed context: every variable is flexible. -/
def newestInstantiation {Γ : Context R} {type : TypeOver Γ} (value : Term Γ type) {count : Nat}
    {body : Tm Head (Γ.arity + count)} (valueCode : value.code = lamsVar count body) (normal : Normal R body)
    (millerBody : miller (bodyFlexible count) body = true) :
    Instantiation R (bodyFlexible (o := Γ.arity + 1) 0) (bodyFlexible (o := Γ.arity) 0)
      (ContextualDependentEta.Elimination.instantiate Γ value).substitution where
  target := 0
  arity := count
  flexibleTarget := rfl
  rename i hi := i.pred hi
  injective := fun _ _ _ _ same => Fin.pred_inj.mp same
  respects := fun _ _ => rfl
  others := by
    intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨prior, rfl⟩
    · exact absurd rfl hi
    · rw [Fin.pred_succ]
      rfl
  outerArity := Γ.arity
  outer := idRen
  outerInjective := fun _ _ same => same
  outerFlexible := fun _ => rfl
  body := body
  solution := by
    change (consSub (value.cast type.reindex_id.symm).code ids) 0 = _
    simp only [consSub, Fin.cases_zero, Term.cast_code]
    rw [valueCode, rename_ext (fun index => liftRenK_id count index) body]
    exact congrArg (lamsVar count) (rename_id body).symm
  bodyMiller := millerBody
  bodyNormal := normal

/-- The arities of the newest instantiation. -/
theorem newestInstantiation_arities {Γ : Context R} {type : TypeOver Γ} (value : Term Γ type) {count : Nat}
    {body : Tm Head (Γ.arity + count)} (valueCode : value.code = lamsVar count body) (normal : Normal R body)
    (millerBody : miller (bodyFlexible count) body = true) (arityOf : piCount type.code = count)
    (aritiesBody : arities (bodyFlexible count) (liftArityK count fun j => piCount (Ctx.lookup Γ.raw j)) body = true) :
    Arities (newestInstantiation value valueCode normal millerBody)
      (fun i => piCount (Ctx.lookup (extend Γ type).raw i)) (fun j => piCount (Ctx.lookup Γ.raw j)) where
  target := by
    change piCount (Ctx.lookup (.snoc Γ.raw type.code) 0) = count
    simp only [Ctx.lookup, Fin.cases_zero, piCount_rename]
    exact arityOf
  rename := by
    intro i hi _
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨prior, rfl⟩
    · exact absurd rfl hi
    · change piCount (Ctx.lookup Γ.raw (prior.succ.pred hi)) = piCount (Ctx.lookup (.snoc Γ.raw type.code) prior.succ)
      simp only [Ctx.lookup, Fin.cases_succ, piCount_rename]
      exact congrArg (fun j => piCount (Ctx.lookup Γ.raw j)) (Fin.pred_succ prior)
  body := aritiesBody

/-- A marking lifted under `count` rigid binders. -/
def liftFlexibleK {k : Nat} : (count : Nat) → (Fin k → Bool) → Fin (k + count) → Bool
  | 0, flexible => flexible
  | count + 1, flexible => liftFlexible (liftFlexibleK count flexible)

/-- The instantiation lifted under `count` binders. -/
def liftK {n m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool} {σ : Sub Head n m} :
    (count : Nat) → (inst : Instantiation R flexible flexible' σ) →
      Instantiation R (liftFlexibleK count flexible) (liftFlexibleK count flexible') (liftSubK count σ)
  | 0, inst => inst
  | count + 1, inst => (liftK count inst).lift

theorem liftK_arities {n m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool} {σ : Sub Head n m}
    {inst : Instantiation R flexible flexible' σ} {arity : Fin n → Nat} {arity' : Fin m → Nat}
    (known : Arities inst arity arity') :
    ∀ count : Nat, Arities (liftK count inst) (liftArityK count arity) (liftArityK count arity')
  | 0 => known
  | count + 1 => (liftK_arities known count).lift

theorem liftFlexibleK_body {o : Nat} : ∀ (count : Nat) (index : Fin (o + count)),
    liftFlexibleK count (bodyFlexible (o := o) 0) index = bodyFlexible count index
  | 0, _ => rfl
  | count + 1, index => by
      rcases Fin.eq_zero_or_eq_succ index with rfl | ⟨prior, rfl⟩
      · rfl
      · exact liftFlexibleK_body count prior

/-! ## Stability of opened sides under the instantiation -/

variable (empty : R.computation = RootComputation.empty)
include empty

/-- **An opened side in the fragment stays in the fragment** when the newest metavariable is
instantiated by a pattern solution and the result normalized. -/
theorem instantiate_side_stable {Γ : Context R} {type : TypeOver Γ} (value : Term Γ type) {arity : Nat}
    {body : Tm Head (Γ.arity + arity)} (valueCode : value.code = lamsVar arity body) (normal : Normal R body)
    (millerBody : miller (bodyFlexible arity) body = true) (arityOf : piCount type.code = arity)
    (aritiesBody : arities (bodyFlexible arity) (liftArityK arity fun j => piCount (Ctx.lookup Γ.raw j)) body = true)
    (count : Nat) {side : Tm Head (Γ.arity + 1 + count)} (inside : InFragmentCode (extend Γ type).raw count side)
    (normalSide : Normal R side) :
    ∃ side', Star (R := R)
        (subst (liftSubK count (ContextualDependentEta.Elimination.instantiate Γ value).substitution) side) side' ∧
      Normal R side' ∧ InFragmentCode Γ.raw count side' := by
  have inst := liftK count (newestInstantiation value valueCode normal millerBody)
  have known := liftK_arities (newestInstantiation_arities value valueCode normal millerBody arityOf aritiesBody) count
  have markSource : liftFlexibleK count (bodyFlexible (o := Γ.arity + 1) 0) = openedFlexible count :=
    funext fun index => (liftFlexibleK_body count index).trans (bodyFlexible_eq count index)
  have markTarget : liftFlexibleK count (bodyFlexible (o := Γ.arity) 0) = openedFlexible count :=
    funext fun index => (liftFlexibleK_body count index).trans (bodyFlexible_eq count index)
  have aritySource : liftArityK count (fun i => piCount (Ctx.lookup (extend Γ type).raw i)) =
      metaArity (extend Γ type).raw count := funext (liftArityK_eq (extend Γ type).raw count)
  have arityTarget : liftArityK count (fun j => piCount (Ctx.lookup Γ.raw j)) = metaArity Γ.raw count :=
    funext (liftArityK_eq Γ.raw count)
  have millerSide : miller (liftFlexibleK count (bodyFlexible (o := Γ.arity + 1) 0)) side = true := by
    rw [markSource]; exact inside.1
  have aritiesSide : arities (liftFlexibleK count (bodyFlexible (o := Γ.arity + 1) 0))
      (liftArityK count (fun i => piCount (Ctx.lookup (extend Γ type).raw i))) side = true := by
    rw [markSource, aritySource]; exact inside.2
  obtain ⟨side', steps, normal', miller', arities', -⟩ :=
    stable empty side (liftK count (newestInstantiation value valueCode normal millerBody)) known millerSide
      aritiesSide normalSide
  refine ⟨side', steps, normal', ?_, ?_⟩
  · rw [← markTarget]; exact miller'
  · rw [← markTarget, ← arityTarget]; exact arities'

/-- **An instantiated equation side, opened, is in the fragment**: every normal form of the opened
instantiated side is in the fragment, when one normal form of the opened original side exists and
the original side is in the fragment. -/
theorem instantiated_side_in_fragment {Γ : Context R} {type : TypeOver Γ} (value : Term Γ type) {arity : Nat}
    {body : Tm Head (Γ.arity + arity)} (valueCode : value.code = lamsVar arity body) (normal : Normal R body)
    (millerBody : miller (bodyFlexible arity) body = true) (arityOf : piCount type.code = arity)
    (aritiesBody : arities (bodyFlexible arity) (liftArityK arity fun j => piCount (Ctx.lookup Γ.raw j)) body = true)
    (count : Nat) {code : Tm Head (Γ.arity + 1)}
    (inside : ∀ opened, Star (R := R) (openCode count code) opened → Normal R opened →
      InFragmentCode (extend Γ type).raw count opened)
    (normalizes : ∃ opened, Star (R := R) (openCode count code) opened ∧ Normal R opened) :
    ∀ opened, Star (R := R) (openCode count (subst (ContextualDependentEta.Elimination.instantiate Γ value).substitution code))
        opened → Normal R opened → InFragmentCode Γ.raw count opened := by
  obtain ⟨N, toN, normalN⟩ := normalizes
  obtain ⟨N', toN', normalN', insideN'⟩ := instantiate_side_stable empty value valueCode normal millerBody arityOf
    aritiesBody count (inside N toN normalN) normalN
  have reaches : Star (R := R) (openCode count (subst (ContextualDependentEta.Elimination.instantiate Γ value).substitution code)) N' := by
    rw [openCode_subst]
    exact (star_subst _ toN).trans toN'
  exact side_of_normal_form empty reaches normalN' insideN'

end ContextualDependentDynamicFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
