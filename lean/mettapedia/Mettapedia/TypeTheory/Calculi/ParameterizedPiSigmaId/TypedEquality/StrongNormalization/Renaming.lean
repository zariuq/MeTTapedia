import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Candidates
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DecoderComputation

/-!
# Strong normalization is stable under renaming

A renaming changes no term former, so a renamed term has the shape of the term:
it is an abstraction, a pair, an application, a spine of a constant, and so on,
exactly when the term is, with renamed parts. Hence β-steps and projections of
pairs from a renamed term are images of steps from the term.

A root computation reflects renaming when every root step from a renamed term
is the image of a root step from the term. The computations of declared
constants reflect every renaming, injective or not: their left-hand sides are
left-linear and headed by a constant, and the arguments they inspect are
constructor forms or reflexivity, whose preimages under a renaming have the
same shape. This covers the equation of a definition, the computation rules of
a recursor and of a definition by structural recursion, the identity
eliminator at reflexivity, and the decoding of codes. Reflection is preserved
by unions.

When the root computation of a package reflects renaming, so does its whole
reduction. Reductions from a renamed term are then images of reductions from
the term, and a renaming of a strongly normalizing term is strongly
normalizing.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace StrongNormalization

open Normalization
open TelescopeAbstraction (applyClosed)

variable {Head : Type}

/-! ## Terms whose renaming has a given shape -/

section Inversion

variable {n m : Nat} {ρ : Ren n m} {t : Tm Head n}

theorem rename_eq_const {c : DeclName} (h : Presentation.rename ρ t = .const c) :
    t = .const c := by
  cases t <;> simp only [Presentation.rename, reduceCtorEq, Tm.const.injEq] at h
  rw [h]

theorem rename_eq_app {f a : Tm Head m} (h : Presentation.rename ρ t = .app f a) :
    ∃ f' a', t = .app f' a' ∧ Presentation.rename ρ f' = f ∧
      Presentation.rename ρ a' = a := by
  cases t <;> simp only [Presentation.rename, reduceCtorEq, Tm.app.injEq] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem rename_eq_lam {b : Tm Head (m + 1)} (h : Presentation.rename ρ t = .lam b) :
    ∃ b', t = .lam b' ∧ Presentation.rename (liftRen ρ) b' = b := by
  cases t <;> simp only [Presentation.rename, reduceCtorEq, Tm.lam.injEq] at h
  exact ⟨_, rfl, h⟩

theorem rename_eq_pair {a b : Tm Head m} (h : Presentation.rename ρ t = .pair a b) :
    ∃ a' b', t = .pair a' b' ∧ Presentation.rename ρ a' = a ∧
      Presentation.rename ρ b' = b := by
  cases t <;> simp only [Presentation.rename, reduceCtorEq, Tm.pair.injEq] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem rename_eq_fst {p : Tm Head m} (h : Presentation.rename ρ t = .fst p) :
    ∃ p', t = .fst p' ∧ Presentation.rename ρ p' = p := by
  cases t <;> simp only [Presentation.rename, reduceCtorEq, Tm.fst.injEq] at h
  exact ⟨_, rfl, h⟩

theorem rename_eq_snd {p : Tm Head m} (h : Presentation.rename ρ t = .snd p) :
    ∃ p', t = .snd p' ∧ Presentation.rename ρ p' = p := by
  cases t <;> simp only [Presentation.rename, reduceCtorEq, Tm.snd.injEq] at h
  exact ⟨_, rfl, h⟩

theorem rename_eq_refl {a : Tm Head m} (h : Presentation.rename ρ t = .refl a) :
    ∃ a', t = .refl a' ∧ Presentation.rename ρ a' = a := by
  cases t <;> simp only [Presentation.rename, reduceCtorEq, Tm.refl.injEq] at h
  exact ⟨_, rfl, h⟩

theorem rename_eq_pi {A : Tm Head m} {B : Tm Head (m + 1)}
    (h : Presentation.rename ρ t = .pi A B) :
    ∃ A' B', t = .pi A' B' ∧ Presentation.rename ρ A' = A ∧
      Presentation.rename (liftRen ρ) B' = B := by
  cases t <;> simp only [Presentation.rename, reduceCtorEq, Tm.pi.injEq] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem rename_eq_sigma {A : Tm Head m} {B : Tm Head (m + 1)}
    (h : Presentation.rename ρ t = .sigma A B) :
    ∃ A' B', t = .sigma A' B' ∧ Presentation.rename ρ A' = A ∧
      Presentation.rename (liftRen ρ) B' = B := by
  cases t <;> simp only [Presentation.rename, reduceCtorEq, Tm.sigma.injEq] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem rename_eq_id {A a b : Tm Head m} (h : Presentation.rename ρ t = .id A a b) :
    ∃ A' a' b', t = .id A' a' b' ∧ Presentation.rename ρ A' = A ∧
      Presentation.rename ρ a' = a ∧ Presentation.rename ρ b' = b := by
  cases t <;> simp only [Presentation.rename, reduceCtorEq, Tm.id.injEq] at h
  exact ⟨_, _, _, rfl, h.1, h.2.1, h.2.2⟩

end Inversion

/-- A term whose renaming is a spine of a constant is a spine of that constant,
with the arguments renamed. -/
theorem rename_eq_constSpine {c : DeclName} :
    ∀ {n m : Nat} {ρ : Ren n m} {t : Tm Head n} {as : List (Tm Head m)},
      Presentation.rename ρ t = appSpine (.const c) as →
        ∃ as', t = appSpine (.const c) as' ∧ as'.map (Presentation.rename ρ) = as
  | _, _, _, .const c', as, h => by
      simp only [Presentation.rename] at h
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective (show appSpine (.const c') [] = _ from h)
      exact ⟨[], rfl, rfl⟩
  | _, _, ρ, .app g a, as, h => by
      simp only [Presentation.rename] at h
      obtain ⟨init, rfl, hg⟩ := appSpine_const_eq_app h.symm
      obtain ⟨init', rfl, hmap⟩ := rename_eq_constSpine hg
      exact ⟨init' ++ [a], (appSpine_concat _ _ _).symm, by simp [hmap]⟩
  | _, _, _, .var _, as, h | _, _, _, .head _, as, h | _, _, _, .pi _ _, as, h
  | _, _, _, .sigma _ _, as, h | _, _, _, .id _ _ _, as, h | _, _, _, .lam _, as, h
  | _, _, _, .pair _ _, as, h | _, _, _, .fst _, as, h | _, _, _, .snd _, as, h
  | _, _, _, .refl _, as, h => by
      simp only [Presentation.rename] at h
      exact absurd h (not_spine_of (by simp) (by simp) c as)

/-- Arguments of an application to a telescope whose renamings are the
arguments of a substitution come from a substitution of the telescope. -/
theorem telescopeArgs_rename_inv {m k : Nat} (ρ : Ren m k) :
    ∀ {n : Nat} (Θ : Ctx Head n) {σ : Sub Head n k} {as : List (Tm Head m)},
      as.map (Presentation.rename ρ) = telescopeArgs Θ σ →
        ∃ τ : Sub Head n m, as = telescopeArgs Θ τ ∧
          (fun i => Presentation.rename ρ (τ i)) = σ
  | _, .nil, _, _, h =>
      ⟨Fin.elim0, List.map_eq_nil_iff.mp h, funext fun i => Fin.elim0 i⟩
  | _, .snoc Θ _, σ, _, h => by
      change _ = telescopeArgs Θ (tailSub σ) ++ [σ 0] at h
      obtain ⟨init, last, rfl, hinit, hlast⟩ := List.map_eq_append_iff.mp h
      obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp hlast
      obtain ⟨τ, rfl, hτ⟩ := telescopeArgs_rename_inv ρ Θ hinit
      refine ⟨consSub x τ, rfl, ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hx
      · exact congrFun hτ j

/-- Renaming the match of a pattern renames the arguments it matches. -/
theorem rename_matchSub {m k s a : Nat} (ρ : Ren m k) (as : List (Tm Head m)) (d : Nat)
    (σ : Sub Head (s + 1 + d) m) :
    (fun ι => Presentation.rename ρ (matchSub s a as d σ ι)) =
      matchSub s a (as.map (Presentation.rename ρ)) d
        (fun i => Presentation.rename ρ (σ i)) := by
  have e : (Presentation.subst (renSub ρ) : Tm Head m → Tm Head k) = Presentation.rename ρ :=
    funext (subst_renSub ρ)
  have h := subst_matchSub (a := a) (renSub ρ) as d σ
  rw [e] at h
  exact h

/-! ## Reflection of root steps -/

/-- A root computation reflects renaming when every root step from a renamed
term is the image of a root step from the term. -/
def RootReflectsRename (C : RootComputation Head) : Prop :=
  ∀ ⦃n m : Nat⦄ (ρ : Ren n m) ⦃t : Tm Head n⦄ ⦃u : Tm Head m⦄,
    C.step (Presentation.rename ρ t) u → ∃ t', C.step t t' ∧ u = Presentation.rename ρ t'

namespace RootReflectsRename

theorem empty : RootReflectsRename (RootComputation.empty (Head := Head)) :=
  fun _ _ _ _ _ step => False.elim step

/-- A union of root computations that reflect renaming reflects renaming. -/
theorem union {first second : RootComputation Head} (h₁ : RootReflectsRename first)
    (h₂ : RootReflectsRename second) :
    RootReflectsRename (RootComputation.union first second) := by
  intro n m ρ t u step
  rcases step with step | step
  · obtain ⟨t', s, rfl⟩ := h₁ ρ step
    exact ⟨t', .inl s, rfl⟩
  · obtain ⟨t', s, rfl⟩ := h₂ ρ step
    exact ⟨t', .inr s, rfl⟩

theorem unionAll :
    ∀ {cs : List (DeclName × RootComputation Head)},
      (∀ entry ∈ cs, RootReflectsRename entry.2) →
        RootReflectsRename (RootComputation.unionAll cs)
  | [], _ => empty
  | entry :: _, h =>
      union (h entry (List.mem_cons_self ..))
        (unionAll fun e mem => h e (List.mem_cons_of_mem _ mem))

end RootReflectsRename

/-- The equation of a definition reflects renaming. -/
theorem definitionComputation_reflectsRename (f : DeclName) {k : Nat} (Θ : Ctx Head k)
    (rhs : Tm Head k) : RootReflectsRename (definitionComputation f Θ rhs) := by
  intro n m ρ t w step
  obtain ⟨σ, hl, rfl⟩ := step
  rw [applyClosed_eq_appSpine] at hl
  obtain ⟨args, rfl, hmap⟩ := rename_eq_constSpine hl
  obtain ⟨τ, rfl, rfl⟩ := telescopeArgs_rename_inv ρ Θ hmap
  exact ⟨Presentation.subst τ rhs, ⟨τ, (applyClosed_eq_appSpine Θ τ _).symm, rfl⟩,
    (rename_subst ρ τ rhs).symm⟩

/-- The identity eliminator's rule reflects renaming. -/
theorem eliminatorComputation_reflectsRename (J : DeclName) :
    RootReflectsRename (eliminatorComputation (Head := Head) J) := by
  intro n m ρ t w step
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, hl, rfl⟩ := step
  obtain ⟨args, rfl, hmap⟩ := rename_eq_constSpine hl
  obtain ⟨b₀, l₀, rfl, rfl, h₀⟩ := List.map_eq_cons_iff.mp hmap
  obtain ⟨b₁, l₁, rfl, rfl, h₁⟩ := List.map_eq_cons_iff.mp h₀
  obtain ⟨b₂, l₂, rfl, rfl, h₂⟩ := List.map_eq_cons_iff.mp h₁
  obtain ⟨b₃, l₃, rfl, rfl, h₃⟩ := List.map_eq_cons_iff.mp h₂
  obtain ⟨b₄, l₄, rfl, rfl, h₄⟩ := List.map_eq_cons_iff.mp h₃
  obtain ⟨b₅, l₅, rfl, h₅, h₆⟩ := List.map_eq_cons_iff.mp h₄
  obtain rfl := List.map_eq_nil_iff.mp h₆
  obtain ⟨c, rfl, rfl⟩ := rename_eq_refl h₅
  exact ⟨b₃, ⟨b₀, b₁, b₂, b₃, b₄, c, rfl, rfl⟩, rfl⟩

/-- The computation rules of a recursor reflect renaming. -/
theorem iotaComputation_reflectsRename (rec : DeclName)
    (ctors : List (DeclName × List (Field Head))) :
    RootReflectsRename (iotaComputation rec ctors) := by
  intro n m ρ t w step
  obtain ⟨p, ms, i, c, fields, args, mt, hms, hi, has, hm, hl, rfl⟩ := step
  obtain ⟨as', rfl, hmap⟩ := rename_eq_constSpine hl
  obtain ⟨p', rest', rfl, rfl, hrest⟩ := List.map_eq_cons_iff.mp hmap
  obtain ⟨ms', xs', rfl, rfl, hx⟩ := List.map_eq_append_iff.mp hrest
  obtain ⟨x', rfl, hx'⟩ := List.map_eq_singleton_iff.mp hx
  obtain ⟨args', rfl, rfl⟩ := rename_eq_constSpine hx'
  have hmi : (ms'.map (Presentation.rename ρ))[i]? = some mt := hm
  rw [List.getElem?_map] at hmi
  obtain ⟨mt', hmt', rfl⟩ := Option.map_eq_some_iff.mp hmi
  refine ⟨appSpine mt' (args' ++ (recArgs fields args').map (recApp rec (p' :: ms'))),
    ⟨p', ms', i, c, fields, args', mt', by rw [← hms, List.length_map], hi,
      by rw [← has, List.length_map], hmt', rfl, rfl⟩, ?_⟩
  rw [rename_appSpine, List.map_append, List.map_map, ← map_recArgs, List.map_map]
  congr 2
  apply List.map_congr_left
  intro a _
  simp only [Function.comp_apply, rename_recApp, List.map_cons]

/-- The equations of a definition by structural recursion reflect renaming. -/
theorem recursionComputation_reflectsRename (f : DeclName)
    (ctors : List (DeclName × List (Field Head))) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)) :
    RootReflectsRename (recursionComputation f ctors e s d body) := by
  intro n m ρ t w step
  obtain ⟨k, fields, σ, as, mem, has, hl, rfl⟩ := step
  rw [applyClosed_eq_appSpine] at hl
  obtain ⟨args, rfl, hmap⟩ := rename_eq_constSpine hl
  obtain ⟨τ, rfl, hτ⟩ := telescopeArgs_rename_inv ρ _ hmap
  have hscrut : Presentation.rename ρ (scrutOf s d τ) = appSpine (.const k) as := by
    rw [← scrutOf_rename, hτ, scrutOf_replaceScrut]
  obtain ⟨as', hx, hmapAs⟩ := rename_eq_constSpine hscrut
  refine ⟨Presentation.subst (matchSub s fields.length as' d τ)
      (Presentation.subst (hypSub f e s d fields) (body k fields)),
    ⟨k, fields, τ, as', mem, by rw [← has, ← hmapAs, List.length_map], ?_, rfl⟩, ?_⟩
  · rw [applyClosed_eq_appSpine, ← hx, replaceScrut_self]
  · rw [rename_subst, rename_matchSub, hmapAs, hτ, matchSub_replaceScrut]

/-- The decoding of codes reflects renaming. -/
theorem decoderComputation_reflectsRename (D : Decoders Head) :
    RootReflectsRename (decoderComputation D) := by
  intro n m ρ t w step
  change DecoderStep D (Presentation.rename ρ t) w at step
  generalize hs : Presentation.rename ρ t = s at step
  cases step with
  | imp p q =>
      obtain ⟨h, c, rfl, hh, hc⟩ := rename_eq_app hs
      obtain rfl := rename_eq_const hh
      obtain ⟨g, q', rfl, hg, rfl⟩ := rename_eq_app hc
      obtain ⟨i, p', rfl, hi, rfl⟩ := rename_eq_app hg
      obtain rfl := rename_eq_const hi
      refine ⟨_, DecoderStep.imp p' q', ?_⟩
      simp only [Presentation.rename, rename_liftRen_wk]
  | all carrier f =>
      obtain ⟨h, c, rfl, hh, hc⟩ := rename_eq_app hs
      obtain rfl := rename_eq_const hh
      obtain ⟨g, f', rfl, hg, rfl⟩ := rename_eq_app hc
      obtain rfl := rename_eq_const hg
      refine ⟨_, DecoderStep.all carrier f', ?_⟩
      have zero : liftRen ρ 0 = 0 := rfl
      simp only [Presentation.rename, rename_liftRen_wk, rename_liftClosed, zero]
  | eq carrier x y =>
      obtain ⟨h, c, rfl, hh, hc⟩ := rename_eq_app hs
      obtain rfl := rename_eq_const hh
      obtain ⟨g, y', rfl, hg, rfl⟩ := rename_eq_app hc
      obtain ⟨i, x', rfl, hi, rfl⟩ := rename_eq_app hg
      obtain rfl := rename_eq_const hi
      refine ⟨_, DecoderStep.eq carrier x' y', ?_⟩
      simp only [Presentation.rename, rename_liftClosed]

/-! ## Reflection of reduction -/

variable {R : Rules Head}

private theorem reduces_rename_inv (reflects : RootReflectsRename R.computation) {m : Nat}
    {s u : Tm Head m} (step : Reduces R s u) :
    ∀ {n : Nat} (ρ : Ren n m) (t : Tm Head n), Presentation.rename ρ t = s →
      ∃ t', Reduces R t t' ∧ u = Presentation.rename ρ t' := by
  induction step with
  | betaPi body a =>
      intro n ρ t h
      obtain ⟨f, a', rfl, hf, rfl⟩ := rename_eq_app h
      obtain ⟨b, rfl, rfl⟩ := rename_eq_lam hf
      exact ⟨inst0 a' b, .betaPi b a', (rename_inst0 ρ a' b).symm⟩
  | betaSigmaFst a b =>
      intro n ρ t h
      obtain ⟨p, rfl, hp⟩ := rename_eq_fst h
      obtain ⟨a', b', rfl, rfl, rfl⟩ := rename_eq_pair hp
      exact ⟨a', .betaSigmaFst a' b', rfl⟩
  | betaSigmaSnd a b =>
      intro n ρ t h
      obtain ⟨p, rfl, hp⟩ := rename_eq_snd h
      obtain ⟨a', b', rfl, rfl, rfl⟩ := rename_eq_pair hp
      exact ⟨b', .betaSigmaSnd a' b', rfl⟩
  | head e => exact e.elim
  | root r =>
      intro n ρ t h
      subst h
      obtain ⟨t', r', rfl⟩ := reflects ρ r
      exact ⟨t', .root r', rfl⟩
  | congPiDom _ ih =>
      intro n ρ t h
      obtain ⟨A, B, rfl, rfl, rfl⟩ := rename_eq_pi h
      obtain ⟨A', s, rfl⟩ := ih ρ A rfl
      exact ⟨.pi A' B, .congPiDom s, rfl⟩
  | congPiCod _ ih =>
      intro n ρ t h
      obtain ⟨A, B, rfl, rfl, rfl⟩ := rename_eq_pi h
      obtain ⟨B', s, rfl⟩ := ih (liftRen ρ) B rfl
      exact ⟨.pi A B', .congPiCod s, rfl⟩
  | congSigmaDom _ ih =>
      intro n ρ t h
      obtain ⟨A, B, rfl, rfl, rfl⟩ := rename_eq_sigma h
      obtain ⟨A', s, rfl⟩ := ih ρ A rfl
      exact ⟨.sigma A' B, .congSigmaDom s, rfl⟩
  | congSigmaCod _ ih =>
      intro n ρ t h
      obtain ⟨A, B, rfl, rfl, rfl⟩ := rename_eq_sigma h
      obtain ⟨B', s, rfl⟩ := ih (liftRen ρ) B rfl
      exact ⟨.sigma A B', .congSigmaCod s, rfl⟩
  | congIdTy _ ih =>
      intro n ρ t h
      obtain ⟨A, a, b, rfl, rfl, rfl, rfl⟩ := rename_eq_id h
      obtain ⟨A', s, rfl⟩ := ih ρ A rfl
      exact ⟨.id A' a b, .congIdTy s, rfl⟩
  | congIdLeft _ ih =>
      intro n ρ t h
      obtain ⟨A, a, b, rfl, rfl, rfl, rfl⟩ := rename_eq_id h
      obtain ⟨a', s, rfl⟩ := ih ρ a rfl
      exact ⟨.id A a' b, .congIdLeft s, rfl⟩
  | congIdRight _ ih =>
      intro n ρ t h
      obtain ⟨A, a, b, rfl, rfl, rfl, rfl⟩ := rename_eq_id h
      obtain ⟨b', s, rfl⟩ := ih ρ b rfl
      exact ⟨.id A a b', .congIdRight s, rfl⟩
  | congLam _ ih =>
      intro n ρ t h
      obtain ⟨b, rfl, rfl⟩ := rename_eq_lam h
      obtain ⟨b', s, rfl⟩ := ih (liftRen ρ) b rfl
      exact ⟨.lam b', .congLam s, rfl⟩
  | congAppFun _ ih =>
      intro n ρ t h
      obtain ⟨f, a, rfl, rfl, rfl⟩ := rename_eq_app h
      obtain ⟨f', s, rfl⟩ := ih ρ f rfl
      exact ⟨.app f' a, .congAppFun s, rfl⟩
  | congAppArg _ ih =>
      intro n ρ t h
      obtain ⟨f, a, rfl, rfl, rfl⟩ := rename_eq_app h
      obtain ⟨a', s, rfl⟩ := ih ρ a rfl
      exact ⟨.app f a', .congAppArg s, rfl⟩
  | congPairFst _ ih =>
      intro n ρ t h
      obtain ⟨a, b, rfl, rfl, rfl⟩ := rename_eq_pair h
      obtain ⟨a', s, rfl⟩ := ih ρ a rfl
      exact ⟨.pair a' b, .congPairFst s, rfl⟩
  | congPairSnd _ ih =>
      intro n ρ t h
      obtain ⟨a, b, rfl, rfl, rfl⟩ := rename_eq_pair h
      obtain ⟨b', s, rfl⟩ := ih ρ b rfl
      exact ⟨.pair a b', .congPairSnd s, rfl⟩
  | congFst _ ih =>
      intro n ρ t h
      obtain ⟨p, rfl, rfl⟩ := rename_eq_fst h
      obtain ⟨p', s, rfl⟩ := ih ρ p rfl
      exact ⟨.fst p', .congFst s, rfl⟩
  | congSnd _ ih =>
      intro n ρ t h
      obtain ⟨p, rfl, rfl⟩ := rename_eq_snd h
      obtain ⟨p', s, rfl⟩ := ih ρ p rfl
      exact ⟨.snd p', .congSnd s, rfl⟩
  | congRefl _ ih =>
      intro n ρ t h
      obtain ⟨a, rfl, rfl⟩ := rename_eq_refl h
      obtain ⟨a', s, rfl⟩ := ih ρ a rfl
      exact ⟨.refl a', .congRefl s, rfl⟩

/-- Every step from a renamed term is the image of a step from the term, when
the root computation reflects renaming. -/
theorem Reduces.rename_inv (reflects : RootReflectsRename R.computation) {n m : Nat}
    {ρ : Ren n m} {t : Tm Head n} {u : Tm Head m}
    (step : Reduces R (Presentation.rename ρ t) u) :
    ∃ t', Reduces R t t' ∧ u = Presentation.rename ρ t' :=
  reduces_rename_inv reflects step ρ t rfl

/-- Every reduction from a renamed term is the image of a reduction from the
term. -/
theorem ReducesStar.rename_inv (reflects : RootReflectsRename R.computation) {n m : Nat}
    {ρ : Ren n m} {t : Tm Head n} {u : Tm Head m}
    (steps : ReducesStar R (Presentation.rename ρ t) u) :
    ∃ t', ReducesStar R t t' ∧ u = Presentation.rename ρ t' := by
  induction steps with
  | refl => exact ⟨t, .refl, rfl⟩
  | tail _ step ih =>
      obtain ⟨t', steps', rfl⟩ := ih
      obtain ⟨t'', step', rfl⟩ := Reduces.rename_inv reflects step
      exact ⟨t'', steps'.tail step', rfl⟩

/-- A renaming of a strongly normalizing term is strongly normalizing, when the
root computation reflects renaming. -/
theorem SN.rename (reflects : RootReflectsRename R.computation) {n m : Nat} (ρ : Ren n m)
    {t : Tm Head n} (sn : SN R t) : SN R (Presentation.rename ρ t) := by
  induction sn with
  | intro t _ ih =>
      refine SN.intro fun u step => ?_
      obtain ⟨t', s, rfl⟩ := Reduces.rename_inv reflects step
      exact ih t' s

theorem SN.rename_iff (reflects : RootReflectsRename R.computation) {n m : Nat} (ρ : Ren n m)
    {t : Tm Head n} : SN R (Presentation.rename ρ t) ↔ SN R t :=
  ⟨SN.of_rename ρ, SN.rename reflects ρ⟩

end StrongNormalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
