import Mettapedia.Languages.Agda.Intrinsic.Events

/-!
# Completeness of the authored Agda reductions

The reference compatible closure uses one generic argument-step relation.
This proof checks that the finite authored list contains every argument
position, including the domain and bound codomain of dependent products.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic.Authored

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

theorem piCong0_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm (.term :: Γ))
    (y : Tm Γ)
    (child : Reduces rules (judgment x0 y)) :
    Reduces rules (judgment (pi x0 x1)
      (pi y x1)) := by
  obtain ⟨tree⟩ := child
  exact ⟨piCong0_event (valuation x1 (.var .zero) x0 y star star star star) tree⟩

theorem piCong1_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm (.term :: Γ))
    (y : Tm (.term :: Γ))
    (child : Reduces rules (judgment x1 y)) :
    Reduces rules (judgment (pi x0 x1)
      (pi x0 y)) := by
  obtain ⟨tree⟩ := child
  exact ⟨piCong1_event (valuation x1 y star star x0 star star star) tree⟩

theorem lamCong0_firing {Γ : Ctx sig} (x0 : Tm (.term :: Γ))
    (y : Tm (.term :: Γ))
    (child : Reduces rules (judgment x0 y)) :
    Reduces rules (judgment (lam x0)
      (lam y)) := by
  obtain ⟨tree⟩ := child
  exact ⟨lamCong0_event (valuation x0 y star star star star star star) tree⟩

theorem appCong0_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x0 y)) :
    Reduces rules (judgment (app x0 x1)
      (app y x1)) := by
  obtain ⟨tree⟩ := child
  exact ⟨appCong0_event (valuation (.var .zero) (.var .zero) x0 y x1 star star star) tree⟩

theorem appCong1_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x1 y)) :
    Reduces rules (judgment (app x0 x1)
      (app x0 y)) := by
  obtain ⟨tree⟩ := child
  exact ⟨appCong1_event (valuation (.var .zero) (.var .zero) x1 y x0 star star star) tree⟩

theorem annCong0_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x0 y)) :
    Reduces rules (judgment (ann x0 x1)
      (ann y x1)) := by
  obtain ⟨tree⟩ := child
  exact ⟨annCong0_event (valuation (.var .zero) (.var .zero) x0 y x1 star star star) tree⟩

theorem annCong1_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x1 y)) :
    Reduces rules (judgment (ann x0 x1)
      (ann x0 y)) := by
  obtain ⟨tree⟩ := child
  exact ⟨annCong1_event (valuation (.var .zero) (.var .zero) x1 y x0 star star star) tree⟩

theorem sigmaCong0_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm (.term :: Γ))
    (y : Tm Γ)
    (child : Reduces rules (judgment x0 y)) :
    Reduces rules (judgment (sigma x0 x1)
      (sigma y x1)) := by
  obtain ⟨tree⟩ := child
  exact ⟨sigmaCong0_event (valuation x1 (.var .zero) x0 y star star star star) tree⟩

theorem sigmaCong1_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm (.term :: Γ))
    (y : Tm (.term :: Γ))
    (child : Reduces rules (judgment x1 y)) :
    Reduces rules (judgment (sigma x0 x1)
      (sigma x0 y)) := by
  obtain ⟨tree⟩ := child
  exact ⟨sigmaCong1_event (valuation x1 y star star x0 star star star) tree⟩

theorem pairCong0_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x0 y)) :
    Reduces rules (judgment (pair x0 x1)
      (pair y x1)) := by
  obtain ⟨tree⟩ := child
  exact ⟨pairCong0_event (valuation (.var .zero) (.var .zero) x0 y x1 star star star) tree⟩

theorem pairCong1_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x1 y)) :
    Reduces rules (judgment (pair x0 x1)
      (pair x0 y)) := by
  obtain ⟨tree⟩ := child
  exact ⟨pairCong1_event (valuation (.var .zero) (.var .zero) x1 y x0 star star star) tree⟩

theorem fstCong0_firing {Γ : Ctx sig} (x0 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x0 y)) :
    Reduces rules (judgment (fst x0)
      (fst y)) := by
  obtain ⟨tree⟩ := child
  exact ⟨fstCong0_event (valuation (.var .zero) (.var .zero) x0 y star star star star) tree⟩

theorem sndCong0_firing {Γ : Ctx sig} (x0 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x0 y)) :
    Reduces rules (judgment (snd x0)
      (snd y)) := by
  obtain ⟨tree⟩ := child
  exact ⟨sndCong0_event (valuation (.var .zero) (.var .zero) x0 y star star star star) tree⟩

theorem sucCong0_firing {Γ : Ctx sig} (x0 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x0 y)) :
    Reduces rules (judgment (suc x0)
      (suc y)) := by
  obtain ⟨tree⟩ := child
  exact ⟨sucCong0_event (valuation (.var .zero) (.var .zero) x0 y star star star star) tree⟩

theorem natrecCong0_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm Γ) (x2 : Tm Γ) (x3 : Tm Γ) (x4 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x0 y)) :
    Reduces rules (judgment (natrec x0 x1 x2 x3 x4)
      (natrec y x1 x2 x3 x4)) := by
  obtain ⟨tree⟩ := child
  exact ⟨natrecCong0_event (valuation (.var .zero) (.var .zero) x0 y x1 x2 x3 x4) tree⟩

theorem natrecCong1_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm Γ) (x2 : Tm Γ) (x3 : Tm Γ) (x4 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x1 y)) :
    Reduces rules (judgment (natrec x0 x1 x2 x3 x4)
      (natrec x0 y x2 x3 x4)) := by
  obtain ⟨tree⟩ := child
  exact ⟨natrecCong1_event (valuation (.var .zero) (.var .zero) x1 y x0 x2 x3 x4) tree⟩

theorem natrecCong2_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm Γ) (x2 : Tm Γ) (x3 : Tm Γ) (x4 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x2 y)) :
    Reduces rules (judgment (natrec x0 x1 x2 x3 x4)
      (natrec x0 x1 y x3 x4)) := by
  obtain ⟨tree⟩ := child
  exact ⟨natrecCong2_event (valuation (.var .zero) (.var .zero) x2 y x0 x1 x3 x4) tree⟩

theorem natrecCong3_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm Γ) (x2 : Tm Γ) (x3 : Tm Γ) (x4 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x3 y)) :
    Reduces rules (judgment (natrec x0 x1 x2 x3 x4)
      (natrec x0 x1 x2 y x4)) := by
  obtain ⟨tree⟩ := child
  exact ⟨natrecCong3_event (valuation (.var .zero) (.var .zero) x3 y x0 x1 x2 x4) tree⟩

theorem natrecCong4_firing {Γ : Ctx sig} (x0 : Tm Γ) (x1 : Tm Γ) (x2 : Tm Γ) (x3 : Tm Γ) (x4 : Tm Γ)
    (y : Tm Γ)
    (child : Reduces rules (judgment x4 y)) :
    Reduces rules (judgment (natrec x0 x1 x2 x3 x4)
      (natrec x0 x1 x2 x3 y)) := by
  obtain ⟨tree⟩ := child
  exact ⟨natrecCong4_event (valuation (.var .zero) (.var .zero) x4 y x0 x1 x2 x3) tree⟩

theorem root_firing : {Γ : Ctx sig} → {source target : Tm Γ} →
    Root source target → Reduces rules (judgment source target)
  | _, _, _, .beta body arg =>
      ⟨beta_event (valuation body (.var .zero) arg star star star star star)⟩
  | _, _, _, .first a b =>
      ⟨first_event (valuation (.var .zero) (.var .zero) a b star star star star)⟩
  | _, _, _, .second a b =>
      ⟨second_event (valuation (.var .zero) (.var .zero) a b star star star star)⟩
  | _, _, _, .annotation t A =>
      ⟨annotation_event (valuation (.var .zero) (.var .zero) t A star star star star)⟩
  | _, _, _, .successor n =>
      ⟨successor_event (valuation (.var .zero) (.var .zero) n star star star star star)⟩
  | _, _, _, .recZero l P z s =>
      ⟨recZero_event (valuation (.var .zero) (.var .zero) l P z s star star)⟩
  | _, _, _, .recSuc l P z s n =>
      ⟨recSuc_event (valuation (.var .zero) (.var .zero) l P z s n star)⟩

private inductive FiringArgs : {Γ : Ctx sig} → {arity : List (List Srt × Srt)} →
    Args sig arity Γ → Args sig arity Γ → Prop where
  | head {Γ bs rest} {a b : Tm (bs ++ Γ)} (tail : Args sig rest Γ) :
      Reduces rules (judgment a b) → FiringArgs (.cons a tail) (.cons b tail)
  | tail {Γ bs rest} (a : Tm (bs ++ Γ)) {as bs' : Args sig rest Γ} :
      FiringArgs as bs' → FiringArgs (.cons a as) (.cons a bs')

private theorem congr_firing : {Γ : Ctx sig} → (op : Op .term) →
    {as bs : Args sig (sig.arity op) Γ} → FiringArgs as bs →
    Reduces rules (judgment (.op op as) (.op op bs))
  | _, .pi, _, _, (.head (.cons x1 .nil) child) => piCong0_firing _ x1 _ child
  | _, .pi, _, _, (.tail x0 (.head .nil child)) => piCong1_firing x0 _ _ child
  | _, .lam, _, _, (.head .nil child) => lamCong0_firing _ _ child
  | _, .app, _, _, (.head (.cons x1 .nil) child) => appCong0_firing _ x1 _ child
  | _, .app, _, _, (.tail x0 (.head .nil child)) => appCong1_firing x0 _ _ child
  | _, .ann, _, _, (.head (.cons x1 .nil) child) => annCong0_firing _ x1 _ child
  | _, .ann, _, _, (.tail x0 (.head .nil child)) => annCong1_firing x0 _ _ child
  | _, .sigma, _, _, (.head (.cons x1 .nil) child) => sigmaCong0_firing _ x1 _ child
  | _, .sigma, _, _, (.tail x0 (.head .nil child)) => sigmaCong1_firing x0 _ _ child
  | _, .pair, _, _, (.head (.cons x1 .nil) child) => pairCong0_firing _ x1 _ child
  | _, .pair, _, _, (.tail x0 (.head .nil child)) => pairCong1_firing x0 _ _ child
  | _, .fst, _, _, (.head .nil child) => fstCong0_firing _ _ child
  | _, .snd, _, _, (.head .nil child) => sndCong0_firing _ _ child
  | _, .suc, _, _, (.head .nil child) => sucCong0_firing _ _ child
  | _, .natrec, _, _, (.head (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))) child) => natrecCong0_firing _ x1 x2 x3 x4 _ child
  | _, .natrec, _, _, (.tail x0 (.head (.cons x2 (.cons x3 (.cons x4 .nil))) child)) => natrecCong1_firing x0 _ x2 x3 x4 _ child
  | _, .natrec, _, _, (.tail x0 (.tail x1 (.head (.cons x3 (.cons x4 .nil)) child))) => natrecCong2_firing x0 x1 _ x3 x4 _ child
  | _, .natrec, _, _, (.tail x0 (.tail x1 (.tail x2 (.head (.cons x4 .nil) child)))) => natrecCong3_firing x0 x1 x2 _ x4 _ child
  | _, .natrec, _, _, (.tail x0 (.tail x1 (.tail x2 (.tail x3 (.head .nil child))))) => natrecCong4_firing x0 x1 x2 x3 _ _ child

/-- Every compatible step has a firing tree in the same authored presentation. -/
theorem firing_complete {Γ : Ctx sig} {source target : Tm Γ}
    (step : Step source target) : Reduces rules (judgment source target) := by
  apply Step.rec
    (motive_1 := fun a b _ => Reduces rules (judgment a b))
    (motive_2 := fun as bs _ => FiringArgs as bs)
    (fun h => root_firing h)
    (by intro Γ op as bs h ih; exact congr_firing op ih)
    (by intro Γ bs rest a b tail h ih; exact FiringArgs.head tail ih)
    (by intro Γ bs rest a as bs' h ih; exact FiringArgs.tail a ih) step

/-- No omitted reductions and no invented reductions, at arbitrary open contexts. -/
theorem firing_iff_step {Γ : Ctx sig} {source target : Tm Γ} :
    Reduces rules (judgment source target) ↔ Step source target :=
  ⟨firing_sound, firing_complete⟩

end Mettapedia.Languages.Agda.Intrinsic.Authored
