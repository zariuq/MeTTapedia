import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.ExactTransitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.LevelConstraints

/-!
# Type codes over cumulative universes with level variables, as frames

A small typed term model in which universes are cumulative and carry level variables, and whose
unknowns are second order: an unknown `W` declared `Sort d ⟶ Sort c` stands for a family of type
codes, applied to a code. Terms have one parameter `par`, the variable bound by the abstraction an
equation lives under (so `λ x. X x ≐ λ x. Y x` is the equation `X par ≐ Y par`).

* Codes: the parameter, a ground type `gnd : Sort 0`, universes `sort l : Sort (l + 1)`, function
  types `arr A B`, and unknowns applied to a code, `app W t`.
* Typing `Ty v Γ p t l`: under the valuation `v` of the level variables, over the unknowns `Γ`,
  with the parameter of `Sort p`, the code `t` is a type of `Sort l`. It is cumulative
  (`Ty.mono`).
* An assignment gives each unknown a body over the parameter; acting on a term replaces each
  `app W t` by `W`'s body with `t` for the parameter. Since every body is a code of a universe and
  codes take no arguments, acting creates no redex. Two codes are equal at a valuation when they
  are the same code once their levels are evaluated (`Tm.lower`); so `sort u ≐ sort w` holds
  exactly when `u` and `w` have the same value.
* `frames v` is an `Interface.Frames` instance: contexts of declarations, scoped terms, typed
  assignments. Typing is kept by acting (`Ty.act`), so composites of typed assignments are typed.
* **Level constraints are equations of the store**: `u ≤ w` is the equation
  `sort (max u w) ≐ sort w` (`solves_levelEquation`). A postponed level constraint is therefore
  an ordinary equation of a store, and of a step's knowledge.

Positive examples: the identity assignment is typed; a code of `Sort 0` is a code of `Sort 1`.
Negative examples: the parameter of `Sort 1` is not a code of `Sort 0` (`Ty.par_inv`); an unknown
whose codomain is `Sort 1` applied to anything is not a code of `Sort 0` (`Ty.app_inv`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace CumulativeCodes

/-- Type codes over one parameter, with second-order unknowns. -/
inductive Tm where
  /-- The parameter: the variable of the abstraction an equation lives under. -/
  | par : Tm
  /-- A ground type, of `Sort 0`. -/
  | gnd : Tm
  /-- The universe `Sort l`, a type of `Sort (l + 1)`. -/
  | sort (l : Level) : Tm
  /-- The type of functions from `A` to `B`. -/
  | arr (A B : Tm) : Tm
  /-- The unknown `W` applied to a code. -/
  | app (W : Nat) (t : Tm) : Tm
  deriving DecidableEq, Repr

namespace Tm

/-- Replace the parameter by `u`. -/
def inst (u : Tm) : Tm → Tm
  | par => u
  | gnd => gnd
  | sort l => sort l
  | arr A B => arr (inst u A) (inst u B)
  | app W t => app W (inst u t)

/-- Act by an assignment: `σ W` is the body of `W`'s solution, with the parameter for its
argument. -/
def act (σ : Nat → Tm) : Tm → Tm
  | par => par
  | gnd => gnd
  | sort l => sort l
  | arr A B => arr (act σ A) (act σ B)
  | app W t => inst (act σ t) (σ W)

/-- The identity assignment. -/
def idA : Nat → Tm := fun W => app W par

/-- First `f`, then `g`. -/
def compA (g f : Nat → Tm) : Nat → Tm := fun W => act g (f W)

/-- The size of a code. -/
def size : Tm → Nat
  | par => 1
  | gnd => 1
  | sort _ => 1
  | arr A B => size A + size B + 1
  | app _ t => size t + 1

@[simp] theorem inst_par_self : ∀ t : Tm, inst par t = t
  | par => rfl
  | gnd => rfl
  | sort _ => rfl
  | arr A B => by simp only [inst, inst_par_self A, inst_par_self B]
  | app W t => by simp only [inst, inst_par_self t]

theorem inst_inst (u w : Tm) : ∀ t : Tm, inst u (inst w t) = inst (inst u w) t
  | par => rfl
  | gnd => rfl
  | sort _ => rfl
  | arr A B => by simp only [inst, inst_inst u w A, inst_inst u w B]
  | app W t => by simp only [inst, inst_inst u w t]

theorem act_inst (σ : Nat → Tm) (u : Tm) : ∀ s : Tm, act σ (inst u s) = inst (act σ u) (act σ s)
  | par => rfl
  | gnd => rfl
  | sort _ => rfl
  | arr A B => by simp only [inst, act, act_inst σ u A, act_inst σ u B]
  | app W t => by
      show inst (act σ (inst u t)) (σ W) = inst (act σ u) (inst (act σ t) (σ W))
      rw [act_inst σ u t, inst_inst]

@[simp] theorem act_id : ∀ t : Tm, act idA t = t
  | par => rfl
  | gnd => rfl
  | sort _ => rfl
  | arr A B => by simp only [act, act_id A, act_id B]
  | app W t => by
      show app W (inst (act idA t) par) = app W t
      rw [show inst (act idA t) par = act idA t from rfl, act_id t]

theorem act_comp (g f : Nat → Tm) : ∀ t : Tm, act (compA g f) t = act g (act f t)
  | par => rfl
  | gnd => rfl
  | sort _ => rfl
  | arr A B => by simp only [act, act_comp g f A, act_comp g f B]
  | app W t => by
      show inst (act (compA g f) t) (act g (f W)) = act g (inst (act f t) (f W))
      rw [act_comp g f t, act_inst]

/-- Evaluate the levels of the universes in a code at a valuation of the level variables. Two
codes are equal at a valuation when their evaluations are the same code. -/
def lower (v : Nat → Nat) : Tm → Tm
  | par => par
  | gnd => gnd
  | sort l => sort (.const (Level.value v l))
  | arr A B => arr (lower v A) (lower v B)
  | app W t => app W (lower v t)

theorem lower_inst (v : Nat → Nat) (u : Tm) :
    ∀ t : Tm, lower v (inst u t) = inst (lower v u) (lower v t)
  | par => rfl
  | gnd => rfl
  | sort _ => rfl
  | arr A B => by simp only [inst, lower, lower_inst v u A, lower_inst v u B]
  | app W t => by simp only [inst, lower, lower_inst v u t]

theorem lower_act (v : Nat → Nat) (σ : Nat → Tm) :
    ∀ t : Tm, lower v (act σ t) = act (fun W => lower v (σ W)) (lower v t)
  | par => rfl
  | gnd => rfl
  | sort _ => rfl
  | arr A B => by simp only [act, lower, lower_act v σ A, lower_act v σ B]
  | app W t => by
      show lower v (inst (act σ t) (σ W)) = inst (act (fun W => lower v (σ W)) (lower v t)) (lower v (σ W))
      rw [lower_inst, lower_act v σ t]

/-- Whether an unknown occurs in a code. -/
def occurs (W : Nat) : Tm → Bool
  | par => false
  | gnd => false
  | sort _ => false
  | arr A B => occurs W A || occurs W B
  | app V t => V == W || occurs W t

/-- Two assignments that agree off `W` act alike on codes without `W`. -/
theorem act_congr_occurs {σ τ : Nat → Tm} {W : Nat} (same : ∀ V, V ≠ W → σ V = τ V) :
    ∀ t : Tm, occurs W t = false → act σ t = act τ t
  | par, _ => rfl
  | gnd, _ => rfl
  | sort _, _ => rfl
  | arr A B, h => by
      simp only [occurs, Bool.or_eq_false_iff] at h
      simp only [act, act_congr_occurs same A h.1, act_congr_occurs same B h.2]
  | app V t, h => by
      simp only [occurs, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      simp only [act, act_congr_occurs same t h.2, same V h.1]

end Tm

/-! ## Scope -/

/-- The unknowns of a code are among the first `n`. -/
inductive Scoped (n : Nat) : Tm → Prop
  | par : Scoped n .par
  | gnd : Scoped n .gnd
  | sort (l : Level) : Scoped n (.sort l)
  | arr {A B : Tm} : Scoped n A → Scoped n B → Scoped n (.arr A B)
  | app {W : Nat} {t : Tm} : W < n → Scoped n t → Scoped n (.app W t)

theorem Scoped.inst {n : Nat} {u : Tm} (hu : Scoped n u) :
    ∀ {t : Tm}, Scoped n t → Scoped n (Tm.inst u t)
  | _, .par => hu
  | _, .gnd => .gnd
  | _, .sort l => .sort l
  | _, .arr hA hB => .arr (Scoped.inst hu hA) (Scoped.inst hu hB)
  | _, .app hW ht => .app hW (Scoped.inst hu ht)

theorem Scoped.lower {n : Nat} (v : Nat → Nat) : ∀ {t : Tm}, Scoped n t → Scoped n (Tm.lower v t)
  | _, .par => .par
  | _, .gnd => .gnd
  | _, .sort _ => .sort _
  | _, .arr hA hB => .arr (Scoped.lower v hA) (Scoped.lower v hB)
  | _, .app hW ht => .app hW (Scoped.lower v ht)

/-- Assignments that agree on the first `n` unknowns act alike on codes scoped by `n`. -/
theorem act_congr {n : Nat} {σ τ : Nat → Tm} (same : ∀ W, W < n → σ W = τ W) :
    ∀ {t : Tm}, Scoped n t → Tm.act σ t = Tm.act τ t
  | _, .par => rfl
  | _, .gnd => rfl
  | _, .sort _ => rfl
  | _, .arr hA hB => by simp only [Tm.act, act_congr same hA, act_congr same hB]
  | _, .app hW ht => by simp only [Tm.act, act_congr same ht, same _ hW]

/-! ## Typing -/

/-- A declaration of an unknown `Sort dom ⟶ Sort cod`. -/
structure Decl where
  dom : Level
  cod : Level
  deriving DecidableEq, Repr

/-- A context of unknowns. -/
abbrev Ctx := List Decl

/-- `Ty v Γ p t l`: at the valuation `v`, over `Γ`, with the parameter of `Sort p`, the code `t`
is a type of `Sort l`. -/
inductive Ty (v : Nat → Nat) (Γ : Ctx) (p : Nat) : Tm → Nat → Prop
  | par {l : Nat} : p ≤ l → Ty v Γ p .par l
  | gnd {l : Nat} : Ty v Γ p .gnd l
  | sort {k : Level} {l : Nat} : Level.value v k + 1 ≤ l → Ty v Γ p (.sort k) l
  | arr {A B : Tm} {l : Nat} : Ty v Γ p A l → Ty v Γ p B l → Ty v Γ p (.arr A B) l
  | app {W : Nat} {t : Tm} {d : Decl} {l : Nat} : Γ[W]? = some d →
      Ty v Γ p t (Level.value v d.dom) → Level.value v d.cod ≤ l → Ty v Γ p (.app W t) l

/-- A typed assignment from `Δ` to `Γ`: each declared unknown gets a body of its codomain over a
parameter of its domain. -/
def TyA (v : Nat → Nat) (Δ Γ : Ctx) (σ : Nat → Tm) : Prop :=
  ∀ (W : Nat) (d : Decl), Δ[W]? = some d →
    Ty v Γ (Level.value v d.dom) (σ W) (Level.value v d.cod)

section Typing

variable {v : Nat → Nat}

/-- **Cumulativity.** -/
theorem Ty.mono {Γ : Ctx} {p : Nat} {t : Tm} {l : Nat} (h : Ty v Γ p t l) :
    ∀ {l' : Nat}, l ≤ l' → Ty v Γ p t l' := by
  induction h with
  | par h => exact fun le => .par (le_trans h le)
  | gnd => exact fun _ => .gnd
  | sort h => exact fun le => .sort (le_trans h le)
  | arr _ _ ihA ihB => exact fun le => .arr (ihA le) (ihB le)
  | app hW ht hc _ => exact fun le => .app hW ht (le_trans hc le)

theorem Ty.par_inv {Γ : Ctx} {p l : Nat} (h : Ty v Γ p .par l) : p ≤ l := by
  cases h
  assumption

theorem Ty.app_inv {Γ : Ctx} {p : Nat} {W : Nat} {t : Tm} {l : Nat} (h : Ty v Γ p (.app W t) l) :
    ∃ d, Γ[W]? = some d ∧ Ty v Γ p t (Level.value v d.dom) ∧ Level.value v d.cod ≤ l := by
  cases h with
  | app hW ht hc => exact ⟨_, hW, ht, hc⟩

/-- Instantiating the parameter keeps typing. -/
theorem Ty.inst {Γ : Ctx} {p q : Nat} {u : Tm} (hu : Ty v Γ p u q) {s : Tm} {l : Nat}
    (hs : Ty v Γ q s l) : Ty v Γ p (Tm.inst u s) l := by
  induction hs with
  | par h => exact hu.mono h
  | gnd => exact .gnd
  | sort h => exact .sort h
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | app hW _ hc ih => exact .app hW ih hc

/-- **Acting by a typed assignment keeps typing.** -/
theorem Ty.act {Δ Γ : Ctx} {σ : Nat → Tm} (hσ : TyA v Δ Γ σ) {p : Nat} {t : Tm} {l : Nat}
    (ht : Ty v Δ p t l) : Ty v Γ p (Tm.act σ t) l := by
  induction ht with
  | par h => exact .par h
  | gnd => exact .gnd
  | sort h => exact .sort h
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | app hW _ hc ih => exact Ty.inst ih ((hσ _ _ hW).mono hc)

theorem Ty.scoped {Γ : Ctx} {p : Nat} {t : Tm} {l : Nat} (h : Ty v Γ p t l) :
    Scoped Γ.length t := by
  induction h with
  | par _ => exact .par
  | gnd => exact .gnd
  | sort _ => exact .sort _
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | app hW _ _ ih => exact .app (List.getElem?_eq_some_iff.mp hW).1 ih

/-- Evaluating the levels keeps typing. -/
theorem Ty.lower {Γ : Ctx} {p : Nat} {t : Tm} {l : Nat} (h : Ty v Γ p t l) :
    Ty v Γ p (Tm.lower v t) l := by
  induction h with
  | par h => exact .par h
  | gnd => exact .gnd
  | sort h => exact .sort h
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | app hW _ hc ih => exact .app hW ih hc

theorem TyA.lower {Δ Γ : Ctx} {σ : Nat → Tm} (hσ : TyA v Δ Γ σ) :
    TyA v Δ Γ (fun W => Tm.lower v (σ W)) :=
  fun W d hW => (hσ W d hW).lower

theorem idA_typed (Δ : Ctx) : TyA v Δ Δ Tm.idA :=
  fun _ _ hW => .app hW (.par le_rfl) le_rfl

theorem compA_typed {Δ Γ Θ : Ctx} {f g : Nat → Tm} (hf : TyA v Δ Γ f) (hg : TyA v Γ Θ g) :
    TyA v Δ Θ (Tm.compA g f) :=
  fun W d hW => Ty.act hg (hf W d hW)

theorem Scoped.act {Δ Γ : Ctx} {σ : Nat → Tm} (hσ : TyA v Δ Γ σ) {t : Tm}
    (ht : Scoped Δ.length t) : Scoped Γ.length (Tm.act σ t) := by
  induction ht with
  | par => exact .par
  | gnd => exact .gnd
  | sort l => exact .sort l
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | app hW _ ih => exact Scoped.inst ih (hσ _ _ (List.getElem?_eq_getElem hW)).scoped

end Typing

/-! ## The frames -/

/-- The terms over a context: codes whose unknowns it declares. -/
abbrev Term (Γ : Ctx) : Type := {t : Tm // Scoped Γ.length t}

/-- The typed assignments at a valuation of the level variables. -/
abbrev Assign (v : Nat → Nat) (Δ Γ : Ctx) : Type := {σ : Nat → Tm // TyA v Δ Γ σ}

/-- **The frames of cumulative codes** at a valuation of the level variables. Two terms are equal
when they are the same code once their levels are evaluated. -/
def frames (v : Nat → Nat) : Frames Term (Assign v) where
  E s t := Tm.lower v s.1 = Tm.lower v t.1
  equivalence _ := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩
  act σ t := ⟨Tm.act σ.1 t.1, Scoped.act σ.2 t.2⟩
  id Δ := ⟨Tm.idA, idA_typed Δ⟩
  comp g f := ⟨Tm.compA g.1 f.1, compA_typed f.2 g.2⟩
  act_id t := Subtype.ext (Tm.act_id t.1)
  act_comp g f t := Subtype.ext (Tm.act_comp g.1 f.1 t.1)
  preserves := @fun _ _ σ s t h => by
    show Tm.lower v (Tm.act σ.1 s.1) = Tm.lower v (Tm.act σ.1 t.1)
    rw [Tm.lower_act, Tm.lower_act]
    exact congrArg _ h

variable {v : Nat → Nat}

theorem models_iff {Δ Γ : Ctx} (σ : Assign v Δ Γ) (S : EquationStore (Term Δ)) :
    (frames v).Models σ S ↔
      ∀ e ∈ S, Tm.lower v (Tm.act σ.1 e.1.1) = Tm.lower v (Tm.act σ.1 e.2.1) :=
  Iff.rfl

/-- Assignments whose bodies agree, once levels are evaluated, on the declared unknowns agree on
every term. -/
theorem agree_of_unknowns {Δ Γ : Ctx} {f g : Assign v Δ Γ}
    (same : ∀ W, W < Δ.length → Tm.lower v (f.1 W) = Tm.lower v (g.1 W)) :
    Agree (frames v) f g := by
  intro t
  show Tm.lower v (Tm.act f.1 t.1) = Tm.lower v (Tm.act g.1 t.1)
  rw [Tm.lower_act, Tm.lower_act]
  exact act_congr same (t.2.lower v)

/-- **A level constraint is an equation of codes**: `u ≤ w` is `sort (max u w) ≐ sort w`. -/
def levelEquation {Δ : Ctx} (c : LevelLe) : Equation (Term Δ) :=
  (⟨.sort (.max c.lhs c.rhs), .sort _⟩, ⟨.sort c.rhs, .sort _⟩)

theorem solves_levelEquation {Δ Γ : Ctx} (f : Assign v Δ Γ) (c : LevelLe) :
    (frames v).Solves f (levelEquation c) ↔ c.Holds v := by
  show Tm.sort (.const (Level.value v (.max c.lhs c.rhs))) = Tm.sort (.const (Level.value v c.rhs))
    ↔ c.Holds v
  rw [LevelLe.holds_iff_max_eq]
  constructor
  · intro h
    exact Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const.inj (Tm.sort.inj h)
  · intro h
    rw [h]

end CumulativeCodes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
