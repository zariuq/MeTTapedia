import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHead

/-!
# Head-form inspection: controls

A toy package over one head with two computing constants. `tcase X d`
inspects `X` for a head form and then steps to `d`; `ccase X` inspects `X` for
a constructor form. The constant `k` is rigid.

* Positive: `tcase` steps at a dependent function type and at a spine of the
  rigid `k`; at a β-redex it first reduces the inspected argument.
* Negative: `tcase` is stuck at a type variable, where the spine is neutral
  and weak-head normal; a package with these roles takes no root step there.
  `ccase` takes no root step at a function type, and is neutral at a rigid
  spine, which a constructor inspection does not accept.
* Stability: head-form acceptance is not preserved when a rigid constant is
  given a computing role, even when every other role is kept. The step of
  `tcase` at `k a` is accepted while `k` is rigid and not once `k` computes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace HeadFormControls

/-- The inspecting constant of the type case. -/
def tcase : DeclName := .mkSimple "tcase"
/-- A constant inspecting a constructor form. -/
def ccase : DeclName := .mkSimple "ccase"
/-- A rigid constant. -/
def k : DeclName := .mkSimple "k"

/-- `tcase` inspects its first argument for a head form and `ccase` its only
argument for a constructor form; every other constant is rigid. -/
def roles : Roles Unit := fun name =>
  if name = tcase then .computes 2 (.split 0 .headForm fun _ => .leaf)
  else if name = ccase then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else .rigid

theorem roles_tcase : roles tcase = .computes 2 (.split 0 .headForm fun _ => .leaf) := rfl
theorem roles_ccase : roles ccase = .computes 1 (.split 0 .constructor fun _ => .leaf) := rfl
theorem roles_k : roles k = .rigid := rfl

/-- `tcase X d ⟶ d` once `X` is a head form. -/
def computation : RootComputation Unit where
  step := fun {n} l r => ∃ X d : Tm Unit n,
    l = appSpine (.const tcase) [X, d] ∧ HeadForm roles X ∧ r = d
  rename := by
    intro n m ρ l r ⟨X, d, e, ⟨key, view⟩, er⟩
    subst e er
    exact ⟨_, _, by rw [rename_appSpine]; rfl, ⟨key, view.rename ρ⟩, rfl⟩
  substitute := by
    intro n m σ l r ⟨X, d, e, ⟨key, view⟩, er⟩
    subst e er
    exact ⟨_, _, by rw [subst_appSpine]; rfl, ⟨key, view.subst σ⟩, rfl⟩

/-- The toy package: no typing structure, only the type case's step. -/
def rules : Rules Unit where
  headTyping _ _ := False
  isUniverse _ := False
  join _ _ _ := False
  cumulative _ _ := False
  headEq _ _ := False
  computation := computation

/-- A spine of `k` is a head form while `k` is rigid. -/
theorem k_headView {n : Nat} (args : List (Tm Unit n)) :
    HeadView roles (appSpine (.const k) args) (.const k) :=
  .spine args fun _ _ computes => nomatch roles_k.symm.trans computes

/-- A variable is not a head form. -/
theorem var_not_headForm {rs : Roles Unit} {n : Nat} (i : Fin n) :
    ¬ HeadForm rs (.var i : Tm Unit n) := by
  rintro ⟨key, view⟩
  generalize e : (Tm.var i : Tm Unit n) = t at view
  cases view with
  | spine args _ => exact appSpine_const_ne_var e.symm
  | _ => cases e

theorem shape : RootShape rules roles where
  spine := by
    intro n t u ⟨X, d, e, ⟨key, view⟩, _⟩
    subst e
    exact ⟨tcase, 2, _, [X, d], roles_tcase, rfl, rfl,
      .headForm (before := []) (after := [d]) rfl view (.leaf _)⟩
  deterministic := by
    intro n t u u' ⟨X, d, e, _, eu⟩ ⟨X', d', e', _, eu'⟩
    rw [e] at e'
    obtain ⟨-, args⟩ := appSpine_const_injective e'
    obtain ⟨-, rest⟩ := List.cons.inj args
    obtain ⟨rfl, -⟩ := List.cons.inj rest
    rw [eu, eu']

/-! ## Positive controls -/

/-- The type case steps at a dependent function type. -/
theorem tcase_pi {n : Nat} (A : Tm Unit n) (B : Tm Unit (n + 1)) (d : Tm Unit n) :
    WhStep rules roles (appSpine (.const tcase) [.pi A B, d]) d :=
  .root ⟨_, _, rfl, ⟨_, .pi A B⟩, rfl⟩

/-- The type case steps at a spine of a rigid constant. -/
theorem tcase_rigid {n : Nat} (a d : Tm Unit n) :
    WhStep rules roles (appSpine (.const tcase) [appSpine (.const k) [a], d]) d :=
  .root ⟨_, _, rfl, ⟨_, k_headView [a]⟩, rfl⟩

/-- The type case first reduces the argument it inspects. -/
theorem tcase_reduces {n : Nat} (A : Tm Unit n) (B : Tm Unit (n + 1)) (d : Tm Unit n) :
    WhRed rules roles
      (appSpine (.const tcase) [.app (.lam (.var 0)) (.pi A B), d]) d := by
  have beta : WhStep rules roles (.app (.lam (.var 0)) (.pi A B)) (.pi A B) :=
    .beta (.var 0) (.pi A B)
  have inner : WhStep rules roles (appSpine (.const tcase) [.app (.lam (.var 0)) (.pi A B), d])
      (appSpine (.const tcase) [.pi A B, d]) :=
    .scrutinee roles_tcase rfl (.here (before := []) (after := [d]) rfl) beta
  exact (Relation.ReflTransGen.single inner).tail (tcase_pi A B d)

/-! ## Negative controls -/

/-- At a type variable the type case is neutral. -/
theorem tcase_var_neutral {n : Nat} (i : Fin n) (d : Tm Unit n) :
    Neutral roles (appSpine (.const tcase) [.var i, d]) :=
  .stuck roles_tcase rfl (.here (before := []) (after := [d]) rfl) (.var i)
    fun _ => var_not_headForm i

/-- At a type variable the type case is weak-head normal. -/
theorem tcase_var_whnf {n : Nat} (i : Fin n) (d : Tm Unit n) :
    Whnf rules roles (appSpine (.const tcase) [.var i, d]) :=
  (tcase_var_neutral i d).whnf shape

/-- No package with these roles has a root step of the type case at a type
variable. -/
theorem tcase_var_no_root {R : Rules Unit} (rootShape : RootShape R roles) {n : Nat}
    (i : Fin n) (d u : Tm Unit n) :
    ¬ R.computation.step (appSpine (.const tcase) [.var i, d]) u := by
  intro step
  obtain ⟨c, arity, inspect, args, role, e, _, accepts⟩ := rootShape.spine step
  obtain ⟨rfl, rfl⟩ := appSpine_const_injective e
  rw [roles_tcase] at role
  injection role with _ same
  subst same
  have focus : (InspectTree.split 0 .headForm fun _ => .leaf).Focus roles [.var i, d]
      [.var i, d] .headForm (.var i) (.var i) := .here (before := []) (after := [d]) rfl
  exact var_not_headForm i (focus.accepted accepts)

/-- No package with these roles has a root step of the constructor inspection
at a dependent function type, which is a head form but no constructor form. -/
theorem ccase_pi_no_root {R : Rules Unit} (rootShape : RootShape R roles) {n : Nat}
    (A : Tm Unit n) (B : Tm Unit (n + 1)) (u : Tm Unit n) :
    ¬ R.computation.step (appSpine (.const ccase) [.pi A B]) u := by
  intro step
  obtain ⟨c, arity, inspect, args, role, e, _, accepts⟩ := rootShape.spine step
  obtain ⟨rfl, rfl⟩ := appSpine_const_injective e
  rw [roles_ccase] at role
  injection role with _ same
  subst same
  obtain ⟨a, found, canonical⟩ := InspectTree.accepts_single.mp accepts
  cases found
  rcases canonical with ⟨x, e⟩ | ⟨c, arity, args, _, e⟩
  · cases e
  · rcases appSpine_const_cases c args with h | ⟨f, x, h⟩ <;> rw [h] at e <;> cases e

/-- At a rigid spine the constructor inspection is neutral. -/
theorem ccase_rigid_neutral {n : Nat} (a : Tm Unit n) :
    Neutral roles (appSpine (.const ccase) [appSpine (.const k) [a]]) :=
  .stuck roles_ccase rfl (.here (before := []) (after := []) rfl) (.rigid [a] roles_k) nofun

/-! ## Stability under a change of roles -/

/-- The roles with `k` computing, inspecting a constructor form: every role
of `roles` that is not rigid is kept. -/
def rolesK : Roles Unit := fun name =>
  if name = k then .computes 1 (.split 0 .constructor fun _ => .leaf) else roles name

theorem rolesK_keep {c : DeclName} {role : Role Unit} (declared : roles c = role)
    (nonrigid : role ≠ .rigid) : rolesK c = role := by
  unfold rolesK
  split
  · subst c
    exact absurd (declared.symm.trans roles_k) nonrigid
  · exact declared

/-- With `k` computing, a spine of `k` is no head form. -/
theorem rolesK_not_headForm {n : Nat} (a : Tm Unit n) :
    ¬ HeadForm rolesK (appSpine (.const k) [a]) := by
  rintro ⟨key, view⟩
  generalize e : appSpine (.const k) [a] = t at view
  cases view with
  | spine args notComputing =>
      obtain ⟨rfl, -⟩ := appSpine_const_injective e.symm
      exact notComputing 1 _ rfl
  | _ => cases e

/-- Keeping the roles that are not rigid does not keep root shape: the type
case's step at `k a` loses its head form once `k` computes. -/
theorem rootShape_not_kept : RootShape rules roles ∧
    (∀ {c : DeclName} {role : Role Unit}, roles c = role → role ≠ .rigid → rolesK c = role) ∧
    ¬ RootShape rules rolesK := by
  refine ⟨shape, rolesK_keep, fun shapeK => ?_⟩
  have step : rules.computation.step
      (appSpine (.const tcase) [appSpine (.const k) [.const k], .const k] : Tm Unit 0) (.const k) :=
    ⟨_, _, rfl, ⟨_, k_headView [.const k]⟩, rfl⟩
  obtain ⟨c, arity, inspect, args, role, e, _, accepts⟩ := shapeK.spine step
  obtain ⟨rfl, rfl⟩ := appSpine_const_injective e
  have role' : rolesK tcase = .computes 2 (.split 0 .headForm fun _ => .leaf) := rfl
  rw [role'] at role
  injection role with _ same
  subst same
  have focus : (InspectTree.split 0 .headForm fun _ => .leaf).Focus rolesK
      [appSpine (.const k) [.const k], .const k] [appSpine (.const k) [.const k], .const k]
      .headForm (appSpine (.const k) [.const k] : Tm Unit 0) (appSpine (.const k) [.const k]) :=
    .here (before := []) (after := [.const k]) rfl
  exact rolesK_not_headForm _ (focus.accepted accepts)

end HeadFormControls
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
