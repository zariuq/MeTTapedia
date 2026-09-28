import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.InductiveConsequences

/-!
# The computation rules of a recursor as a root computation

The computation rules of the recursor of a simple inductive type,
`rec P m₁ ⋯ m_c (kᵢ a₁ ⋯ aₐ) ⟶ mᵢ a₁ ⋯ aₐ (rec P m₁ ⋯ m_c aⱼ) ⋯`, form a root
computation closed under renaming and substitution. Its steps occur at full
applications of the recursor with a constructor form as scrutinee, and they
are deterministic when the constructors have distinct names. In a rule package
declaring the type, they preserve typing.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

theorem map_recArgs {n m : Nat} (f : Tm Head n → Tm Head m) :
    ∀ (fs : List (Field Head)) (as : List (Tm Head n)),
      (recArgs fs as).map f = recArgs fs (as.map f)
  | .recursive :: fs, a :: as => by simp [recArgs, map_recArgs f fs as]
  | .closed _ :: fs, _ :: as => by simp [recArgs, map_recArgs f fs as]
  | [], _ => by simp [recArgs]
  | .recursive :: _, [] => by simp [recArgs]
  | .closed _ :: _, [] => by simp [recArgs]

theorem rename_recApp {n m : Nat} (ρ : Ren n m) (rec : DeclName) (pre : List (Tm Head n))
    (t : Tm Head n) :
    Presentation.rename ρ (recApp rec pre t) =
      recApp rec (pre.map (Presentation.rename ρ)) (Presentation.rename ρ t) := by
  simp [recApp, rename_appSpine, Presentation.rename]

theorem subst_recApp {n m : Nat} (σ : Sub Head n m) (rec : DeclName) (pre : List (Tm Head n))
    (t : Tm Head n) :
    Presentation.subst σ (recApp rec pre t) =
      recApp rec (pre.map (Presentation.subst σ)) (Presentation.subst σ t) := by
  simp [recApp, subst_appSpine, Presentation.subst]

/-- A computation rule of the recursor `rec` of the constructors `ctors`. -/
def IotaStep (rec : DeclName) (ctors : List (DeclName × List (Field Head))) {n : Nat}
    (l r : Tm Head n) : Prop :=
  ∃ (p : Tm Head n) (ms : List (Tm Head n)) (i : Nat) (k : DeclName) (fields : List (Field Head))
    (args : List (Tm Head n)) (m : Tm Head n),
    ms.length = ctors.length ∧ ctors[i]? = some (k, fields) ∧ args.length = fields.length ∧
    ms[i]? = some m ∧ l = recApp rec (p :: ms) (appSpine (.const k) args) ∧
    r = appSpine m (args ++ (recArgs fields args).map (recApp rec (p :: ms)))

/-- The computation rules of a recursor, as a root computation. -/
def iotaComputation (rec : DeclName) (ctors : List (DeclName × List (Field Head))) :
    RootComputation Head where
  step := IotaStep rec ctors
  rename := by
    rintro n m ρ l r ⟨p, ms, i, k, fields, args, mt, hms, hi, has, hm, rfl, rfl⟩
    refine ⟨Presentation.rename ρ p, ms.map (Presentation.rename ρ), i, k, fields,
      args.map (Presentation.rename ρ), Presentation.rename ρ mt, by simp [hms], hi,
      by simp [has], by simp [hm], ?_, ?_⟩
    · rw [rename_recApp, rename_appSpine]
      rfl
    · rw [rename_appSpine, List.map_append, List.map_map, ← map_recArgs]
      simp only [List.map_map, Function.comp_def, rename_recApp, List.map_cons]
  substitute := by
    rintro n m σ l r ⟨p, ms, i, k, fields, args, mt, hms, hi, has, hm, rfl, rfl⟩
    refine ⟨Presentation.subst σ p, ms.map (Presentation.subst σ), i, k, fields,
      args.map (Presentation.subst σ), Presentation.subst σ mt, by simp [hms], hi,
      by simp [has], by simp [hm], ?_, ?_⟩
    · rw [subst_recApp, subst_appSpine]
      rfl
    · rw [subst_appSpine, List.map_append, List.map_map, ← map_recArgs]
      simp only [List.map_map, Function.comp_def, subst_recApp, List.map_cons]

/-! ## Shape -/

theorem nodup_getElem?_inj {α : Type} :
    ∀ {l : List α}, l.Nodup → ∀ {i j : Nat} {a : α}, l[i]? = some a → l[j]? = some a → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | b :: l, nodup, i, j, a, hi, hj => by
      rw [List.nodup_cons] at nodup
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j =>
              simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
              subst hi
              exact absurd (List.mem_of_getElem? hj) nodup.1
      | succ i =>
          cases j with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
              subst hj
              exact absurd (List.mem_of_getElem? hi) nodup.1
          | succ j =>
              simp only [List.getElem?_cons_succ] at hi hj
              exact congrArg (· + 1) (nodup_getElem?_inj nodup.2 hi hj)

section Shape

variable {roles : Roles Head} {T rec : DeclName} {ctors : List (DeclName × List (Field Head))}
  (role : roles T = .inductive ctors)
  (recRole : roles rec = .computes (ctors.length + 2) (.split (ctors.length + 1) .constructor fun _ => .leaf))
  (declared : ConstructorsDeclared roles)
include role recRole declared

/-- A computation rule applies to a full application of the recursor whose
scrutinee is a constructor form. -/
theorem IotaStep.spine {n : Nat} {l r : Tm Head n} (step : IotaStep rec ctors l r) :
    ∃ c arity scrutinee args, roles c = .computes arity scrutinee ∧
      l = appSpine (.const c) args ∧ args.length = arity ∧ scrutinee.Accepts roles args := by
  obtain ⟨p, ms, i, k, fields, args, mt, hms, hi, has, hm, rfl, rfl⟩ := step
  refine ⟨rec, ctors.length + 2, _, p :: ms ++ [appSpine (.const k) args],
    recRole, rfl, by simp [hms], InspectTree.accepts_single.mpr ⟨appSpine (.const k) args, ?_,
      .inr ⟨k, _, args, declared.arity role (List.mem_of_getElem? hi), rfl⟩⟩⟩
  rw [List.cons_append, List.getElem?_cons_succ, List.getElem?_append_right (by omega)]
  simp [hms]

omit recRole in
/-- The computation rules are deterministic. -/
theorem IotaStep.deterministic {n : Nat} {l r r' : Tm Head n} (step : IotaStep rec ctors l r)
    (step' : IotaStep rec ctors l r') : r' = r := by
  obtain ⟨p, ms, i, k, fields, args, mt, hms, hi, has, hm, rfl, rfl⟩ := step
  obtain ⟨p', ms', i', k', fields', args', mt', hms', hi', has', hm', e, rfl⟩ := step'
  obtain ⟨_, lists⟩ := appSpine_const_injective e
  simp only [List.cons_append, List.cons.injEq] at lists
  obtain ⟨rfl, lists⟩ := lists
  obtain ⟨rfl, last⟩ := List.append_inj' lists (by simp)
  simp only [List.cons.injEq, and_true] at last
  obtain ⟨rfl, rfl⟩ := appSpine_const_injective last
  have names : (ctors.map Prod.fst)[i]? = some k := by simp [hi]
  have names' : (ctors.map Prod.fst)[i']? = some k := by simp [hi']
  obtain rfl := nodup_getElem?_inj (declared.distinct role) names names'
  rw [hi] at hi'
  obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj hi')
  rw [hm] at hm'
  obtain rfl := Option.some.inj hm'
  rfl

end Shape

/-! ## Preservation -/

section Preservation

variable {S S₀ : Setting Head L} (facts : FormFacts S.R S.roles)
  {T : DeclName} {v : Head} {ctors : List (DeclName × List (Field Head))} {rec : DeclName}
  {R₀ R₁ R₂ : Rules Head} {u : Head} (decl : DeclaresInductive S₀ R₀ R₁ R₂ T u ctors rec v)
  (sub : RulesSub S₀.R S.R)
include facts decl sub

/-- The computation rules of a declared recursor preserve typing, in every
package containing the declaring one. -/
theorem DeclaresInductive.step_preserves {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {l r A : Tm Head n} (step : IotaStep rec ctors l r) (typing : Typed S.R Γ l A) :
    Typed S.R Γ r A := by
  obtain ⟨p, ms, i, k, fields, args, mt, hms, hi, has, hm, rfl, rfl⟩ := step
  exact decl.iota_preserves facts sub formed hms hi has hm typing

end Preservation

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
