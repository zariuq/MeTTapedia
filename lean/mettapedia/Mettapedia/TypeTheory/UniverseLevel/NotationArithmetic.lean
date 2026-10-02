import Mettapedia.TypeTheory.UniverseLevel.Notation
import Mettapedia.TypeTheory.UniverseLevel.NotationCode

/-!
# Arithmetic of the ordinal notations below ε₀

Sum, product and power of notation trees, computed on the trees themselves.
`oadd e n a` is `ω ^ e * (n + 1) + a`. On normal forms these are the ordinal
operations, so a closed level expression denotes a normal notation even when
it is not written in normal form: `1 + ω` is `ω`, `2 · ω` is `ω`, and
`ω + ω ^ 2` is `ω ^ 2`.

The operations are defined on every tree. The laws that mention a normal form
are the ones that fail off normal form, where `1 + ω` is a different tree from
`ω`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

namespace Cnf

/-! ## Comparison -/

/-- `≤` in the lexicographic order is transitive. -/
theorem cmp_le_trans {x y z : Cnf} (hxy : cmp x y ≠ .gt) (hyz : cmp y z ≠ .gt) :
    cmp x z ≠ .gt := by
  intro hxz
  cases hxy' : cmp x y with
  | gt => exact hxy hxy'
  | eq =>
    rw [eq_of_cmp_eq hxy'] at hxz
    exact hyz hxz
  | lt =>
    cases hyz' : cmp y z with
    | gt => exact hyz hyz'
    | eq =>
      rw [← eq_of_cmp_eq hyz'] at hxz
      rw [hxy'] at hxz
      exact nomatch hxz
    | lt =>
      rw [cmp_lt_trans hxy' hyz'] at hxz
      exact nomatch hxz

/-- A strict comparison is not the opposite one. -/
theorem cmp_ne_gt_of_lt {x y : Cnf} (h : cmp x y = .lt) : cmp x y ≠ .gt := by
  rw [h]
  exact nofun

/-- Below `ω ^ e₁` and `e₁` below `e` implies below `ω ^ e`. -/
theorem lt_omegaPow_trans {a e₁ e : Cnf} (ha : cmp a (omegaPow e₁) = .lt)
    (he : cmp e₁ e = .lt) : cmp a (omegaPow e) = .lt := by
  cases a with
  | zero => rfl
  | oadd ea _ _ =>
    exact oadd_lt_omegaPow.mpr (cmp_lt_trans (oadd_lt_omegaPow.mp ha) he)

/-- `ω ^ e` compares as `e` does. -/
theorem cmp_omegaPow (e₁ e₂ : Cnf) : cmp (omegaPow e₁) (omegaPow e₂) = cmp e₁ e₂ := by
  rw [omegaPow, omegaPow, cmp_oadd, cmp_self, Nat.compare_eq_eq.mpr rfl]
  cases h : cmp e₁ e₂ <;> rfl

/-- A natural number lies below `ω ^ e` whenever `e` is positive. -/
theorem ofNat_lt_omegaPow_of_pos {e : Cnf} (m : Nat) (he : cmp .zero e = .lt) :
    cmp (ofNat m) (omegaPow e) = .lt := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [ofNat, oadd_lt_omegaPow]
    exact he

/-- Below a bound, and no greater than something else below that bound, stays below it. -/
theorem cmp_lt_of_le_of_lt {x y e : Cnf} (hxy : cmp x y ≠ .gt)
    (hy : cmp y (omegaPow e) = .lt) : cmp x (omegaPow e) = .lt := by
  cases hx : cmp x (omegaPow e) with
  | lt => rfl
  | eq => exact False.elim (hxy (cmp_eq_gt.mpr (eq_of_cmp_eq hx ▸ hy)))
  | gt => exact False.elim (hxy (cmp_eq_gt.mpr (cmp_lt_trans hy (cmp_eq_gt.mp hx))))

/-! ## Sum -/

/-- Attach a leading term `ω ^ e * (n + 1)` to a tree, merging it into a larger or equal
leading term of the tree. -/
def addAux (e : Cnf) (n : Nat) : Cnf → Cnf
  | .zero => .oadd e n .zero
  | .oadd e' n' a' =>
    match cmp e e' with
    | .lt => .oadd e' n' a'
    | .eq => .oadd e (n + n' + 1) a'
    | .gt => .oadd e n (.oadd e' n' a')

theorem addAux_zero (e : Cnf) (n : Nat) : addAux e n .zero = .oadd e n .zero := rfl

theorem addAux_oadd (e : Cnf) (n : Nat) (e' : Cnf) (n' : Nat) (a' : Cnf) :
    addAux e n (.oadd e' n' a') =
      match cmp e e' with
      | .lt => .oadd e' n' a'
      | .eq => .oadd e (n + n' + 1) a'
      | .gt => .oadd e n (.oadd e' n' a') := rfl

theorem addAux_lt {e : Cnf} {n : Nat} {e' : Cnf} {n' : Nat} {a' : Cnf}
    (h : cmp e e' = .lt) : addAux e n (.oadd e' n' a') = .oadd e' n' a' := by
  rw [addAux_oadd, h]

theorem addAux_eq_exp (e : Cnf) (n n' : Nat) (a' : Cnf) :
    addAux e n (.oadd e n' a') = .oadd e (n + n' + 1) a' := by
  rw [addAux_oadd, cmp_self]

theorem addAux_gt {e : Cnf} {n : Nat} {e' : Cnf} {n' : Nat} {a' : Cnf}
    (h : cmp e e' = .gt) : addAux e n (.oadd e' n' a') = .oadd e n (.oadd e' n' a') := by
  rw [addAux_oadd, h]

/-- A sum is not strictly below the power of its own leading exponent. -/
theorem oadd_exp_not_lt (e : Cnf) (n : Nat) (a : Cnf) :
    cmp (.oadd e n a) (omegaPow e) ≠ .lt := by
  intro h
  rw [oadd_lt_omegaPow, cmp_self] at h
  exact nomatch h

/-- Ordinal sum of notation trees. -/
def add : Cnf → Cnf → Cnf
  | .zero, y => y
  | .oadd e n a, y => addAux e n (add a y)

theorem zero_add (y : Cnf) : add .zero y = y := rfl

theorem oadd_add (e : Cnf) (n : Nat) (a y : Cnf) :
    add (.oadd e n a) y = addAux e n (add a y) := rfl

/-- A tree already below `ω ^ e` is unchanged by writing the leading coefficient in front. -/
theorem addAux_below {e : Cnf} {n : Nat} {a : Cnf} (h : cmp a (omegaPow e) = .lt) :
    addAux e n a = .oadd e n a := by
  cases a with
  | zero => rfl
  | oadd e' n' a' =>
    have hgt : cmp e e' = .gt := cmp_eq_gt.mpr (oadd_lt_omegaPow.mp h)
    rw [addAux_gt hgt]

/-- The sum of two normal forms is a normal form. -/
theorem nf_addAux {e : Cnf} {n : Nat} {o : Cnf} (he : NF e) (ho : NF o) : NF (addAux e n o) := by
  cases o with
  | zero => exact .oadd n he .zero rfl
  | oadd e' n' a' =>
    cases h : cmp e e' with
    | lt =>
      rw [addAux_lt h]
      exact ho
    | eq =>
      obtain rfl := eq_of_cmp_eq h
      rw [addAux_eq_exp]
      exact .oadd (n + n' + 1) he ho.snd ho.lt
    | gt =>
      rw [addAux_gt h]
      exact .oadd n he ho (oadd_lt_omegaPow.mpr (cmp_eq_gt.mp h))

theorem nf_add : ∀ {x y : Cnf}, NF x → NF y → NF (add x y)
  | .zero, _, _, hy => hy
  | .oadd _ _ _, _, hx, hy => nf_addAux hx.fst (nf_add hx.snd hy)

/-- Adding zero on the right drops out of a normal form. -/
theorem add_zero : ∀ {x : Cnf}, NF x → add x .zero = x
  | .zero, _ => rfl
  | .oadd _ _ _, h => by rw [oadd_add, add_zero h.snd, addAux_below h.lt]

/-- Two trees below `ω ^ e` have their sum below `ω ^ e`. -/
theorem add_below : ∀ {x y e : Cnf}, NF x → NF y → cmp x (omegaPow e) = .lt →
    cmp y (omegaPow e) = .lt → cmp (add x y) (omegaPow e) = .lt
  | .zero, _, _, _, _, _, hy => hy
  | .oadd ex _ ax, y, e, hx, hy, hxlt, hylt => by
    have hex : cmp ex e = .lt := oadd_lt_omegaPow.mp hxlt
    have hax : cmp ax (omegaPow e) = .lt := lt_omegaPow_trans hx.lt hex
    have ih := add_below hx.snd hy hax hylt
    rw [oadd_add]
    cases hsum : add ax y with
    | zero =>
      rw [addAux_zero]
      exact oadd_lt_omegaPow.mpr hex
    | oadd es _ _ =>
      have hes : cmp es e = .lt := oadd_lt_omegaPow.mp (hsum ▸ ih)
      cases hc : cmp ex es with
      | lt =>
        rw [addAux_lt hc]
        exact oadd_lt_omegaPow.mpr hes
      | eq =>
        obtain rfl := eq_of_cmp_eq hc
        rw [addAux_eq_exp]
        exact oadd_lt_omegaPow.mpr hex
      | gt =>
        rw [addAux_gt hc]
        exact oadd_lt_omegaPow.mpr hex

/-- A tree below `ω ^ e` is absorbed by anything at least `ω ^ e`. -/
theorem add_absorb : ∀ {x e y : Cnf}, NF x → cmp x (omegaPow e) = .lt →
    cmp y (omegaPow e) ≠ .lt → add x y = y
  | .zero, _, _, _, _, _ => rfl
  | .oadd ex _ ax, e, y, hx, hxlt, hy => by
    have hex : cmp ex e = .lt := oadd_lt_omegaPow.mp hxlt
    have hax : cmp ax (omegaPow e) = .lt := lt_omegaPow_trans hx.lt hex
    have ih := add_absorb hx.snd hax hy
    rw [oadd_add, ih]
    cases y with
    | zero => exact absurd rfl hy
    | oadd ey _ _ =>
      have hey : cmp ey e ≠ .lt := by
        intro hlt
        exact hy (oadd_lt_omegaPow.mpr hlt)
      cases hc : cmp ex ey with
      | lt => rw [addAux_lt hc]
      | eq =>
        obtain rfl := eq_of_cmp_eq hc
        exact absurd hex hey
      | gt =>
        exact absurd (cmp_lt_trans (cmp_eq_gt.mp hc) hex) hey

/-- The leading term dominates a strictly smaller exponent. -/
theorem add_oadd_gt {e : Cnf} {n : Nat} {a y : Cnf} (hx : NF (.oadd e n a))
    (hy : NF y) (hlt : cmp y (omegaPow e) = .lt) :
    add (.oadd e n a) y = .oadd e n (add a y) := by
  have hsum : cmp (add a y) (omegaPow e) = .lt := add_below hx.snd hy hx.lt hlt
  rw [oadd_add, addAux_below hsum]

/-- Equal leading exponents add their coefficients and keep the right-hand tail. -/
theorem add_oadd_eq {e : Cnf} {n n' : Nat} {a b : Cnf} (hx : NF (.oadd e n a)) :
    add (.oadd e n a) (.oadd e n' b) = .oadd e (n + n' + 1) b := by
  rw [oadd_add, add_absorb hx.snd hx.lt (oadd_exp_not_lt e n' b), addAux_eq_exp]

/-- A strictly smaller leading exponent is absorbed. -/
theorem add_oadd_lt {e e' : Cnf} {n n' : Nat} {a b : Cnf} (hx : NF (.oadd e n a))
    (hlt : cmp e e' = .lt) : add (.oadd e n a) (.oadd e' n' b) = .oadd e' n' b :=
  add_absorb hx (oadd_lt_omegaPow.mpr hlt) (oadd_exp_not_lt e' n' b)

/-- `ω ^ e * (n + 1) + a`, added to anything, stays at least `ω ^ e`. -/
theorem omegaPow_le_add_oadd (e : Cnf) (n : Nat) (a z : Cnf) :
    cmp (add (.oadd e n a) z) (omegaPow e) ≠ .lt := by
  rw [oadd_add]
  cases add a z with
  | zero =>
    rw [addAux_zero]
    exact oadd_exp_not_lt e n .zero
  | oadd ew nw aw =>
    cases h : cmp e ew with
    | lt =>
      rw [addAux_lt h]
      intro hlt
      exact nomatch (h.symm.trans (cmp_eq_gt.mpr (oadd_lt_omegaPow.mp hlt)))
    | eq =>
      obtain rfl := eq_of_cmp_eq h
      rw [addAux_eq_exp]
      exact oadd_exp_not_lt _ _ _
    | gt =>
      rw [addAux_gt h]
      exact oadd_exp_not_lt _ _ _

/-- A leading exponent below the exponent of a tree at least `ω ^ ey` is absorbed. -/
theorem addAux_absorb {e ey : Cnf} {n : Nat} {w : Cnf} (hlt : cmp e ey = .lt)
    (hge : cmp w (omegaPow ey) ≠ .lt) : addAux e n w = w := by
  cases w with
  | zero => exact absurd rfl hge
  | oadd ew _ _ =>
    have hlt' : cmp e ew = .lt := by
      cases hew : cmp ey ew with
      | lt => exact cmp_lt_trans hlt hew
      | eq =>
        rw [← eq_of_cmp_eq hew]
        exact hlt
      | gt => exact absurd (oadd_lt_omegaPow.mpr (cmp_eq_gt.mp hew)) hge
    rw [addAux_lt hlt']

/-- The coefficient of two merged equal exponents. -/
theorem coef_merge (n k nw : Nat) : n + (k + nw + 1) + 1 = n + k + 1 + nw + 1 := by
  calc
    n + (k + nw + 1) + 1
      = n + (k + 1 + nw) + 1 := by rw [Nat.add_right_comm k nw 1]
    _ = n + (k + 1) + nw + 1 := by rw [← Nat.add_assoc n (k + 1) nw]
    _ = n + k + 1 + nw + 1 := by rw [← Nat.add_assoc n k 1]

/-- Attaching the same leading exponent twice merges the coefficients. -/
theorem addAux_addAux (e : Cnf) (n k : Nat) (w : Cnf) :
    addAux e n (addAux e k w) = addAux e (n + k + 1) w := by
  cases w with
  | zero => rw [addAux_zero, addAux_eq_exp, addAux_zero]
  | oadd ew nw aw =>
    cases h : cmp e ew with
    | lt => rw [addAux_lt h, addAux_lt h, addAux_lt h]
    | eq =>
      obtain rfl := eq_of_cmp_eq h
      rw [addAux_eq_exp, addAux_eq_exp, addAux_eq_exp, coef_merge]
    | gt => rw [addAux_gt h, addAux_eq_exp, addAux_gt h]

/-- Attaching a leading term stays at least at that power. -/
theorem addAux_not_lt (e : Cnf) (n : Nat) (w : Cnf) :
    cmp (addAux e n w) (omegaPow e) ≠ .lt := by
  cases w with
  | zero =>
    rw [addAux_zero]
    exact oadd_exp_not_lt e n .zero
  | oadd ew nw aw =>
    cases h : cmp e ew with
    | lt =>
      rw [addAux_lt h]
      intro hlt
      exact nomatch (h.symm.trans (cmp_eq_gt.mpr (oadd_lt_omegaPow.mp hlt)))
    | eq =>
      obtain rfl := eq_of_cmp_eq h
      rw [addAux_eq_exp]
      exact oadd_exp_not_lt _ _ _
    | gt =>
      rw [addAux_gt h]
      exact oadd_exp_not_lt _ _ _

/-- Sum is associative on normal forms. -/
theorem add_assoc : ∀ {x y z : Cnf}, NF x → NF y → NF z →
    add (add x y) z = add x (add y z)
  | .zero, _, _, _, _, _ => rfl
  | .oadd e n a, y, z, hx, hy, hz => by
    cases y with
    | zero => rw [add_zero hx, zero_add]
    | oadd ey ny ay =>
      cases hc : cmp e ey with
      | lt =>
        rw [add_oadd_lt hx hc,
          add_absorb hx (oadd_lt_omegaPow.mpr hc) (omegaPow_le_add_oadd ey ny ay z)]
      | eq =>
        have hey : ey = e := (eq_of_cmp_eq hc).symm
        cases hey
        rw [add_oadd_eq hx, oadd_add, oadd_add, oadd_add]
        have habsorb :
            add a (addAux e ny (add ay z)) = addAux e ny (add ay z) :=
          add_absorb hx.snd hx.lt (addAux_not_lt e ny (add ay z))
        rw [habsorb, addAux_addAux]
      | gt =>
        have hylt : cmp (.oadd ey ny ay) (omegaPow e) = .lt :=
          oadd_lt_omegaPow.mpr (cmp_eq_gt.mp hc)
        rw [add_oadd_gt hx hy hylt, oadd_add, oadd_add, add_assoc hx.snd hy hz]

/-- Attaching a leading term does not go below the tree it was attached to. -/
theorem addAux_ge (e : Cnf) (n : Nat) (w : Cnf) : cmp w (addAux e n w) ≠ .gt := by
  cases w with
  | zero =>
    rw [addAux_zero]
    exact cmp_zero_left _
  | oadd ew nw _ =>
    cases hc : cmp e ew with
    | lt =>
      rw [addAux_lt hc, cmp_self]
      exact nofun
    | eq =>
      obtain rfl := eq_of_cmp_eq hc
      have hlt : nw < n + nw + 1 := Nat.lt_succ_of_le (Nat.le_add_left nw n)
      rw [addAux_eq_exp, cmp_oadd, cmp_self, Nat.compare_eq_lt.mpr hlt]
      exact nofun
    | gt =>
      rw [addAux_gt hc, cmp_oadd, cmp_eq_gt.mp hc]
      exact nofun

/-- The right summand is at most the sum. -/
theorem le_add_right : ∀ {x y : Cnf}, NF x → cmp y (add x y) ≠ .gt
  | .zero, _, _ => by rw [zero_add, cmp_self]; exact nofun
  | .oadd e n a, y, hx => by
    rw [oadd_add]
    exact cmp_le_trans (le_add_right (y := y) hx.snd) (addAux_ge e n (add a y))

/-- The left summand is at most the sum, on a normal left summand. -/
theorem le_add_left : ∀ {x y : Cnf}, NF x → cmp x (add x y) ≠ .gt
  | .zero, _, _ => cmp_zero_left _
  | .oadd e n a, y, hx => by
    have ih := le_add_left (y := y) hx.snd
    rw [oadd_add]
    cases hw : add a y with
    | zero =>
      have ha : a = .zero := by
        have hle : cmp a .zero ≠ .gt := by rw [hw] at ih; exact ih
        cases ha : cmp a .zero with
        | lt => exact absurd ha (cmp_zero_right a)
        | eq => exact eq_of_cmp_eq ha
        | gt => exact absurd ha hle
      rw [addAux_zero, ha, cmp_self]
      exact nofun
    | oadd ew nw _ =>
      cases hc : cmp e ew with
      | lt =>
        rw [addAux_lt hc, cmp_oadd, hc]
        exact nofun
      | eq =>
        obtain rfl := eq_of_cmp_eq hc
        have hlt : n < n + nw + 1 := Nat.lt_succ_of_le (Nat.le_add_right n nw)
        rw [addAux_eq_exp, cmp_oadd, cmp_self, Nat.compare_eq_lt.mpr hlt]
        exact nofun
      | gt =>
        rw [addAux_gt hc, cmp_oadd, cmp_self, Nat.compare_eq_eq.mpr rfl]
        rw [hw] at ih
        exact ih

/-- Attaching one leading term is strictly monotone in the tree it is attached to. -/
theorem addAux_strict (e : Cnf) (n : Nat) {w₁ w₂ : Cnf} (h : cmp w₁ w₂ = .lt) :
    cmp (addAux e n w₁) (addAux e n w₂) = .lt := by
  cases w₁ with
  | zero =>
    cases w₂ with
    | zero => nomatch h
    | oadd e₂ n₂ a₂ =>
      cases hc : cmp e e₂ with
      | lt =>
        rw [addAux_zero, addAux_lt hc, cmp_oadd, hc]
        rfl
      | eq =>
        obtain rfl := eq_of_cmp_eq hc
        have hlt : n < n + n₂ + 1 := Nat.lt_succ_of_le (Nat.le_add_right n n₂)
        rw [addAux_zero, addAux_eq_exp, cmp_oadd, cmp_self, Nat.compare_eq_lt.mpr hlt]
        rfl
      | gt =>
        rw [addAux_zero, addAux_gt hc, cmp_oadd, cmp_self, Nat.compare_eq_eq.mpr rfl]
        exact h
  | oadd e₁ n₁ a₁ =>
    cases w₂ with
    | zero => exact absurd h (cmp_zero_right _)
    | oadd e₂ n₂ a₂ =>
      cases h₁ : cmp e e₁ with
      | lt =>
        cases h₂ : cmp e e₂ with
        | lt =>
          rw [addAux_lt h₁, addAux_lt h₂]
          exact h
        | eq =>
          obtain rfl := eq_of_cmp_eq h₂
          have hgt : cmp e₁ e = .gt := cmp_eq_gt.mpr h₁
          have hcmp : cmp (.oadd e₁ n₁ a₁) (.oadd e n₂ a₂) = .gt := by
            rw [cmp_oadd, hgt]
            rfl
          exact absurd hcmp (cmp_ne_gt_of_lt h)
        | gt =>
          have h21 : cmp e₂ e₁ = .lt := cmp_lt_trans (cmp_eq_gt.mp h₂) h₁
          have hcmp : cmp (.oadd e₁ n₁ a₁) (.oadd e₂ n₂ a₂) = .gt := by
            rw [cmp_oadd, cmp_eq_gt.mpr h21]
            rfl
          exact absurd hcmp (cmp_ne_gt_of_lt h)
      | eq =>
        have he₁ : e₁ = e := (eq_of_cmp_eq h₁).symm
        cases he₁
        cases h₂ : cmp e e₂ with
        | lt =>
          rw [addAux_eq_exp, addAux_lt h₂, cmp_oadd, h₂]
          rfl
        | gt =>
          have hcmp : cmp (.oadd e₂ n₂ a₂) (.oadd e n₁ a₁) = .lt := by
            rw [cmp_oadd, cmp_eq_gt.mp h₂]
            rfl
          exact absurd (cmp_eq_gt.mpr hcmp) (cmp_ne_gt_of_lt h)
        | eq =>
          obtain rfl := eq_of_cmp_eq h₂
          rw [cmp_oadd, cmp_self] at h
          have hcmp : (compare n₁ n₂).then (cmp a₁ a₂) = .lt := h
          rw [addAux_eq_exp, addAux_eq_exp, cmp_oadd, cmp_self]
          rcases Ordering.then_eq_lt.mp hcmp with hn | ⟨hn, ha⟩
          · have hlt : n + n₁ + 1 < n + n₂ + 1 :=
              Nat.add_lt_add_right (Nat.add_lt_add_left (Nat.compare_eq_lt.mp hn) n) 1
            rw [Nat.compare_eq_lt.mpr hlt]
            rfl
          · obtain rfl := Nat.compare_eq_eq.mp hn
            rw [Nat.compare_eq_eq.mpr rfl, ha]
            rfl
      | gt =>
        cases h₂ : cmp e e₂ with
        | lt =>
          rw [addAux_gt h₁, addAux_lt h₂, cmp_oadd, h₂]
          rfl
        | eq =>
          obtain rfl := eq_of_cmp_eq h₂
          have hlt : n < n + n₂ + 1 := Nat.lt_succ_of_le (Nat.le_add_right n n₂)
          rw [addAux_gt h₁, addAux_eq_exp, cmp_oadd, cmp_self, Nat.compare_eq_lt.mpr hlt]
          rfl
        | gt =>
          rw [addAux_gt h₁, addAux_gt h₂, cmp_oadd, cmp_self, Nat.compare_eq_eq.mpr rfl]
          exact h

/-- Sum is strictly monotone in its right argument. -/
theorem add_strict_right : ∀ x y z : Cnf, cmp y z = .lt → cmp (add x y) (add x z) = .lt
  | .zero, _, _, h => h
  | .oadd e n a, y, z, h => by
    rw [oadd_add, oadd_add]
    exact addAux_strict e n (add_strict_right a y z h)

/-- Sum is monotone in its right argument. -/
theorem add_mono_right {x y z : Cnf} (h : cmp y z ≠ .gt) : cmp (add x y) (add x z) ≠ .gt := by
  cases hyz : cmp y z with
  | eq =>
    rw [eq_of_cmp_eq hyz, cmp_self]
    exact nofun
  | lt => exact cmp_ne_gt_of_lt (add_strict_right x y z hyz)
  | gt => exact absurd hyz h

/-- On normal forms, `x ≤ y` is a right difference. -/
theorem exists_add_of_le : ∀ {y x : Cnf}, NF y → NF x → cmp x y ≠ .gt →
    ∃ c, NF c ∧ add x c = y
  | .zero, x, _, _, h => by
    have hx0 : x = .zero := by
      cases hc : cmp x .zero with
      | lt => exact absurd hc (cmp_zero_right x)
      | eq => exact eq_of_cmp_eq hc
      | gt => exact absurd hc h
    refine ⟨.zero, .zero, ?_⟩
    rw [hx0, zero_add]
  | .oadd ey ny ay, x, hy, hx, h => by
    cases x with
    | zero => exact ⟨.oadd ey ny ay, hy, zero_add _⟩
    | oadd ex nx ax =>
      cases hc : cmp ex ey with
      | lt =>
        exact ⟨.oadd ey ny ay, hy,
          add_absorb hx (oadd_lt_omegaPow.mpr hc) (oadd_exp_not_lt ey ny ay)⟩
      | gt =>
        have hcmp : cmp (.oadd ex nx ax) (.oadd ey ny ay) = .gt := by
          rw [cmp_oadd, hc]
          rfl
        exact absurd hcmp h
      | eq =>
        have hex : ex = ey := eq_of_cmp_eq hc
        cases hex
        cases hn : compare nx ny with
        | gt =>
          have hcmp : cmp (.oadd ey nx ax) (.oadd ey ny ay) = .gt := by
            rw [cmp_oadd, cmp_self, hn]
            rfl
          exact absurd hcmp h
        | lt =>
          have hnx : nx < ny := Nat.compare_eq_lt.mp hn
          have hle : nx + 1 ≤ ny := Nat.succ_le_of_lt hnx
          let k : Nat := ny - (nx + 1)
          have hk : nx + k + 1 = ny := by
            have hsum : nx + 1 + k = ny := Nat.add_sub_of_le hle
            rw [Nat.add_assoc, Nat.add_comm k 1, ← Nat.add_assoc, hsum]
          refine ⟨.oadd ey k ay, .oadd k hy.fst hy.snd hy.lt, ?_⟩
          rw [add_oadd_eq hx, hk]
        | eq =>
          obtain rfl := Nat.compare_eq_eq.mp hn
          have htail : cmp ax ay ≠ .gt := by
            intro hgt
            have hcmp : cmp (.oadd ey nx ax) (.oadd ey nx ay) = .gt := by
              rw [cmp_oadd, cmp_self, Nat.compare_eq_eq.mpr rfl, hgt]
              rfl
            exact h hcmp
          rcases exists_add_of_le hy.snd hx.snd htail with ⟨c, hcnf, heq⟩
          have hle : cmp c (add ax c) ≠ .gt := le_add_right hx.snd
          have hclt : cmp c (omegaPow ey) = .lt := by
            rw [heq] at hle
            exact cmp_lt_of_le_of_lt hle hy.lt
          refine ⟨c, hcnf, ?_⟩
          rw [add_oadd_gt hx hcnf hclt, heq]

/-- Sum is monotone in its left argument, on normal forms. -/
theorem add_mono_left {x y z : Cnf} (hx : NF x) (hy : NF y) (hz : NF z)
    (h : cmp x y ≠ .gt) : cmp (add x z) (add y z) ≠ .gt := by
  rcases exists_add_of_le hy hx h with ⟨c, hc, hxc⟩
  have hle : cmp z (add c z) ≠ .gt := le_add_right hc
  have hmono : cmp (add x z) (add x (add c z)) ≠ .gt := add_mono_right hle
  rw [← add_assoc hx hc hz, hxc] at hmono
  exact hmono

/-- The successor is addition of one, on normal forms. -/
theorem succ_eq_add_one : ∀ {x : Cnf}, NF x → succ x = add x (ofNat 1)
  | .zero, _ => rfl
  | .oadd .zero _ _, h => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero h.lt
    rfl
  | .oadd (.oadd _ _ _) _ _, h => by
    have hlt := succ_lt_omegaPow h.lt
    rw [succ_eq_add_one h.snd] at hlt
    rw [succ, oadd_add, succ_eq_add_one h.snd, ← addAux_below hlt]

/-- Numerals add as natural numbers. -/
theorem ofNat_add (m n : Nat) : add (ofNat m) (ofNat n) = ofNat (m + n) := by
  cases m with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ m =>
    cases n with
    | zero =>
      rw [Nat.add_zero]
      exact add_zero (nf_ofNat (m + 1))
    | succ n =>
      rw [ofNat, ofNat, oadd_add, zero_add, addAux_eq_exp]
      have hr : (m + 1) + (n + 1) = (m + n + 1) + 1 := by
        rw [Nat.add_succ, Nat.succ_add]
      rw [hr]
      rfl

/-! ## Product -/

/-- `(m + 1) * (n + 1) = m * n + m + n + 1`. -/
theorem succ_mul_succ (m n : Nat) : (m + 1) * (n + 1) = m * n + m + n + 1 := by
  calc
    (m + 1) * (n + 1) = (m + 1) * n + (m + 1) := by rw [Nat.mul_succ]
    _ = m * n + n + (m + 1) := by rw [Nat.succ_mul]
    _ = m * n + (n + (m + 1)) := by rw [Nat.add_assoc]
    _ = m * n + (m + (n + 1)) := by rw [Nat.add_left_comm n m 1]
    _ = m * n + m + (n + 1) := by rw [← Nat.add_assoc]
    _ = m * n + m + n + 1 := by rw [← Nat.add_assoc (m * n + m) n 1]

/-- The finite coefficient `n * k + n + k` is associative. -/
theorem coef_mul_assoc (a b c : Nat) :
    (a * b + a + b) * c + (a * b + a + b) + c =
      a * (b * c + b + c) + a + (b * c + b + c) := by
  apply Nat.add_one_inj.mp
  show (a * b + a + b) * c + (a * b + a + b) + c + 1 =
    a * (b * c + b + c) + a + (b * c + b + c) + 1
  rw [← succ_mul_succ (a * b + a + b) c, ← succ_mul_succ a (b * c + b + c),
    ← succ_mul_succ a b, ← succ_mul_succ b c, Nat.mul_assoc]

/-- A finite coefficient distributes over a merged coefficient. -/
theorem coef_mul_add (n a b : Nat) :
    n * (a + b + 1) + n + (a + b + 1) = n * a + n + a + (n * b + n + b) + 1 := by
  apply Nat.add_one_inj.mp
  show n * (a + b + 1) + n + (a + b + 1) + 1 =
    n * a + n + a + (n * b + n + b) + 1 + 1
  rw [← succ_mul_succ n (a + b + 1)]
  have regroup : n * a + n + a + (n * b + n + b) + 1 + 1 =
      (n * a + n + a + 1) + (n * b + n + b + 1) := by
    calc
      n * a + n + a + (n * b + n + b) + 1 + 1
        = n * a + n + a + (n * b + n + b + 1) + 1 := by
          rw [← Nat.add_assoc (n * a + n + a) (n * b + n + b) 1]
      _ = n * a + n + a + (1 + (n * b + n + b)) + 1 := by
          rw [Nat.add_comm (n * b + n + b) 1]
      _ = n * a + n + a + 1 + (n * b + n + b) + 1 := by
          rw [Nat.add_assoc (n * a + n + a) 1 (n * b + n + b)]
      _ = (n * a + n + a + 1) + (n * b + n + b + 1) := by
          rw [← Nat.add_assoc (n * a + n + a + 1) (n * b + n + b) 1]
  have hexp : (a + b + 1) + 1 = (a + 1) + (b + 1) := by
    calc
      (a + b + 1) + 1 = a + (b + 1) + 1 := by rw [← Nat.add_assoc a b 1]
      _ = a + (1 + b) + 1 := by rw [Nat.add_comm b 1]
      _ = a + 1 + b + 1 := by rw [Nat.add_assoc a 1 b]
      _ = (a + 1) + (b + 1) := by rw [← Nat.add_assoc (a + 1) b 1]
  rw [regroup, ← succ_mul_succ n a, ← succ_mul_succ n b, hexp, Nat.mul_add]

/-- A positive right summand makes the sum strictly larger. -/
theorem lt_add_of_pos {e y : Cnf} (he : NF e) (hy : cmp .zero y = .lt) :
    cmp e (add e y) = .lt := by
  have h := add_strict_right e .zero y hy
  rw [add_zero he] at h
  exact h

/-- Ordinal product of notation trees. The right-hand exponent `0` multiplies the
finite coefficient; a positive right-hand exponent shifts the left exponent. -/
def mul : Cnf → Cnf → Cnf
  | .zero, _ => .zero
  | .oadd _ _ _, .zero => .zero
  | .oadd e₁ n₁ a₁, .oadd .zero n₂ _ => .oadd e₁ (n₁ * n₂ + n₁ + n₂) a₁
  | .oadd e₁ n₁ a₁, .oadd (.oadd e₂ n₂e a₂e) n₂ a₂ =>
    .oadd (add e₁ (.oadd e₂ n₂e a₂e)) n₂ (mul (.oadd e₁ n₁ a₁) a₂)

theorem zero_mul : ∀ y : Cnf, mul .zero y = .zero
  | .zero => rfl
  | .oadd _ _ _ => rfl

theorem mul_zero : ∀ x : Cnf, mul x .zero = .zero
  | .zero => rfl
  | .oadd _ _ _ => rfl

theorem mul_oadd_zero (e₁ : Cnf) (n₁ : Nat) (a₁ : Cnf) (n₂ : Nat) (a₂ : Cnf) :
    mul (.oadd e₁ n₁ a₁) (.oadd .zero n₂ a₂) = .oadd e₁ (n₁ * n₂ + n₁ + n₂) a₁ := rfl

theorem mul_oadd_oadd (e₁ : Cnf) (n₁ : Nat) (a₁ e₂ : Cnf) (n₂e : Nat) (a₂e : Cnf)
    (n₂ : Nat) (a₂ : Cnf) :
    mul (.oadd e₁ n₁ a₁) (.oadd (.oadd e₂ n₂e a₂e) n₂ a₂) =
      .oadd (add e₁ (.oadd e₂ n₂e a₂e)) n₂ (mul (.oadd e₁ n₁ a₁) a₂) := rfl

theorem mul_one : ∀ x : Cnf, mul x (ofNat 1) = x
  | .zero => rfl
  | .oadd _ n _ => by rw [ofNat, mul_oadd_zero, Nat.mul_zero, Nat.zero_add, Nat.add_zero]

theorem one_mul : ∀ {x : Cnf}, NF x → mul (ofNat 1) x = x
  | .zero, _ => rfl
  | .oadd .zero _ a, h => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero h.lt
    rw [ofNat, mul_oadd_zero, Nat.zero_mul, Nat.zero_add]
  | .oadd (.oadd _ _ _) _ _, h => by
    rw [ofNat, mul_oadd_oadd, zero_add]
    have htail := one_mul h.snd
    rw [ofNat] at htail
    rw [htail]

theorem ofNat_mul (m n : Nat) : mul (ofNat m) (ofNat n) = ofNat (m * n) := by
  cases m with
  | zero => rw [Nat.zero_mul, ofNat, zero_mul]
  | succ m =>
    cases n with
    | zero => rw [Nat.mul_zero, ofNat, mul_zero]
    | succ n =>
      rw [ofNat, ofNat, mul_oadd_zero, succ_mul_succ]
      rfl

/-- `ω ^ e₁ * y` stays below `ω ^ (e₁ + e)` when `y` is below `ω ^ e`. -/
theorem oadd_mul_below {e₁ : Cnf} {n₁ : Nat} {a₁ y e : Cnf} (hx : NF (.oadd e₁ n₁ a₁))
    (hy : cmp y (omegaPow e) = .lt) :
    cmp (mul (.oadd e₁ n₁ a₁) y) (omegaPow (add e₁ e)) = .lt := by
  cases y with
  | zero => rfl
  | oadd ey _ _ =>
    cases ey with
    | zero =>
      rw [mul_oadd_zero, oadd_lt_omegaPow]
      exact lt_add_of_pos hx.fst (oadd_lt_omegaPow.mp hy)
    | oadd ey₁ nye aye =>
      rw [mul_oadd_oadd, oadd_lt_omegaPow]
      exact add_strict_right e₁ (.oadd ey₁ nye aye) e (oadd_lt_omegaPow.mp hy)

theorem nf_mul : ∀ {x y : Cnf}, NF x → NF y → NF (mul x y)
  | .zero, _, _, _ => by rw [zero_mul]; exact .zero
  | .oadd _ _ _, .zero, _, _ => .zero
  | .oadd _ n₁ _, .oadd .zero n₂ _, hx, _ => by
    rw [mul_oadd_zero]
    exact .oadd (n₁ * n₂ + n₁ + n₂) hx.fst hx.snd hx.lt
  | .oadd _ _ _, .oadd (.oadd _ _ _) n₂ _, hx, hy => by
    rw [mul_oadd_oadd]
    exact .oadd n₂ (nf_add hx.fst hy.fst) (nf_mul hx hy.snd) (oadd_mul_below hx hy.lt)

/-- A leading term keeps a sum strictly above zero. -/
theorem zero_lt_add_oadd (e : Cnf) (n : Nat) (a y : Cnf) :
    cmp .zero (add (.oadd e n a) y) = .lt := by
  rw [oadd_add]
  cases add a y with
  | zero =>
    rw [addAux_zero]
    rfl
  | oadd e' n' a' =>
    cases h : cmp e e' with
    | lt =>
      rw [addAux_lt h]
      rfl
    | eq =>
      obtain rfl := eq_of_cmp_eq h
      rw [addAux_eq_exp]
      rfl
    | gt =>
      rw [addAux_gt h]
      rfl

/-- Multiplication by a positive exponent shifts the left exponent. -/
theorem mul_oadd_pos {e₁ : Cnf} {n₁ : Nat} {a₁ e : Cnf} {n : Nat} {a : Cnf}
    (he : cmp .zero e = .lt) :
    mul (.oadd e₁ n₁ a₁) (.oadd e n a) =
      .oadd (add e₁ e) n (mul (.oadd e₁ n₁ a₁) a) := by
  cases e with
  | zero =>
    rw [cmp_self] at he
    exact nomatch he
  | oadd _ _ _ => rw [mul_oadd_oadd]

theorem mul_assoc : ∀ {x y z : Cnf}, NF x → NF y → NF z →
    mul (mul x y) z = mul x (mul y z)
  | _, _, .zero, _, _, _ => by rw [mul_zero, mul_zero, mul_zero]
  | .zero, _, _, _, _, _ => by rw [zero_mul, zero_mul, zero_mul]
  | _, .zero, _, _, _, _ => by rw [mul_zero, zero_mul, mul_zero]
  | .oadd _ _ _, .oadd .zero _ _, .oadd .zero _ _, _, _, _ => by
    rw [mul_oadd_zero, mul_oadd_zero, mul_oadd_zero, mul_oadd_zero, coef_mul_assoc]
  | .oadd _ _ _, .oadd (.oadd _ _ _) _ _, .oadd .zero _ _, _, _, _ => by
    rw [mul_oadd_oadd, mul_oadd_zero, mul_oadd_zero, mul_oadd_oadd]
  | .oadd ex nx ax, .oadd .zero ny ay, .oadd (.oadd ez ne ae) nz az, hx, hy, hz => by
    have ih := mul_assoc (z := az) hx hy hz.snd
    have htail :
        mul (.oadd ex (nx * ny + nx + ny) ax) az =
          mul (.oadd ex nx ax) (mul (.oadd .zero ny ay) az) := by
      rw [← mul_oadd_zero ex nx ax ny ay]
      exact ih
    rw [mul_oadd_zero ex nx ax ny ay,
      mul_oadd_oadd ex (nx * ny + nx + ny) ax ez ne ae nz az,
      mul_oadd_oadd .zero ny ay ez ne ae nz az,
      zero_add,
      mul_oadd_oadd ex nx ax ez ne ae nz (mul (.oadd .zero ny ay) az),
      htail]
  | .oadd ex nx ax, .oadd (.oadd ey₁ nye aye) ny ay, .oadd (.oadd ez ne ae) nz az,
      hx, hy, hz => by
    have ih := mul_assoc (z := az) hx hy hz.snd
    have htail :
        mul (.oadd (add ex (.oadd ey₁ nye aye)) ny (mul (.oadd ex nx ax) ay)) az =
          mul (.oadd ex nx ax) (mul (.oadd (.oadd ey₁ nye aye) ny ay) az) := by
      rw [← mul_oadd_oadd ex nx ax ey₁ nye aye ny ay]
      exact ih
    rw [mul_oadd_oadd ex nx ax ey₁ nye aye ny ay,
      mul_oadd_oadd (add ex (.oadd ey₁ nye aye)) ny (mul (.oadd ex nx ax) ay)
        ez ne ae nz az,
      mul_oadd_oadd (.oadd ey₁ nye aye) ny ay ez ne ae nz az,
      mul_oadd_pos (zero_lt_add_oadd ey₁ nye aye (.oadd ez ne ae)),
      add_assoc hx.fst hy.fst hz.fst,
      htail]

/-- Product distributes over a sum on the right, on normal forms. -/
theorem mul_add : ∀ {x y z : Cnf}, NF x → NF y → NF z →
    mul x (add y z) = add (mul x y) (mul x z)
  | .zero, _, _, _, _, _ => by rw [zero_mul, zero_mul, zero_mul, zero_add]
  | _, .zero, _, _, _, _ => by rw [zero_add, mul_zero, zero_add]
  | x, y, .zero, hx, hy, _ => by rw [add_zero hy, mul_zero, add_zero (nf_mul hx hy)]
  | .oadd ex nx ax, .oadd ey ny ay, .oadd ez nz az, hx, hy, hz => by
    cases hc : cmp ey ez with
    | lt =>
      rw [add_oadd_lt hy hc]
      cases ey with
      | zero =>
        cases ez with
        | zero => exact absurd hc (cmp_zero_right .zero)
        | oadd ez₁ nze aze =>
          rw [mul_oadd_zero, mul_oadd_oadd]
          exact (add_oadd_lt (nf_mul hx hy) (lt_add_of_pos hx.fst rfl)).symm
      | oadd ey₁ nye aye =>
        cases ez with
        | zero => exact absurd hc (cmp_zero_right _)
        | oadd ez₁ nze aze =>
          rw [mul_oadd_oadd, mul_oadd_oadd]
          exact (add_oadd_lt (nf_mul hx hy)
            (add_strict_right ex (.oadd ey₁ nye aye) (.oadd ez₁ nze aze) hc)).symm
    | eq =>
      cases ey with
      | zero =>
        have hez : ez = .zero := (eq_of_cmp_eq hc).symm
        cases hez
        rw [add_oadd_eq hy, mul_oadd_zero, mul_oadd_zero, mul_oadd_zero,
          add_oadd_eq (nf_mul hx hy), coef_mul_add]
      | oadd ey₁ nye aye =>
        have hez : ez = .oadd ey₁ nye aye := (eq_of_cmp_eq hc).symm
        cases hez
        rw [add_oadd_eq hy, mul_oadd_oadd, mul_oadd_oadd, mul_oadd_oadd,
          add_oadd_eq (nf_mul hx hy)]
    | gt =>
      have hzlt : cmp (.oadd ez nz az) (omegaPow ey) = .lt :=
        oadd_lt_omegaPow.mpr (cmp_eq_gt.mp hc)
      cases ey with
      | zero => exact nomatch (eq_zero_of_lt_omegaPow_zero hzlt)
      | oadd ey₁ nye aye =>
        have ih := mul_add (y := ay) (z := .oadd ez nz az) hx hy.snd hz
        have htail := oadd_mul_below (e₁ := ex) (n₁ := nx) (a₁ := ax) hx hzlt
        rw [add_oadd_gt hy hz hzlt,
          mul_oadd_oadd ex nx ax ey₁ nye aye ny (add ay (.oadd ez nz az)), ih,
          mul_oadd_oadd ex nx ax ey₁ nye aye ny ay,
          add_oadd_gt (nf_mul hx hy) (nf_mul hx hz) htail]

/-! ## Power -/

theorem mul_pos {a b : Nat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  cases a with
  | zero => exact absurd ha (Nat.not_lt_zero 0)
  | succ a =>
    rw [Nat.succ_mul]
    exact Nat.lt_add_left (a * b) hb

theorem succ_pow_pos (m k : Nat) : 0 < (m + 1) ^ k := by
  induction k with
  | zero =>
    rw [Nat.pow_zero]
    exact Nat.zero_lt_one
  | succ k ih =>
    rw [Nat.pow_succ]
    exact mul_pos ih (Nat.zero_lt_succ m)

theorem ofNat_eq_oadd_pred {t : Nat} (ht : 0 < t) :
    ofNat t = .oadd .zero (t - 1) .zero := by
  cases t with
  | zero => exact absurd ht (Nat.not_lt_zero 0)
  | succ _ => rfl

/-- Strict increase on the right cancels a common left summand. -/
theorem cmp_of_add_strict_right {x y z : Cnf}
    (h : cmp (add x y) (add x z) = .lt) : cmp y z = .lt := by
  cases hc : cmp y z with
  | lt => rfl
  | eq =>
    rw [eq_of_cmp_eq hc, cmp_self] at h
    exact nomatch h
  | gt =>
    exact nomatch (h.symm.trans (cmp_eq_gt.mpr (add_strict_right x z y (cmp_eq_gt.mp hc))))

/-- Left subtraction of one. A positive finite coefficient decreases, and a positive
exponent is unchanged, since `1 + e = e` for infinite `e`. -/
def subOne : Cnf → Cnf
  | .zero => .zero
  | .oadd .zero 0 a => a
  | .oadd .zero (n + 1) a => .oadd .zero n a
  | .oadd e@(.oadd _ _ _) n a => .oadd e n a

theorem subOne_finite_zero (a : Cnf) : subOne (.oadd .zero 0 a) = a := rfl

theorem subOne_finite_succ (n : Nat) (a : Cnf) :
    subOne (.oadd .zero (n + 1) a) = .oadd .zero n a := rfl

theorem subOne_infinite (e : Cnf) (n' : Nat) (a' : Cnf) (n : Nat) (a : Cnf) :
    subOne (.oadd (.oadd e n' a') n a) = .oadd (.oadd e n' a') n a := rfl

theorem nf_subOne : ∀ {e : Cnf}, NF e → NF (subOne e)
  | .zero, _ => .zero
  | .oadd .zero 0 _, h => h.snd
  | .oadd .zero (_ + 1) _, h => .oadd _ .zero h.snd h.lt
  | .oadd (.oadd e n' a') n a, h => by
    rw [subOne_infinite e n' a' n a]
    exact h

theorem one_add_subOne : ∀ {e : Cnf}, NF e → cmp .zero e = .lt →
    add (ofNat 1) (subOne e) = e
  | .zero, _, h => nomatch h
  | .oadd .zero 0 a, h, _ => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero h.lt
    rw [subOne_finite_zero, add_zero (nf_ofNat 1)]
    rfl
  | .oadd .zero (n + 1) a, h, _ => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero h.lt
    rw [subOne_finite_succ, show .oadd .zero n .zero = ofNat (n + 1) from rfl, ofNat_add,
      Nat.add_comm 1 (n + 1)]
    rfl
  | .oadd (.oadd e n' a') n a, _, _ => by
    rw [subOne_infinite e n' a' n a]
    exact add_oadd_lt (nf_ofNat 1) rfl

theorem nf_omegaPow {e : Cnf} (he : NF e) : NF (omegaPow e) :=
  .oadd 0 he .zero rfl

/-- Quotient and remainder by `ω`: `split o = (q, r)` means `o = q + r` and `ω` divides `q`. -/
def split : Cnf → Cnf × Nat
  | .zero => (.zero, 0)
  | .oadd .zero n _ => (.zero, n + 1)
  | .oadd e@(.oadd _ _ _) n a =>
    match split a with
    | (q, m) => (.oadd e n q, m)

/-- Quotient and remainder by `ω` from the left: `split' o = (q, r)` means `o = ω * q + r`. -/
def split' : Cnf → Cnf × Nat
  | .zero => (.zero, 0)
  | .oadd .zero n _ => (.zero, n + 1)
  | .oadd e@(.oadd _ _ _) n a =>
    match split' a with
    | (q, m) => (.oadd (subOne e) n q, m)

/-- `scale x o` is the tree for `ω ^ x * o`. -/
def scale (x : Cnf) : Cnf → Cnf
  | .zero => .zero
  | .oadd e n a => .oadd (add x e) n (scale x a)

theorem scale_zero (x : Cnf) : scale x .zero = .zero := rfl

theorem scale_oadd (x e : Cnf) (n : Nat) (a : Cnf) :
    scale x (.oadd e n a) = .oadd (add x e) n (scale x a) := rfl

theorem scale_below {x e a : Cnf} (hlt : cmp a (omegaPow e) = .lt) :
    cmp (scale x a) (omegaPow (add x e)) = .lt := by
  cases a with
  | zero => rfl
  | oadd ea _ _ =>
    rw [scale_oadd, oadd_lt_omegaPow]
    exact add_strict_right x ea e (oadd_lt_omegaPow.mp hlt)

theorem nf_scale : ∀ {x y : Cnf}, NF x → NF y → NF (scale x y)
  | _, .zero, _, _ => .zero
  | _, .oadd _ n _, hx, hy => by
    rw [scale_oadd]
    exact .oadd n (nf_add hx hy.fst) (nf_scale hx hy.snd) (scale_below hy.lt)

theorem scale_omega (x : Cnf) : scale x omega = omegaPow (add x (ofNat 1)) := by
  unfold omega
  rw [scale_oadd, scale_zero, omegaPow]
  rfl

/-- `mulNat o m` is the tree for `o * m`. -/
def mulNat : Cnf → Nat → Cnf
  | .zero, _ => .zero
  | _, 0 => .zero
  | .oadd e n a, m + 1 => .oadd e (n * (m + 1) + m) a

theorem mulNat_zero (x : Cnf) : mulNat x 0 = .zero := by
  cases x <;> rfl

theorem nf_mulNat {x : Cnf} (m : Nat) (hx : NF x) : NF (mulNat x m) := by
  cases m with
  | zero =>
    rw [mulNat_zero]
    exact .zero
  | succ m =>
    cases x with
    | zero => exact .zero
    | oadd e n a =>
      rw [show mulNat (.oadd e n a) (m + 1) = .oadd e (n * (m + 1) + m) a from rfl]
      exact .oadd (n * (m + 1) + m) hx.fst hx.snd hx.lt

theorem mulNat_ofNat_one : ∀ n : Nat, mulNat (ofNat 1) n = ofNat n
  | 0 => rfl
  | n + 1 => by
    rw [show mulNat (ofNat 1) (n + 1) = .oadd .zero (0 * (n + 1) + n) .zero from rfl,
      Nat.zero_mul, Nat.zero_add]
    rfl

/-- The quotient of a normal form is normal, and restoring the remainder recovers it. -/
theorem split_ok : ∀ {o : Cnf}, NF o →
    NF (split o).1 ∧ add (split o).1 (ofNat (split o).2) = o
  | .zero, _ => ⟨.zero, rfl⟩
  | .oadd .zero n a, h => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero h.lt
    unfold split
    refine ⟨.zero, ?_⟩
    rw [zero_add]
    rfl
  | .oadd (.oadd ei ni ai) n a, h => by
    have ih := split_ok h.snd
    cases hs : split a with
    | mk q m =>
      have hq : NF q := by
        have t := ih.1
        rw [hs] at t
        exact t
      have hspec : add q (ofNat m) = a := by
        have t := ih.2
        rw [hs] at t
        exact t
      have hqlt : cmp q (omegaPow (.oadd ei ni ai)) = .lt :=
        cmp_lt_of_le_of_lt (le_add_left (y := ofNat m) hq) (hspec ▸ h.lt)
      unfold split
      rw [hs]
      refine ⟨.oadd n h.fst hq hqlt, ?_⟩
      have hnf : NF (.oadd (.oadd ei ni ai) n q) := .oadd n h.fst hq hqlt
      have hm : cmp (ofNat m) (omegaPow (.oadd ei ni ai)) = .lt :=
        ofNat_lt_omegaPow_of_pos m rfl
      rw [add_oadd_gt hnf (nf_ofNat m) hm, hspec]

/-- The base-`ω` quotient of a normal form is normal, and `ω * q + r` recovers it. -/
theorem split'_ok : ∀ {o : Cnf}, NF o →
    NF (split' o).1 ∧ add (scale (ofNat 1) (split' o).1) (ofNat (split' o).2) = o
  | .zero, _ => ⟨.zero, rfl⟩
  | .oadd .zero n a, h => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero h.lt
    unfold split'
    refine ⟨.zero, ?_⟩
    rw [scale_zero, zero_add]
    rfl
  | .oadd (.oadd ei ni ai) n a, h => by
    have ih := split'_ok h.snd
    cases hs : split' a with
    | mk q m =>
      have hq : NF q := by
        have t := ih.1
        rw [hs] at t
        exact t
      have hspec : add (scale (ofNat 1) q) (ofNat m) = a := by
        have t := ih.2
        rw [hs] at t
        exact t
      have hsub : add (ofNat 1) (subOne (.oadd ei ni ai)) = .oadd ei ni ai :=
        one_add_subOne h.fst rfl
      have hscale_lt : cmp (scale (ofNat 1) q) (omegaPow (.oadd ei ni ai)) = .lt :=
        cmp_lt_of_le_of_lt (le_add_left (nf_scale (nf_ofNat 1) hq)) (hspec ▸ h.lt)
      have hqlt : cmp q (omegaPow (subOne (.oadd ei ni ai))) = .lt := by
        cases q with
        | zero => rfl
        | oadd eq _ _ =>
          rw [scale_oadd, oadd_lt_omegaPow] at hscale_lt
          rw [← hsub] at hscale_lt
          exact oadd_lt_omegaPow.mpr (cmp_of_add_strict_right hscale_lt)
      unfold split'
      rw [hs]
      refine ⟨.oadd n (nf_subOne h.fst) hq hqlt, ?_⟩
      have hscaled : scale (ofNat 1) (.oadd (subOne (.oadd ei ni ai)) n q) =
          .oadd (.oadd ei ni ai) n (scale (ofNat 1) q) := by
        rw [scale_oadd, hsub]
      rw [hscaled]
      have htail : NF (scale (ofNat 1) q) := nf_scale (nf_ofNat 1) hq
      have hhead : NF (.oadd (.oadd ei ni ai) n (scale (ofNat 1) q)) :=
        .oadd n h.fst htail hscale_lt
      have hm : cmp (ofNat m) (omegaPow (.oadd ei ni ai)) = .lt :=
        ofNat_lt_omegaPow_of_pos m rfl
      rw [add_oadd_gt hhead (nf_ofNat m) hm, hspec]

/-- One finite step of a power whose base is a positive multiple of `ω`. -/
def opowAux (e a0 a : Cnf) : Nat → Nat → Cnf
  | _, 0 => .zero
  | 0, m + 1 => .oadd e m .zero
  | k + 1, m + 1 => add (scale (add e (mulNat a0 k)) a) (opowAux e a0 a k (m + 1))

theorem opowAux_zero (e a0 a : Cnf) : ∀ k : Nat, opowAux e a0 a k 0 = .zero
  | 0 => rfl
  | _ + 1 => rfl

theorem nf_opowAux {e a0 a : Cnf} (he : NF e) (ha0 : NF a0) (ha : NF a) :
    ∀ k m : Nat, NF (opowAux e a0 a k m)
  | 0, 0 => .zero
  | _ + 1, 0 => .zero
  | 0, m + 1 => by
    unfold opowAux
    exact .oadd m he .zero rfl
  | k + 1, m + 1 => by
    unfold opowAux
    exact nf_add (nf_scale (nf_add he (nf_mulNat k ha0)) ha)
      (nf_opowAux he ha0 ha k (m + 1))

/-- Power, dispatched on the shape of the exponent and on `split` of the base. -/
def opowAux2 (exp : Cnf) : Cnf × Nat → Cnf
  | (.zero, 0) =>
    match exp with
    | .zero => ofNat 1
    | .oadd _ _ _ => .zero
  | (.zero, 1) => ofNat 1
  | (.zero, m + 1) =>
    match split' exp with
    | (b', k) => .oadd b' ((m + 1) ^ k - 1) .zero
  | (.oadd a0 n0 t0, m) =>
    match split exp with
    | (b, 0) => .oadd (mul a0 b) 0 .zero
    | (b, k + 1) =>
      add (scale (add (mul a0 b) (mulNat a0 k)) (.oadd a0 n0 t0))
        (opowAux (mul a0 b) a0 (mulNat (.oadd a0 n0 t0) m) k m)

/-- Ordinal power of notation trees. -/
def pow (base exp : Cnf) : Cnf := opowAux2 exp (split base)

theorem opowAux2_omega_zero {e b : Cnf} (h : split e = (b, 0)) :
    opowAux2 e (omega, 0) = .oadd (mul (ofNat 1) b) 0 .zero := by
  unfold omega opowAux2
  rw [h]
  rfl

theorem opowAux2_omega_succ {e b : Cnf} {k : Nat} (h : split e = (b, k + 1)) :
    opowAux2 e (omega, 0) =
      add (scale (add (mul (ofNat 1) b) (mulNat (ofNat 1) k)) omega)
        (opowAux (mul (ofNat 1) b) (ofNat 1) .zero k 0) := by
  unfold omega opowAux2
  rw [h]
  rfl

theorem pow_zero : ∀ x : Cnf, pow x .zero = ofNat 1
  | .zero => rfl
  | .oadd .zero 0 _ => by
    unfold pow split opowAux2
    rfl
  | .oadd .zero (_ + 1) _ => by
    unfold pow split opowAux2 split'
    rfl
  | .oadd (.oadd e n' a') n a => by
    unfold pow
    cases hs : split a with
    | mk q m =>
      have hsplit : split (.oadd (.oadd e n' a') n a) =
          (.oadd (.oadd e n' a') n q, m) := by
        unfold split
        rw [hs]
      rw [hsplit]
      cases m with
      | zero =>
        unfold opowAux2
        rfl
      | succ _ =>
        unfold opowAux2
        rfl

theorem pow_one (y : Cnf) : pow (ofNat 1) y = ofNat 1 := by
  unfold pow ofNat split
  rfl

theorem ofNat_pow {m : Nat} (hm : 0 < m) (n : Nat) :
    pow (ofNat m) (ofNat n) = ofNat (m ^ n) := by
  cases m with
  | zero => exact absurd hm (Nat.not_lt_zero 0)
  | succ m =>
    cases m with
    | zero =>
      rw [Nat.one_pow]
      exact pow_one (ofNat n)
    | succ m =>
      cases n with
      | zero =>
        rw [show ofNat 0 = .zero from rfl, Nat.pow_zero, pow_zero]
      | succ n =>
        unfold pow opowAux2
        have hs : split (ofNat (m + 2)) = (.zero, m + 2) := by
          rw [ofNat, split]
        rw [hs]
        have hsp : split' (ofNat (n + 1)) = (.zero, n + 1) := by
          rw [ofNat, split']
        rw [hsp, ofNat_eq_oadd_pred (succ_pow_pos (m + 1) (n + 1))]
        rfl

/-- `ω ^ e` for a normal exponent. -/
theorem pow_omega {e : Cnf} (he : NF e) : pow omega e = omegaPow e := by
  have hok := split_ok he
  unfold pow
  have hsw : split omega = (omega, 0) := by
    unfold omega split
    rfl
  rw [hsw]
  cases hs : split e with
  | mk b r =>
    have hb : NF b := by
      have t := hok.1
      rw [hs] at t
      exact t
    have hspec : add b (ofNat r) = e := by
      have t := hok.2
      rw [hs] at t
      exact t
    cases r with
    | zero =>
      rw [opowAux2_omega_zero hs]
      rw [ofNat, add_zero hb] at hspec
      rw [hspec, one_mul he]
      rfl
    | succ k =>
      rw [opowAux2_omega_succ hs, one_mul hb, mulNat_ofNat_one k, opowAux_zero, scale_omega]
      have hsum : add (add b (ofNat k)) (ofNat 1) = e := by
        rw [add_assoc hb (nf_ofNat k) (nf_ofNat 1), ofNat_add, hspec]
      rw [add_zero (nf_omegaPow (nf_add (nf_add hb (nf_ofNat k)) (nf_ofNat 1))), hsum]

/-- `ω ^ y * ω ^ z = ω ^ (y + z)` on normal forms. -/
theorem omegaPow_add {y z : Cnf} (hy : NF y) (_hz : NF z) :
    mul (omegaPow y) (omegaPow z) = omegaPow (add y z) := by
  cases z with
  | zero =>
    rw [add_zero hy, omegaPow, omegaPow, mul_oadd_zero, Nat.zero_mul, Nat.zero_add]
  | oadd _ _ _ =>
    rw [omegaPow, omegaPow, mul_oadd_oadd, mul_zero]
    rfl

/-- Power of `ω` turns a sum of exponents into a product. -/
theorem pow_add_omega {y z : Cnf} (hy : NF y) (hz : NF z) :
    pow omega (add y z) = mul (pow omega y) (pow omega z) := by
  rw [pow_omega (nf_add hy hz), pow_omega hy, pow_omega hz, omegaPow_add hy hz]

/-- Power of a positive numeral agrees with the natural-number power, so a sum of finite
exponents becomes a product. -/
theorem pow_add_ofNat {m : Nat} (hm : 0 < m) (y z : Nat) :
    pow (ofNat m) (ofNat (y + z)) =
      mul (pow (ofNat m) (ofNat y)) (pow (ofNat m) (ofNat z)) := by
  rw [ofNat_pow hm, ofNat_pow hm, ofNat_pow hm, Nat.pow_add, ofNat_mul]

theorem nf_pow {x y : Cnf} (hx : NF x) (hy : NF y) : NF (pow x y) := by
  unfold pow
  have hox := split_ok hx
  cases hsx : split x with
  | mk q r =>
    have hq : NF q := by
      have t := hox.1
      rw [hsx] at t
      exact t
    cases q with
    | zero =>
      cases r with
      | zero =>
        unfold opowAux2
        cases y with
        | zero => exact nf_ofNat 1
        | oadd _ _ _ => exact .zero
      | succ r =>
        cases r with
        | zero =>
          unfold opowAux2
          exact nf_ofNat 1
        | succ p =>
          have hoy := split'_ok hy
          cases hsy : split' y with
          | mk b k =>
            have hb : NF b := by
              have t := hoy.1
              rw [hsy] at t
              exact t
            unfold opowAux2
            rw [hsy]
            exact .oadd ((p + 2) ^ k - 1) hb .zero rfl
    | oadd a0 _ _ =>
      have ha0 : NF a0 := hq.fst
      cases hsy : split y with
      | mk b s =>
        have hoby := split_ok hy
        have hb : NF b := by
          have t := hoby.1
          rw [hsy] at t
          exact t
        unfold opowAux2
        rw [hsy]
        cases s with
        | zero => exact .oadd 0 (nf_mul ha0 hb) .zero rfl
        | succ k =>
          exact nf_add
            (nf_scale (nf_add (nf_mul ha0 hb) (nf_mulNat k ha0)) hq)
            (nf_opowAux (nf_mul ha0 hb) ha0 (nf_mulNat r hq) k r)

/-- Two finite leading terms compare as their coefficients do. -/
theorem cmp_nat_oadd_zero (n₁ n₂ : Nat) :
    cmp (.oadd .zero n₁ .zero) (.oadd .zero n₂ .zero) = compare n₁ n₂ := by
  rw [cmp_oadd, cmp_self, Ordering.eq_then]
  cases compare n₁ n₂ with
  | lt => rw [Ordering.lt_then]
  | eq => rw [Ordering.eq_then]
  | gt => rw [Ordering.gt_then]

/-- Left subtraction of one is strictly monotone on positive normal forms. -/
theorem subOne_strict : ∀ {a b : Cnf}, NF a → NF b → cmp .zero a = .lt →
    cmp a b = .lt → cmp (subOne a) (subOne b) = .lt
  | .zero, _, _, _, h, _ => nomatch h
  | .oadd .zero 0 _, b, ha, hb, _, hlt => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero ha.lt
    rw [subOne_finite_zero]
    cases b with
    | zero => exact absurd hlt (cmp_zero_right _)
    | oadd eb nb _ =>
      cases eb with
      | zero =>
        obtain rfl := eq_zero_of_lt_omegaPow_zero hb.lt
        cases nb with
        | zero =>
          rw [cmp_self] at hlt
          exact nomatch hlt
        | succ _ =>
          rw [subOne_finite_succ]
          rfl
      | oadd _ _ _ =>
        rw [subOne_infinite]
        rfl
  | .oadd .zero (na + 1) _, b, ha, hb, _, hlt => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero ha.lt
    cases b with
    | zero => exact absurd hlt (cmp_zero_right _)
    | oadd eb nb _ =>
      cases eb with
      | zero =>
        obtain rfl := eq_zero_of_lt_omegaPow_zero hb.lt
        rw [cmp_nat_oadd_zero] at hlt
        cases nb with
        | zero =>
          rw [Nat.compare_eq_gt.mpr (Nat.zero_lt_succ na)] at hlt
          exact nomatch hlt
        | succ nb =>
          rw [subOne_finite_succ, subOne_finite_succ, cmp_nat_oadd_zero,
            Nat.compare_eq_lt.mpr (Nat.lt_of_succ_lt_succ (Nat.compare_eq_lt.mp hlt))]
      | oadd _ _ _ =>
        rw [subOne_finite_succ, subOne_infinite, cmp_oadd]
        rfl
  | .oadd (.oadd eyi nyi ayi) _ _, b, _, hb, _, hlt => by
    cases b with
    | zero => exact absurd hlt (cmp_zero_right _)
    | oadd eb _ _ =>
      cases eb with
      | zero =>
        obtain rfl := eq_zero_of_lt_omegaPow_zero hb.lt
        have hgt : cmp (.oadd eyi nyi ayi) .zero = .gt := rfl
        rw [cmp_oadd, hgt] at hlt
        exact nomatch hlt
      | oadd _ _ _ =>
        rw [subOne_infinite, subOne_infinite]
        exact hlt

/-- `split'` of a numeral is the numeral itself, with quotient zero. -/
theorem split'_ofNat (n : Nat) : split' (ofNat n) = (.zero, n) := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [ofNat, split']

/-- Adding a numeral on the right increases the finite remainder and keeps the quotient. -/
theorem split'_add_ofNat : ∀ {y : Cnf}, NF y → ∀ n : Nat,
    split' (add y (ofNat n)) = ((split' y).1, (split' y).2 + n)
  | .zero, _, n => by
    rw [zero_add, split', split'_ofNat, Nat.zero_add]
  | .oadd .zero ny _, h, n => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero h.lt
    rw [show .oadd .zero ny .zero = ofNat (ny + 1) from rfl, ofNat_add, split'_ofNat,
      split'_ofNat]
  | .oadd (.oadd ei ni ai) ny a, h, n => by
    have ih := split'_add_ofNat h.snd n
    have hlt : cmp (ofNat n) (omegaPow (.oadd ei ni ai)) = .lt :=
      ofNat_lt_omegaPow_of_pos n rfl
    rw [add_oadd_gt h (nf_ofNat n) hlt]
    cases hs : split' a with
    | mk q m =>
      have htail : split' (add a (ofNat n)) = (q, m + n) := by
        have t := ih
        rw [hs] at t
        exact t
      have hsp : split' (.oadd (.oadd ei ni ai) ny a) =
          (.oadd (subOne (.oadd ei ni ai)) ny q, m) := by
        unfold split'
        rw [hs]
      have hsum : split' (.oadd (.oadd ei ni ai) ny (add a (ofNat n))) =
          (.oadd (subOne (.oadd ei ni ai)) ny q, m + n) := by
        unfold split'
        rw [htail]
      rw [hsp, hsum]

/-- When the right summand is at least `ω`, the base-`ω` quotient adds and the
remainder is the right remainder. -/
theorem split'_add_pos : ∀ {y z : Cnf}, NF y → NF z →
    cmp .zero (split' z).1 = .lt →
    split' (add y z) = (add (split' y).1 (split' z).1, (split' z).2)
  | _, .zero, _, _, hpos => by
    rw [split'] at hpos
    exact nomatch hpos
  | _, .oadd .zero nz _, _, hz, hpos => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero hz.lt
    rw [show split' (.oadd .zero nz .zero) = (.zero, nz + 1) from rfl] at hpos
    exact nomatch hpos
  | .zero, .oadd (.oadd _ _ _) _ _, _, _, _ => by
    rw [zero_add, split', zero_add]
  | .oadd .zero ny _, .oadd (.oadd ei ni ai) nz az, hy, _, _ => by
    obtain rfl := eq_zero_of_lt_omegaPow_zero hy.lt
    have hlt : cmp .zero (.oadd ei ni ai) = .lt := rfl
    rw [add_oadd_lt hy hlt]
    rw [show .oadd .zero ny .zero = ofNat (ny + 1) from rfl, split'_ofNat, zero_add]
  | .oadd (.oadd eyi nyi ayi) ny ay, .oadd (.oadd ei ni ai) nz az, hy, hz, hpos => by
    cases hc : cmp (.oadd eyi nyi ayi) (.oadd ei ni ai) with
    | lt =>
      rw [add_oadd_lt hy hc]
      cases hsy : split' ay with
      | mk qay may =>
        cases hsz : split' az with
        | mk qaz maz =>
          have hqy : split' (.oadd (.oadd eyi nyi ayi) ny ay) =
              (.oadd (subOne (.oadd eyi nyi ayi)) ny qay, may) := by
            unfold split'
            rw [hsy]
          have hqz : split' (.oadd (.oadd ei ni ai) nz az) =
              (.oadd (subOne (.oadd ei ni ai)) nz qaz, maz) := by
            unfold split'
            rw [hsz]
          have hnfqy : NF (.oadd (subOne (.oadd eyi nyi ayi)) ny qay) := by
            have t := (split'_ok hy).1
            rw [hqy] at t
            exact t
          have hsub : cmp (subOne (.oadd eyi nyi ayi)) (subOne (.oadd ei ni ai)) = .lt :=
            subOne_strict hy.fst hz.fst rfl hc
          rw [hqy, hqz, add_oadd_lt hnfqy hsub]
    | eq =>
      have heq : oadd eyi nyi ayi = oadd ei ni ai := eq_of_cmp_eq hc
      cases heq
      rw [add_oadd_eq hy]
      cases hsz : split' az with
      | mk qaz maz =>
        cases hsy : split' ay with
        | mk qay may =>
          have hqy : split' (.oadd (.oadd eyi nyi ayi) ny ay) =
              (.oadd (subOne (.oadd eyi nyi ayi)) ny qay, may) := by
            unfold split'
            rw [hsy]
          have hqz : split' (.oadd (.oadd eyi nyi ayi) nz az) =
              (.oadd (subOne (.oadd eyi nyi ayi)) nz qaz, maz) := by
            unfold split'
            rw [hsz]
          have hsp : split' (.oadd (.oadd eyi nyi ayi) (ny + nz + 1) az) =
              (.oadd (subOne (.oadd eyi nyi ayi)) (ny + nz + 1) qaz, maz) := by
            unfold split'
            rw [hsz]
          have hnfqy : NF (.oadd (subOne (.oadd eyi nyi ayi)) ny qay) := by
            have t := (split'_ok hy).1
            rw [hqy] at t
            exact t
          rw [hsp, hqy, hqz, add_oadd_eq hnfqy]
    | gt =>
      have hzl : cmp (.oadd (.oadd ei ni ai) nz az)
          (omegaPow (.oadd eyi nyi ayi)) = .lt :=
        oadd_lt_omegaPow.mpr (cmp_eq_gt.mp hc)
      rw [add_oadd_gt hy hz hzl]
      have ih := split'_add_pos hy.snd hz hpos
      cases hsy : split' ay with
      | mk qay may =>
        cases hsz : split' az with
        | mk qaz maz =>
          have hqy : split' (.oadd (.oadd eyi nyi ayi) ny ay) =
              (.oadd (subOne (.oadd eyi nyi ayi)) ny qay, may) := by
            unfold split'
            rw [hsy]
          have hqz : split' (.oadd (.oadd ei ni ai) nz az) =
              (.oadd (subOne (.oadd ei ni ai)) nz qaz, maz) := by
            unfold split'
            rw [hsz]
          have hnfqy : NF (.oadd (subOne (.oadd eyi nyi ayi)) ny qay) := by
            have t := (split'_ok hy).1
            rw [hqy] at t
            exact t
          have hnfqz : NF (.oadd (subOne (.oadd ei ni ai)) nz qaz) := by
            have t := (split'_ok hz).1
            rw [hqz] at t
            exact t
          have hsub : cmp (subOne (.oadd ei ni ai)) (subOne (.oadd eyi nyi ayi)) = .lt :=
            subOne_strict hz.fst hy.fst rfl (cmp_eq_gt.mp hc)
          have hadd : add (.oadd (subOne (.oadd eyi nyi ayi)) ny qay)
              (.oadd (subOne (.oadd ei ni ai)) nz qaz) =
              .oadd (subOne (.oadd eyi nyi ayi)) ny
                (add qay (.oadd (subOne (.oadd ei ni ai)) nz qaz)) :=
            add_oadd_gt hnfqy hnfqz (oadd_lt_omegaPow.mpr hsub)
          have hih : split' (add ay (.oadd (.oadd ei ni ai) nz az)) =
              (add qay (.oadd (subOne (.oadd ei ni ai)) nz qaz), maz) := by
            have t := ih
            rw [hsy, hqz] at t
            exact t
          have hsp : split' (.oadd (.oadd eyi nyi ayi) ny
              (add ay (.oadd (.oadd ei ni ai) nz az))) =
              (.oadd (subOne (.oadd eyi nyi ayi)) ny
                (add qay (.oadd (subOne (.oadd ei ni ai)) nz qaz)), maz) := by
            unfold split'
            rw [hih]
          rw [hsp, hqy, hqz, hadd]

/-- The coefficient identity behind a product of two finite powers. -/
theorem coef_pow_mul (b ry rz : Nat) :
    ((b + 2) ^ ry - 1) * ((b + 2) ^ rz - 1) + ((b + 2) ^ ry - 1) +
        ((b + 2) ^ rz - 1) =
      (b + 2) ^ (ry + rz) - 1 := by
  have hA : 0 < (b + 2) ^ ry := succ_pow_pos (b + 1) ry
  have hB : 0 < (b + 2) ^ rz := succ_pow_pos (b + 1) rz
  have hA1 : (b + 2) ^ ry - 1 + 1 = (b + 2) ^ ry :=
    Nat.succ_pred_eq_of_pos hA
  have hB1 : (b + 2) ^ rz - 1 + 1 = (b + 2) ^ rz :=
    Nat.succ_pred_eq_of_pos hB
  have hmul : ((b + 2) ^ ry - 1) * ((b + 2) ^ rz - 1) + ((b + 2) ^ ry - 1) =
      ((b + 2) ^ ry - 1) * (b + 2) ^ rz := by
    have hsucc : ((b + 2) ^ rz - 1).succ = (b + 2) ^ rz - 1 + 1 := rfl
    rw [← Nat.mul_succ, hsucc, hB1]
  have hdist : ((b + 2) ^ ry - 1) * (b + 2) ^ rz + (b + 2) ^ rz =
      ((b + 2) ^ ry - 1) * (b + 2) ^ rz + 1 * (b + 2) ^ rz := by
    rw [Nat.one_mul]
  have hstep : ((b + 2) ^ ry - 1) * ((b + 2) ^ rz - 1) + ((b + 2) ^ ry - 1) +
      ((b + 2) ^ rz - 1) + 1 = (b + 2) ^ ry * (b + 2) ^ rz := by
    rw [Nat.add_assoc (((b + 2) ^ ry - 1) * ((b + 2) ^ rz - 1) + ((b + 2) ^ ry - 1))
        ((b + 2) ^ rz - 1) 1, hB1, hmul, hdist, ← Nat.add_mul, hA1]
  rw [Nat.pow_add, ← hstep, Nat.add_sub_cancel]

/-- A numeral at least `2`, to any exponent, is `ω ^ q * n ^ r` for `split'`. -/
theorem pow_ofNat_large (m : Nat) (e : Cnf) :
    pow (ofNat (m + 2)) e =
      .oadd (split' e).1 ((m + 2) ^ (split' e).2 - 1) .zero := by
  unfold pow
  have hs : split (ofNat (m + 2)) = (.zero, m + 2) := by
    rw [ofNat, split]
  rw [hs]
  cases hsp : split' e with
  | mk b k =>
    unfold opowAux2
    rw [hsp]
    rfl

/-- A positive numeral to a sum of normal exponents is the product of the powers. -/
theorem pow_add_finite {n : Nat} (hn : 0 < n) {y z : Cnf} (hy : NF y) (hz : NF z) :
    pow (ofNat n) (add y z) = mul (pow (ofNat n) y) (pow (ofNat n) z) := by
  cases n with
  | zero => exact absurd hn (Nat.not_lt_zero 0)
  | succ n =>
    cases n with
    | zero =>
      rw [pow_one, pow_one, pow_one, show ofNat 1 = .oadd .zero 0 .zero from rfl,
        mul_oadd_zero, Nat.zero_mul, Nat.zero_add]
    | succ n =>
      cases hsy : split' y with
      | mk qy ry =>
        cases hsz : split' z with
        | mk qz rz =>
          cases qz with
          | zero =>
            have hzfin : z = ofNat rz := by
              have hsum := (split'_ok hz).2
              rw [hsz, scale_zero, zero_add] at hsum
              exact hsum.symm
            have hsadd : split' (add y z) = (qy, ry + rz) := by
              have t := split'_add_ofNat hy rz
              rw [← hzfin, hsy] at t
              exact t
            rw [pow_ofNat_large n (add y z), pow_ofNat_large n y, pow_ofNat_large n z,
              hsadd, hsy, hsz, mul_oadd_zero, coef_pow_mul]
          | oadd ez nn aa =>
            have hsadd : split' (add y z) =
                (add qy (.oadd ez nn aa), rz) := by
              have t := split'_add_pos hy hz (by rw [hsz]; rfl)
              rw [hsy, hsz] at t
              exact t
            rw [pow_ofNat_large n (add y z), pow_ofNat_large n y, pow_ofNat_large n z,
              hsadd, hsy, hsz, mul_oadd_oadd, mul_zero]

end Cnf

namespace Level

/-- Sum of two levels. -/
def add (x y : Level) : Level := ⟨Cnf.add x.1 y.1, Cnf.nf_add x.2 y.2⟩

/-- Product of two levels. -/
def mul (x y : Level) : Level := ⟨Cnf.mul x.1 y.1, Cnf.nf_mul x.2 y.2⟩

theorem add_zero (x : Level) : add x zero = x := by
  apply ext
  exact Cnf.add_zero x.2

theorem zero_add (x : Level) : add zero x = x := by
  apply ext
  rfl

theorem add_assoc (x y z : Level) : add (add x y) z = add x (add y z) := by
  apply ext
  exact Cnf.add_assoc x.2 y.2 z.2

theorem succ_eq_add_one (x : Level) : succ x = add x (ofNat 1) := by
  apply ext
  exact Cnf.succ_eq_add_one x.2

theorem ofNat_add (m n : Nat) : add (ofNat m) (ofNat n) = ofNat (m + n) := by
  apply ext
  exact Cnf.ofNat_add m n

theorem mul_zero (x : Level) : mul x zero = zero := by
  apply ext
  exact Cnf.mul_zero x.1

theorem zero_mul (x : Level) : mul zero x = zero := by
  apply ext
  exact Cnf.zero_mul x.1

theorem mul_one (x : Level) : mul x (ofNat 1) = x := by
  apply ext
  exact Cnf.mul_one x.1

theorem one_mul (x : Level) : mul (ofNat 1) x = x := by
  apply ext
  exact Cnf.one_mul x.2

theorem mul_assoc (x y z : Level) : mul (mul x y) z = mul x (mul y z) := by
  apply ext
  exact Cnf.mul_assoc x.2 y.2 z.2

theorem mul_add (x y z : Level) : mul x (add y z) = add (mul x y) (mul x z) := by
  apply ext
  exact Cnf.mul_add x.2 y.2 z.2

theorem ofNat_mul (m n : Nat) : mul (ofNat m) (ofNat n) = ofNat (m * n) := by
  apply ext
  exact Cnf.ofNat_mul m n

/-- A power of levels. -/
def pow (x y : Level) : Level := ⟨Cnf.pow x.1 y.1, Cnf.nf_pow x.2 y.2⟩

/-- `ω ^ e` as a level. -/
def omegaPow (e : Level) : Level := ⟨Cnf.omegaPow e.1, Cnf.nf_omegaPow e.2⟩

theorem pow_zero (x : Level) : pow x zero = ofNat 1 := by
  apply ext
  exact Cnf.pow_zero x.1

theorem pow_one (y : Level) : pow (ofNat 1) y = ofNat 1 := by
  apply ext
  exact Cnf.pow_one y.1

theorem ofNat_pow {m : Nat} (hm : 0 < m) (n : Nat) :
    pow (ofNat m) (ofNat n) = ofNat (m ^ n) := by
  apply ext
  exact Cnf.ofNat_pow hm n

theorem pow_omega (e : Level) : pow omega e = omegaPow e := by
  apply ext
  exact Cnf.pow_omega e.2

theorem pow_add_omega (y z : Level) :
    pow omega (add y z) = mul (pow omega y) (pow omega z) := by
  apply ext
  exact Cnf.pow_add_omega y.2 z.2

theorem pow_add_ofNat {m : Nat} (hm : 0 < m) (y z : Nat) :
    pow (ofNat m) (ofNat (y + z)) =
      mul (pow (ofNat m) (ofNat y)) (pow (ofNat m) (ofNat z)) := by
  apply ext
  exact Cnf.pow_add_ofNat hm y z

theorem pow_add_finite {n : Nat} (hn : 0 < n) (y z : Level) :
    pow (ofNat n) (add y z) = mul (pow (ofNat n) y) (pow (ofNat n) z) := by
  apply ext
  exact Cnf.pow_add_finite hn y.2 z.2

theorem add_strict_right {x y z : Level} (h : y < z) : add x y < add x z :=
  Cnf.add_strict_right x.1 y.1 z.1 h

theorem add_mono_left {x y : Level} (z : Level) (h : x ≤ y) : add x z ≤ add y z :=
  Cnf.add_mono_left x.2 y.2 z.2 h

theorem le_add_left (x y : Level) : x ≤ add x y :=
  Cnf.le_add_left (y := y.1) x.2

theorem le_add_right (x y : Level) : y ≤ add x y :=
  Cnf.le_add_right x.2

end Level

/-! ## Closed level expressions -/

/-- A closed level expression: a numeral, `ω`, or a sum, product or power of closed
expressions. Its value is a normal notation below `ε₀`. -/
inductive ClosedLevel where
  | num : Nat → ClosedLevel
  | omega : ClosedLevel
  | add : ClosedLevel → ClosedLevel → ClosedLevel
  | mul : ClosedLevel → ClosedLevel → ClosedLevel
  | pow : ClosedLevel → ClosedLevel → ClosedLevel
  deriving DecidableEq, Repr

namespace ClosedLevel

/-- The level denoted by a closed expression. -/
def value : ClosedLevel → Level
  | .num n => Level.ofNat n
  | .omega => Level.omega
  | .add x y => Level.add (value x) (value y)
  | .mul x y => Level.mul (value x) (value y)
  | .pow x y => Level.pow (value x) (value y)

/-- The code of the value. It is computed from the expression. -/
def code (e : ClosedLevel) : List Nat := (value e).code

theorem one_add_omega : value (.add (.num 1) .omega) = value .omega := by decide

theorem two_mul_omega : value (.mul (.num 2) .omega) = value .omega := by decide

theorem omega_add_one :
    value (.add .omega (.num 1)) = Level.succ (value .omega) := by decide

theorem omega_mul_two :
    value (.mul .omega (.num 2)) = value (.add .omega .omega) := by decide

theorem omega_add_omega_sq :
    value (.add .omega (.pow .omega (.num 2))) = value (.pow .omega (.num 2)) := by decide

theorem two_pow_omega : value (.pow (.num 2) .omega) = value .omega := by decide

theorem omega_pow_two :
    value (.pow .omega (.num 2)) = value (.mul .omega .omega) := by decide

theorem omega_add_one_mul_two :
    value (.mul (.add .omega (.num 1)) (.num 2)) =
      value (.add (.mul .omega (.num 2)) (.num 1)) := by decide

theorem omega_add_one_ne :
    value (.add .omega (.num 1)) ≠ value (.add (.num 1) .omega) := by decide

theorem omega_mul_two_ne :
    value (.mul .omega (.num 2)) ≠ value (.mul (.num 2) .omega) := by decide

theorem omega_pow_two_ne :
    value (.pow .omega (.num 2)) ≠ value (.pow (.num 2) .omega) := by decide

theorem not_add_one_le_left :
    ¬ value (.add .omega (.num 1)) ≤ value .omega := by decide

theorem code_omega : code .omega = [1, 1, 0, 0, 0] := by decide

theorem code_omega_sq : code (.pow .omega (.num 2)) = [1, 2, 0, 0, 0] := by decide

theorem code_one_add_omega : code (.add (.num 1) .omega) = code .omega := by decide

end ClosedLevel

end Mettapedia.TypeTheory.UniverseLevel
