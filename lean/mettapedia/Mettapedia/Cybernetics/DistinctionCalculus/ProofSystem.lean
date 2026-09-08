import Mettapedia.Cybernetics.DistinctionCalculus.Basic

/-!
# Proof objects for the metric-completion fragment

An upper distance bound is derived from authored edges, reflexivity, the unit
bound, symmetry, capped triangle composition, and weakening. Raw proof objects
contain no proof fields. Their total checker verifies junctions and weakening
bounds, and is sound and complete for the separately defined derivation
relation. Soundness is also proved against every metric tolerance extending
the authored similarity. For a nonmetric seed, this is NOT truth in the seed.
Rejection of a certificate does not establish the negation of its claim.

This presents the path-inference part of Goertzel's distinction calculus,
Sections 2.3 and 8.4. It does not claim semantic completeness for all real
observer models or implement the calculus's statistical and analytic parts.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus

universe u

structure Claim (V : Type u) where
  source : V
  target : V
  bound : ℚ
  deriving DecidableEq

inductive Certificate (V : Type u) where
  | edge (source target : V)
  | refl (source : V)
  | unitBound (source target : V)
  | symm (proof : Certificate V)
  | triangle (first second : Certificate V)
  | weaken (bound : ℚ) (proof : Certificate V)

/-- A declarative relation independent of the checker implementation. -/
inductive Derives {V : Type u} (a : Tolerance V) : Claim V → Prop where
  | edge (x y : V) : Derives a ⟨x, y, a.distance x y⟩
  | refl (x : V) : Derives a ⟨x, x, 0⟩
  | unitBound (x y : V) : Derives a ⟨x, y, 1⟩
  | symm {x y : V} {r : ℚ} : Derives a ⟨x, y, r⟩ → Derives a ⟨y, x, r⟩
  | triangle {x y z : V} {r s : ℚ} :
      Derives a ⟨x, y, r⟩ → Derives a ⟨y, z, s⟩ →
      Derives a ⟨x, z, min 1 (r + s)⟩
  | weaken {x y : V} {r s : ℚ} :
      Derives a ⟨x, y, r⟩ → r ≤ s → Derives a ⟨x, y, s⟩

def infer {V : Type u} [DecidableEq V] (a : Tolerance V) : Certificate V → Option (Claim V)
  | .edge x y => some ⟨x, y, a.distance x y⟩
  | .refl x => some ⟨x, x, 0⟩
  | .unitBound x y => some ⟨x, y, 1⟩
  | .symm proof => (infer a proof).map fun c => ⟨c.target, c.source, c.bound⟩
  | .triangle first second =>
      match infer a first, infer a second with
      | some c, some d =>
          if c.target = d.source then some ⟨c.source, d.target, min 1 (c.bound + d.bound)⟩
          else none
      | _, _ => none
  | .weaken bound proof =>
      match infer a proof with
      | some c => if c.bound ≤ bound then some ⟨c.source, c.target, bound⟩ else none
      | none => none

/-- A receipt must establish the exact requested endpoints and bound. -/
def check {V : Type u} [DecidableEq V] (a : Tolerance V)
    (requested : Claim V) (proof : Certificate V) : Bool :=
  decide (infer a proof = some requested)

theorem infer_derives {V : Type u} [DecidableEq V] (a : Tolerance V)
    (proof : Certificate V) {claim : Claim V} (accepted : infer a proof = some claim) :
    Derives a claim := by
  induction proof generalizing claim with
  | edge x y =>
      simp only [infer, Option.some.injEq] at accepted
      subst claim
      exact .edge x y
  | refl x =>
      simp only [infer, Option.some.injEq] at accepted
      subst claim
      exact .refl x
  | unitBound x y =>
      simp only [infer, Option.some.injEq] at accepted
      subst claim
      exact .unitBound x y
  | symm proof ih =>
      cases h : infer a proof with
      | none => simp [infer, h] at accepted
      | some c =>
          have equal : ⟨c.target, c.source, c.bound⟩ = claim := by simpa [infer, h] using accepted
          subst claim
          exact .symm (ih h)
  | triangle first second ihFirst ihSecond =>
      cases hFirst : infer a first with
      | none => simp [infer, hFirst] at accepted
      | some c =>
          cases hSecond : infer a second with
          | none => simp [infer, hFirst, hSecond] at accepted
          | some d =>
              by_cases join : c.target = d.source
              · have equal : ⟨c.source, d.target, min 1 (c.bound + d.bound)⟩ = claim := by
                  simpa [infer, hFirst, hSecond, join] using accepted
                subst claim
                have left := ihFirst hFirst
                have right := ihSecond hSecond
                cases c with
                | mk x y r =>
                    cases d with
                    | mk y' z s =>
                        dsimp at join
                        subst y'
                        exact .triangle left right
              · simp [infer, hFirst, hSecond, join] at accepted
  | weaken bound proof ih =>
      cases h : infer a proof with
      | none => simp [infer, h] at accepted
      | some c =>
          by_cases monotoneBound : c.bound ≤ bound
          · have equal : ⟨c.source, c.target, bound⟩ = claim := by
              simpa [infer, h, monotoneBound] using accepted
            subst claim
            exact .weaken (ih h) monotoneBound
          · simp [infer, h, monotoneBound] at accepted

theorem derives_has_certificate {V : Type u} [DecidableEq V] {a : Tolerance V}
    {claim : Claim V} (derivation : Derives a claim) :
    ∃ proof, infer a proof = some claim := by
  induction derivation with
  | edge x y => exact ⟨.edge x y, rfl⟩
  | refl x => exact ⟨.refl x, rfl⟩
  | unitBound x y => exact ⟨.unitBound x y, rfl⟩
  | symm _ ih =>
      obtain ⟨proof, h⟩ := ih
      exact ⟨.symm proof, by simp [infer, h]⟩
  | triangle _ _ ihFirst ihSecond =>
      obtain ⟨first, hFirst⟩ := ihFirst
      obtain ⟨second, hSecond⟩ := ihSecond
      exact ⟨.triangle first second, by simp [infer, hFirst, hSecond]⟩
  | @weaken x y r s _ bound ih =>
      obtain ⟨proof, h⟩ := ih
      exact ⟨.weaken s proof, by simp [infer, h, bound]⟩

theorem derives_iff_checked {V : Type u} [DecidableEq V]
    (a : Tolerance V) (claim : Claim V) :
    Derives a claim ↔ ∃ proof, check a claim proof = true := by
  simp only [check, decide_eq_true_eq]
  exact ⟨derives_has_certificate, fun ⟨proof, accepted⟩ => infer_derives a proof accepted⟩

/-- Semantic soundness ranges over independently supplied coherent models. -/
theorem Derives.sound {V : Type u} {a : Tolerance V} {claim : Claim V}
    (derivation : Derives a claim) (model : Tolerance V)
    (metric : model.Metric) (hExt : a.Extends model) :
    model.distance claim.source claim.target ≤ claim.bound := by
  induction derivation with
  | edge x y => exact Tolerance.distance_le_of_extends hExt x y
  | refl x => simp
  | unitBound x y => exact model.distance_bounded x y
  | symm _ ih => simpa only [model.distance_symm] using ih
  | triangle _ _ left right =>
      exact le_min (model.distance_bounded _ _)
        (le_trans (metric _ _ _) (add_le_add left right))
  | weaken _ bound ih => exact le_trans ih bound

theorem check_sound {V : Type u} [DecidableEq V] {a : Tolerance V}
    {claim : Claim V} {proof : Certificate V} (accepted : check a claim proof = true)
    (model : Tolerance V) (metric : model.Metric) (hExt : a.Extends model) :
    model.distance claim.source claim.target ≤ claim.bound :=
  (infer_derives a proof (of_decide_eq_true accepted)).sound model metric hExt

/-- Only a coherent seed licenses reading every checked bound in that seed. -/
theorem check_sound_in_seed {V : Type u} [DecidableEq V] {a : Tolerance V}
    (metric : a.Metric) {claim : Claim V} {proof : Certificate V}
    (accepted : check a claim proof = true) :
    a.distance claim.source claim.target ≤ claim.bound :=
  check_sound accepted a metric (fun _ _ => le_rfl)

/-- Capped distance addition is exactly the Lukasiewicz similarity product. -/
theorem capped_distance_complement (a b : ℚ) :
    1 - min 1 ((1 - a) + (1 - b)) = max 0 (a + b - 1) := by
  by_cases bound : (1 : ℚ) ≤ (1 - a) + (1 - b)
  · rw [min_eq_left bound, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right (le_of_not_ge bound), max_eq_right (by linarith)]
    ring

/-- The paper's similarity inference follows from the distance proof rule. -/
theorem two_edge_similarity_sound {V : Type u} (base model : Tolerance V)
    (metric : model.Metric) (hExt : base.Extends model) (x y z : V) :
    max 0 (base.similarity x y + base.similarity y z - 1) ≤ model.similarity x z := by
  have first : Derives base ⟨x, y, base.distance x y⟩ := .edge x y
  have second : Derives base ⟨y, z, base.distance y z⟩ := .edge y z
  have bound := (Derives.triangle first second).sound model metric hExt
  dsimp [Tolerance.distance] at bound
  rw [← capped_distance_complement]
  linarith

end Mettapedia.Cybernetics.DistinctionCalculus
