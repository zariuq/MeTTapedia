import Mettapedia.Logic.ASP.Driver

/-!
# Enumerating all stable models by blocking

The solver's transition system learns only nogoods that hold in every stable
model, so a found model cannot be excluded by a learned nogood. Enumeration
therefore blocks each found model by a constraint and solves again.

## Blocking constraints

A normal program has no integrity constraints, and over the program's own atoms a
model whose atoms are all true cannot be excluded. The blocked program
(`Program.blocked`) lives over `Option A`, with `none` as one fresh atom:

* every rule `a :- B` becomes `some a :- some B` (`Rule.lift`);
* each found model `M` adds `none :- some M, not none, not some b₁, …, not some bₖ`
  (`Program.blockRule`), where the `bᵢ` are the head atoms outside `M`.

The rule derives `none` exactly when the true head atoms are those of `M`, and
`none` can never hold, because the rule needs `not none`.

* **The stable models of the blocked program** (`Program.stable_blocked_iff`) are
  the images of the stable models of the program that are not among the found
  models, with `none` false.

## Enumeration

`Program.enumerate` solves the blocked program with the reference driver, adds
each model it returns to the blocked list, and stops at the first `unsat`. Its
fuel is one more than the number of sets of head atoms.

* **Exactly the stable models, each once** (`Program.enumerate_spec`): every listed
  model is stable, every stable model is listed, and no two listed models have
  the same atoms.
* **The last certificate** is accepted by the certificate checker of the blocked
  program: it certifies that there is no further stable model.
* The fuel never runs out (`Program.enumerate_ne_outOfFuel`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

universe u

variable {A : Type u}

/-- A rule over `Option A`: every atom `a` becomes `some a`. -/
def Rule.lift (r : Rule A) : Rule (Option A) := ⟨some r.head, r.pos.map some, r.neg.map some⟩

theorem Rule.lift_holds (r : Rule A) (I N : Set (Option A)) :
    r.lift.Holds I N ↔ r.Holds (some ⁻¹' I) (some ⁻¹' N) := by
  simp [Rule.lift, Rule.Holds]

section Enumeration

variable [DecidableEq A]

namespace Program

variable (P : Program A)

/-- **The constraint blocking `M`**: the fresh atom `none` follows exactly when the true head atoms
are those of `M`, and cannot hold. -/
def blockRule (M : List A) : Rule (Option A) :=
  ⟨none, M.map some, none :: (P.atomList.filter fun a => a ∉ M).map some⟩

/-- The program with the models `Ms` blocked. -/
def blocked (Ms : List (List A)) : Program (Option A) := P.map Rule.lift ++ Ms.map P.blockRule

theorem blockRule_holds {M : List A} {I N : Set (Option A)} :
    (P.blockRule M).Holds I N ↔ (∀ a ∈ M, some a ∈ I) ∧ none ∉ N ∧ ∀ a ∈ P.atomList, a ∉ M → some a ∉ N := by
  simp only [blockRule, Rule.Holds, List.mem_map, List.mem_cons, List.mem_filter, decide_eq_true_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · rintro ⟨pos, neg⟩
    refine ⟨pos, neg none (Or.inl rfl), fun a ha out => neg _ (Or.inr ⟨a, ⟨ha, out⟩, rfl⟩)⟩
  · rintro ⟨pos, none_out, out⟩
    refine ⟨pos, ?_⟩
    rintro b (rfl | ⟨a, ⟨ha, notIn⟩, rfl⟩)
    · exact none_out
    · exact out a ha notIn

theorem some_mem_step_blocked (Ms : List (List A)) (I N : Set (Option A)) (a : A) :
    some a ∈ (P.blocked Ms).step I N ↔ a ∈ P.step (some ⁻¹' I) (some ⁻¹' N) := by
  constructor
  · rintro ⟨r, hr, head, holds⟩
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      exact ⟨r₀, hr₀, Option.some.inj head, (r₀.lift_holds I N).mp holds⟩
    · obtain ⟨M, -, rfl⟩ := List.mem_map.mp hr
      cases head
  · rintro ⟨r, hr, rfl, holds⟩
    exact ⟨r.lift, List.mem_append_left _ (List.mem_map_of_mem hr), rfl, (r.lift_holds I N).mpr holds⟩

theorem none_mem_step_blocked (Ms : List (List A)) (I N : Set (Option A)) :
    none ∈ (P.blocked Ms).step I N ↔ ∃ M ∈ Ms, (P.blockRule M).Holds I N := by
  constructor
  · rintro ⟨r, hr, head, holds⟩
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r₀, -, rfl⟩ := List.mem_map.mp hr
      cases head
    · obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hr
      exact ⟨M, hM, holds⟩
  · rintro ⟨M, hM, holds⟩
    exact ⟨P.blockRule M, List.mem_append_right _ (List.mem_map_of_mem hM), rfl, holds⟩

/-- The `some` part of the reduct's least model is the least model of the program's reduct. -/
theorem preimage_glOp_blocked (Ms : List (List A)) (N : Set (Option A)) :
    some ⁻¹' ((P.blocked Ms).glOp N) = P.glOp (some ⁻¹' N) := by
  apply le_antisymm
  · set T : Set (Option A) := {x | ∀ a, x = some a → a ∈ P.glOp (some ⁻¹' N)} with hT
    have preT : some ⁻¹' T = P.glOp (some ⁻¹' N) := by
      ext a
      simp only [Set.mem_preimage, hT, Set.mem_ofPred_eq, Option.some.injEq, forall_eq']
    have closed : (P.blocked Ms).glOp N ⊆ T := by
      apply OrderHom.lfp_le
      intro x hx a ha
      subst ha
      have := (P.some_mem_step_blocked Ms T N a).mp hx
      rw [preT, P.glOp_fixed] at this
      exact this
    intro a ha
    exact closed ha a rfl
  · apply OrderHom.lfp_le
    intro a ha
    have := (P.some_mem_step_blocked Ms ((P.blocked Ms).glOp N) N a).mpr ha
    rw [(P.blocked Ms).glOp_fixed] at this
    exact this

theorem none_mem_glOp_blocked (Ms : List (List A)) (N : Set (Option A)) :
    none ∈ (P.blocked Ms).glOp N ↔ ∃ M ∈ Ms, (P.blockRule M).Holds ((P.blocked Ms).glOp N) N := by
  rw [← P.none_mem_step_blocked, (P.blocked Ms).glOp_fixed]

/-- A blocking constraint holds at a stable model of the program only for that model. -/
theorem eq_of_blockRule_holds {Ms : List (List A)} {N : Set (Option A)} (stable : P.Stable (some ⁻¹' N))
    {M : List A} (holds : (P.blockRule M).Holds ((P.blocked Ms).glOp N) N) : some ⁻¹' N = ↑M.toFinset := by
  rw [blockRule_holds] at holds
  obtain ⟨pos, -, out⟩ := holds
  ext a
  simp only [Set.mem_preimage, List.coe_toFinset, Set.mem_ofPred_eq]
  constructor
  · intro ha
    by_contra notIn
    have head : a ∈ P.atomList := (P.mem_atomList).mpr (Stable.subset_headSet P stable ha)
    exact out a head notIn ha
  · intro ha
    have := pos a ha
    rw [← Set.mem_preimage, P.preimage_glOp_blocked, ← stable] at this
    exact this

/-- **The stable models of the blocked program** are the stable models of the program, outside the
blocked ones, with the fresh atom false. -/
theorem stable_blocked_iff (Ms : List (List A)) (N : Set (Option A)) :
    (P.blocked Ms).Stable N ↔ none ∉ N ∧ P.Stable (some ⁻¹' N) ∧ ∀ M ∈ Ms, some ⁻¹' N ≠ ↑M.toFinset := by
  constructor
  · intro stable
    have noneOut : none ∉ N := by
      intro hN
      have inGl : none ∈ (P.blocked Ms).glOp N := stable ▸ hN
      obtain ⟨M, -, holds⟩ := (P.none_mem_glOp_blocked Ms N).mp inGl
      exact ((P.blockRule_holds).mp holds).2.1 hN
    have stableP : P.Stable (some ⁻¹' N) := by
      unfold Stable
      rw [← P.preimage_glOp_blocked Ms, ← stable]
    refine ⟨noneOut, stableP, fun M hM same => noneOut ?_⟩
    have holds : (P.blockRule M).Holds ((P.blocked Ms).glOp N) N := by
      rw [← stable, P.blockRule_holds]
      refine ⟨fun a ha => ?_, noneOut, fun a _ notIn hN => notIn ?_⟩
      · have : a ∈ some ⁻¹' N := by rw [same]; simpa using ha
        exact this
      · have : a ∈ some ⁻¹' N := hN
        rw [same] at this
        simpa using this
    have := (P.none_mem_glOp_blocked Ms N).mpr ⟨M, hM, holds⟩
    rwa [← stable] at this
  · rintro ⟨noneOut, stableP, free⟩
    unfold Stable
    ext x
    cases x with
    | none =>
      refine ⟨fun h => absurd h noneOut, fun h => ?_⟩
      obtain ⟨M, hM, holds⟩ := (P.none_mem_glOp_blocked Ms N).mp h
      exact absurd (P.eq_of_blockRule_holds stableP holds) (free M hM)
    | some a =>
      change a ∈ some ⁻¹' N ↔ a ∈ some ⁻¹' ((P.blocked Ms).glOp N)
      rw [P.preimage_glOp_blocked, ← stableP]

theorem preimage_coe_toFinset (M : List (Option A)) :
    some ⁻¹' (↑M.toFinset : Set (Option A)) = ↑(M.filterMap id).toFinset := by
  ext a
  simp

/-! ## Enumeration -/

/-- What enumeration returns: the models found and the certificate that there is no other, or
nothing when the fuel runs out. -/
inductive Enumeration (A : Type u)
  | done (models : List (List A)) (certificate : List CertStep)
  | outOfFuel

/-- The models of an enumeration, if it finished. -/
def Enumeration.models? {A : Type u} : Enumeration A → Option (List (List A))
  | .done Ms _ => some Ms
  | .outOfFuel => none

/-- The final certificate of an enumeration, if it finished. -/
def Enumeration.certificate? {A : Type u} : Enumeration A → Option (List CertStep)
  | .done _ cert => some cert
  | .outOfFuel => none

/-- **Enumeration by blocking**, at most `n` more solver calls. -/
def enumerateFuel : ℕ → List (List A) → Enumeration A
  | 0, _ => .outOfFuel
  | n + 1, Ms =>
    match (P.blocked Ms).solve with
    | .sat M => enumerateFuel n (Ms ++ [M.filterMap id])
    | .unsat cert => .done Ms cert
    | .outOfFuel => .outOfFuel

/-- **All stable models**, each once. -/
def enumerate : Enumeration A := P.enumerateFuel (2 ^ P.atomList.length + 1) []

/-- What enumeration establishes. -/
def EnumOK : Enumeration A → Prop
  | .done Ms cert => (∀ M ∈ Ms, P.Stable ↑M.toFinset) ∧ (∀ S, P.Stable S → ∃ M ∈ Ms, ↑M.toFinset = S) ∧
      (Ms.map List.toFinset).Nodup ∧ (P.blocked Ms).checkCert cert = true
  | .outOfFuel => False

theorem heads_card : P.heads.card = P.atomList.length := by
  rw [heads, List.card_toFinset]
  rfl

/-- Distinct stable models are at most as many as the sets of head atoms. -/
theorem length_le_of_stable {Ms : List (List A)} (stable : ∀ M ∈ Ms, P.Stable ↑M.toFinset)
    (nodup : (Ms.map List.toFinset).Nodup) : Ms.length ≤ 2 ^ P.atomList.length := by
  have card := List.toFinset_card_of_nodup nodup
  rw [List.length_map] at card
  rw [← card, ← P.heads_card, ← Finset.card_powerset]
  apply Finset.card_le_card
  intro F hF
  obtain ⟨M, hM, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hF)
  rw [Finset.mem_powerset]
  intro a ha
  have := Stable.subset_headSet P (stable M hM) (show a ∈ (↑M.toFinset : Set A) from ha)
  rw [← P.coe_heads] at this
  exact this

theorem enumerateFuel_spec : ∀ (n : ℕ) (Ms : List (List A)), (∀ M ∈ Ms, P.Stable ↑M.toFinset) →
    (Ms.map List.toFinset).Nodup → 2 ^ P.atomList.length - Ms.length < n → P.EnumOK (P.enumerateFuel n Ms)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, Ms, stable, nodup, fuel => by
    unfold enumerateFuel
    cases h : (P.blocked Ms).solve with
    | sat M' =>
      dsimp only
      have stableQ := (P.blocked Ms).solve_sat_stable h
      rw [stable_blocked_iff, preimage_coe_toFinset] at stableQ
      obtain ⟨-, stableM, free⟩ := stableQ
      have stable' : ∀ M ∈ Ms ++ [M'.filterMap id], P.Stable ↑M.toFinset := by
        intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · exact stable M hM
        · rw [List.mem_singleton.mp hM]
          exact stableM
      have nodup' : ((Ms ++ [M'.filterMap id]).map List.toFinset).Nodup := by
        rw [List.map_append, List.map_singleton]
        refine List.nodup_append.mpr ⟨nodup, List.nodup_singleton _, ?_⟩
        intro F hF G hG same
        obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hF
        rw [List.mem_singleton] at hG
        subst hG
        exact free M hM (by rw [same])
      have bound := P.length_le_of_stable stable' nodup'
      rw [List.length_append, List.length_singleton] at bound
      exact enumerateFuel_spec n _ stable' nodup' (by rw [List.length_append, List.length_singleton]; omega)
    | unsat cert =>
      refine ⟨stable, fun S stableS => ?_, nodup, (P.blocked Ms).solve_unsat_accepted h⟩
      by_contra none
      push Not at none
      apply (P.blocked Ms).solve_unsat_no_stable h (some '' S)
      rw [stable_blocked_iff, Set.preimage_image_eq _ (Option.some_injective A)]
      refine ⟨by simp, stableS, fun M hM same => none M hM same.symm⟩
    | outOfFuel => exact absurd h (P.blocked Ms).solve_ne_outOfFuel

/-- **Enumeration is correct.** -/
theorem enumerate_spec : P.EnumOK P.enumerate :=
  P.enumerateFuel_spec _ [] (fun _ h => absurd h List.not_mem_nil) List.nodup_nil (by simp)

theorem enumerate_ne_outOfFuel : P.enumerate ≠ .outOfFuel := by
  intro h
  have := P.enumerate_spec
  rw [h] at this
  exact this

/-- **The listed models are exactly the stable models, each once.** -/
theorem enumerate_models {Ms : List (List A)} {cert : List CertStep} (h : P.enumerate = .done Ms cert) :
    (∀ S, P.Stable S ↔ ∃ M ∈ Ms, ↑M.toFinset = S) ∧ (Ms.map List.toFinset).Nodup := by
  have := P.enumerate_spec
  rw [h] at this
  obtain ⟨stable, complete, nodup, -⟩ := this
  refine ⟨fun S => ⟨complete S, ?_⟩, nodup⟩
  rintro ⟨M, hM, rfl⟩
  exact stable M hM

end Program

end Enumeration

end Mettapedia.Logic.ASP
