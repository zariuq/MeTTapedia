-- SPDX-License-Identifier: Apache-2.0
import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingTransport

/-!
# Unification completeness: satisfiable equation systems have Robinson unifiers

The soundness direction — a successful `Metta.Unify.unifyRounds` yields a common
valuation — is established in `LeaTTaBindingTransport` / `LeaTTaMatcherCongruence`
(`exists_unifyRounds_equations_satisfied_empty`, `decomposeEq_solution_iff`, …).

This file proves the converse **completeness** direction: whenever a
host-float-free equation worklist is satisfied by a common valuation,
`unifyRounds` returns `some`.

Three semantic facts drive it, each a thing a common valuation forbids Robinson:

* **no clash** (§1) — `decomposeAll` never returns `none` (a symbol / arity
  mismatch would contradict `applyClassSolution`-equality);
* **no occurs-cycle** (§2) — the occurs-check never fires (a proper
  self-occurrence would make one side strictly larger under the valuation);
* **enough fuel** (§3) — the number of elimination rounds is bounded by the
  number of distinct variables (`eqVars_step_card`), dominated by the structural
  term size.

All three layers are established here, together with the concrete `equationFuel`
/ `reconcileAll` / `wholeBindingReconciliation` / `unifyValues` success
corollaries (§4–§5) and the positive nested-expression and negative
occurs-cycle / insufficient-fuel oracles (§6).

Scope, precisely: this is a **semantic/fuel certificate about Robinson
unification only**.  A successful run is *not* by itself an original HE
`MatchRel` or a live `MergeRel`, and nothing here discharges
`HESatisfiedMatcherMergeRelExists` — that operational keystone is constructed
elsewhere, and consumes this file as a lower-layer input.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Metta
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

/-! ## §1  No clash: a satisfiable equation decomposes -/

/-- A single host-float-free equation satisfied by a common valuation never
clashes: structural decomposition returns `some`.  Mirrors the case structure of
`decomposeEq_solution_iff`, but establishes existence rather than the solution
equivalence. -/
theorem decomposeEq_isSome_of_satisfied
    (valuation : String → Metta.Atom) :
    ∀ (left right : Metta.Atom),
      MettaAtomNoFloat left → MettaAtomNoFloat right →
      MettaEquationSatisfied valuation (left, right) →
      ∃ constraints, Metta.Unify.decomposeEq left right = some constraints := by
  intro left
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ left
  · -- left = sym symbol
    intro symbol right _hleft _hright hsat
    cases right with
    | sym other =>
        have hso : symbol = other := by
          simpa [MettaEquationSatisfied, applyClassSolution] using hsat
        exact ⟨[], by simp [Metta.Unify.decomposeEq, hso]⟩
    | var v => exact ⟨[(v, Metta.Atom.sym symbol)], by simp [Metta.Unify.decomposeEq]⟩
    | gnd g => exact absurd hsat (by simp [MettaEquationSatisfied, applyClassSolution])
    | expr atoms =>
        exact absurd hsat (by simp [MettaEquationSatisfied, applyClassSolution])
  · -- left = var v: `decomposeEq (var v) _` is always `some`
    intro v right _hleft _hright _hsat
    cases right with
    | var w =>
        by_cases hvw : v = w
        · exact ⟨[], by simp [Metta.Unify.decomposeEq, hvw]⟩
        · exact ⟨[(v, Metta.Atom.var w)], by simp [Metta.Unify.decomposeEq, hvw]⟩
    | sym s => exact ⟨[(v, Metta.Atom.sym s)], by simp [Metta.Unify.decomposeEq]⟩
    | gnd g => exact ⟨[(v, Metta.Atom.gnd g)], by simp [Metta.Unify.decomposeEq]⟩
    | expr a => exact ⟨[(v, Metta.Atom.expr a)], by simp [Metta.Unify.decomposeEq]⟩
  · -- left = gnd g
    intro g right hleft hright hsat
    cases right with
    | sym s => exact absurd hsat (by simp [MettaEquationSatisfied, applyClassSolution])
    | var w => exact ⟨[(w, Metta.Atom.gnd g)], by simp [Metta.Unify.decomposeEq]⟩
    | gnd other =>
        have hgo : g = other := by
          have hthis := hsat
          simp only [MettaEquationSatisfied, applyClassSolution] at hthis
          exact Metta.Atom.gnd.inj hthis
        subst hgo
        have hequivRefl : Metta.Ground.equiv g g = true := by
          cases g <;>
            simp_all [Metta.Ground.equiv, Metta.Ground.beq,
              MettaAtomNoFloat, storedBindings_beq_self_noFloat]
        exact ⟨[], by simp [Metta.Unify.decomposeEq, hequivRefl]⟩
    | expr atoms =>
        exact absurd hsat (by simp [MettaEquationSatisfied, applyClassSolution])
  · -- left = expr atoms
    intro atoms ih right hleft hright hsat
    cases right with
    | sym s => exact absurd hsat (by simp [MettaEquationSatisfied, applyClassSolution])
    | gnd g => exact absurd hsat (by simp [MettaEquationSatisfied, applyClassSolution])
    | var w => exact ⟨[(w, Metta.Atom.expr atoms)], by simp [Metta.Unify.decomposeEq]⟩
    | expr rights =>
        -- lists are pointwise satisfied, so `decomposeList` succeeds
        have hlistSat : MettaAtomListsSatisfied valuation atoms rights := by
          have := hsat
          simp only [MettaEquationSatisfied, applyClassSolution] at this
          simpa [MettaAtomListsSatisfied] using this
        have hleftChildren : ∀ atom ∈ atoms, MettaAtomNoFloat atom := by
          simpa [MettaAtomNoFloat] using hleft
        have hrightChildren : ∀ atom ∈ rights, MettaAtomNoFloat atom := by
          simpa [MettaAtomNoFloat] using hright
        have hlist : ∀ (lefts rights : List Metta.Atom),
            (∀ atom ∈ lefts, atom ∈ atoms) →
            (∀ atom ∈ lefts, MettaAtomNoFloat atom) →
            (∀ atom ∈ rights, MettaAtomNoFloat atom) →
            MettaAtomListsSatisfied valuation lefts rights →
            ∃ constraints,
              Metta.Unify.decomposeList lefts rights = some constraints := by
          intro lefts
          induction lefts with
          | nil =>
              intro rights _ _ _ hsatList
              cases rights with
              | nil => exact ⟨[], by simp [Metta.Unify.decomposeList]⟩
              | cons rHead rTail =>
                  simp [MettaAtomListsSatisfied] at hsatList
          | cons head tail ihTail =>
              intro rights hsubset hlefts hrights hsatList
              cases rights with
              | nil => simp [MettaAtomListsSatisfied] at hsatList
              | cons rHead rTail =>
                  have hcons := hsatList
                  simp only [MettaAtomListsSatisfied, List.map_cons,
                    List.cons.injEq] at hcons
                  have hsatHead : MettaEquationSatisfied valuation (head, rHead) := by
                    simpa [MettaEquationSatisfied] using hcons.1
                  have hsatTail : MettaAtomListsSatisfied valuation tail rTail := by
                    simpa [MettaAtomListsSatisfied] using hcons.2
                  obtain ⟨headConstraints, hhead⟩ :=
                    ih head (hsubset head (by simp)) rHead
                      (hlefts head (by simp)) (hrights rHead (by simp)) hsatHead
                  obtain ⟨tailConstraints, htail⟩ :=
                    ihTail rTail
                      (fun atom hmem => hsubset atom (by simp [hmem]))
                      (fun atom hmem => hlefts atom (by simp [hmem]))
                      (fun atom hmem => hrights atom (by simp [hmem])) hsatTail
                  exact ⟨headConstraints ++ tailConstraints, by
                    simp [Metta.Unify.decomposeList, hhead, htail]⟩
        obtain ⟨constraints, hconstraints⟩ :=
          hlist atoms rights (fun atom hmem => hmem)
            hleftChildren hrightChildren hlistSat
        exact ⟨constraints, by simp [Metta.Unify.decomposeEq, hconstraints]⟩

/-- A satisfiable host-float-free worklist decomposes without clashing. -/
theorem decomposeAll_isSome_of_satisfied
    {valuation : String → Metta.Atom} :
    ∀ (equations : List (Metta.Atom × Metta.Atom)),
      (∀ eq ∈ equations, MettaAtomNoFloat eq.1 ∧ MettaAtomNoFloat eq.2) →
      MettaEquationsSatisfied valuation equations →
      ∃ constraints, Metta.Unify.decomposeAll equations = some constraints := by
  intro equations
  induction equations with
  | nil => intro _ _; exact ⟨[], by simp [Metta.Unify.decomposeAll]⟩
  | cons head tail ih =>
      obtain ⟨a, b⟩ := head
      intro hnoFloat hsat
      obtain ⟨headC, hhead⟩ :=
        decomposeEq_isSome_of_satisfied valuation a b
          (hnoFloat (a, b) (by simp)).1 (hnoFloat (a, b) (by simp)).2
          (hsat (a, b) (by simp))
      obtain ⟨tailC, htail⟩ :=
        ih (fun eq hmem => hnoFloat eq (by simp [hmem]))
          (fun eq hmem => hsat eq (by simp [hmem]))
      exact ⟨headC ++ tailC, by simp [Metta.Unify.decomposeAll, hhead, htail]⟩

/-! ## §2  No occurs-cycle: satisfaction forbids the occurs-check firing -/

/-- A satisfied constraint `x ↦ t` (with `t` not the trivial `$x` itself) never
triggers the occurs-check: if `$x` occurred properly in `t`, the valuation would
make one side strictly larger than the other. -/
theorem occurs_eq_false_of_constraint_satisfied
    {valuation : String → Metta.Atom} {x : String} {t : Metta.Atom}
    (hsat : valuation x = applyClassSolution valuation t)
    (hne : t ≠ Metta.Atom.var x) :
    Metta.Subst.occurs x t = false := by
  rw [← Bool.not_eq_true]
  intro hocc
  have hmem : x ∈ t.vars := by
    by_contra hnm
    rw [occurs_eq_false_of_not_mem_vars x t hnm] at hocc
    exact absurd hocc (by simp)
  cases t with
  | sym s => simp [Metta.Atom.vars] at hmem
  | gnd g => simp [Metta.Atom.vars] at hmem
  | var y =>
      simp only [Metta.Atom.vars, List.mem_singleton] at hmem
      exact hne (by rw [hmem])
  | expr xs =>
      simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map] at hmem
      obtain ⟨ys, ⟨a, ha, rfl⟩, hxa⟩ := hmem
      have hle := size_applyClassSolution_ge_of_mem_vars valuation x a hxa
      have hmemSize : Metta.Atom.size (applyClassSolution valuation a) ∈
          (xs.map (applyClassSolution valuation)).map Metta.Atom.size :=
        List.mem_map.mpr
          ⟨applyClassSolution valuation a, List.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩
      have hsum : Metta.Atom.size (applyClassSolution valuation a) ≤
          ((xs.map (applyClassSolution valuation)).map Metta.Atom.size).sum :=
        List.single_le_sum (by intro _ _; exact Nat.zero_le _) _ hmemSize
      have hexpr : Metta.Atom.size (applyClassSolution valuation (Metta.Atom.expr xs)) =
          1 + ((xs.map (applyClassSolution valuation)).map Metta.Atom.size).sum := by
        simp [applyClassSolution, Metta.Atom.size]
      have hsize : Metta.Atom.size (valuation x) =
          Metta.Atom.size (applyClassSolution valuation (Metta.Atom.expr xs)) :=
        congrArg Metta.Atom.size hsat
      omega

/-! ## §3  Fuel adequacy: the elimination round count is bounded by the variables -/

/-- The variables occurring anywhere in an equation worklist. -/
def eqVars (eqs : List (Metta.Atom × Metta.Atom)) : Finset String :=
  (eqs.flatMap fun e => e.1.vars ++ e.2.vars).toFinset

/-- The variables occurring anywhere in a decomposed constraint list (the
constraint key plus the target's variables). -/
def cVars (c : List (String × Metta.Atom)) : Finset String :=
  (c.flatMap fun p => p.1 :: p.2.vars).toFinset

theorem mem_eqVars {eqs : List (Metta.Atom × Metta.Atom)} {v : String} :
    v ∈ eqVars eqs ↔ ∃ e ∈ eqs, v ∈ e.1.vars ∨ v ∈ e.2.vars := by
  simp [eqVars, List.mem_flatMap]

theorem mem_cVars {c : List (String × Metta.Atom)} {v : String} :
    v ∈ cVars c ↔ ∃ p ∈ c, v = p.1 ∨ v ∈ p.2.vars := by
  simp [cVars, List.mem_flatMap]

/-- Structural decomposition introduces no new variables: every variable of the
resulting constraints already occurred in the two decomposed atoms. -/
theorem decomposeEq_cVars_subset :
    ∀ (a b : Metta.Atom) (c : List (String × Metta.Atom)),
      Metta.Unify.decomposeEq a b = some c →
      cVars c ⊆ a.vars.toFinset ∪ b.vars.toFinset := by
  intro a
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ a
  · intro s b c hdec
    cases b with
    | sym o =>
        by_cases h : s = o
        · subst h; simp [Metta.Unify.decomposeEq] at hdec
          subst hdec; simp [cVars]
        · simp [Metta.Unify.decomposeEq, h] at hdec
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        intro w hw
        rw [mem_cVars] at hw
        obtain ⟨p, hp, hcase⟩ := hw
        simp only [List.mem_singleton] at hp; subst hp
        rcases hcase with h | h
        · subst h; simp [Metta.Atom.vars]
        · simp [Metta.Atom.vars] at h
    | gnd g => simp [Metta.Unify.decomposeEq] at hdec
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdec
  · intro v b c hdec w hw
    rw [mem_cVars] at hw
    obtain ⟨p, hp, hcase⟩ := hw
    cases b with
    | var y =>
        by_cases h : v = y
        · subst h; simp [Metta.Unify.decomposeEq] at hdec
          subst hdec; simp at hp
        · simp [Metta.Unify.decomposeEq, h] at hdec; subst hdec
          simp only [List.mem_singleton] at hp; subst hp
          rcases hcase with h2 | h2
          · subst h2; simp [Metta.Atom.vars]
          · simp [Metta.Atom.vars] at h2; subst h2; simp [Metta.Atom.vars]
    | sym s =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp
        rcases hcase with h2 | h2
        · subst h2; simp [Metta.Atom.vars]
        · simp [Metta.Atom.vars] at h2
    | gnd g =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp
        rcases hcase with h2 | h2
        · subst h2; simp [Metta.Atom.vars]
        · simp [Metta.Atom.vars] at h2
    | expr atoms =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp
        rcases hcase with h2 | h2
        · subst h2; simp [Metta.Atom.vars]
        · simp only [Finset.mem_union, List.mem_toFinset]
          exact Or.inr h2
  · intro g b c hdec
    cases b with
    | sym s => simp [Metta.Unify.decomposeEq] at hdec
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        intro w hw
        rw [mem_cVars] at hw
        obtain ⟨p, hp, hcase⟩ := hw
        simp only [List.mem_singleton] at hp; subst hp
        rcases hcase with h | h
        · subst h; simp [Metta.Atom.vars]
        · simp [Metta.Atom.vars] at h
    | gnd o =>
        by_cases h : Metta.Ground.equiv g o = true
        · simp [Metta.Unify.decomposeEq, h] at hdec
          subst hdec; simp [cVars]
        · simp [Metta.Unify.decomposeEq, h] at hdec
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdec
  · intro atoms ih b c hdec
    cases b with
    | sym s => simp [Metta.Unify.decomposeEq] at hdec
    | gnd g => simp [Metta.Unify.decomposeEq] at hdec
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        intro w hw
        rw [mem_cVars] at hw
        obtain ⟨p, hp, hcase⟩ := hw
        simp only [List.mem_singleton] at hp; subst hp
        rcases hcase with h | h
        · subst h; simp [Metta.Atom.vars]
        · simp only [Finset.mem_union, List.mem_toFinset]
          exact Or.inl h
    | expr rights =>
        simp only [Metta.Unify.decomposeEq] at hdec
        -- decomposeList atoms rights = some c
        have hlist : ∀ (lefts rights : List Metta.Atom)
            (c : List (String × Metta.Atom)),
            (∀ atom ∈ lefts, atom ∈ atoms) →
            Metta.Unify.decomposeList lefts rights = some c →
            cVars c ⊆ (lefts.flatMap Metta.Atom.vars).toFinset ∪
              (rights.flatMap Metta.Atom.vars).toFinset := by
          intro lefts
          induction lefts with
          | nil =>
              intro rights c _ hdec
              cases rights with
              | nil =>
                  simp [Metta.Unify.decomposeList] at hdec
                  subst hdec; simp [cVars]
              | cons rHead rTail => simp [Metta.Unify.decomposeList] at hdec
          | cons head tail ihTail =>
              intro rights c hsubset hdec
              cases rights with
              | nil => simp [Metta.Unify.decomposeList] at hdec
              | cons rHead rTail =>
                  cases hh : Metta.Unify.decomposeEq head rHead with
                  | none => simp [Metta.Unify.decomposeList, hh] at hdec
                  | some c1 =>
                      cases ht : Metta.Unify.decomposeList tail rTail with
                      | none =>
                          simp [Metta.Unify.decomposeList, hh, ht] at hdec
                      | some c2 =>
                          simp [Metta.Unify.decomposeList, hh, ht] at hdec
                          subst hdec
                          have h1 := ih head (hsubset head (by simp)) rHead c1 hh
                          have h2 := ihTail rTail c2
                            (fun a ha => hsubset a (by simp [ha])) ht
                          intro w hw
                          rw [mem_cVars] at hw
                          obtain ⟨p, hp, hcase⟩ := hw
                          simp only [List.mem_append] at hp
                          rcases hp with hp | hp
                          · have := h1 (mem_cVars.mpr ⟨p, hp, hcase⟩)
                            simp only [Finset.mem_union, List.mem_toFinset,
                              List.mem_flatMap] at this ⊢
                            rcases this with hl | hr
                            · exact Or.inl ⟨head, by simp, hl⟩
                            · exact Or.inr ⟨rHead, by simp, hr⟩
                          · have := h2 (mem_cVars.mpr ⟨p, hp, hcase⟩)
                            simp only [Finset.mem_union, List.mem_toFinset,
                              List.mem_flatMap] at this ⊢
                            rcases this with hl | hr
                            · obtain ⟨a, ha, hva⟩ := hl
                              exact Or.inl ⟨a, by simp [ha], hva⟩
                            · obtain ⟨a, ha, hva⟩ := hr
                              exact Or.inr ⟨a, by simp [ha], hva⟩
        have := hlist atoms rights c (fun _ hm => hm) hdec
        intro w hw
        have hw2 := this hw
        simp only [Finset.mem_union, List.mem_toFinset, List.mem_flatMap,
          List.mem_flatten, List.mem_map, Metta.Atom.vars,
          exists_exists_and_eq_and] at hw2 ⊢
        exact hw2

/-- Worklist form: decomposing a worklist introduces no new variables. -/
theorem decomposeAll_cVars_subset :
    ∀ (eqs : List (Metta.Atom × Metta.Atom)) (c : List (String × Metta.Atom)),
      Metta.Unify.decomposeAll eqs = some c → cVars c ⊆ eqVars eqs := by
  intro eqs
  induction eqs with
  | nil =>
      intro c hdec
      simp [Metta.Unify.decomposeAll] at hdec; subst hdec; simp [cVars]
  | cons head tail ih =>
      obtain ⟨a, b⟩ := head
      intro c hdec
      cases hh : Metta.Unify.decomposeEq a b with
      | none => simp [Metta.Unify.decomposeAll, hh] at hdec
      | some c1 =>
          cases ht : Metta.Unify.decomposeAll tail with
          | none => simp [Metta.Unify.decomposeAll, hh, ht] at hdec
          | some c2 =>
              simp [Metta.Unify.decomposeAll, hh, ht] at hdec
              subst hdec
              have h1 := decomposeEq_cVars_subset a b c1 hh
              have h2 := ih c2 ht
              intro w hw
              rw [mem_cVars] at hw
              obtain ⟨p, hp, hcase⟩ := hw
              simp only [List.mem_append] at hp
              rw [mem_eqVars]
              rcases hp with hp | hp
              · have hin := h1 (mem_cVars.mpr ⟨p, hp, hcase⟩)
                simp only [Finset.mem_union, List.mem_toFinset] at hin
                exact ⟨(a, b), by simp, hin⟩
              · have hin := h2 (mem_cVars.mpr ⟨p, hp, hcase⟩)
                rw [mem_eqVars] at hin
                obtain ⟨e, he, hce⟩ := hin
                exact ⟨e, by simp [he], hce⟩

/-- Structural decomposition never emits the trivial constraint `$x ↦ $x`
(variable/variable pairs on the same name are dropped). -/
theorem decomposeEq_noTrivial :
    ∀ (a b : Metta.Atom) (c : List (String × Metta.Atom)),
      Metta.Unify.decomposeEq a b = some c →
      ∀ p ∈ c, p.2 ≠ Metta.Atom.var p.1 := by
  intro a
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ a
  · intro s b c hdec p hp
    cases b with
    | sym o =>
        by_cases h : s = o
        · subst h; simp [Metta.Unify.decomposeEq] at hdec; subst hdec; simp at hp
        · simp [Metta.Unify.decomposeEq, h] at hdec
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; simp
    | gnd g => simp [Metta.Unify.decomposeEq] at hdec
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdec
  · intro v b c hdec p hp
    cases b with
    | var y =>
        by_cases h : v = y
        · subst h; simp [Metta.Unify.decomposeEq] at hdec; subst hdec; simp at hp
        · simp [Metta.Unify.decomposeEq, h] at hdec; subst hdec
          simp only [List.mem_singleton] at hp; subst hp
          simp only [ne_eq, Metta.Atom.var.injEq]
          exact fun heq => h heq.symm
    | sym s =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; simp
    | gnd g =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; simp
    | expr atoms =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; simp
  · intro g b c hdec p hp
    cases b with
    | sym s => simp [Metta.Unify.decomposeEq] at hdec
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; simp
    | gnd o =>
        by_cases h : Metta.Ground.equiv g o = true
        · simp [Metta.Unify.decomposeEq, h] at hdec; subst hdec; simp at hp
        · simp [Metta.Unify.decomposeEq, h] at hdec
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdec
  · intro atoms ih b c hdec p hp
    cases b with
    | sym s => simp [Metta.Unify.decomposeEq] at hdec
    | gnd g => simp [Metta.Unify.decomposeEq] at hdec
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; simp
    | expr rights =>
        simp only [Metta.Unify.decomposeEq] at hdec
        have hlist : ∀ (lefts rights : List Metta.Atom)
            (c : List (String × Metta.Atom)),
            (∀ atom ∈ lefts, atom ∈ atoms) →
            Metta.Unify.decomposeList lefts rights = some c →
            ∀ p ∈ c, p.2 ≠ Metta.Atom.var p.1 := by
          intro lefts
          induction lefts with
          | nil =>
              intro rights c _ hdec p hp
              cases rights with
              | nil => simp [Metta.Unify.decomposeList] at hdec; subst hdec; simp at hp
              | cons rHead rTail => simp [Metta.Unify.decomposeList] at hdec
          | cons head tail ihTail =>
              intro rights c hsubset hdec p hp
              cases rights with
              | nil => simp [Metta.Unify.decomposeList] at hdec
              | cons rHead rTail =>
                  cases hh : Metta.Unify.decomposeEq head rHead with
                  | none => simp [Metta.Unify.decomposeList, hh] at hdec
                  | some c1 =>
                      cases ht : Metta.Unify.decomposeList tail rTail with
                      | none =>
                          simp [Metta.Unify.decomposeList, hh, ht] at hdec
                      | some c2 =>
                          simp [Metta.Unify.decomposeList, hh, ht] at hdec
                          subst hdec
                          simp only [List.mem_append] at hp
                          rcases hp with hp | hp
                          · exact ih head (hsubset head (by simp)) rHead c1 hh p hp
                          · exact ihTail rTail c2
                              (fun a ha => hsubset a (by simp [ha])) ht p hp
        exact hlist atoms rights c (fun _ hm => hm) hdec p hp

/-- Worklist form of the no-trivial-constraint invariant. -/
theorem decomposeAll_noTrivial :
    ∀ (eqs : List (Metta.Atom × Metta.Atom)) (c : List (String × Metta.Atom)),
      Metta.Unify.decomposeAll eqs = some c →
      ∀ p ∈ c, p.2 ≠ Metta.Atom.var p.1 := by
  intro eqs
  induction eqs with
  | nil =>
      intro c hdec p hp
      simp [Metta.Unify.decomposeAll] at hdec; subst hdec; simp at hp
  | cons head tail ih =>
      obtain ⟨a, b⟩ := head
      intro c hdec p hp
      cases hh : Metta.Unify.decomposeEq a b with
      | none => simp [Metta.Unify.decomposeAll, hh] at hdec
      | some c1 =>
          cases ht : Metta.Unify.decomposeAll tail with
          | none => simp [Metta.Unify.decomposeAll, hh, ht] at hdec
          | some c2 =>
              simp [Metta.Unify.decomposeAll, hh, ht] at hdec
              subst hdec
              simp only [List.mem_append] at hp
              rcases hp with hp | hp
              · exact decomposeEq_noTrivial a b c1 hh p hp
              · exact ih c2 ht p hp

/-- Applying a single elimination `$x ↦ t` can only introduce variables of `t`,
and removes `$x` from everything it touches. -/
theorem vars_subst_single {x : String} {t : Metta.Atom} :
    ∀ (a : Metta.Atom) (v : String),
      v ∈ (Metta.Subst.apply [(x, t)] a).vars →
      v ∈ t.vars ∨ (v ∈ a.vars ∧ v ≠ x) := by
  intro a
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ a
  · intro s v hv; simp [Metta.Subst.apply, Metta.Atom.vars] at hv
  · intro y v hv
    by_cases h : y = x
    · have hyx : (y == x) = true := by rw [beq_iff_eq]; exact h
      have happly : Metta.Subst.apply [(x, t)] (Metta.Atom.var y) = t := by
        simp [Metta.Subst.apply, Metta.Subst.lookup, hyx]
      rw [happly] at hv
      exact Or.inl hv
    · have hyx : (y == x) = false := by
        by_contra hcon
        rw [Bool.not_eq_false, beq_iff_eq] at hcon
        exact h hcon
      have happly : Metta.Subst.apply [(x, t)] (Metta.Atom.var y) = Metta.Atom.var y := by
        simp [Metta.Subst.apply, Metta.Subst.lookup, hyx]
      rw [happly, Metta.Atom.vars, List.mem_singleton] at hv
      subst hv
      exact Or.inr ⟨by simp [Metta.Atom.vars], h⟩
  · intro g v hv; simp [Metta.Subst.apply, Metta.Atom.vars] at hv
  · intro xs ih v hv
    simp only [Metta.Subst.apply, Metta.Atom.vars, List.mem_flatten, List.mem_map,
      exists_exists_and_eq_and] at hv
    obtain ⟨child, hchild, hvchild⟩ := hv
    rcases ih child hchild v hvchild with hl | ⟨hr, hne⟩
    · exact Or.inl hl
    · refine Or.inr ⟨?_, hne⟩
      simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map,
        exists_exists_and_eq_and]
      exact ⟨child, hchild, hr⟩

/-- One Robinson elimination round strictly shrinks the variable set: the
eliminated `$x` is removed (the occurs-check guarantees it does not reappear in
`t`), and no new variable is introduced. -/
theorem eqVars_step_card
    {eqs : List (Metta.Atom × Metta.Atom)} {x : String} {t : Metta.Atom}
    {rest : List (String × Metta.Atom)}
    (hdec : Metta.Unify.decomposeAll eqs = some ((x, t) :: rest))
    (hocc : Metta.Subst.occurs x t = false) :
    (eqVars (rest.map fun p =>
        (Metta.Subst.apply [(x, t)] (Metta.Atom.var p.1),
         Metta.Subst.apply [(x, t)] p.2))).card < (eqVars eqs).card := by
  have hcsub : cVars ((x, t) :: rest) ⊆ eqVars eqs :=
    decomposeAll_cVars_subset eqs _ hdec
  have hxmem : x ∈ eqVars eqs :=
    hcsub (mem_cVars.mpr ⟨(x, t), by simp, Or.inl rfl⟩)
  have hxnt : x ∉ t.vars := not_mem_vars_of_occurs_eq_false x t hocc
  have htv : ∀ w ∈ t.vars, w ∈ eqVars eqs := fun w hw =>
    hcsub (mem_cVars.mpr ⟨(x, t), by simp, Or.inr hw⟩)
  have hsub : eqVars (rest.map fun p =>
      (Metta.Subst.apply [(x, t)] (Metta.Atom.var p.1),
       Metta.Subst.apply [(x, t)] p.2)) ⊆ (eqVars eqs).erase x := by
    intro v hv
    rw [mem_eqVars] at hv
    obtain ⟨eq, heq, hcase⟩ := hv
    rw [List.mem_map] at heq
    obtain ⟨p, hp, rfl⟩ := heq
    rw [Finset.mem_erase]
    have hp1 : p.1 ∈ eqVars eqs :=
      hcsub (mem_cVars.mpr ⟨p, by simp [hp], Or.inl rfl⟩)
    have hp2 : ∀ w ∈ p.2.vars, w ∈ eqVars eqs := fun w hw =>
      hcsub (mem_cVars.mpr ⟨p, by simp [hp], Or.inr hw⟩)
    rcases hcase with hc | hc
    · rcases vars_subst_single (Metta.Atom.var p.1) v hc with hl | ⟨hr, hne⟩
      · exact ⟨fun hvx => hxnt (hvx ▸ hl), htv v hl⟩
      · simp only [Metta.Atom.vars, List.mem_singleton] at hr
        subst hr
        exact ⟨hne, hp1⟩
    · rcases vars_subst_single p.2 v hc with hl | ⟨hr, hne⟩
      · exact ⟨fun hvx => hxnt (hvx ▸ hl), htv v hl⟩
      · exact ⟨hne, hp2 v hr⟩
  calc (eqVars (rest.map fun p =>
          (Metta.Subst.apply [(x, t)] (Metta.Atom.var p.1),
           Metta.Subst.apply [(x, t)] p.2))).card
      ≤ ((eqVars eqs).erase x).card := Finset.card_le_card hsub
    _ < (eqVars eqs).card := Finset.card_erase_lt_of_mem hxmem

/-! ### Float-freeness is preserved through decomposition -/

/-- Every constraint target produced by decomposing two host-float-free atoms is
itself host-float-free (it is a subterm of one of them). -/
theorem decomposeEq_noFloat :
    ∀ (a b : Metta.Atom),
      MettaAtomNoFloat a → MettaAtomNoFloat b →
      ∀ (c : List (String × Metta.Atom)),
        Metta.Unify.decomposeEq a b = some c →
        ∀ p ∈ c, MettaAtomNoFloat p.2 := by
  intro a
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ a
  · intro s b hleft hright c hdec p hp
    cases b with
    | sym o =>
        by_cases h : s = o
        · subst h; simp [Metta.Unify.decomposeEq] at hdec; subst hdec; simp at hp
        · simp [Metta.Unify.decomposeEq, h] at hdec
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; exact hleft
    | gnd g => simp [Metta.Unify.decomposeEq] at hdec
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdec
  · intro v b hleft hright c hdec p hp
    cases b with
    | var y =>
        by_cases h : v = y
        · subst h; simp [Metta.Unify.decomposeEq] at hdec; subst hdec; simp at hp
        · simp [Metta.Unify.decomposeEq, h] at hdec; subst hdec
          simp only [List.mem_singleton] at hp; subst hp; simp [MettaAtomNoFloat]
    | sym s =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; exact hright
    | gnd g =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; exact hright
    | expr atoms =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; exact hright
  · intro g b hleft hright c hdec p hp
    cases b with
    | sym s => simp [Metta.Unify.decomposeEq] at hdec
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; exact hleft
    | gnd o =>
        by_cases h : Metta.Ground.equiv g o = true
        · simp [Metta.Unify.decomposeEq, h] at hdec; subst hdec; simp at hp
        · simp [Metta.Unify.decomposeEq, h] at hdec
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdec
  · intro atoms ih b hleft hright c hdec p hp
    cases b with
    | sym s => simp [Metta.Unify.decomposeEq] at hdec
    | gnd g => simp [Metta.Unify.decomposeEq] at hdec
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdec; subst hdec
        simp only [List.mem_singleton] at hp; subst hp; exact hleft
    | expr rights =>
        simp only [Metta.Unify.decomposeEq] at hdec
        have hlchildren : ∀ atom ∈ atoms, MettaAtomNoFloat atom := by
          simpa [MettaAtomNoFloat] using hleft
        have hrchildren : ∀ atom ∈ rights, MettaAtomNoFloat atom := by
          simpa [MettaAtomNoFloat] using hright
        have hlist : ∀ (lefts rights : List Metta.Atom)
            (c : List (String × Metta.Atom)),
            (∀ atom ∈ lefts, atom ∈ atoms) →
            (∀ atom ∈ lefts, MettaAtomNoFloat atom) →
            (∀ atom ∈ rights, MettaAtomNoFloat atom) →
            Metta.Unify.decomposeList lefts rights = some c →
            ∀ p ∈ c, MettaAtomNoFloat p.2 := by
          intro lefts
          induction lefts with
          | nil =>
              intro rights c _ _ _ hdec p hp
              cases rights with
              | nil =>
                  simp [Metta.Unify.decomposeList] at hdec; subst hdec; simp at hp
              | cons rH rT => simp [Metta.Unify.decomposeList] at hdec
          | cons head tail ihTail =>
              intro rights c hsubset hlefts hrights hdec p hp
              cases rights with
              | nil => simp [Metta.Unify.decomposeList] at hdec
              | cons rHead rTail =>
                  cases hh : Metta.Unify.decomposeEq head rHead with
                  | none => simp [Metta.Unify.decomposeList, hh] at hdec
                  | some c1 =>
                      cases ht : Metta.Unify.decomposeList tail rTail with
                      | none =>
                          simp [Metta.Unify.decomposeList, hh, ht] at hdec
                      | some c2 =>
                          simp [Metta.Unify.decomposeList, hh, ht] at hdec
                          subst hdec
                          simp only [List.mem_append] at hp
                          rcases hp with hp | hp
                          · exact ih head (hsubset head (by simp)) rHead
                              (hlefts head (by simp)) (hrights rHead (by simp))
                              c1 hh p hp
                          · exact ihTail rTail c2
                              (fun a ha => hsubset a (by simp [ha]))
                              (fun a ha => hlefts a (by simp [ha]))
                              (fun a ha => hrights a (by simp [ha])) ht p hp
        exact hlist atoms rights c (fun _ hm => hm) hlchildren hrchildren hdec p hp

/-- Worklist form of decomposition float-freeness. -/
theorem decomposeAll_noFloat :
    ∀ (eqs : List (Metta.Atom × Metta.Atom)),
      (∀ eq ∈ eqs, MettaAtomNoFloat eq.1 ∧ MettaAtomNoFloat eq.2) →
      ∀ (c : List (String × Metta.Atom)),
        Metta.Unify.decomposeAll eqs = some c →
        ∀ p ∈ c, MettaAtomNoFloat p.2 := by
  intro eqs
  induction eqs with
  | nil =>
      intro _ c hdec p hp
      simp [Metta.Unify.decomposeAll] at hdec; subst hdec; simp at hp
  | cons head tail ih =>
      obtain ⟨a, b⟩ := head
      intro hnoFloat c hdec p hp
      cases hh : Metta.Unify.decomposeEq a b with
      | none => simp [Metta.Unify.decomposeAll, hh] at hdec
      | some c1 =>
          cases ht : Metta.Unify.decomposeAll tail with
          | none => simp [Metta.Unify.decomposeAll, hh, ht] at hdec
          | some c2 =>
              simp [Metta.Unify.decomposeAll, hh, ht] at hdec
              subst hdec
              simp only [List.mem_append] at hp
              rcases hp with hp | hp
              · exact decomposeEq_noFloat a b (hnoFloat (a, b) (by simp)).1
                  (hnoFloat (a, b) (by simp)).2 c1 hh p hp
              · exact ih (fun eq hmem => hnoFloat eq (by simp [hmem])) c2 ht p hp

/-! ### The main induction: a satisfiable float-free worklist always unifies -/

/-- Robinson completeness, fuel-parameterized.  If a host-float-free equation
worklist is satisfied by a common valuation and the fuel bounds the number of
distinct variables, `unifyRounds` succeeds.  The three semantic obstructions
are ruled out by satisfaction: no head clash (`decomposeAll` is `some`), no
occurs-cycle (the occurs-check never fires under §2), and the variable count
strictly decreases each round (§3, so the fuel never runs out prematurely). -/
theorem unifyRounds_isSome_of_satisfied_aux {valuation : String → Metta.Atom} :
    ∀ (fuel : Nat) (eqs : List (Metta.Atom × Metta.Atom)) (s : Metta.Subst),
      (∀ eq ∈ eqs, MettaAtomNoFloat eq.1 ∧ MettaAtomNoFloat eq.2) →
      MettaEquationsSatisfied valuation eqs →
      (eqVars eqs).card ≤ fuel →
      ∃ result, Metta.Unify.unifyRounds fuel eqs s = some result := by
  intro fuel
  induction fuel with
  | zero =>
      intro eqs s hnoFloat hsat hcard
      obtain ⟨c, hc⟩ := decomposeAll_isSome_of_satisfied eqs hnoFloat hsat
      have hempty : eqVars eqs = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have hsub : cVars c ⊆ eqVars eqs := decomposeAll_cVars_subset eqs c hc
      rw [hempty] at hsub
      have hcnil : c = [] := by
        cases c with
        | nil => rfl
        | cons p rest =>
            exfalso
            exact absurd (hsub (mem_cVars.mpr ⟨p, by simp, Or.inl rfl⟩)) (by simp)
      subst hcnil
      exact ⟨s, by simp [Metta.Unify.unifyRounds, hc]⟩
  | succ fuel ih =>
      intro eqs s hnoFloat hsat hcard
      obtain ⟨c, hc⟩ := decomposeAll_isSome_of_satisfied eqs hnoFloat hsat
      cases c with
      | nil => exact ⟨s, by simp [Metta.Unify.unifyRounds, hc]⟩
      | cons head rest =>
          obtain ⟨x, t⟩ := head
          have hcSat : MettaConstraintsSatisfied valuation ((x, t) :: rest) :=
            (decomposeAll_solution_iff valuation eqs ((x, t) :: rest)
              hnoFloat hc).mp hsat
          have hxt : valuation x = applyClassSolution valuation t :=
            hcSat (x, t) (by simp)
          have hne : t ≠ Metta.Atom.var x :=
            decomposeAll_noTrivial eqs ((x, t) :: rest) hc (x, t) (by simp)
          have hocc : Metta.Subst.occurs x t = false :=
            occurs_eq_false_of_constraint_satisfied hxt hne
          have htNoFloat : MettaAtomNoFloat t :=
            decomposeAll_noFloat eqs hnoFloat ((x, t) :: rest) hc (x, t) (by simp)
          have hsubSat : MettaConstraintsSatisfied valuation [(x, t)] := by
            intro constraint hmem
            simp only [List.mem_singleton] at hmem
            subst hmem
            exact hxt
          have hrestNoFloat : ∀ eq ∈ (rest.map fun p =>
              (Metta.Subst.apply [(x, t)] (Metta.Atom.var p.1),
               Metta.Subst.apply [(x, t)] p.2)),
              MettaAtomNoFloat eq.1 ∧ MettaAtomNoFloat eq.2 := by
            intro eq hmem
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
            exact ⟨apply_singleton_noFloat htNoFloat _ (by simp [MettaAtomNoFloat]),
              apply_singleton_noFloat htNoFloat _
                (decomposeAll_noFloat eqs hnoFloat ((x, t) :: rest) hc p
                  (by simp [hp]))⟩
          have hrestSat : MettaEquationsSatisfied valuation (rest.map fun p =>
              (Metta.Subst.apply [(x, t)] (Metta.Atom.var p.1),
               Metta.Subst.apply [(x, t)] p.2)) := by
            intro eq hmem
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
            show applyClassSolution valuation
                (Metta.Subst.apply [(x, t)] (Metta.Atom.var p.1)) =
              applyClassSolution valuation (Metta.Subst.apply [(x, t)] p.2)
            rw [mettaSubst_apply_solution valuation hsubSat,
                mettaSubst_apply_solution valuation hsubSat]
            simpa [applyClassSolution] using hcSat p (by simp [hp])
          have hcard' : (eqVars (rest.map fun p =>
              (Metta.Subst.apply [(x, t)] (Metta.Atom.var p.1),
               Metta.Subst.apply [(x, t)] p.2))).card ≤ fuel :=
            Nat.lt_succ_iff.mp
              (Nat.lt_of_lt_of_le (eqVars_step_card hc hocc) hcard)
          obtain ⟨result, hresult⟩ :=
            ih _ (Metta.Subst.extend s x t) hrestNoFloat hrestSat hcard'
          refine ⟨result, ?_⟩
          simp only [Metta.Unify.unifyRounds, hc]
          rw [hocc]
          simpa using hresult

/-- Robinson completeness at the canonical fuel.  Any fuel at least the number
of distinct variables in a satisfiable host-float-free worklist makes
`unifyRounds` succeed; downstream callers instantiate `fuel` with their own
structural bound and discharge the variable-count inequality via
`card_eqVars_le`. -/
theorem exists_unifyRounds_of_satisfied
    {valuation : String → Metta.Atom}
    (eqs : List (Metta.Atom × Metta.Atom)) (s : Metta.Subst)
    (hnoFloat : ∀ eq ∈ eqs, MettaAtomNoFloat eq.1 ∧ MettaAtomNoFloat eq.2)
    (hsat : MettaEquationsSatisfied valuation eqs) :
    ∀ fuel, (eqVars eqs).card ≤ fuel →
      ∃ result, Metta.Unify.unifyRounds fuel eqs s = some result :=
  fun fuel hfuel =>
    unifyRounds_isSome_of_satisfied_aux fuel eqs s hnoFloat hsat hfuel

/-! ## §4  Fuel discharge: the callers' structural fuel bounds the variable count -/

/-- An atom lists at most `size`-many variable occurrences: the number of
distinct variables is bounded by the total structural size. -/
theorem length_vars_le_size : ∀ a : Metta.Atom, a.vars.length ≤ a.size := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro s; simp [Metta.Atom.vars, Metta.Atom.size]
  · intro x; simp [Metta.Atom.vars, Metta.Atom.size]
  · intro g; simp [Metta.Atom.vars, Metta.Atom.size]
  · intro xs ih
    simp only [Metta.Atom.vars, Metta.Atom.size, List.length_flatten, List.map_map]
    refine le_trans (List.sum_le_sum (fun a ha => ih a ha)) (Nat.le_add_left _ _)

/-- The structural fuel `equationFuel` used by `reconcileAll` bounds the number
of distinct variables in the worklist, so it is always adequate for Robinson
elimination. -/
theorem card_eqVars_le_equationFuel (work : List (Metta.Atom × Metta.Atom)) :
    (eqVars work).card ≤ Metta.Bindings.equationFuel work := by
  unfold eqVars Metta.Bindings.equationFuel
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.length_flatMap]
  refine List.sum_le_sum (fun e _ => ?_)
  simp only [List.length_append]
  exact Nat.add_le_add (length_vars_le_size e.1) (length_vars_le_size e.2)

/-- The structural fuel `unifyValues` supplies (the head size plus the tail
sizes) bounds the number of distinct variables in the class-equation worklist. -/
theorem card_eqVars_le_unifyValuesFuel
    (first : Metta.Atom) (rest : List Metta.Atom) :
    (eqVars (rest.map fun v => (first, v))).card ≤
      first.size + (rest.map Metta.Atom.size).sum := by
  have hsub : eqVars (rest.map fun v => (first, v)) ⊆
      first.vars.toFinset ∪ (rest.flatMap Metta.Atom.vars).toFinset := by
    intro w hw
    rw [mem_eqVars] at hw
    obtain ⟨e, he, hcase⟩ := hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_flatMap]
    rcases hcase with hcase | hcase
    · exact Or.inl hcase
    · exact Or.inr ⟨v, hv, hcase⟩
  calc (eqVars (rest.map fun v => (first, v))).card
      ≤ (first.vars.toFinset ∪ (rest.flatMap Metta.Atom.vars).toFinset).card :=
        Finset.card_le_card hsub
    _ ≤ first.vars.toFinset.card + (rest.flatMap Metta.Atom.vars).toFinset.card :=
        Finset.card_union_le _ _
    _ ≤ first.vars.length + (rest.flatMap Metta.Atom.vars).length :=
        Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
    _ ≤ first.size + (rest.map Metta.Atom.size).sum := by
        refine Nat.add_le_add (length_vars_le_size first) ?_
        rw [List.length_flatMap]
        exact List.sum_le_sum (fun v _ => length_vars_le_size v)

/-! ## §5  Operational success corollaries at the callers' own fuel -/

/-- `unifyRounds` at the `equationFuel` fuel succeeds on any satisfiable
host-float-free worklist.  This is the shared engine behind `reconcileAll`. -/
theorem exists_unifyRounds_equationFuel_of_satisfied
    {valuation : String → Metta.Atom}
    (work : List (Metta.Atom × Metta.Atom))
    (hnoFloat : ∀ eq ∈ work, MettaAtomNoFloat eq.1 ∧ MettaAtomNoFloat eq.2)
    (hsat : MettaEquationsSatisfied valuation work) :
    ∃ result,
      Metta.Unify.unifyRounds (Metta.Bindings.equationFuel work) work [] = some result :=
  exists_unifyRounds_of_satisfied work [] hnoFloat hsat
    (Metta.Bindings.equationFuel work) (card_eqVars_le_equationFuel work)

/-- `reconcileAll` succeeds whenever its full first-order presentation
(the binding equations together with the extra constraints) is satisfied by a
common host-float-free valuation. -/
theorem exists_reconcileAll_of_satisfied
    {valuation : String → Metta.Atom}
    (b : Metta.Bindings) (extra : List (Metta.Atom × Metta.Atom))
    (hnoFloat : ∀ eq ∈ (Metta.Bindings.equations b ++ extra),
        MettaAtomNoFloat eq.1 ∧ MettaAtomNoFloat eq.2)
    (hsat : MettaEquationsSatisfied valuation (Metta.Bindings.equations b ++ extra)) :
    ∃ sigma, Metta.Bindings.reconcileAll b extra = some sigma := by
  unfold Metta.Bindings.reconcileAll
  exact exists_unifyRounds_equationFuel_of_satisfied _ hnoFloat hsat

/-- Bridge to the whole-binding reconciliation surface consumed by the
matcher-origin reconciliation-witness construction.  A satisfiable,
host-float-free combined equation system (the binding's own equations together
with the extra constraints) makes `wholeBindingReconciliation` succeed — this is
exactly the `hreconcile` hypothesis that the downstream witness builder assumes,
now discharged from satisfiability rather than posited. -/
theorem exists_wholeBindingReconciliation_of_satisfied
    {valuation : String → Metta.Atom}
    (source : Metta.Bindings) (extra : List (Metta.Atom × Metta.Atom))
    (hnoFloat : ∀ eq ∈ (Metta.Bindings.equations source ++ extra),
        MettaAtomNoFloat eq.1 ∧ MettaAtomNoFloat eq.2)
    (hsat : MettaEquationsSatisfied valuation
        (Metta.Bindings.equations source ++ extra)) :
    ∃ result, wholeBindingReconciliation source extra = some result :=
  exists_reconcileAll_of_satisfied source extra hnoFloat hsat

/-- `unifyValues` succeeds whenever every value in an equality class shares a
common host-float-free image under some valuation. -/
theorem exists_unifyValues_of_satisfied
    {valuation : String → Metta.Atom}
    (first : Metta.Atom) (rest : List Metta.Atom)
    (hfirst : MettaAtomNoFloat first)
    (hrest : ∀ v ∈ rest, MettaAtomNoFloat v)
    (hsat : ∀ v ∈ rest,
      applyClassSolution valuation first = applyClassSolution valuation v) :
    ∃ sigma, Metta.Bindings.unifyValues (first :: rest) = some sigma := by
  cases rest with
  | nil => exact ⟨[], by simp [Metta.Bindings.unifyValues]⟩
  | cons r rs =>
      have hwork : ∀ eq ∈ ((r :: rs).map fun v => (first, v)),
          MettaAtomNoFloat eq.1 ∧ MettaAtomNoFloat eq.2 := by
        intro eq hmem
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hmem
        exact ⟨hfirst, hrest v hv⟩
      have hworkSat :
          MettaEquationsSatisfied valuation ((r :: rs).map fun v => (first, v)) := by
        intro eq hmem
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hmem
        exact hsat v hv
      obtain ⟨result, hresult⟩ :=
        exists_unifyRounds_of_satisfied ((r :: rs).map fun v => (first, v)) []
          hwork hworkSat _ (card_eqVars_le_unifyValuesFuel first (r :: rs))
      exact ⟨result, by simpa [Metta.Bindings.unifyValues] using hresult⟩

/-! ## §6  Oracles and canaries

The corollaries above are existence statements; the examples below tie them to
real reductions.  The positive oracle exhibits an actual nested-expression
reconciliation (checked by kernel `rfl`, and predicted by the completeness
corollary from a concrete valuation).  The negative canaries confirm the two
obstructions our theorem's hypotheses exclude really do block the engine: an
occurs-cycle worklist (unsatisfiable, so the theorem correctly does not apply)
and a satisfiable worklist starved of fuel (`card > fuel`, so the fuel
hypothesis is load-bearing rather than cosmetic). -/

/-- Positive oracle: two doubly-nested expressions sharing one variable
reconcile to the grounding substitution `$x ↦ a`, and `unifyValues` really
returns it. -/
example :
    Metta.Bindings.unifyValues
        [Atom.expr [Atom.sym "f", Atom.expr [Atom.sym "g", Atom.var "x"]],
         Atom.expr [Atom.sym "f", Atom.expr [Atom.sym "g", Atom.sym "a"]]]
      = some [("x", Atom.sym "a")] := by
  simp [Metta.Bindings.unifyValues, Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
    Metta.Unify.decomposeEq, Metta.Unify.decomposeList, Metta.Subst.extend,
    Metta.Subst.erase, Metta.Atom.size]

/-- Positive oracle: `reconcileAll` on empty seed bindings with one nested
constraint returns the same grounding. -/
example :
    Metta.Bindings.reconcileAll []
        [(Atom.expr [Atom.sym "f", Atom.var "x"],
          Atom.expr [Atom.sym "f", Atom.sym "a"])]
      = some [("x", Atom.sym "a")] := by
  simp [Metta.Bindings.reconcileAll, Metta.Bindings.equations, Metta.Bindings.equationFuel,
    Metta.Unify.unifyRounds, Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
    Metta.Unify.decomposeList, Metta.Subst.extend, Metta.Subst.erase, Metta.Atom.size]

/-- The completeness corollary predicts that success from a concrete valuation:
`fun s => if s = "x" then a else s` maps both nested expressions to the same
image, so `exists_unifyValues_of_satisfied` yields the `some` witness the oracle
computes. -/
example :
    ∃ sigma, Metta.Bindings.unifyValues
        [Atom.expr [Atom.sym "f", Atom.var "x"],
         Atom.expr [Atom.sym "f", Atom.sym "a"]] = some sigma := by
  refine exists_unifyValues_of_satisfied
    (valuation := fun s => if s = "x" then Atom.sym "a" else Atom.var s)
    _ _ ?_ ?_ ?_
  · simp [MettaAtomNoFloat]
  · intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    simp [MettaAtomNoFloat]
  · intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    simp [applyClassSolution]

/-- Negative canary (occurs-cycle): `$x =? (f $x)` has no valuation solution
(the image of `$x` would have to be a proper subterm of itself), the occurs
check fires, and `unifyValues` returns `none`. -/
example :
    Metta.Bindings.unifyValues
        [Atom.var "x", Atom.expr [Atom.sym "f", Atom.var "x"]] = none := by
  simp [Metta.Bindings.unifyValues, Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
    Metta.Unify.decomposeEq, Metta.Subst.occurs, Metta.Atom.size]

/-- Negative canary (insufficient fuel): the worklist `$x =? a` is satisfiable
and has one distinct variable, but running the loop with fuel `0 < 1` starves
it, so `unifyRounds` returns `none`.  Fuel adequacy (`card ≤ fuel`) is therefore
a genuine hypothesis of the completeness theorem. -/
example :
    Metta.Unify.unifyRounds 0 [(Atom.var "x", Atom.sym "a")] [] = none := by rfl

/-- The starved worklist above is genuinely satisfiable, witnessing that the
fuel gap — not unsatisfiability — is what defeats the previous canary. -/
example :
    MettaEquationsSatisfied (fun s => if s = "x" then Atom.sym "a" else Atom.var s)
      [(Atom.var "x", Atom.sym "a")] := by
  intro eq hmem
  simp only [List.mem_singleton] at hmem
  subst hmem
  simp [MettaEquationSatisfied, applyClassSolution]

end Mettapedia.Languages.MeTTa.HE
