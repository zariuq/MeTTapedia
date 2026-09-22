import Mettapedia.GSLT.Meredith.LambdaTheory
import Mettapedia.OSLF.Framework.ModalHypercube

/-!
# Rewrite Modalities: §5.4 of "Generating Hypercubes of Type Systems"

Formalization of the modal type formers generated from base rewrites
and redex positions in a lambda theory.

## Main Definitions

* `RedexPosition` — a choice of subterm and one-hole context in a base rewrite (§5.4)
* `ModalitySlots` — the local sort slots for a modality (§5.6)
* `ModalTyping` — the typing judgment extended with modal types:
  - `M-Form`: formation rule for ⟨K_j⟩ modalities
  - `M-Intro`: introduction from typing the reduct under relies
  - `M-Step`: elimination yielding operational step
  - `M-Elim⇝`: elimination yielding typing of the reduct

## Key Insight (§5.4)

Each base rewrite `L(x̄) ⇝ R(x̄)` and each subterm position `t_j ⊆ L`
generates a modality `⟨K_j⟩_{x̄ :: Ā} B` at carrier `Y_j`, where:
- `K_j[−]` is the one-hole context with `K_j[t_j] = L`
- `V_j = FV(K_j) \ FV(t_j)` — the "rely" variables
- The modality asserts: under rely assumptions, placing `t` in `K_j[−]`
  takes one step to `R(x̄)` which inhabits `B`.

## References

- Stay, Meredith & Wells, "Generating Hypercubes of Type Systems" (2026), §5.4
-/

namespace Mettapedia.GSLT.Meredith.Modal

open Mettapedia.GSLT.Meredith
open Mettapedia.OSLF.Framework.ModalHypercube

/-! ## Redex Positions (§5.4) -/

/-- A redex position in a base rewrite.

    §5.4: "Choose any subterm occurrence t_j ⊆ L with carrier Y_j and
    one-holed context K_j[−] (so that K_j[t_j] = L)."

    We represent this abstractly: a redex position selects a subterm of
    the left-hand side and a one-hole context that reconstructs it.

    * `relyArity` — number of rely variables: |V_j| = |FV(K_j) \ FV(t_j)|
    * `subterm` — the selected subterm t_j (as a morphism in context)
    * `context` — the one-hole context K_j[−] (as a function filling the hole)
    * `fills` — K_j[t_j] = L (the context applied to the subterm gives the LHS)
-/
structure RedexPosition (T : LambdaTheory) (br : BaseRewrite T) where
  /-- The carrier of the subterm (Y_j in the paper). -/
  subtermCarrier : T.Obj
  /-- Number of rely parameters: variables free in K_j but not in t_j. -/
  relyArity : ℕ
  /-- The sort of each rely parameter's carrier, `s^{X_k}_k` of §5.6.  Recording
  it is what lets the formation rule below be an equation that can fail. -/
  relySort : Fin relyArity → HSort
  /-- The subterm t_j : ctx ⟶ Y_j (projected from the base rewrite context). -/
  subterm : br.ctx ⟶ subtermCarrier
  /-- The one-hole context K_j[−]: given a term of carrier Y_j, produces a process.
      §5.4: K_j is a one-hole context with K_j[t_j] = L. -/
  fillContext : (br.ctx ⟶ subtermCarrier) → (br.ctx ⟶ T.Pr)
  /-- K_j[t_j] = L: the context applied to the subterm gives the LHS. -/
  fills : fillContext subterm = br.lhs

/-! ## Sort Slots for Modalities (§5.6) -/

/-- The sort slot family for a modality at a given redex position.

    §5.6: "Each modality ⟨K_j⟩ carries its own slot family
    Slots(K_j, B) := {s^{X_k}_k}_{k ∈ V_j} ∪ {s_out}."

    Total number of slots = relyArity + 1 (rely inputs + one output).
-/
def modalitySlotCount (relyArity : ℕ) : ℕ := relyArity + 1

/-- The output slot index (last slot). -/
def outputSlot (relyArity : ℕ) : Fin (modalitySlotCount relyArity) :=
  ⟨relyArity, Nat.lt_succ_of_le (Nat.le_refl _)⟩

/-- A rely slot index (for the k-th rely parameter). -/
def relySlot {relyArity : ℕ} (k : Fin relyArity) : Fin (modalitySlotCount relyArity) :=
  ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩

/-! ## Modal Typing Judgment (§5.4) -/

/-- A modal type specification: the data needed to form a modal type ⟨K_j⟩_{x̄::Ā} B.

    This bundles a redex position with sort assignments for each slot.
    §5.4: The modality `⟨K_j⟩_{x̄::Ā} B` is a type former at carrier Y_j
    carrying one sort slot per rely input and one output slot.
-/
structure ModalTypeSpec (T : LambdaTheory) where
  /-- The underlying base rewrite. -/
  baseRewrite : BaseRewrite T
  /-- The chosen redex position. -/
  position : RedexPosition T baseRewrite
  /-- Sort assignment for each slot (rely inputs + output). -/
  sortAssignment : Fin (modalitySlotCount position.relyArity) → HSort
  /-- The sort of the postcondition, `s_out` of §5.6. -/
  outputSort : HSort

/-! ## Formation, Introduction, and Elimination

    We define these as propositions (judgment forms) rather than inductive types,
    since the full typing judgment requires the ambient lambda theory's
    type-theoretic structure which we keep abstract.
-/

/-- **M-Form**: The modality ⟨K_j⟩_{x̄::Ā} B is well-formed when each
    rely type A_k is well-sorted and the postcondition B is well-sorted.

    §5.4.1: "The modality ⟨K_j⟩_{x̄::Ā} B is a type former at carrier Y_j."
-/
structure ModalFormation (spec : ModalTypeSpec T) : Prop where
  /-- Each rely slot carries the sort of its own parameter's carrier. -/
  relySorted : ∀ k : Fin spec.position.relyArity,
    spec.sortAssignment (relySlot k) = spec.position.relySort k
  /-- And the output slot carries the postcondition's sort. -/
  postSorted : spec.sortAssignment (outputSlot spec.position.relyArity) = spec.outputSort

/-- The slot family of a well-formed modality is determined by the position and
the postcondition: there is nothing left to choose. -/
theorem ModalFormation.sortAssignment_eq {spec : ModalTypeSpec T}
    (formed : ModalFormation spec) :
    spec.sortAssignment = fun slot =>
      if hslot : slot.val < spec.position.relyArity then
        spec.position.relySort ⟨slot.val, hslot⟩
      else spec.outputSort := by
  funext slot
  have bounded : slot.val < spec.position.relyArity + 1 := slot.isLt
  by_cases hslot : slot.val < spec.position.relyArity
  · rw [dif_pos hslot]
    have same : slot = relySlot ⟨slot.val, hslot⟩ := Fin.ext rfl
    have key := formed.relySorted ⟨slot.val, hslot⟩
    rwa [← same] at key
  · rw [dif_neg hslot]
    have same : slot = outputSlot spec.position.relyArity := by
      refine Fin.ext ?_
      simp only [outputSlot]
      omega
    rw [same, formed.postSorted]

/-- **And formation can fail.**  A specification whose output slot is assigned
the other sort is not well formed, so the rule above is a condition rather than
a restatement. -/
theorem not_modalFormation_of_outputSort_ne {spec : ModalTypeSpec T}
    (mismatch : spec.sortAssignment (outputSlot spec.position.relyArity) ≠ spec.outputSort) :
    ¬ ModalFormation spec := fun formed => mismatch formed.postSorted

/-- **M-Step**: Elimination yielding operational step.

    §5.4.3: "Step to the specified RHS":
    ```
    Γ Δ ⊢ t :: ⟨K_j⟩_{x̄::Ā} B    Γ Δ ⊢ u_k :: A_k
    ────────────────────────────────────────────────────
    Γ Δ ⊢ K_j[t][ū/x̄] ⇝ R(ū)
    ```
-/
structure ModalStep (T : LambdaTheory) (br : BaseRewrite T)
    (pos : RedexPosition T br) : Prop where
  /-- The operational step fires: K_j[t][ū/x̄] ⇝ R(ū). -/
  steps : T.rewriteRel (pos.fillContext pos.subterm) br.rhs
  -- This follows directly from pos.fills and br.fires

/-- M-Step is derivable from the base rewrite and the context fill. -/
theorem modalStep_from_base (T : LambdaTheory) (br : BaseRewrite T)
    (pos : RedexPosition T br) : ModalStep T br pos where
  steps := pos.fills ▸ br.fires

/-! ## The rely-possibly reading (§5.4.4)

§5.4.4 reads the type former as a comprehension:

    ⟨K_j⟩_{x̄::Ā} B  =  { t : Y_j | ∀ x̄ :: Ā.  K_j(t) ⇝ R(x̄)  ∧  R(x̄) :: B }

and the two eliminations — the operational step and the typing of the reduct —
are its two projections.

**Where the reading below departs from the display, and why.**  Taking the
second conjunct at the rule's own right-hand side makes it independent of `t`:
the postcondition would then say nothing about the term inhabiting the
modality, and elimination would be a projection out of a constant rather than a
rule.  `rhsOnlyReading_independent_of_term` states that defect as a theorem so
it cannot return unnoticed.  The reading used here quantifies the reduct
instead — a possibility modality's target is existential — and recovers the
display exactly at the authored subterm, where the reduct *is* the right-hand
side.  Nothing is lost and the postcondition becomes a condition on `t`.
-/

/-- **The rely-possibly comprehension.**  A term of the subterm's carrier
inhabits the modality when placing it in the context steps to some reduct that
the postcondition accepts. -/
def RelyPossibly {T : LambdaTheory} {br : BaseRewrite T} (pos : RedexPosition T br)
    (post : (br.ctx ⟶ T.Pr) → Prop) (t : br.ctx ⟶ pos.subtermCarrier) : Prop :=
  ∃ reduct : br.ctx ⟶ T.Pr,
    T.rewriteRel (pos.fillContext t) reduct ∧ post reduct

/-- **M-Intro.**  The authored subterm inhabits the modality whose
postcondition holds of the rule's right-hand side.  The step obligation is the
base rewrite itself, transported along `K_j[t_j] = L`. -/
theorem relyPossibly_intro {T : LambdaTheory} {br : BaseRewrite T}
    (pos : RedexPosition T br) {post : (br.ctx ⟶ T.Pr) → Prop}
    (rhsTyped : post br.rhs) :
    RelyPossibly pos post pos.subterm :=
  ⟨br.rhs, pos.fills ▸ br.fires, rhsTyped⟩

/-- **M-Step.**  An inhabitant supplies the operational half: the context
filled with it rewrites. -/
theorem relyPossibly_step {T : LambdaTheory} {br : BaseRewrite T}
    {pos : RedexPosition T br} {post : (br.ctx ⟶ T.Pr) → Prop}
    {t : br.ctx ⟶ pos.subtermCarrier} (inhabits : RelyPossibly pos post t) :
    ∃ reduct : br.ctx ⟶ T.Pr, T.rewriteRel (pos.fillContext t) reduct := by
  obtain ⟨reduct, steps, -⟩ := inhabits
  exact ⟨reduct, steps⟩

/-- **M-Elim⇝.**  And the typing half: the reduct it steps to is accepted by
the postcondition.  Both halves name the same reduct, which is what makes them
two projections of one membership rather than two separate assertions. -/
theorem relyPossibly_elim {T : LambdaTheory} {br : BaseRewrite T}
    {pos : RedexPosition T br} {post : (br.ctx ⟶ T.Pr) → Prop}
    {t : br.ctx ⟶ pos.subtermCarrier} (inhabits : RelyPossibly pos post t) :
    ∃ reduct : br.ctx ⟶ T.Pr,
      T.rewriteRel (pos.fillContext t) reduct ∧ post reduct :=
  inhabits

/-- The modality is monotone in its postcondition, as a comprehension over
reducts must be. -/
theorem relyPossibly_mono {T : LambdaTheory} {br : BaseRewrite T}
    {pos : RedexPosition T br} {post post' : (br.ctx ⟶ T.Pr) → Prop}
    (weaker : ∀ q, post q → post' q) {t : br.ctx ⟶ pos.subtermCarrier}
    (inhabits : RelyPossibly pos post t) : RelyPossibly pos post' t := by
  obtain ⟨reduct, steps, accepted⟩ := inhabits
  exact ⟨reduct, steps, weaker reduct accepted⟩

/-- **And the postcondition is load-bearing.**  At a postcondition that accepts
no reduct, nothing inhabits the modality — including the authored subterm, for
which the step obligation is discharged by the base rewrite.  So inhabitation
is not a consequence of the position alone. -/
theorem not_relyPossibly_of_post_empty {T : LambdaTheory} {br : BaseRewrite T}
    (pos : RedexPosition T br) {post : (br.ctx ⟶ T.Pr) → Prop}
    (empty : ∀ q, ¬ post q) (t : br.ctx ⟶ pos.subtermCarrier) :
    ¬ RelyPossibly pos post t := by
  rintro ⟨reduct, -, accepted⟩
  exact empty reduct accepted

/-! ### The reading that was rejected, and the reason -/

/-- The reading that takes the postcondition at the rule's own right-hand side. -/
def rhsOnlyReading {T : LambdaTheory} {br : BaseRewrite T} (pos : RedexPosition T br)
    (post : (br.ctx ⟶ T.Pr) → Prop) (t : br.ctx ⟶ pos.subtermCarrier) : Prop :=
  T.rewriteRel (pos.fillContext t) br.rhs ∧ post br.rhs

/-- **Why it is not used.**  Its postcondition does not mention the inhabitant,
so any two terms whose contexts step to the right-hand side inhabit it
together.  A modality whose elimination cannot distinguish its own inhabitants
is a conjunction of a term predicate with a constant, not a modality. -/
theorem rhsOnlyReading_independent_of_term {T : LambdaTheory} {br : BaseRewrite T}
    {pos : RedexPosition T br} {post : (br.ctx ⟶ T.Pr) → Prop}
    {t u : br.ctx ⟶ pos.subtermCarrier}
    (inhabits : rhsOnlyReading pos post t)
    (steps : T.rewriteRel (pos.fillContext u) br.rhs) :
    rhsOnlyReading pos post u :=
  ⟨steps, inhabits.2⟩

/-- It does imply the reading used here, so nothing the display asserts is
given up by quantifying the reduct. -/
theorem relyPossibly_of_rhsOnlyReading {T : LambdaTheory} {br : BaseRewrite T}
    {pos : RedexPosition T br} {post : (br.ctx ⟶ T.Pr) → Prop}
    {t : br.ctx ⟶ pos.subtermCarrier} (inhabits : rhsOnlyReading pos post t) :
    RelyPossibly pos post t :=
  ⟨br.rhs, inhabits.1, inhabits.2⟩

/-- And at the authored subterm the two agree, which is the display recovered. -/
theorem rhsOnlyReading_subterm_iff {T : LambdaTheory} {br : BaseRewrite T}
    (pos : RedexPosition T br) (post : (br.ctx ⟶ T.Pr) → Prop) :
    rhsOnlyReading pos post pos.subterm ↔ post br.rhs := by
  constructor
  · exact fun inhabits => inhabits.2
  · exact fun accepted => ⟨pos.fills ▸ br.fires, accepted⟩

end Mettapedia.GSLT.Meredith.Modal
