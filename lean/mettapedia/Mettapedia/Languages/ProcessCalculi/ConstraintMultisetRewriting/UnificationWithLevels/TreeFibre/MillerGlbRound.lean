import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlb
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerDecided

/-!
# The Miller solver without the chain of codomains: lowering to the greatest lower bound as a round

The Miller solver is stuck on exactly one shape: `λ ȳ. F y_ā ≐ λ ȳ. G y_b̄` with `F ≠ G`, both sides covering each
other, and incomparable codomains. Lowering both unknowns, in place, to a greatest lower bound `g` of the codomains is
exact (`millerGlb_exact`). After it the two codomains are both `g`, so the solving step applies at once:
`G := λ z̄. F z_{b⁻¹ā}` over the lowered telescope.

* **A lowering keeps the reading** (`lowerSide`, `lowerView`, `lowering_views`, `lowering_families`): every equation
  is read over the lowered telescope with the same codes and unknowns, the lowered unknown at the lower codomain.
* **A lowering keeps the rank** (`occ_lowered`, `weight_lowered`, `millerRank_lowered`): the occurring unknowns and
  their arities do not change.
* **The round** (`glbSolveRound`): the lowering, then the solving step, as one update (`roundAfter`). Its rank is
  below the store's, because the solving step lowers the weight of the lowered store, whose rank is the store's.
  Lowering alone would lower no rank.
* **The solver** (`stepViewGlb`, `millerGlbRound`, `millerGlbSolver`): the Miller round, except that the shape it is
  stuck on is lowered and solved, for a greatest lower bound given by a function (`glb`, with its specification).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## A lowering keeps the reading and the rank -/

section Lowering

variable {S : Setting Head L} (algebra : CumulativeAlgebra S.R)

/-- A lowering keeps every declaration a universe family. -/
theorem lowering_families {Θ : Context S.R} (ℓ : CodomainLowering Θ) (families : Families Θ) :
    Families ℓ.target := by
  intro i
  by_cases h : i = ℓ.index
  · rw [h]
    exact ⟨ℓ.ps, ℓ.lower, ℓ.lookup_self, ℓ.universes, ℓ.universe_lower⟩
  · obtain ⟨ps, c, hi, u, hc⟩ := families i
    exact ⟨ps, c, (ℓ.lookup_ne h).trans hi, u, hc⟩

/-- The codes of a term read over the lowered telescope are its codes. -/
theorem lowered_code {Θ : Context S.R} (ℓ : CodomainLowering Θ) (t : TotalTerm Θ) :
    ((frames S.levels).act ℓ.hom t).2.code = t.2.code := by
  change Presentation.subst ids t.2.code = t.2.code
  exact subst_ids _

theorem lowered_typeCode {Θ : Context S.R} (ℓ : CodomainLowering Θ) (t : TotalTerm Θ) :
    ((frames S.levels).act ℓ.hom t).1.code = t.1.code := by
  change Presentation.subst ids t.1.code = t.1.code
  exact subst_ids _

include algebra in
/-- **A side read over the lowered telescope**: the same code and unknown; the lowered unknown at the lower codomain,
which still lies below the annotation's codomain. -/
def lowerSide {Θ : Context S.R} (ℓ : CodomainLowering Θ) {qs : List Head} {d : Head} (t : TotalTerm Θ) :
    SideView (S := S) Θ.raw qs d t.2.code →
      SideView (S := S) ℓ.target.raw qs d ((frames S.levels).act ℓ.hom t).2.code
  | .flex D below =>
      if h : D.unknown = ℓ.index then
        have same : Ctx.lookup Θ.raw ℓ.index = famCode D.ps D.c := h ▸ D.declared
        have parts := famCode_inj (ℓ.declared.symm.trans same)
        .flex
          { unknown := D.unknown
            ps := D.ps
            c := ℓ.lower
            img := D.img
            side := (lowered_code ℓ t).trans D.side
            declared := by rw [h, ℓ.lookup_self, parts.1]
            injective := D.injective
            domains := D.domains }
          (algebra.trans ℓ.below (by rw [parts.2]; exact below))
      else
        .flex
          { unknown := D.unknown
            ps := D.ps
            c := D.c
            img := D.img
            side := (lowered_code ℓ t).trans D.side
            declared := (ℓ.lookup_ne h).trans D.declared
            injective := D.injective
            domains := D.domains }
          below
  | .rigid l side below => .rigid l ((lowered_code ℓ t).trans side) below

include algebra in
/-- **An equation read over the lowered telescope.** -/
def lowerView {Θ : Context S.R} (ℓ : CodomainLowering Θ) {e : Equation (TotalTerm Θ)} (v : EqView (S := S) e) :
    EqView (S := S)
      (((frames S.levels).act ℓ.hom e.1, (frames S.levels).act ℓ.hom e.2) : Equation (TotalTerm ℓ.target)) where
  qs := v.qs
  d := v.d
  annotation_left := (lowered_typeCode ℓ e.1).trans v.annotation_left
  annotation_right := (lowered_typeCode ℓ e.2).trans v.annotation_right
  universes := v.universes
  universe_d := v.universe_d
  left := lowerSide algebra ℓ e.1 v.left
  right := lowerSide algebra ℓ e.2 v.right

include algebra in
/-- **A lowering keeps every equation read.** -/
theorem lowering_views {Θ : Context S.R} (ℓ : CodomainLowering Θ) (store : EquationStore (TotalTerm Θ))
    (views : ∀ e ∈ store, Nonempty (EqView (S := S) e)) :
    ∀ e ∈ (frames S.levels).applyStore ℓ.hom store, Nonempty (EqView (S := S) e) := by
  intro e member
  obtain ⟨e₁, inStore, rfl⟩ := List.mem_map.mp member
  obtain ⟨w⟩ := views e₁ inStore
  exact ⟨lowerView algebra ℓ w⟩

/-- **A lowering keeps the occurring unknowns.** -/
theorem occ_lowered {Θ : Context S.R} (ℓ : CodomainLowering Θ) :
    ∀ store : EquationStore (TotalTerm Θ), occ ((frames S.levels).applyStore ℓ.hom store) = occ store
  | [] => rfl
  | e :: rest => by
      show ((frames S.levels).act ℓ.hom e.1).2.code.support ∪ ((frames S.levels).act ℓ.hom e.2).2.code.support ∪
          occ ((frames S.levels).applyStore ℓ.hom rest) = e.1.2.code.support ∪ e.2.2.code.support ∪ occ rest
      rw [lowered_code ℓ e.1, lowered_code ℓ e.2, occ_lowered ℓ rest]
      rfl

/-- **A lowering keeps the weight**: the arity of the lowered family does not change. -/
theorem weight_lowered {Θ : Context S.R} (ℓ : CodomainLowering Θ) (store : EquationStore (TotalTerm Θ)) :
    weight ((frames S.levels).applyStore ℓ.hom store) = weight store := by
  unfold weight
  rw [occ_lowered ℓ store]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = ℓ.index
  · rw [h, ℓ.lookup_self, ℓ.declared, famArity_famCode, famArity_famCode]
  · rw [ℓ.lookup_ne h]
    rfl

/-- **A lowering keeps the rank of the Miller solver.** -/
theorem millerRank_lowered {Θ : Context S.R} (ℓ : CodomainLowering Θ) (store : EquationStore (TotalTerm Θ)) :
    millerRank ((frames S.levels).applyStore ℓ.hom store) = millerRank store := by
  unfold millerRank
  rw [weight_lowered ℓ store]
  simp [Frames.applyStore]

end Lowering

/-! ## A round after an update that keeps the rank -/

section After

variable {S : Setting Head L}

/-- A store with a solution has a residual store with one. -/
theorem solvable_remaining {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (first : Update S.levels problem) (solvable : (frames S.levels).Solvable problem) :
    (frames S.levels).Solvable first.remaining := by
  obtain ⟨Δ, f, solved⟩ := solvable
  obtain ⟨residual, models, _⟩ := first.complete Δ f solved
  exact ⟨Δ, residual, models⟩

/-- **The update, then the round on its residual store**, when the update keeps the rank. -/
def roundAfter {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (first : Update S.levels problem)
    (same : millerRank first.remaining = millerRank problem) :
    Round S.levels millerRank first.remaining → Round S.levels millerRank problem
  | .progress u smaller => .progress (first.then u) (by rw [← same]; exact smaller)
  | .refuted absent => .refuted fun solvable => absent (solvable_remaining first solvable)
  | .stuck => .stuck

theorem roundAfter_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (first : Update S.levels problem) (same : millerRank first.remaining = millerRank problem)
    {r : Round S.levels millerRank first.remaining} (moves : r ≠ .stuck) : roundAfter first same r ≠ .stuck := by
  cases r with
  | progress u smaller => intro h; cases h
  | refuted absent => intro h; cases h
  | stuck => exact absurd rfl moves

theorem roundAfter_progress {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (first : Update S.levels problem) (same : millerRank first.remaining = millerRank problem)
    {r : Round S.levels millerRank first.remaining} {update : Update S.levels problem}
    {smaller : Below (millerRank update.remaining) (millerRank problem)}
    (progressed : roundAfter first same r = .progress update smaller) :
    ∃ u s, r = .progress u s ∧ update = first.then u := by
  cases r with
  | progress u s =>
      cases progressed
      exact ⟨u, s, rfl, rfl⟩
  | refuted absent => cases progressed
  | stuck => cases progressed

end After

/-! ## The round: lower both unknowns to the greatest lower bound, then solve -/

section Round

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Inhabitants S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- **The equation opens over the lowered telescope**: a solution of the lowered store is one of the store through
the two lowerings, which act as the identity on codes. -/
theorem lowered_opens {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code)
    (b₁ : S.R.cumulative D₁.c v.d) (D₂ : FlexData Θ.raw v.qs e.2.2.code) (b₂ : S.R.cumulative D₂.c v.d)
    (hl : v.left = .flex D₁ b₁) (hr : v.right = .flex D₂ b₂) {g : Head} (isGlb : IsGlb S.R g D₁.c D₂.c)
    (ne : D₁.unknown ≠ D₂.unknown) :
    ∀ {Δ : Context S.R} (f : Δ ⟶ (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).target),
      (frames S.levels).Models f ((frames S.levels).applyStore
        (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).hom
          ((frames S.levels).applyStore (millerLowerF families v D₁ D₂.c isGlb).hom (e :: rest))) →
      Equal S.R (ctx Δ.raw v.qs)
        (Presentation.rename (sideRen v.qs D₁.ps D₁.img) (opened D₁.ps (f.substitution D₁.unknown)))
        (Presentation.rename (sideRen v.qs D₂.ps D₂.img) (opened D₂.ps (f.substitution D₂.unknown))) (.head v.d) := by
  intro Δ f solved
  have middle := (Frames.models_applyStore (X := frames S.levels)
    (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).hom f
    ((frames S.levels).applyStore (millerLowerF families v D₁ D₂.c isGlb).hom (e :: rest))).mp solved
  have back := (Frames.models_applyStore (X := frames S.levels)
    (millerLowerF families v D₁ D₂.c isGlb).hom _ (e :: rest)).mp middle
  exact opens_flexFlex v D₁ b₁ D₂ b₂ hl hr _ back

include inh facts roots heads algebra rigid complete headTypingUnique in
/-- **Lower, then solve.** For `λ ȳ. F y_ā ≐ λ ȳ. G y_b̄` with `F ≠ G` and every local of `ā` among `b̄`: both
unknowns lowered to `g`, then `G := λ z̄. F z_{b⁻¹ā}` over the lowered telescope. -/
def glbSolveRound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code)
    (b₁ : S.R.cumulative D₁.c v.d) (D₂ : FlexData Θ.raw v.qs e.2.2.code) (b₂ : S.R.cumulative D₂.c v.d)
    (hl : v.left = .flex D₁ b₁) (hr : v.right = .flex D₂ b₂) {g : Head} (isGlb : IsGlb S.R g D₁.c D₂.c)
    (ne : D₁.unknown ≠ D₂.unknown) (cover : ∀ i, ∃ j, D₂.img j = D₁.img i) :
    Round S.levels millerRank (e :: rest) :=
  roundAfter
    (millerGlbUpdate inh facts roots heads algebra rigid complete headTypingUnique families v D₁ b₁ D₂ b₂ hl hr isGlb
      (fun h => ne h.symm) rest)
    (by
      show millerRank ((frames S.levels).applyStore (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).hom
        ((frames S.levels).applyStore (millerLowerF families v D₁ D₂.c isGlb).hom (e :: rest))) = _
      rw [millerRank_lowered, millerRank_lowered])
    (solveRound facts roots heads algebra rigid complete inh
      (e := ((frames S.levels).act (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).hom
          ((frames S.levels).act (millerLowerF families v D₁ D₂.c isGlb).hom e.1),
        (frames S.levels).act (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).hom
          ((frames S.levels).act (millerLowerF families v D₁ D₂.c isGlb).hom e.2)))
      ((frames S.levels).applyStore (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).hom
        ((frames S.levels).applyStore (millerLowerF families v D₁ D₂.c isGlb).hom rest))
      (lowering_families _ (lowering_families _ families)) v.universes v.universe_d D₂.img D₁.img
      (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).lookup_self
      (((millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).lookup_ne ne).trans
        (millerLowerF families v D₁ D₂.c isGlb).lookup_self)
      D₂.injective D₁.injective D₂.domains D₁.domains (algebra.trans isGlb.2.2.1 b₂) ne cover
      (S.levels.cumulative_refl isGlb.1)
      (by
        show D₂.unknown ∈ occ ((frames S.levels).applyStore (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).hom
          ((frames S.levels).applyStore (millerLowerF families v D₁ D₂.c isGlb).hom (e :: rest)))
        rw [occ_lowered, occ_lowered]
        exact occurs_side D₂ (.inr rfl))
      (by
        show D₁.unknown ∈ occ ((frames S.levels).applyStore (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).hom
          ((frames S.levels).applyStore (millerLowerF families v D₁ D₂.c isGlb).hom (e :: rest)))
        rw [occ_lowered, occ_lowered]
        exact occurs_side D₁ (.inl rfl))
      (lowered_opens rest families v D₁ b₁ D₂ b₂ hl hr isGlb ne))

/-- **The shape the Miller solver is stuck on**: two flex sides of different unknowns covering each other, with
incomparable codomains. -/
def GlbShape {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {qs : List Head}
    (D₁ : FlexData Θ.raw qs e.1.2.code) (D₂ : FlexData Θ.raw qs e.2.2.code) : Prop :=
  D₁.unknown ≠ D₂.unknown ∧ (∀ i, ∃ j, D₂.img j = D₁.img i) ∧ (∀ j, ∃ i, D₁.img i = D₂.img j) ∧
    ¬ S.R.cumulative D₁.c D₂.c ∧ ¬ S.R.cumulative D₂.c D₁.c

instance {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {qs : List Head} (D₁ : FlexData Θ.raw qs e.1.2.code)
    (D₂ : FlexData Θ.raw qs e.2.2.code) : Decidable (GlbShape (S := S) D₁ D₂) := by
  unfold GlbShape
  infer_instance

include facts roots heads algebra rigid complete normalizes inh headTypingUnique spec in
/-- **One step on a Miller equation, without the chain**: the Miller step, except that its stuck shape is lowered to
the greatest lower bound and solved. -/
def stepViewGlb {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) (v : EqView (S := S) e) : Round S.levels millerRank (e :: rest) :=
  match hl : v.left, hr : v.right with
  | .flex D₁ b₁, .flex D₂ b₂ =>
      if shape : GlbShape (S := S) D₁ D₂ then
        match found : glb D₁.c D₂.c with
        | some _ =>
            glbSolveRound facts roots heads algebra rigid complete inh headTypingUnique rest families v D₁ b₁ D₂ b₂
              hl hr (spec found) shape.1 shape.2.1
        | none => .stuck
      else stepView facts roots heads algebra rigid complete normalizes inh rest families v
  | _, _ => stepView facts roots heads algebra rigid complete normalizes inh rest families v

include facts roots heads algebra rigid complete normalizes inh headTypingUnique spec in
/-- **The round of the Miller solver without the chain.** -/
def millerGlbRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) →
    Round S.levels millerRank problem
  | _, [] => .stuck
  | Γ, e :: rest =>
      if hf : Families Γ then
        match readEq (S := S) e with
        | some v =>
            stepViewGlb facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec rest hf v
        | none => .stuck
      else .stuck

/-- **The Miller solver without the chain of codomains.** -/
def millerGlbSolver : ContextualDependentWorklist.Solver S.levels where
  rank := millerRank
  round := millerGlbRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec

end Round

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
