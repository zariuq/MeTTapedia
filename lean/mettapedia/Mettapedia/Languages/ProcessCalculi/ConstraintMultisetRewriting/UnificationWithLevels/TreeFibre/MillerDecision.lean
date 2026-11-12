import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerSolver

/-!
# The tree's driver decides Miller patterns with arbitrary distinct locals

The round of the Miller solver (`millerRound`) reads the first equation and dispatches on its two sides
(`stepView`): two rigid locals (delete or refute), a Miller side against a rigid local in either orientation (project
or refute), two Miller sides (delete, intersect, prune either side, solve either way). On the fragment `InMiller`:

* **progress by shape** (`millerRound_ne_stuck`): a nonempty store is never stuck. The only stuck case, two Miller
  sides with the same locals and incomparable codomains, is excluded by the chain of codomains;
* **stability** (`millerRound_stable`): every step's residual store is again in the fragment;
* **decision** (`miller_decided`): the tree's driver `run`, from some budget on, is fixed and ends with a principal
  answer or a certified refutation.
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

/-! ## Opened equations through the views -/

section Opens

variable {S : Setting Head L}

theorem sideRen_opened_cast {n : Nat} {qs ps ps' : List Head} (img : Fin ps.length → Fin qs.length) (h : ps = ps')
    (t : Tm Head n) :
    Presentation.rename (sideRen qs ps img) (opened ps t) = Presentation.rename (sideRen qs ps' (castImg img h)) (opened ps' t) := by
  subst h
  rfl

theorem opens_flexFlex {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code) (b₁ : S.R.cumulative D₁.c v.d)
    (D₂ : FlexData Θ.raw v.qs e.2.2.code) (b₂ : S.R.cumulative D₂.c v.d) (hl : v.left = .flex D₁ b₁)
    (hr : v.right = .flex D₂ b₂) :
    ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs) (Presentation.rename (sideRen v.qs D₁.ps D₁.img) (opened D₁.ps (f.substitution D₁.unknown)))
        (Presentation.rename (sideRen v.qs D₂.ps D₂.img) (opened D₂.ps (f.substitution D₂.unknown))) (.head v.d) := by
  intro Δ f solved
  have h := eq_opened v f (solved e List.mem_cons_self)
  rw [hl, hr] at h
  simpa only [sideBody, subst_flexBody_opened] using h

theorem opens_flexLocal {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (v : EqView (S := S) e) (D : FlexData Θ.raw v.qs e.1.2.code) (b : S.R.cumulative D.c v.d) (l : Fin v.qs.length)
    (sl : e.2.2.code = localSide v.qs l) (bl : S.R.cumulative (v.qs.get l) v.d) (hl : v.left = .flex D b)
    (hr : v.right = .rigid l sl bl) :
    ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs) (Presentation.rename (sideRen v.qs D.ps D.img) (opened D.ps (f.substitution D.unknown)))
        (.var (loc v.qs l)) (.head v.d) := by
  intro Δ f solved
  have h := eq_opened v f (solved e List.mem_cons_self)
  rw [hl, hr] at h
  simpa only [sideBody, subst_flexBody_opened, Presentation.subst, liftSubs_loc] using h

theorem opens_localFlex {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (v : EqView (S := S) e) (l : Fin v.qs.length) (sl : e.1.2.code = localSide v.qs l)
    (bl : S.R.cumulative (v.qs.get l) v.d) (D : FlexData Θ.raw v.qs e.2.2.code) (b : S.R.cumulative D.c v.d)
    (hl : v.left = .rigid l sl bl) (hr : v.right = .flex D b) :
    ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs) (Presentation.rename (sideRen v.qs D.ps D.img) (opened D.ps (f.substitution D.unknown)))
        (.var (loc v.qs l)) (.head v.d) := by
  intro Δ f solved
  have h := eq_opened v f (solved e List.mem_cons_self)
  rw [hl, hr] at h
  have h' : Equal S.R (ctx Δ.raw v.qs) (.var (loc v.qs l))
      (Presentation.rename (sideRen v.qs D.ps D.img) (opened D.ps (f.substitution D.unknown))) (.head v.d) := by
    simpa only [sideBody, subst_flexBody_opened, Presentation.subst, liftSubs_loc] using h
  exact h'.symm

end Opens

/-! ## The dispatch -/

section Dispatch

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Inhabitants S.R)

include rigid complete in
/-- **Two rigid locals**: delete or refute. -/
def stepLocals {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (v : EqView (S := S) e) (l m : Fin v.qs.length) (sl : e.1.2.code = localSide v.qs l)
    (bl : S.R.cumulative (v.qs.get l) v.d) (sm : e.2.2.code = localSide v.qs m)
    (bm : S.R.cumulative (v.qs.get m) v.d) : Round S.levels millerRank (e :: rest) :=
  if h : l = m then
    .progress (deleteSame (v.annotation_left.trans v.annotation_right.symm) (sl.trans (by rw [h, ← sm])) rest)
      (rank_delete e rest)
  else .refuted (locals_unsolvable rigid complete rest v.annotation_left v.universes v.universe_d sl sm bl bm h)

include facts roots heads algebra rigid complete normalizes inh in
/-- **Two Miller sides**: delete, intersect, prune, or solve. -/
def stepFlexFlex {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code)
    (b₁ : S.R.cumulative D₁.c v.d) (D₂ : FlexData Θ.raw v.qs e.2.2.code) (b₂ : S.R.cumulative D₂.c v.d)
    (opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs) (Presentation.rename (sideRen v.qs D₁.ps D₁.img) (opened D₁.ps (f.substitution D₁.unknown)))
        (Presentation.rename (sideRen v.qs D₂.ps D₂.img) (opened D₂.ps (f.substitution D₂.unknown))) (.head v.d)) :
    Round S.levels millerRank (e :: rest) :=
  if hcode : e.1.2.code = e.2.2.code then
    .progress (deleteSame (v.annotation_left.trans v.annotation_right.symm) hcode rest) (rank_delete e rest)
  else if hF : D₁.unknown = D₂.unknown then
    have hps : D₂.ps = D₁.ps :=
      ((famCode_inj (D₁.declared.symm.trans ((congrArg (Ctx.lookup Θ.raw) hF).trans D₂.declared))).1).symm
    pruneRound facts roots heads algebra rigid complete inh rest families v.universe_d D₁.declared b₁
      (fun i => decide (D₁.img i = castImg D₂.img hps i))
      (by
        by_contra all
        apply hcode
        have same : D₁.img = castImg D₂.img hps := by
          funext i
          by_contra ne
          exact all ⟨i, by simp [ne]⟩
        rw [D₁.side, D₂.side, flexSide_cast D₂.unknown D₂.img hps, ← same, ← hF])
      (occurs_side D₁ (.inl rfl))
      (fun {Δ} f solved => by
        have equal := opens f solved
        rw [sideRen_opened_cast D₂.img hps, ← hF] at equal
        exact intersect_forced inh rigid complete normalizes f v.qs D₁.img (castImg D₂.img hps) D₁.declared
          v.universes (famFacts families D₁.declared).1 (famFacts families D₁.declared).2 b₁ D₁.domains
          (domains_cast hps D₂.domains) _ ((List.nodup_finRange _).filter _)
          (fun i h => List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true h⟩) equal)
  else if hcov₁ : ∀ i, ∃ j, D₂.img j = D₁.img i then
    if hcov₂ : ∀ j, ∃ i, D₁.img i = D₂.img j then
      if hc : S.R.cumulative D₁.c D₂.c then
        solveRound facts roots heads algebra rigid complete inh rest families v.universes v.universe_d D₂.img D₁.img
          D₂.declared D₁.declared D₂.injective D₁.injective D₂.domains D₁.domains b₂ hF hcov₁ hc
          (occurs_side D₂ (.inr rfl)) (occurs_side D₁ (.inl rfl)) opens
      else if hc' : S.R.cumulative D₂.c D₁.c then
        solveRound facts roots heads algebra rigid complete inh rest families v.universes v.universe_d D₁.img D₂.img
          D₁.declared D₂.declared D₁.injective D₂.injective D₁.domains D₂.domains b₁ (fun h => hF h.symm) hcov₂ hc'
          (occurs_side D₁ (.inl rfl)) (occurs_side D₂ (.inr rfl)) (fun f solved => (opens f solved).symm)
      else .stuck
    else
      pruneRound facts roots heads algebra rigid complete inh rest families v.universe_d D₂.declared b₂
        (fun j => decide (∃ i, D₁.img i = D₂.img j))
        (by
          by_contra all
          apply hcov₂
          intro j
          by_contra missing
          exact all ⟨j, by simp [missing]⟩)
        (occurs_side D₂ (.inr rfl))
        (fun {Δ} f solved => prune_forced inh f v.qs D₂.img D₁.img v.universes
          (famFacts families D₂.declared).1 D₂.domains D₂.injective _ ((List.nodup_finRange _).filter _)
          (fun j h => List.mem_filter.mpr ⟨List.mem_finRange j, decide_eq_true h⟩) (opens f solved).symm)
  else
    pruneRound facts roots heads algebra rigid complete inh rest families v.universe_d D₁.declared b₁
      (fun i => decide (∃ j, D₂.img j = D₁.img i))
      (by
        by_contra all
        apply hcov₁
        intro i
        by_contra missing
        exact all ⟨i, by simp [missing]⟩)
      (occurs_side D₁ (.inl rfl))
      (fun {Δ} f solved => prune_forced inh f v.qs D₁.img D₂.img v.universes
        (famFacts families D₁.declared).1 D₁.domains D₁.injective _ ((List.nodup_finRange _).filter _)
        (fun i h => List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true h⟩) (opens f solved))

include facts roots heads algebra rigid complete normalizes inh in
/-- **One step on a Miller equation.** -/
def stepView {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) (v : EqView (S := S) e) : Round S.levels millerRank (e :: rest) :=
  match hl : v.left, hr : v.right with
  | .rigid l sl bl, .rigid m sm bm => stepLocals rigid complete rest v l m sl bl sm bm
  | .flex D b, .rigid l sl bl =>
      stepFlexLocal facts roots heads algebra rigid complete inh rest families v.universes v.universe_d D.img
        D.declared D.injective D.domains b l (occurs_side D (.inl rfl)) (opens_flexLocal v D b l sl bl hl hr)
  | .rigid l sl bl, .flex D b =>
      stepFlexLocal facts roots heads algebra rigid complete inh rest families v.universes v.universe_d D.img
        D.declared D.injective D.domains b l (occurs_side D (.inr rfl)) (opens_localFlex v l sl bl D b hl hr)
  | .flex D₁ b₁, .flex D₂ b₂ =>
      stepFlexFlex facts roots heads algebra rigid complete normalizes inh rest families v D₁ b₁ D₂ b₂
        (opens_flexFlex v D₁ b₁ D₂ b₂ hl hr)

include facts roots heads algebra rigid complete normalizes inh in
/-- **The round of the Miller solver.** -/
def millerRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels millerRank problem
  | _, [] => .stuck
  | Γ, e :: rest =>
      if hf : Families Γ then
        match readEq (S := S) e with
        | some v => stepView facts roots heads algebra rigid complete normalizes inh rest hf v
        | none => .stuck
      else .stuck

/-- **The Miller solver of the tree's driver.** -/
def millerSolver : ContextualDependentWorklist.Solver S.levels where
  rank := millerRank
  round := millerRound facts roots heads algebra rigid complete normalizes inh

end Dispatch

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
