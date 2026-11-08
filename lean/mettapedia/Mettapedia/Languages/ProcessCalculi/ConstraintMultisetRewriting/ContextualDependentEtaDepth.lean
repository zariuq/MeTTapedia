import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReads

/-!
# Equal abstraction depths by η-expansion

The readers of codes at depth 0 (the head clash, the decompositions) read both sides under their common abstractions,
so they need both sides to have the same abstraction structure. A store equation can have sides of different depths,
`λ g. g ≐ λ g x. x`, and the census opens both at the left side's depth only. Such fragment stores leave the
under-binder round stuck (`ContextualDependentEtaDepthGap`).

**η-expansion to a depth** (`expandTo`) keeps leading abstractions and applies a side that is not an abstraction to
fresh variables, until the depth is reached. At an annotation with at least that many Π binders:

* it is typed equality (`expand_equal`), by function η (`eta_equal`) and congruence under abstractions;
* it keeps closed normal Miller reducts (`MarkedReduct.expand`): applying to a fresh rigid local keeps Miller
  occurrences (`miller_apply_fresh`, `MarkedReduct.apply_fresh`).

**The η-long store** (`expandStore`) expands both sides of every equation to their annotations' Π counts. It has exactly
the store's solutions (`expand_equivalent`), its weight (`storeWeight_expand`, since the weight is read on η-long normal
forms) and stays in the permuted Miller class (`PermutedMiller.expand`). On a store with homogeneous normal annotations
both sides of every equation then have the annotation's full depth, the η-long reading of R88.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Function η**: a function equals the abstraction of its application to a fresh variable. -/
theorem eta_equal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {f A : Tm Head n} {B : Tm Head (n + 1)}
    (typed : Typed S.R Γ f (.pi A B)) :
    Equal S.R Γ f (.lam (.app (Presentation.rename wk f) (.var 0))) (.pi A B) := by
  obtain ⟨u, hu, piTyped⟩ := TypedEquality.Normalization.Typed.isType typed formed
  have body := ContextualDependentEtaLong.typed_apply_fresh (S := S) typed
  have lamTyped : Typed S.R Γ (.lam (.app (Presentation.rename wk f) (.var 0))) (.pi A B) :=
    .lamIntro piTyped hu body
  refine .etaPi typed lamTyped ?_
  have piWeak : Typed S.R (.snoc Γ A) (Presentation.rename wk (Tm.pi A B))
      (Presentation.rename wk (Tm.head u : Tm Head n)) := piTyped.weaken
  have bodyWeak := body.rename (CtxRen.snoc (Gamma := Γ) (Delta := .snoc Γ A) (rho := wk) (fun _ => rfl) A)
  have beta := Derivable.betaPi (R := S.R) piWeak hu bodyWeak (Derivable.var 0)
  rw [inst0_var_rename_liftRen_wk, inst0_var_rename_liftRen_wk] at beta
  exact .symm beta

/-- **η-expansion to a depth**: abstractions are kept, and below them a side that is not an abstraction is applied to
fresh variables, until `count` abstractions are reached. -/
def expandTo {n : Nat} : Nat → Tm Head n → Tm Head n
  | 0, t => t
  | count + 1, .lam body => .lam (expandTo count body)
  | count + 1, t => .lam (expandTo count (.app (Presentation.rename wk t) (.var 0)))

variable (facts : FormFacts S.R S.roles)

include facts in
/-- **η-expansion is typed equality** at an annotation with at least as many Π binders. -/
theorem expand_equal : ∀ (count : Nat) {n : Nat} {Γ : Ctx Head n} {t T : Tm Head n}, CtxFormed S.R Γ →
    Typed S.R Γ t T → count ≤ piCount T → Equal S.R Γ t (expandTo count t) T
  | 0, _, _, _, _, _, typed, _ => .refl typed
  | count + 1, n, Γ, t, T, formed, typed, deep => by
      cases T
      case pi A B =>
        obtain ⟨u, hu, piTyped⟩ := TypedEquality.Normalization.Typed.isType typed formed
        have deepB : count ≤ piCount B := by
          simp only [piCount] at deep
          omega
        have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed (IsType.pi_parts ⟨u, hu, piTyped⟩).1
        cases t
        case lam body =>
          exact .lamCong piTyped hu (expand_equal count formedA (Typed.lam_inv facts typed formed) deepB)
        all_goals
          exact .trans (eta_equal formed typed) (.lamCong piTyped hu
            (expand_equal count formedA (ContextualDependentEtaLong.typed_apply_fresh typed) deepB))
      all_goals
        simp only [piCount] at deep
        omega

/-! ## Miller reducts -/

section Reducts

open ContextualDependentCumulativeClosure ContextualDependentExecutableJoin ContextualDependentCensus
open ContextualDependentGeneralPattern (liftFlexible)

variable {R : Rules Head}

omit [UniverseLevel.LevelOrder L] in
/-- A side with Miller occurrences whose spine head is flexible is a Miller spine. -/
theorem millerSpine_of_flexible {n : Nat} {mark : Fin n → Bool} {t : Tm Head n} (holds : miller mark t = true)
    (flexible : flexHead mark (spineHead t) = true) : millerSpine mark t = true := by
  cases t
  case var i =>
    simp only [spineHead, flexHead] at flexible
    simp [millerSpine, readSpine, flexible]
  case app f a =>
    simp only [spineHead] at flexible
    simp only [miller, flexible, if_true] at holds
    exact holds
  all_goals simp [spineHead, flexHead] at flexible

omit [UniverseLevel.LevelOrder L] in
/-- A Miller spine applied to a fresh rigid local is a Miller spine. -/
theorem millerSpine_apply_fresh {n : Nat} {mark : Fin n → Bool} {t : Tm Head n} (spine : millerSpine mark t = true) :
    millerSpine (liftFlexible mark) (.app (Presentation.rename wk t) (.var 0)) = true := by
  unfold millerSpine at spine ⊢
  simp only [readSpine, readSpine_rename]
  cases read : readSpine t with
  | none => rw [read] at spine; cases spine
  | some found =>
      obtain ⟨head, arguments⟩ := found
      rw [read] at spine
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_true_eq] at spine
      obtain ⟨⟨flexibleHead, rigidArguments⟩, distinct⟩ := spine
      simp only [Option.map_some, Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.mem_map,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, List.nodup_cons]
      refine ⟨⟨flexibleHead, ?_⟩, ?_, distinct.map (Fin.succ_injective _)⟩
      · rintro argument (rfl | ⟨prior, member, rfl⟩)
        · rfl
        · exact rigidArguments prior member
      · rintro ⟨prior, _, same⟩
        exact Fin.succ_ne_zero _ same

omit [UniverseLevel.LevelOrder L] in
/-- **Miller occurrences are kept by applying to a fresh rigid local.** -/
theorem miller_apply_fresh {n : Nat} {mark : Fin n → Bool} {t : Tm Head n} (holds : miller mark t = true) :
    miller (liftFlexible mark) (.app (Presentation.rename wk t) (.var 0)) = true := by
  simp only [miller]
  split
  · rename_i flexibleSpine
    rw [spineHead_rename, flexHead_rename wk (flexible := mark) (fun _ => rfl)] at flexibleSpine
    exact millerSpine_apply_fresh (millerSpine_of_flexible holds flexibleSpine)
  · simp only [Bool.and_eq_true]
    exact ⟨miller_rename t (Fin.succ_injective _) (fun _ => rfl) holds, trivial⟩

variable (empty : R.computation = RootComputation.empty)
include empty

omit [UniverseLevel.LevelOrder L] in
/-- **Applying to a fresh local keeps a normal Miller reduct**, with the local rigid. -/
theorem MarkedReduct.apply_fresh {n : Nat} {mark : Fin n → Bool} {t : Tm Head n} (reduct : MarkedReduct R mark t) :
    MarkedReduct R (liftFlexible mark) (.app (Presentation.rename wk t) (.var 0)) := by
  obtain ⟨t', steps, normal, millerT⟩ := reduct
  refine ⟨openNormal 1 t', (star_app (star_rename wk steps) .refl).trans (openCode_star t' 1),
    openNormal_normal empty normal 1, ?_⟩
  rw [show openNormal 1 t' = ContextualDependentCoverageReadersHalf.openStep t' from
    ContextualDependentCoverageReadersHalf.openNormal_succ t' 0]
  cases t'
  case lam body => exact millerT
  all_goals exact miller_apply_fresh millerT

omit [UniverseLevel.LevelOrder L] in
/-- **η-expansion keeps a normal Miller reduct**, at every marking. -/
theorem MarkedReduct.expand : ∀ (count : Nat) {n : Nat} {mark : Fin n → Bool} {t : Tm Head n},
    MarkedReduct R mark t → MarkedReduct R mark (expandTo count t)
  | 0, _, _, _, reduct => reduct
  | count + 1, _, _, t, reduct => by
      cases t
      case lam body =>
        exact MarkedReduct.lam empty (MarkedReduct.expand count (MarkedReduct.of_lam empty reduct))
      all_goals exact MarkedReduct.lam empty (MarkedReduct.expand count (MarkedReduct.apply_fresh empty reduct))

end Reducts

/-! ## The η-long store -/

section Store

open ContextualDependentRank ContextualDependentMillerClosure ContextualDependentCumulativeClosure

variable (facts : FormFacts S.R S.roles)

/-- **A side η-expanded to its annotation's Π count.** -/
def expandSide {Θ : Context S.R} (term : TotalTerm Θ) : TotalTerm Θ :=
  ⟨term.1, ⟨expandTo (piCount term.1.code) term.2.code,
    (TypedEquality.Normalization.Equal.typed (expand_equal facts _ Θ.formed term.2.typed le_rfl) Θ.formed).2⟩⟩

theorem expandSide_equivalent {Θ : Context S.R} (term : TotalTerm Θ) :
    (frames S.levels).E term (expandSide facts term) :=
  ⟨IsType.refl term.1.isType, expand_equal facts _ Θ.formed term.2.typed le_rfl⟩

/-- **The η-long store**: both sides of every equation η-expanded to their annotations' Π counts. -/
def expandStore {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : EquationStore (TotalTerm Θ) :=
  problem.map fun equation => (expandSide facts equation.1, expandSide facts equation.2)

theorem expand_solves {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ)) :
    (frames S.levels).Solves σ (expandSide facts equation.1, expandSide facts equation.2) ↔
      (frames S.levels).Solves σ equation := by
  have first := (frames S.levels).preserves σ (expandSide_equivalent facts equation.1)
  have second := (frames S.levels).preserves σ (expandSide_equivalent facts equation.2)
  have eqv := (frames S.levels).equivalence Δ
  exact ⟨fun solved => eqv.trans first (eqv.trans solved (eqv.symm second)),
    fun solved => eqv.trans (eqv.symm first) (eqv.trans solved second)⟩

/-- **The η-long store has exactly the solutions of the store.** -/
theorem expand_equivalent {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    (frames S.levels).Equivalent problem (expandStore facts problem) := fun _ σ => by
  simp only [expandStore, Frames.Models, List.forall_mem_map]
  exact forall₂_congr fun equation _ => (expand_solves facts σ equation).symm

variable (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

/-- **The η-long store has the weight of the store.** -/
theorem storeWeight_expand {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      storeWeight facts roots heads algebra rigid complete (expandStore facts problem) =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      have tail := storeWeight_expand rest
      simp only [expandStore, List.map_cons, storeWeight, equationWeight] at tail ⊢
      rw [tail, ← sideWeight_of_equivalent facts roots heads algebra rigid complete
        (expandSide_equivalent facts equation.1), ← sideWeight_of_equivalent facts roots heads algebra rigid complete
        (expandSide_equivalent facts equation.2)]

include rigid in
/-- **The η-long store stays in the permuted Miller class** on a strongly normalizing package without root
computation. -/
theorem PermutedMiller.expand (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels (expandStore facts problem) :=
  PermutedMiller.map_equivalent permuted (expandSide facts) (expandSide_equivalent facts)
    (fun _ _ sides => by
      obtain ⟨left, right⟩ := side_reduct rigid sn sides
      exact sides_of_reducts (computation_empty rigid)
        (MarkedReduct.expand (computation_empty rigid) _ left)
        (MarkedReduct.expand (computation_empty rigid) _ right))

end Store

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
