import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCoverageReadersHalfEvery

/-!
# Dead binders under live binders: the solutions, the weight and the class

The every-rule family reads a dead binder only as the outermost abstraction of both sides
(`ContextualDependentAcceptance4.middle_gap`). Under live binders, the dead binder is the last declaration of the
opened context, where R119's dead binder applies. This file proves the logical half of reading it there.

**An equation of abstractions read over its binder** (`Abstracts`): both annotations are Π types over one domain and
both sides are abstractions; the opened equation lives over the binder's declaration. Such an equation has the opened
equation's solutions under the lifted solution (`solves_abstracts_iff`) and its weight (`equationWeight_abstracts`),
since an abstraction weighs what its body weighs.

**Dropping a dead binder under live binders** (`DropsDead`) is R119's dead binder in front, or, under one live binder
of both sides, dropping a dead binder from the opened equation and closing it again. It keeps the solutions where
typed equality strengthens past an unused variable (`DropsDead.solves`), the weight (`DropsDead.weight`), equal
annotations (`DropsDead.sameType`), closed normal Miller reducts of both sides at every marking (`DropsDead.reducts`)
and so the permuted Miller class (`PermutedMiller.dropsDead`), and it removes one abstraction from the left side
(`DropsDead.depth`).

The executable reading of `DropsDead` and its eventual constancy are in `ContextualDependentAcceptance4UnderReading`;
the family running every rule behind it is in `ContextualDependentAcceptance4UnderFamily`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance4

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentDynamicFragment
open ContextualDependentExecutableJoin ContextualDependentCumulativeClosure ContextualDependentOpenedNormal
open ContextualDependentIntersectionGeneral ContextualDependentEtaLong

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Equations of abstractions -/

/-- **An equation of abstractions read over its binder.** -/
structure Abstracts {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (domain : TypeOver Θ)
    (opened : Equation (TotalTerm (extend Θ domain))) : Prop where
  leftType : equation.1.1.code = .pi domain.code opened.1.1.code
  rightType : equation.2.1.code = .pi domain.code opened.2.1.code
  leftTerm : equation.1.2.code = .lam opened.1.2.code
  rightTerm : equation.2.2.code = .lam opened.2.2.code

section Solutions

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)

include facts roots in
/-- **An equation of abstractions has the opened equation's solutions** under the lifted solution. -/
theorem solves_abstracts_iff {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {domain : TypeOver Θ}
    {opened : Equation (TotalTerm (extend Θ domain))} (abstracts : Abstracts equation domain opened)
    (same : opened.2.1.code = opened.1.1.code) {Δ : Context S.R} (σ : Δ ⟶ Θ) :
    (frames S.levels).Solves σ equation ↔ (frames S.levels).Solves (rawLift σ domain) opened := by
  have sameTypes : equation.2.1.code = equation.1.1.code := by
    rw [abstracts.rightType, abstracts.leftType, same]
  constructor
  · rintro ⟨_, equal⟩
    change Equal S.R Δ.raw (subst σ.substitution equation.1.2.code) (subst σ.substitution equation.2.2.code)
        (subst σ.substitution equation.1.1.code) at equal
    have isPi := (equation.1.1.reindex σ).isType
    change IsType S.R Δ.raw (subst σ.substitution equation.1.1.code) at isPi
    rw [abstracts.leftType] at isPi equal
    rw [abstracts.leftTerm, abstracts.rightTerm] at equal
    change Equal S.R Δ.raw (.lam (subst (liftSub σ.substitution) opened.1.2.code))
      (.lam (subst (liftSub σ.substitution) opened.2.2.code))
      (.pi (subst σ.substitution domain.code) (subst (liftSub σ.substitution) opened.1.1.code)) at equal
    change IsType S.R Δ.raw (.pi (subst σ.substitution domain.code)
      (subst (liftSub σ.substitution) opened.1.1.code)) at isPi
    have domainType : IsType S.R Δ.raw (subst σ.substitution domain.code) := (IsType.pi_parts isPi).1
    have formedExt : CtxFormed S.R (.snoc Δ.raw (subst σ.substitution domain.code)) := Δ.formed.snoc domainType
    have weakened := Equal.weaken (extension := subst σ.substitution domain.code) equal
    have applied := Derivable.appCong weakened (.refl (Derivable.var 0))
    change Equal S.R _ _ _ (inst0 (.var 0) (Presentation.rename (liftRen wk)
      (subst (liftSub σ.substitution) opened.1.1.code))) at applied
    rw [inst0_var_rename_liftRen_wk] at applied
    have left := (WhRed.preserve facts roots formedExt (whRed_eta_lam (R := S.R) (roles := S.roles)
      (subst (liftSub σ.substitution) opened.1.2.code)) (Equal.typed applied formedExt).1).2
    have right := (WhRed.preserve facts roots formedExt (whRed_eta_lam (R := S.R) (roles := S.roles)
      (subst (liftSub σ.substitution) opened.2.2.code)) (Equal.typed applied formedExt).2).2
    refine ⟨?_, left.symm.trans (applied.trans right)⟩
    change TypeEq S.R _ (subst (liftSub σ.substitution) opened.1.1.code)
      (subst (liftSub σ.substitution) opened.2.1.code)
    rw [same]
    exact (opened.1.1.reindex (rawLift σ domain)).isType.refl
  · rintro ⟨_, equal⟩
    change Equal S.R (.snoc Δ.raw (subst σ.substitution domain.code))
      (subst (liftSub σ.substitution) opened.1.2.code) (subst (liftSub σ.substitution) opened.2.2.code)
      (subst (liftSub σ.substitution) opened.1.1.code) at equal
    have formed := (equation.1.1.reindex σ).formed
    have universe' := (equation.1.1.reindex σ).universeWitness
    refine ⟨?_, ?_⟩
    · change TypeEq S.R Δ.raw (subst σ.substitution equation.1.1.code) (subst σ.substitution equation.2.1.code)
      rw [sameTypes]
      exact (equation.1.1.reindex σ).isType.refl
    change Typed S.R Δ.raw (subst σ.substitution equation.1.1.code) _ at formed
    change Equal S.R Δ.raw (subst σ.substitution equation.1.2.code) (subst σ.substitution equation.2.2.code)
      (subst σ.substitution equation.1.1.code)
    rw [abstracts.leftType] at formed ⊢
    rw [abstracts.leftTerm, abstracts.rightTerm]
    exact Derivable.lamCong formed universe' equal

end Solutions

section Weights

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **An abstraction weighs what its body weighs**, over the binder's declaration. -/
theorem sideWeight_abstraction {Θ : Context S.R} (term : TotalTerm Θ) (domain : TypeOver Θ)
    (body : TotalTerm (extend Θ domain)) (typeCode : term.1.code = .pi domain.code body.1.code)
    (termCode : term.2.code = .lam body.2.code) :
    sideWeight facts roots heads algebra rigid complete term =
      sideWeight facts roots heads algebra rigid complete body := by
  obtain ⟨v, normal⟩ := long_exists facts roots heads algebra rigid complete (extend Θ domain).formed body.2.typed
  have isPi : IsType S.R Θ.raw term.1.code := term.1.isType
  have formedPi : Typed S.R Θ.raw term.1.code (.head term.1.level) := term.1.formed
  rw [typeCode] at isPi formedPi
  have domainType : IsType S.R Θ.raw domain.code := (IsType.pi_parts isPi).1
  have typedV : Typed S.R (extend Θ domain).raw v body.1.code := (Equal.typed normal.2 (extend Θ domain).formed).2
  have normalLam : NormalForm S.R S.roles Θ.raw term.2.code (.lam v) term.1.code := by
    rw [typeCode, termCode]
    exact ⟨Long.lam (IsType.refl isPi) domainType
        (Derivable.lamIntro formedPi term.1.universeWitness typedV) normal.1,
      Derivable.lamCong formedPi term.1.universeWitness normal.2⟩
  rw [sideWeight_eq facts roots heads algebra rigid complete term normalLam,
    sideWeight_eq facts roots heads algebra rigid complete body normal]
  simp only [weight]

/-- **An equation of abstractions weighs what the opened equation weighs.** -/
theorem equationWeight_abstracts {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {domain : TypeOver Θ}
    {opened : Equation (TotalTerm (extend Θ domain))} (abstracts : Abstracts equation domain opened) :
    equationWeight facts roots heads algebra rigid complete equation =
      equationWeight facts roots heads algebra rigid complete opened := by
  unfold equationWeight
  rw [sideWeight_abstraction facts roots heads algebra rigid complete equation.1 domain opened.1 abstracts.leftType
      abstracts.leftTerm,
    sideWeight_abstraction facts roots heads algebra rigid complete equation.2 domain opened.2 abstracts.rightType
      abstracts.rightTerm]

end Weights

/-! ## Dropping a dead binder under live binders -/

/-- **Dropping a dead binder under live binders**: R119's dead binder in front, or, under one live binder of both
sides, dropping a dead binder from the opened equation and closing it again. -/
inductive DropsDead : {Θ : Context S.R} → Equation (TotalTerm Θ) → Equation (TotalTerm Θ) → Prop
  | front {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (dead : DeadBinder equation) :
      DropsDead equation dead.reduced
  | under {Θ : Context S.R} {equation reduced : Equation (TotalTerm Θ)} (domain : TypeOver Θ)
      {opened openedReduced : Equation (TotalTerm (extend Θ domain))} :
      Abstracts equation domain opened → opened.2.1.code = opened.1.1.code →
      Abstracts reduced domain openedReduced → openedReduced.2.1.code = openedReduced.1.1.code →
      DropsDead opened openedReduced → DropsDead equation reduced

namespace DropsDead

/-- The reduced equation has equal annotations. -/
theorem sameType {Θ : Context S.R} {equation reduced : Equation (TotalTerm Θ)}
    (drops : DropsDead equation reduced) : reduced.2.1.code = reduced.1.1.code := by
  induction drops with
  | front dead => exact dead.sameType
  | under domain _ _ closes closedSame _ _ => rw [closes.rightType, closes.leftType, closedSame]

/-- **Dropping keeps the solutions**, where typed equality strengthens past an unused variable. -/
theorem solves (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (strengthening : EqualStrengthening S.R)
    {Θ : Context S.R} {equation reduced : Equation (TotalTerm Θ)} (drops : DropsDead equation reduced) :
    ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Solves σ equation ↔ (frames S.levels).Solves σ reduced := by
  induction drops with
  | front dead =>
      exact fun σ => ⟨reduced_of_solves facts roots strengthening dead σ, solves_of_reduced dead σ⟩
  | under domain opens openedSame closes closedSame _ inner =>
      intro Δ σ
      rw [solves_abstracts_iff facts roots opens openedSame σ, inner (rawLift σ domain),
        ← solves_abstracts_iff facts roots closes closedSame σ]

/-- **Dropping keeps the weight.** -/
theorem weight (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
    (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
    (complete : AlgorithmicComplete S.R S.roles) {Θ : Context S.R} {equation reduced : Equation (TotalTerm Θ)}
    (drops : DropsDead equation reduced) :
    equationWeight facts roots heads algebra rigid complete reduced =
      equationWeight facts roots heads algebra rigid complete equation := by
  induction drops with
  | front dead => exact (equationWeight_dead facts roots heads algebra rigid complete dead).symm
  | under domain opens _ closes _ _ inner =>
      rw [equationWeight_abstracts facts roots heads algebra rigid complete opens,
        equationWeight_abstracts facts roots heads algebra rigid complete closes, inner]

/-- **Dropping removes one abstraction from the left side.** -/
theorem depth {Θ : Context S.R} {equation reduced : Equation (TotalTerm Θ)} (drops : DropsDead equation reduced) :
    lamDepth equation.1.2.code = lamDepth reduced.1.2.code + 1 := by
  induction drops with
  | front dead =>
      rw [dead.leftTerm]
      simp only [lamDepth, ContextualDependentCoverageReadersHalf.lamDepth_rename]
  | under domain opens _ closes _ _ inner =>
      rw [opens.leftTerm, closes.leftTerm]
      simp only [lamDepth, inner]

/-- **A side whose weakening sits under an abstraction keeps a normal Miller reduct**, at every marking. -/
theorem _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4.MarkedReduct_unweaken
    (rigid : ∀ name, S.roles name = .rigid) (sn : StronglyNormalizing S.R) {Θ : Context S.R}
    {type : TypeOver Θ} (body : Term Θ type) (mark : Fin Θ.arity → Bool)
    (closed : MarkedReduct S.R mark (.lam (Presentation.rename wk body.code))) :
    MarkedReduct S.R mark body.code := by
  have empty := computation_empty rigid
  have lifted := MarkedReduct.of_lam empty closed
  obtain ⟨N, toN, normalN⟩ := term_normal sn body
  have renamed := star_rename (R := S.R) wk toN
  have normalRenamed : Normal S.R (Presentation.rename wk N) :=
    (ContextualDependentNormalizing.normal_rename_iff empty wk N).mpr normalN
  have millerRenamed := all_miller_of_one empty lifted _ renamed normalRenamed
  exact ⟨N, toN, normalN, miller_rename_reflect N (Fin.succ_injective _) (fun _ => rfl) millerRenamed⟩

/-- **Dropping keeps normal Miller reducts of both sides**, at every marking. -/
theorem reducts (rigid : ∀ name, S.roles name = .rigid) (sn : StronglyNormalizing S.R) {Θ : Context S.R}
    {equation reduced : Equation (TotalTerm Θ)} (drops : DropsDead equation reduced) :
    ∀ mark : Fin Θ.arity → Bool,
      (MarkedReduct S.R mark equation.1.2.code → MarkedReduct S.R mark reduced.1.2.code) ∧
        (MarkedReduct S.R mark equation.2.2.code → MarkedReduct S.R mark reduced.2.2.code) := by
  have empty := computation_empty rigid
  induction drops with
  | front dead =>
      intro mark
      refine ⟨fun left => ?_, fun right => ?_⟩
      · rw [dead.leftTerm] at left
        exact MarkedReduct_unweaken rigid sn dead.reduced.1.2 mark left
      · rw [dead.rightTerm] at right
        exact MarkedReduct_unweaken rigid sn dead.reduced.2.2 mark right
  | under domain opens _ closes _ _ inner =>
      intro mark
      refine ⟨fun left => ?_, fun right => ?_⟩
      · rw [opens.leftTerm] at left
        rw [closes.leftTerm]
        exact MarkedReduct.lam empty ((inner _).1 (MarkedReduct.of_lam empty left))
      · rw [opens.rightTerm] at right
        rw [closes.rightTerm]
        exact MarkedReduct.lam empty ((inner _).2 (MarkedReduct.of_lam empty right))

/-- **Dropping keeps Miller sides.** -/
theorem sides (rigid : ∀ name, S.roles name = .rigid) (sn : StronglyNormalizing S.R) {Θ : Context S.R}
    {equation reduced : Equation (TotalTerm Θ)} (drops : DropsDead equation reduced)
    (held : FragmentSidesMiller equation) : FragmentSidesMiller reduced := by
  obtain ⟨left, right⟩ := side_reduct rigid sn held
  exact sides_of_reducts (computation_empty rigid) ((drops.reducts rigid sn _).1 left)
    ((drops.reducts rigid sn _).2 right)

end DropsDead

/-- **Dropping a dead binder under live binders from the first equation keeps the permuted Miller class**, where
typed equality strengthens past an unused variable. -/
theorem PermutedMiller.dropsDead (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
    (rigid : ∀ name, S.roles name = .rigid) (sn : StronglyNormalizing S.R) (strengthening : EqualStrengthening S.R)
    {Θ : Context S.R} {equation reduced : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (drops : DropsDead equation reduced) (permuted : PermutedMiller S.levels (equation :: rest)) :
    PermutedMiller S.levels (reduced :: rest) :=
  permuted.splice_of (pieces := [reduced]) fun before after stratified =>
    StratifiedMiller.splice stratified
      (fun σ => ⟨fun solved => (drops.solves facts roots strengthening σ).mpr
          (solved _ (List.mem_singleton_self _)),
        fun solved piece member => by
          obtain rfl := List.mem_singleton.mp member
          exact (drops.solves facts roots strengthening σ).mp solved⟩)
      (fun piece member => by
        obtain rfl := List.mem_singleton.mp member
        exact drops.sides rigid sn (stratified before after equation rfl).1)
      (fun first last piece split => by
        intro Δ σ _
        have member : piece ∈ [reduced] := by
          rw [split]
          simp
        obtain rfl := List.mem_singleton.mp member
        change TypeEq S.R _ (subst σ.substitution piece.1.1.code) (subst σ.substitution piece.2.1.code)
        rw [drops.sameType]
        exact (piece.1.1.reindex σ).isType.refl)

end ContextualDependentAcceptance4
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
