import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulativeRun

/-!
# A store of the fragment that is solvable and has no principal answer

`crossStore`: over `X : U0 → U0, Y : U1 → U1`,

  `λ x. X x ≐ λ x. Y x`  at  `Π (x : U0). U1`.

It is in the dynamic pattern fragment and solvable. **It has no principal answer** (`cross_no_principal`): no
substitution solves it and factors every solution. So on this store no solver returns "a principal answer or a
certified refutation", whatever its rules: acceptance, as stated for the dynamic pattern fragment over the
cumulative tower, is false. The store passes a local of `U0` to an unknown that declares `U1` for its argument;
that is what the fragment has to exclude, or what answers have to express.

**The argument** (`no_common_answer`, for any package). Let an answer send `X` to `aX` and `Y` to `aY`, and let `T`
be `aY z` over a fresh `z : U1`, with normal form `Z`.

* The answer solves the store, so over `x : U0` the type `aY x` is equal to `aX x`, a type of `U0`. The normal form
  `Z` is normal over `x : U0` as well (narrowing keeps normal forms), so `Z` is a type of `U0` over `x : U0`
  (`normal_typed_of_equal`).
* The identity solution factors through the answer by some `ρ`, so `Z` under `ρ` is equal to `z`. A universe, a Π
  type, a Σ type and an identity type are not equal to a variable; so `Z` is neutral.
* If `Z` is the variable `z`, the constant solution cannot factor: `z` under any substitution of the answer's
  context is `z`, and `z` is not equal to the ground type.
* Otherwise `Z` is a neutral type that keeps its principal type under the narrowing of `z`
  (`spine_small_wide`), so `Z` is a type of `U0` over `z : U1` already. Then `Z` under `ρ` is a type of `U0` equal
  to `z`, and `z : U1` is not a type of `U0` (`var_not_small`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUniverseInjective

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentRank

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts in
/-- **An abstraction equal to a function has its body equal to the function at a fresh variable.** -/
theorem equal_of_lam_left {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A g : Tm Head n}
    {body B : Tm Head (n + 1)} (equal : Equal S.R Γ (.lam body) g (.pi A B)) :
    Equal S.R (.snoc Γ A) body (.app (Presentation.rename wk g) (.var 0)) B := by
  obtain ⟨tLam, _⟩ := Equal.typed equal formed
  obtain ⟨w, hw, tPi⟩ := Typed.isType tLam formed
  have typedBody : Typed S.R (.snoc Γ A) body B := Typed.lam_inv facts tLam formed
  have compared : Equal S.R (.snoc Γ A) (.app (Presentation.rename wk (.lam body)) (.var 0))
      (.app (Presentation.rename wk g) (.var 0)) B := by
    have step := Derivable.appCong (equal.rename (CtxRen.wk Γ A))
      (Derivable.refl (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0))
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using step
  have beta : Equal S.R (.snoc Γ A) (.app (Presentation.rename wk (.lam body)) (.var 0)) body B := by
    have step := Derivable.betaPi (tPi.rename (CtxRen.wk Γ A)) hw
      (typedBody.rename ((CtxRen.wk Γ A).snoc A)) (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0)
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using step
  exact .trans (.symm beta) compared

include facts algebra in
/-- **A neutral type that keeps its principal type under a narrowing, and is a type of a universe in the narrowed
context, is a type of that universe already.** -/
theorem spine_small_wide {n : Nat} {W N : Ctx Head n} (narrows : CtxNarrows S.R W N) (formedW : CtxFormed S.R W)
    (formedN : CtxFormed S.R N) {V U : Tm Head n} {top u : Head}
    (spineW : Long S.R S.roles (.spine W V U)) (spineN : Long S.R S.roles (.spine N V U))
    (htop : S.R.isUniverse top) (le : Below S.R W U (.head top)) (small : Typed S.R N V (.head u)) :
    Typed S.R W V (.head u) := by
  obtain ⟨w, hw, eU, _⟩ := Below.universe_target facts le formedW htop
    (IsType.refl (IsType.head_of_universe htop))
  have principal : Below S.R N U (.head u) := spine_principal facts V formedN spineN small
  obtain ⟨x, _, eX, c⟩ := Below.universe_cumulative facts algebra principal formedN hw (typeEq_narrow narrows eU)
  exact Derivable.cumul (Typed.convType spineW.spine_typed eU)
    (algebra.same_right c (TypeEq.head_injective facts eX.symm formedN))

include facts in
/-- A variable is not equal, as a type, to a universe, a Π type, a Σ type or an identity type. -/
theorem var_not_former {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (i : Fin n) {T : Tm Head n}
    (equal : TypeEq S.R Γ (.var i) T) :
    (∀ h, T ≠ .head h) ∧ (∀ A B, T ≠ .pi A B) ∧ (∀ A B, T ≠ .sigma A B) ∧ (∀ A a b, T ≠ .id A a b) := by
  refine ⟨fun h same => ?_, fun A B same => ?_, fun A B same => ?_, fun A a b same => ?_⟩
  · subst same
    exact (TypeEq.neutral_form facts equal formed (.var i) (.inl ⟨_, rfl⟩)).not_former.1 _ rfl
  · subst same
    exact (TypeEq.neutral_form facts equal formed (.var i) (.inr (.inl ⟨_, _, rfl⟩))).not_former.2.1 _ _ rfl
  · subst same
    exact (TypeEq.neutral_form facts equal formed (.var i) (.inr (.inr (.inl ⟨_, _, rfl⟩)))).not_former.2.2.1 _ _ rfl
  · subst same
    exact (TypeEq.neutral_form facts equal formed (.var i)
      (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))).not_former.2.2.2 _ _ _ rfl

include facts roots heads algebra rigid complete in
/-- **No answer is common to the identity and to a constant family.** Let `aX` be a family of `u → u` and `aY` a
family of `v → v` that agree at a variable of `u`, where `u` lies below `v` and `v` does not lie below `u`. Then
`aY` has no instance equal to the identity together with an instance equal to the constant family at a ground
type. -/
theorem no_common_answer (noConstants : ∀ name, S.R.constantType name = none) {n : Nat} {Δ : Ctx Head n}
    (formed : CtxFormed S.R Δ) {u v g : Head} (hu : S.R.isUniverse u) (hv : S.R.isUniverse v)
    (lower : S.R.cumulative u v) (apart : ¬ S.R.cumulative v u) {aX aY : Tm Head n}
    (tX : Typed S.R Δ aX (.pi (.head u) (.head u))) (tY : Typed S.R Δ aY (.pi (.head v) (.head v)))
    (agree : Equal S.R (.snoc Δ (.head u)) (.app (Presentation.rename wk aX) (.var 0))
      (.app (Presentation.rename wk aY) (.var 0)) (.head v))
    {m₁ : Nat} {Γ₁ : Ctx Head m₁} (formed₁ : CtxFormed S.R Γ₁) {ρ₁ : Sub Head n m₁} (typed₁ : SubstMor S.R Δ Γ₁ ρ₁)
    (identity : Equal S.R Γ₁ (.lam (.var 0)) (Presentation.subst ρ₁ aY) (.pi (.head v) (.head v)))
    {m₂ : Nat} {Γ₂ : Ctx Head m₂} (formed₂ : CtxFormed S.R Γ₂) {ρ₂ : Sub Head n m₂} (typed₂ : SubstMor S.R Δ Γ₂ ρ₂)
    (constant : Equal S.R Γ₂ (.lam (.head g)) (Presentation.subst ρ₂ aY) (.pi (.head v) (.head v))) : False := by
  have isV : ∀ {k : Nat} (Γ : Ctx Head k), IsType S.R Γ (.head v) := fun _ => IsType.head_of_universe hv
  have formedW : CtxFormed S.R (.snoc Δ (.head v)) := formed.snoc (isV Δ)
  have formedN : CtxFormed S.R (.snoc Δ (.head u)) := formed.snoc (IsType.head_of_universe hu)
  have formedE₁ : CtxFormed S.R (.snoc Γ₁ (.head v)) := formed₁.snoc (isV Γ₁)
  have formedE₂ : CtxFormed S.R (.snoc Γ₂ (.head v)) := formed₂.snoc (isV Γ₂)
  have narrows : CtxNarrows S.R (.snoc Δ (.head v)) (.snoc Δ (.head u)) := .lower (CtxNarrows.refl Δ) lower
  have typedT : Typed S.R (.snoc Δ (.head v)) (.app (Presentation.rename wk aY) (.var 0)) (.head v) :=
    Derivable.appElim (tY.rename (CtxRen.wk Δ (.head v))) (Derivable.var (R := S.R) (Γ := .snoc Δ (.head v)) 0)
  have typedS : Typed S.R (.snoc Δ (.head u)) (.app (Presentation.rename wk aX) (.var 0)) (.head u) :=
    Derivable.appElim (tX.rename (CtxRen.wk Δ (.head u))) (Derivable.var (R := S.R) (Γ := .snoc Δ (.head u)) 0)
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formedW ⟨v, hv, typedT⟩
  obtain ⟨tZ, eZ⟩ := atZ hv typedT
  have smallN : Typed S.R (.snoc Δ (.head u)) Z (.head u) :=
    normal_typed_of_equal facts roots heads algebra rigid complete formedN hu typedS
      ⟨v, hv, .trans agree (equal_narrow narrows eZ)⟩ (Long.type_narrow facts lZ narrows formedW formedN)
  -- The instances of `Z` under the two factorizations.
  have code : ∀ {m : Nat} (ρ : Sub Head n m),
      Presentation.subst (liftSub ρ) (.app (Presentation.rename wk aY) (.var 0)) =
        .app (Presentation.rename wk (Presentation.subst ρ aY)) (.var 0) := by
    intro m ρ
    change Tm.app (Presentation.subst (liftSub ρ) (Presentation.rename wk aY)) (.var 0) = _
    rw [subst_liftSub_wk]
  have first : Equal S.R (.snoc Γ₁ (.head v)) (.var 0) (Presentation.subst (liftSub ρ₁) Z) (.head v) := by
    have opened := equal_of_lam_left facts formed₁ identity
    rw [← code ρ₁] at opened
    exact .trans opened (eZ.substitute (typed₁.lift (.head v)))
  have second : Equal S.R (.snoc Γ₂ (.head v)) (.head g) (Presentation.subst (liftSub ρ₂) Z) (.head v) := by
    have opened := equal_of_lam_left facts formed₂ constant
    rw [← code ρ₂] at opened
    exact .trans opened (eZ.substitute (typed₂.lift (.head v)))
  have firstType : TypeEq S.R (.snoc Γ₁ (.head v)) (.var 0) (Presentation.subst (liftSub ρ₁) Z) := ⟨v, hv, first⟩
  have formers := var_not_former facts formedE₁ 0 firstType
  -- A type of `u` over the wide context contradicts the identity.
  have finish : Typed S.R (.snoc Δ (.head v)) Z (.head u) → False := fun small =>
    var_not_small facts roots heads algebra rigid complete formedE₁ rfl hv hu apart
      (small.substitute (typed₁.lift (.head v))) firstType.symm
  cases lZ with
  | head _ => exact formers.1 _ rfl
  | pi _ _ _ => exact formers.2.1 _ _ rfl
  | sigma _ _ _ => exact formers.2.2.1 _ _ rfl
  | id _ _ _ _ => exact formers.2.2.2 _ _ _ rfl
  | neutralType ls htop le =>
      cases ls with
      | var i e =>
          cases i using Fin.cases with
          | zero =>
              have secondType : TypeEq S.R (.snoc Γ₂ (.head v)) (.var 0) (.head g) := ⟨v, hv, .symm second⟩
              exact (var_not_former facts formedE₂ 0 secondType).1 _ rfl
          | succ j =>
              exact finish (spine_small_wide facts algebra narrows formedW formedN (.var j.succ e)
                (.var j.succ (typeEq_narrow narrows e)) htop le smallN)
      | const _ declared _ _ =>
          rw [noConstants] at declared
          cases declared
      | app lf eF la eU =>
          rcases Long.narrow facts lf narrows formedW formedN with kept | ⟨_, _, e, _, _⟩
          · exact finish (spine_small_wide facts algebra narrows formedW formedN (.app lf eF la eU)
              (.app kept (typeEq_narrow narrows eF) (Long.term_narrow facts la narrows formedW formedN)
                (typeEq_narrow narrows eU)) htop le smallN)
          · exact absurd (TypeEq.trans S.levels eF.symm e) (TypeEq.pi_ne_head facts formedW)
      | fst lp eP eU =>
          rcases Long.narrow facts lp narrows formedW formedN with kept | ⟨_, _, e, _, _⟩
          · exact finish (spine_small_wide facts algebra narrows formedW formedN (.fst lp eP eU)
              (.fst kept (typeEq_narrow narrows eP) (typeEq_narrow narrows eU)) htop le smallN)
          · exact absurd (TypeEq.trans S.levels eP.symm e) (TypeEq.sigma_ne_head facts formedW)
      | snd lp eP eU =>
          rcases Long.narrow facts lp narrows formedW formedN with kept | ⟨_, _, e, _, _⟩
          · exact finish (spine_small_wide facts algebra narrows formedW formedN (.snd lp eP eU)
              (.snd kept (typeEq_narrow narrows eP) (typeEq_narrow narrows eU)) htop le smallN)
          · exact absurd (TypeEq.trans S.levels eP.symm e) (TypeEq.sigma_ne_head facts formedW)

end ContextualDependentUniverseInjective

namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls

/-- `U1 → U1`, over `X Y`: the type of `Y`. -/
def crossWide : TypeOver ctxCross :=
  formIn ctxCross (.pi (.head (.sort (.succ Tower.zero))) (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- The unknown `Y`, as a term over `X Y`. -/
def crossY : TotalTerm ctxCross := termIn ctxCross crossWide (.var 0) (by decide +kernel)

/-- **`crossStore` has no principal answer.** -/
theorem cross_no_principal {Δ : Context setting.R} (answer : Δ ⟶ ctxCross) :
    ¬ (frames setting.levels).Principal crossStore answer := by
  intro principal
  have smallCode : smallFamily.code = .pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)) := formIn_code _ _ _
  have largeCode : largeFamily.code =
      .pi (.head (.sort (.succ Tower.zero))) (.head (.sort (.succ Tower.zero))) := formIn_code _ _ _
  have typeCode : crossEquation.1.1.code =
      .pi (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero))) := formIn_code _ _ _
  have wideCode : crossWide.code =
      .pi (.head (.sort (.succ Tower.zero))) (.head (.sort (.succ Tower.zero))) := formIn_code _ _ _
  -- The declared types of the two components of the answer.
  have tY := answer.typed (⟨0, Nat.zero_lt_two⟩ : Fin 2)
  change Typed setting.R Δ.raw (answer.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2))
    (subst answer.substitution (Presentation.rename wk largeFamily.code)) at tY
  rw [largeCode] at tY
  have tX := answer.typed (⟨1, Nat.one_lt_two⟩ : Fin 2)
  change Typed setting.R Δ.raw (answer.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2))
    (subst answer.substitution (Presentation.rename wk (Presentation.rename wk smallFamily.code))) at tX
  rw [smallCode] at tX
  -- The answer solves the store.
  have held := principal.sound crossEquation List.mem_cons_self
  rw [ContextualDependentRigidFormers.solves_raw] at held
  obtain ⟨_, equal⟩ := held
  rw [typeCode] at equal
  have agree := ContextualDependentUniverseInjective.equal_of_lam (S := setting) TowerModel.facts Δ.formed equal
  -- The two solutions factor.
  obtain ⟨ρ₁, factor₁⟩ := principal.factors _ crossIdentity cross_two_answers.2.1
  obtain ⟨ρ₂, factor₂⟩ := principal.factors _ crossConstant cross_two_answers.2.2
  have identity := (factor₁ crossY).2
  change Equal setting.R (empty setting.R).raw (crossIdentity.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2))
    (subst ρ₁.substitution (answer.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2)))
    (subst crossIdentity.substitution crossWide.code) at identity
  rw [wideCode, show crossIdentity.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2) = .lam (.var 0) from by
    decide +kernel] at identity
  have constant := (factor₂ crossY).2
  change Equal setting.R (empty setting.R).raw (crossConstant.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2))
    (subst ρ₂.substitution (answer.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2)))
    (subst crossConstant.substitution crossWide.code) at constant
  rw [wideCode, show crossConstant.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2) = .lam (.head .legacyGround) from by
    decide +kernel] at constant
  exact ContextualDependentUniverseInjective.no_common_answer (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => rfl) Δ.formed (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) tX tY
    agree (empty setting.R).formed ρ₁.typed identity (empty setting.R).formed ρ₂.typed constant

/-- **Acceptance fails on the dynamic pattern fragment as stated**: a store of the fragment that is solvable, so
that no refutation of it is sound, and that has no principal answer. -/
theorem fragment_without_principal_answer :
    InFragmentStore crossStore ∧ (frames setting.levels).Solvable crossStore ∧
      ∀ {Δ : Context setting.R} (answer : Δ ⟶ ctxCross), ¬ (frames setting.levels).Principal crossStore answer :=
  ⟨cross_in_fragment, cross_identity, fun answer => cross_no_principal answer⟩

/-- **No family decides `crossStore`**: at no budget and number of rounds does a run of any solver family end with
a principal answer or with a refutation. -/
theorem cross_undecided (family : ContextualDependentDecisiveDriver.Family setting.levels) (fuel rounds : Nat) :
    ¬ ((∃ state finished, run (family.solver fuel) crossStore rounds = .solved state finished ∧
          (frames setting.levels).Principal crossStore state.answer) ∨
        (∃ absent, run (family.solver fuel) crossStore rounds = .refuted absent)) := by
  rintro (⟨state, _, _, principal⟩ | ⟨absent, _⟩)
  · exact cross_no_principal state.answer principal
  · exact absent cross_identity

/-- **The conclusion of acceptance is false for every family**, on a store of the fragment. -/
theorem acceptance_conclusion_false (family : ContextualDependentDecisiveDriver.Family setting.levels) :
    ¬ ∃ budget, ∀ larger, budget ≤ larger →
      run (family.solver larger) crossStore larger = run (family.solver budget) crossStore budget ∧
      ((∃ state finished, run (family.solver larger) crossStore larger = .solved state finished ∧
          (frames setting.levels).Principal crossStore state.answer) ∨
        (∃ absent, run (family.solver larger) crossStore larger = .refuted absent)) := by
  rintro ⟨budget, decided⟩
  exact cross_undecided family budget budget (decided budget (Nat.le_refl budget)).2

end ContextualDependentSweep.Witnesses

namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentRank ContextualDependentSpinesMany ContextualDependentCoverageReadersHalf
open ContextualDependentConstantHeads ContextualDependentMillerClosure
open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4

/-- **The hypothesis of the acceptance reduction for the top family is false**: the reduction would decide
`crossStore`. The same holds for the reductions of the families below, whose conclusions have the same form. -/
theorem tower_sort_uncovered_false :
    ¬ ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PermutedMiller setting.levels problem → problem ≠ [] → ∀ threshold,
        (∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem) →
        ∀ equation ∈ (towerPrepare threshold problem).remaining,
          ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation → CensusHead equation →
          ContextualDependentShortClosure.FragmentSidesMiller equation →
          Kind (openedFlexible (piCount equation.1.1.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.1.2.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.2.2.code)) →
          ¬ MixedCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerSortReads larger problem :=
  fun uncovered => ContextualDependentSweep.Witnesses.acceptance_conclusion_false sortTower
    (tower_sort_decided_of_uncovered uncovered ContextualDependentSweep.Witnesses.cross_in_fragment)

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
