import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulative

/-!
# An unknown applied to a local of a smaller universe: the other side is read at the declared universe

Let an unknown declare an argument at a universe `v` and be applied to a local of a universe `u` below `v`, and
let the instance be equal to a type whose normal form is `N`. Then `N` is a type over a variable of `v` already, and
it is the value of the unknown at that variable (`applied_wide_reading`). So against such a side

* the value of the unknown is determined: two solutions agree on it;
* there is a solution only if the normal form of the other side is typed with the local read at the universe the
  unknown declares.

**`loopStore`**: over `P : U1 → U1`,

  `λ x. P x ≐ λ x. Id U0 x x`  at  `Π (x : U0). U1`.

It is in the dynamic pattern fragment and has no solution (`loop_unsolvable`): `Id U0 z z` is not typed over
`z : U1`. The top family (`sortTower`) is stuck on it wherever its compiled run reads `stuck`.
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

include facts roots heads algebra rigid complete in
/-- **The other side is read at the declared universe.** Let `aY` be a family of `v → w` whose instance at a
variable of `u`, a universe below `v`, is equal to a normal type `N`. Then `N` is a type of `w` over a variable of
`v`, and it is the instance of `aY` at that variable. -/
theorem applied_wide_reading {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ) {u v w : Head}
    (hu : S.R.isUniverse u) (hv : S.R.isUniverse v) (hw : S.R.isUniverse w) (lower : S.R.cumulative u v)
    {aY : Tm Head n} (tY : Typed S.R Δ aY (.pi (.head v) (.head w))) {N : Tm Head (n + 1)}
    (normal : Long S.R S.roles (.type (.snoc Δ (.head u)) N))
    (agree : TypeEq S.R (.snoc Δ (.head u)) (.app (Presentation.rename wk aY) (.var 0)) N) :
    Typed S.R (.snoc Δ (.head v)) N (.head w) ∧
      Equal S.R (.snoc Δ (.head v)) (.app (Presentation.rename wk aY) (.var 0)) N (.head w) := by
  have formedW : CtxFormed S.R (.snoc Δ (.head v)) := formed.snoc (IsType.head_of_universe hv)
  have formedN : CtxFormed S.R (.snoc Δ (.head u)) := formed.snoc (IsType.head_of_universe hu)
  have narrows : CtxNarrows S.R (.snoc Δ (.head v)) (.snoc Δ (.head u)) := .lower (CtxNarrows.refl Δ) lower
  have typedT : Typed S.R (.snoc Δ (.head v)) (.app (Presentation.rename wk aY) (.var 0)) (.head w) :=
    Derivable.appElim (tY.rename (CtxRen.wk Δ (.head v))) (Derivable.var (R := S.R) (Γ := .snoc Δ (.head v)) 0)
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formedW ⟨w, hw, typedT⟩
  obtain ⟨tZ, eZ⟩ := atZ hw typedT
  have sZ : TypeEq S.R (.snoc Δ (.head u)) (.app (Presentation.rename wk aY) (.var 0)) Z :=
    ⟨w, hw, equal_narrow narrows eZ⟩
  have same := long_type_unique facts roots heads algebra complete formedN
    (Long.type_narrow facts lZ narrows formedW formedN) normal (TypeEq.trans S.levels sZ.symm agree)
  have equal := Long.sameEqual facts heads lZ formedW same hw tZ
  exact ⟨(Equal.typed equal formedW).2, .trans eZ equal⟩

end ContextualDependentUniverseInjective

namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls ContextualDependentEtaLong

/-- `U1 → U1`, over no unknown. -/
def wideFamily : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head (.sort (.succ Tower.zero))) (.head (.sort (.succ Tower.zero))))
    (by decide +kernel)

/-- `P : U1 → U1`. -/
abbrev ctxWide := extend (empty setting.R) wideFamily

/-- `Π (x : U0). U1`, over `P`. -/
def loopType : TypeOver ctxWide :=
  formIn ctxWide (.pi (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `λ x. P x ≐ λ x. Id U0 x x` at `Π (x : U0). U1`. -/
def loopEquation : Equation (TotalTerm ctxWide) :=
  (termIn ctxWide loopType (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn ctxWide loopType (.lam (.id (.head (.sort Tower.zero)) (.var 0) (.var 0))) (by decide +kernel))

def loopStore : EquationStore (TotalTerm ctxWide) := [loopEquation]

/-- The raw problem of the sweep. -/
def loopProblem : Problem :=
  { unknowns := [.pi .u1 .u1],
    equations := [(.pi .u0 .u1, .lam (.app (.var 1) (.var 0)), .lam (.id .u0 (.var 0) (.var 0)))] }

theorem loop_in_fragment : InFragmentStore loopStore := storeInside_sound (by decide +kernel)

/-- **The store has no solution**: under a solution `P := p`, the type `p x` is equal to `Id U0 x x` for `x : U0`,
so `Id U0 z z` is a type over `z : U1`; and `z : U1` is not a type of `U0`. -/
theorem loop_unsolvable : ¬ (frames setting.levels).Solvable loopStore := by
  rintro ⟨Δ, σ, solved⟩
  have held := solved loopEquation List.mem_cons_self
  rw [ContextualDependentRigidFormers.solves_raw] at held
  obtain ⟨_, equal⟩ := held
  have typeCode : loopEquation.1.1.code =
      .pi (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero))) := formIn_code _ _ _
  rw [typeCode] at equal
  have bodies := ContextualDependentUniverseInjective.equal_of_lam (S := setting) TowerModel.facts Δ.formed equal
  have familyCode : wideFamily.code =
      .pi (.head (.sort (.succ Tower.zero))) (.head (.sort (.succ Tower.zero))) := formIn_code _ _ _
  have declared := σ.typed (⟨0, Nat.zero_lt_one⟩ : Fin 1)
  change Typed setting.R Δ.raw (σ.substitution (⟨0, Nat.zero_lt_one⟩ : Fin 1))
    (subst σ.substitution (Presentation.rename wk wideFamily.code)) at declared
  rw [familyCode] at declared
  have small : setting.R.isUniverse (.sort Tower.zero) := by decide +kernel
  have large : setting.R.isUniverse (.sort (.succ Tower.zero)) := by decide +kernel
  have formedN : CtxFormed setting.R (.snoc Δ.raw (.head (.sort Tower.zero))) :=
    Δ.formed.snoc (IsType.head_of_universe small)
  have formedW : CtxFormed setting.R (.snoc Δ.raw (.head (.sort (.succ Tower.zero)))) :=
    Δ.formed.snoc (IsType.head_of_universe large)
  have isSmall : IsType setting.R (.snoc Δ.raw (.head (.sort Tower.zero))) (.head (.sort Tower.zero)) :=
    IsType.head_of_universe small
  have spine : Long setting.R setting.roles
      (.spine (.snoc Δ.raw (.head (.sort Tower.zero))) (.var 0) (.head (.sort Tower.zero))) :=
    .var 0 (IsType.refl isSmall)
  have point : Long setting.R setting.roles
      (.term (.snoc Δ.raw (.head (.sort Tower.zero))) (.var 0) (.head (.sort Tower.zero))) :=
    .univ small (IsType.refl isSmall)
      (Derivable.var (R := setting.R) (Γ := .snoc Δ.raw (.head (.sort Tower.zero))) 0)
      (.neutralType spine small (IsType.refl isSmall).below)
  have normal : Long setting.R setting.roles (.type (.snoc Δ.raw (.head (.sort Tower.zero)))
      (.id (.head (.sort Tower.zero)) (.var 0) (.var 0))) :=
    .id (.head isSmall) point point ⟨_, large, (Equal.typed bodies formedN).2⟩
  have wide := (ContextualDependentUniverseInjective.applied_wide_reading (S := setting) TowerModel.facts
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid
    TowerModel.complete Δ.formed small large large (by decide +kernel) declared normal ⟨_, large, bodies⟩).1
  have generation : GenerationAt setting.R _ (.id _ _ _) (.head (.sort (.succ Tower.zero))) :=
    Typed.generation wide
  obtain ⟨_, _, _, typedLocal, _, _⟩ := generation
  have declaredLe : TypeLe setting.R (.snoc Δ.raw (.head (.sort (.succ Tower.zero))))
      (.head (.sort (.succ Tower.zero))) (.head (.sort Tower.zero)) := Typed.generation typedLocal
  have below : setting.R.cumulative (.sort (.succ Tower.zero)) (.sort Tower.zero) :=
    ContextualDependentUniverseInjective.typeLe_head_cumulative (S := setting) TowerModel.facts TowerModel.algebra
      formedW large small declaredLe
  exact absurd below (by decide +kernel)

/-- The top family is stuck on the store wherever its compiled run reads `stuck`. -/
theorem loop_stuck_of_ending {fuel rounds : Nat} (read : endingSort fuel rounds ctxWide loopStore = .stuck) :
    InFragmentStore loopStore ∧ ¬ (frames setting.levels).Solvable loopStore ∧
      isStuck (run (sortTower.solver fuel) loopStore rounds) = true :=
  ⟨loop_in_fragment, loop_unsolvable, stuck_of_endingSort read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
