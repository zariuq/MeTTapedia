import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringEventual
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentStrengthening

/-!
# The pattern step is never pending on the inversion row

For a recognized pattern `F x̄ ≐ t` whose right side is normal and mentions only variables in the image of the
argument map, the outer variables other than `F` and the locals `x̄`, the inverse image of `t` is a body over
`F`'s own telescope. It is typed there: the executable checker certifies `t` at its type in the local telescope
(`ContextualDependentExecutableChecking.realized`), and the certificate reflects along the compatible inclusion
(`ContextualDependentStrengthening.recover`). So a recovery exists (`recovery_exists`), the budgeted recovery
eventually returns it (`recover_eventually`), and the general pattern step returns the principal answer from that
budget on (`step_solved_eventually`).

The other ways the step can be pending on a fragment pattern are outside this row: a local of `t` outside `x̄`
(read by the rigid rule when it occurs rigidly; a pruning when it occurs only under other metavariables), and an
occurrence of `F` in `t` (the occurs check, or the intersection when `t` is a spine of `F`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ExecutableChecking ContextualDependentExecutableJoin ContextualDependentExecutableConversion
open ContextualDependentExecutableChecking ContextualDependentPiSpine ContextualDependentGeneralPattern
open ContextualDependentTypedInversion ContextualDependentScope

section Code

variable {Head : Type} {rules : Rules Head}
variable {Γ : Context rules} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}

/-- **The type of a recognized right side** is the result type of the pattern's own telescope, renamed by the
inversion map. -/
theorem pattern_type_code (pattern : Pattern spine scope) :
    ((lifted spine).result.reindex pattern.map.hom).code = Presentation.rename pattern.bodyRen spine.result.code := by
  change subst (renSub pattern.map.forward) (lifted spine).result.code = _
  rw [subst_renSub]
  have shifted := congrArg TypeOver.code (spine.result_reindex (projectionHom Γ type))
  change Presentation.rename pattern.map.forward ((spine.reindex (projectionHom Γ type)).result.code) = _
  rw [← shifted]
  change Presentation.rename pattern.map.forward
    (subst (spine.map (projectionHom Γ type)).substitution spine.result.code) = _
  rw [spine.mapRen_substitution (projectionHom Γ type) wk rfl, subst_renSub, rename_comp]
  rfl

end Code

variable {L : Type} [UniverseLevel.LevelOrder L]
variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative]

local instance settingHeadEq' (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.headEq :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).headEq)

local instance settingUniverse' (valuation : Nat → L) (head : LevelTower.Head L) :
    Decidable ((TowerModel.setting valuation).R.isUniverse head) :=
  inferInstanceAs (Decidable ((LevelTower.rules L).isUniverse head))

local instance settingCumulative' (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.cumulative :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).cumulative)

variable (valuation : Nat → L)
variable (reflects : ContextualDependentReductionReflection.RootReflectsInjections (TowerModel.setting valuation).R.computation)

variable {Γ : Context (TowerModel.setting valuation).R} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}

include reflects in
/-- **A recovery exists on the inversion row.** -/
theorem recovery_exists (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (normal : Normal (LevelTower.rules L) right.code)
    (inside : ∀ index ∈ right.code.support, ∃ prior, pattern.bodyRen prior = index) :
    Nonempty (Recovery pattern.bodyInclusion spine.result right.code) := by
  obtain ⟨fuel, result, computed⟩ := (realized right.code scope.target.formed normal).2 right.typed
  have certificate : CheckingAlgorithm (TowerModel.setting valuation).R .check scope.target.raw right.code
      (Presentation.rename pattern.bodyInclusion.forward spine.result.code) := by
    change CheckingAlgorithm (TowerModel.setting valuation).R .check scope.target.raw right.code
      (Presentation.rename pattern.bodyRen spine.result.code)
    rw [← pattern_type_code]
    exact result.down
  obtain ⟨body, found⟩ := Option.isSome_iff_exists.mp
    ((ContextualDependentSupport.invert_lookup_defined_iff pattern.bodyRen pattern.bodyRen_injective
      right.code).mpr inside)
  have recovered := ContextualDependentStrengthening.recover_code (S := TowerModel.setting valuation)
    TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra reflects declared pattern.bodyInclusion
    pattern.bodyRen_compatible spine.result right.code certificate found
  cases computed' : ContextualDependentStrengthening.recover (S := TowerModel.setting valuation) TowerModel.facts
      TowerModel.roots TowerModel.heads TowerModel.algebra reflects declared pattern.bodyInclusion
      pattern.bodyRen_compatible spine.result right.code certificate with
  | none => rw [computed'] at recovered; cases recovered
  | some recovery => exact ⟨recovery⟩

variable (rigid : ∀ name, (TowerModel.setting valuation).roles name = .rigid)
  (complete : AlgorithmicComplete (TowerModel.setting valuation).R (TowerModel.setting valuation).roles)
  (normalizes : ∀ {Θ : Context (TowerModel.setting valuation).R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm (LevelTower.Head L) Θ.arity, ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation)
      code ∧ Equal (TowerModel.setting valuation).R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm (LevelTower.Head L) n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) term)))

include reflects in
/-- **The pattern step is never pending on the inversion row**: from some budget on it returns the principal
answer. -/
theorem step_solved_eventually (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (normal : Normal (LevelTower.rules L) right.code)
    (inside : ∀ index ∈ right.code.support, ∃ prior, pattern.bodyRen prior = index) :
    ∃ (fuel : Nat) (recovered : Recovery pattern.bodyInclusion spine.result right.code), ∀ larger, fuel ≤ larger →
      Pattern.step (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra declared reflects complete rigid normalizes certifyNormal tc red larger pattern right =
        .solved (pattern.replace TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra reflects complete
          recovered.body right recovered.recovers.symm) rfl := by
  obtain ⟨recovered⟩ := recovery_exists valuation reflects pattern right normal inside
  obtain ⟨fuel, recovers⟩ := recover_eventually valuation pattern.bodyInclusion spine.result recovered normal
  exact ⟨fuel, recovered, fun larger enough => Pattern.step_of_recovered (S := TowerModel.setting valuation)
    TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra declared reflects complete rigid normalizes
    certifyNormal tc red larger pattern right recovered (recovers larger enough)⟩

/-- **The conversion pattern rule solves a recognized pattern of the inversion row**: once the spine of the
metavariable is discovered and the pattern recognized, from some budget on the rule on that reading returns the
principal answer, which removes the newest declaration. -/
theorem tryActiveConv_solved_eventually (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend Γ type)))
    {headIndex : Fin scope.target.arity} {arguments : List (Fin scope.target.arity)}
    (read : readApplication active.left.code = some (headIndex, arguments))
    {f₁ : Nat} (discovered : ∀ larger, f₁ ≤ larger →
      ContextualDependentPiSpineDiscovery.discover (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots
        TowerModel.heads TowerModel.algebra declared tc red larger arguments.length type = some spine)
    {recognized : Recognized spine scope active} {f₂ : Nat} (recognizes : ∀ larger, f₂ ≤ larger →
      ContextualDependentRecognitionConversion.recognizeConv (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra red larger spine scope active = some recognized)
    (normal : Normal (LevelTower.rules L) recognized.right.code)
    (inside : ∀ index ∈ recognized.right.code.support, ∃ prior, recognized.pattern.bodyRen prior = index) :
    ∃ fuel, ∀ larger, fuel ≤ larger → ∀ rest : EquationStore (TotalTerm (extend Γ type)),
      ∀ view : ∀ {Δ : Context (TowerModel.setting valuation).R} (solution : Δ ⟶ extend Γ type),
        (ContextualDependentEta.frames (TowerModel.setting valuation).levels).Models solution [equation] ↔
          (scope.toScoped active).Holds solution,
      ∃ update smaller,
        ContextualDependentRecognitionConversion.tryActiveConv (S := TowerModel.setting valuation) TowerModel.facts
          TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red rigid complete normalizes certifyNormal
          larger type scope active equation view rest = some (.solved update smaller) := by
  obtain ⟨f₃, recovered, steps⟩ := step_solved_eventually valuation
    (ContextualDependentScopeConsequence.root_reflection rigid) rigid complete normalizes certifyNormal
    recognized.pattern recognized.right normal inside
  refine ⟨max (max f₁ f₂) f₃, fun larger enough rest view => ?_⟩
  have stepped := steps larger (by omega)
  unfold ContextualDependentRecognitionConversion.tryActiveConv
  rw [read]
  dsimp only
  erw [discovered larger (by omega)]
  dsimp only
  erw [recognizes larger (by omega)]
  dsimp only
  erw [stepped]
  dsimp only
  split
  · rename_i smaller
    exact ⟨_, smaller, rfl⟩
  · rename_i notSmaller
    exact (notSmaller (Nat.lt_succ_self Γ.arity)).elim

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
