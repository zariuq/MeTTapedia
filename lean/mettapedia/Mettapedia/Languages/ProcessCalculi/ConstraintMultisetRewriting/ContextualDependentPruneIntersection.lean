import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPrune
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternReplacement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScopeConsequence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingReplay

/-!
# Flex-flex equations force pruning to the intersection

Under a local rigid telescope, the newest metavariable `G` is applied to distinct locals `ȳ`
and the other side applies any term `f`, for instance an older metavariable `F`, to distinct
locals `x̄`, through its own dependent spine. Then every solution, in every future context,
gives `G` a value whose opening at fresh arguments is typed-equal to a renaming of a body over
the binders of `G` whose argument occurs among `x̄`, together with all outer variables.

The proof normalizes both opened values, renames them into the local telescope, and reads the
common parameters off the typed equality of normal forms (`common_parameters_forced`).
Inversion through the kept binders then succeeds, and the inverted body is typed by checking
reflection, with no budget. The result is transported from the spine read in `G`'s context and
reindexed by the solution to the spine reindexed directly, by the composition laws of
`ContextualDependentSpineTransport`.

Consequently pruning `G` to any restriction that covers the intersection loses no solution of
a store that contains the equation (`pruneFlexFlex`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPrune

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentEta
open ContextualDependentUpdate ContextualDependentTypedInversion ContextualDependentScope
open ContextualDependentPiSpine.Transport

section Generic

variable {Head : Type} {rules : Rules Head}

theorem equal_transport {first second : Context rules} (same : first = second)
    {left right type : Tm Head first.arity} {left' right' type' : Tm Head second.arity}
    (sameLeft : HEq left left') (sameRight : HEq right right') (sameType : HEq type type')
    (equal : Equal rules first.raw left right type) : Equal rules second.raw left' right' type' := by
  subst same
  obtain rfl := eq_of_heq sameLeft
  obtain rfl := eq_of_heq sameRight
  obtain rfl := eq_of_heq sameType
  exact equal

theorem typeOver_code_heq {first second : Context rules} (same : first = second) {one : TypeOver first}
    {two : TypeOver second} (sameType : HEq one two) : HEq one.code two.code := by
  subst same
  obtain rfl := eq_of_heq sameType
  rfl

/-- A term moved along an equality of contexts and annotations. -/
def transportTerm {first second : Context rules} (same : first = second) {one : TypeOver first}
    {two : TypeOver second} (sameType : HEq one two) (term : Term first one) : Term second two := by
  subst same
  exact (eq_of_heq sameType) ▸ term

theorem transportTerm_heq {first second : Context rules} (same : first = second) {one : TypeOver first}
    {two : TypeOver second} (sameType : HEq one two) (term : Term first one) :
    HEq (transportTerm same sameType term) term := by
  subst same
  obtain rfl := eq_of_heq sameType
  rfl

namespace Restriction

variable {Γ : Context rules} {type keptType : TypeOver Γ} {spine : Spine type} {kept : Spine keptType}
  (restriction : Restriction spine kept)

theorem resultAt_code {Δ : Context rules} (base : Δ ⟶ Γ) :
    Presentation.rename (restriction.ren base) (kept.reindex base).result.code = (spine.reindex base).result.code := by
  have same := congrArg TypeOver.code (restriction.resultAt base)
  change subst (renSub (restriction.ren base)) (kept.reindex base).result.code = _ at same
  rwa [subst_renSub] at same

/-- **A restriction is natural**: it is again a restriction after any outer substitution. -/
def reindex {Δ : Context rules} (base : Δ ⟶ Γ) : Restriction (spine.reindex base) (kept.reindex base) where
  keep := reindexArgs kept spine restriction.keep base
  injective := reindexArgs_injective kept spine restriction.keep base restriction.injective
  compatible := restriction.ren_compatible base
  resultCode := (restriction.resultAt_code base).symm
  resultLevel := (congrArg TypeOver.level (restriction.resultAt base)).symm

theorem reindex_ren {Δ Θ : Context rules} (base : Δ ⟶ Γ) (refinement : Θ ⟶ Δ) :
    HEq ((restriction.reindex base).ren refinement) (restriction.ren (refinement ≫ base)) :=
  Spine.argRen_comp_heq kept spine restriction.keep base refinement

end Restriction

/-- **An application** of a term to distinct locals of a scope, through its own dependent spine. -/
structure Application {Θ : Context rules} {scopeType : TypeOver Θ} (scope : Spine scopeType) where
  functionType : TypeOver Θ
  function : Term Θ functionType
  spine : Spine functionType
  args : spine.Local → scope.Local
  injective : Function.Injective args
  compatible : CtxRen spine.target.raw scope.target.raw (argRen spine scope idRen args)

namespace Application

variable {Θ : Context rules} {scopeType : TypeOver Θ} {scope : Spine scopeType} (app : Application scope)

def map : Inclusion app.spine.target scope.target :=
  inclusion app.spine scope idRen app.args Function.injective_id app.injective app.compatible

/-- The application `f x̄` in the local telescope. -/
def term : Term scope.target (app.spine.result.reindex app.map.hom) :=
  (app.spine.openFunction app.function).reindex app.map.hom

def reread {Δ : Context rules} (solution : Δ ⟶ Θ) : Ren (app.spine.reindex solution).target.arity
    (scope.reindex solution).target.arity :=
  argRen (app.spine.reindex solution) (scope.reindex solution) idRen (reindexArgs app.spine scope app.args solution)

theorem reread_compatible {Δ : Context rules} (solution : Δ ⟶ Θ) :
    CtxRen (app.spine.reindex solution).target.raw (scope.reindex solution).target.raw (app.reread solution) :=
  reindex_compatible app.spine scope app.args solution app.compatible

theorem term_code {Δ : Context rules} (solution : Δ ⟶ Θ) :
    subst (scope.map solution).substitution app.term.code =
      Presentation.rename (app.reread solution) ((app.spine.reindex solution).openFunction (app.function.reindex solution)).code := by
  change subst (scope.map solution).substitution (subst (renSub app.map.forward) (app.spine.openFunction app.function).code) = _
  rw [subst_renSub]
  exact (subst_map_rename app.spine scope app.args solution _).trans
    (congrArg (Presentation.rename (app.reread solution)) (app.spine.openFunction_reindex_code solution app.function))

theorem annotation_code {Δ : Context rules} (solution : Δ ⟶ Θ) :
    subst (scope.map solution).substitution (app.spine.result.reindex app.map.hom).code =
      Presentation.rename (app.reread solution) (app.spine.reindex solution).result.code := by
  change subst (scope.map solution).substitution (subst (renSub app.map.forward) app.spine.result.code) = _
  rw [subst_renSub]
  exact (subst_map_rename app.spine scope app.args solution _).trans
    (congrArg (fun result => Presentation.rename (app.reread solution) (TypeOver.code result))
      (app.spine.result_reindex solution))

end Application

end Generic

section Forcing

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (facts : FormFacts S.R S.roles) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (declared : DeclaredTypesFormed S.R)


variable {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}

include rigid complete facts algebra headTypingUnique roots heads declared in
/-- **The forcing core.** If every support variable of `G`'s normal opening is hit, through the
local telescope, by the argument map of the other side, then `G`'s opening is a renaming of a
body over the kept binders, for every restriction covering the intersection. -/
theorem forced_of_hits (pattern : Pattern spine scope) (app : Application scope)
    {keptType : TypeOver Γ} {kept : Spine keptType} (restriction : Restriction spine kept)
    (covers : ∀ position : spine.Local, (∃ other, app.args other = pattern.args position) →
      ∃ chosen, restriction.keep chosen = position)
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type)
    (gCode : Tm Head ((lifted spine).reindex solution).target.arity)
    (gNormal : ContextualDependentNormalChecking.Normal (S := S) gCode)
    (gSame : Equal S.R ((lifted spine).reindex solution).target.raw
      (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution)).code gCode
      ((lifted spine).reindex solution).result.code)
    (hits : ∀ index ∈ gCode.support, ∃ other, app.reread solution other = pattern.reread solution index) :
    ∃ inner : Term (kept.reindex (solution ≫ projectionHom Γ type)).target
        (kept.reindex (solution ≫ projectionHom Γ type)).result,
      Equal S.R (spine.reindex (solution ≫ projectionHom Γ type)).target.raw
        ((spine.reindex (solution ≫ projectionHom Γ type)).openFunction (pulledNewest solution)).code
        (Presentation.rename (restriction.ren (solution ≫ projectionHom Γ type)) inner.code)
        (spine.reindex (solution ≫ projectionHom Γ type)).result.code := by
  -- The support of `G`'s normal opening lies in the kept binders.
  let lifted' := restriction.reindex (projectionHom Γ type)
  have inside : ∀ index ∈ gCode.support, ∃ original, lifted'.ren solution original = index := by
    intro index present
    obtain ⟨other, hit⟩ := hits index present
    rcases ((lifted spine).reindex solution).variable_cases index with ⟨prior, rfl⟩ | ⟨position, rfl⟩
    · exact ⟨((kept.reindex (projectionHom Γ type)).reindex solution).outerRen prior,
        argRen_outer _ _ _ _ prior⟩
    · have hitLocal := hit
      change argRen (app.spine.reindex solution) (scope.reindex solution) idRen
          (reindexArgs app.spine scope app.args solution) other =
        argRen ((lifted spine).reindex solution) (scope.reindex solution) idRen
          (reindexArgs (lifted spine) scope pattern.liftedArgs solution)
          (((lifted spine).reindex solution).localIndex position) at hitLocal
      rw [argRen_local] at hitLocal
      rcases (app.spine.reindex solution).variable_cases other with ⟨outerOther, rfl⟩ | ⟨localOther, rfl⟩
      · rw [argRen_outer] at hitLocal
        exact ((scope.reindex solution).outer_ne_local _ _ hitLocal).elim
      · rw [argRen_local] at hitLocal
        have sameLocal := (scope.reindex solution).localIndex_injective hitLocal
        unfold reindexArgs at sameLocal
        have sameArgument := (scope.localReindexEquiv solution).symm.injective sameLocal
        obtain ⟨chosen, chosenKeep⟩ := covers
          (spine.localReindexEquiv (projectionHom Γ type)
            ((spine.reindex (projectionHom Γ type)).localReindexEquiv solution position))
          ⟨app.spine.localReindexEquiv solution localOther, sameArgument⟩
        refine ⟨((kept.reindex (projectionHom Γ type)).reindex solution).localIndex
          (((kept.reindex (projectionHom Γ type)).localReindexEquiv solution).symm
            ((kept.localReindexEquiv (projectionHom Γ type)).symm chosen)), ?_⟩
        change argRen ((kept.reindex (projectionHom Γ type)).reindex solution)
            ((spine.reindex (projectionHom Γ type)).reindex solution) idRen
            (reindexArgs (kept.reindex (projectionHom Γ type)) (spine.reindex (projectionHom Γ type))
              (reindexArgs kept spine restriction.keep (projectionHom Γ type)) solution) _ = _
        rw [argRen_local]
        congr 1
        simp only [reindexArgs, Equiv.apply_symm_apply, chosenKeep, Equiv.symm_apply_apply]
  -- Inversion through the kept binders and typing by checking reflection.
  have invertible := (ContextualDependentSupport.invert_lookup_defined_iff (lifted'.ren solution)
    (lifted'.ren_injective solution) gCode).mpr inside
  obtain ⟨bodyCode, found⟩ := Option.isSome_iff_exists.mp invertible
  have image := ContextualDependentInversion.invert_sound gCode (lifted'.ren solution) _
    (ContextualDependentInversion.lookup_exact _ (lifted'.ren_injective solution)) bodyCode found
  have gTyped := (Equal.typed (S := S) gSame ((lifted spine).reindex solution).target.formed).2
  have bodyTyped := ContextualDependentCheckingReplay.normal_typing_reflects facts algebra headTypingUnique
    complete roots heads declared (ContextualDependentScopeConsequence.root_reflection rigid)
    (lifted'.inclusionAt solution) (lifted'.ren_compatible solution)
    ((kept.reindex (projectionHom Γ type)).reindex solution).result bodyCode
    (by
      change Typed S.R _ (Presentation.rename (lifted'.ren solution) bodyCode)
        (Presentation.rename (lifted'.ren solution) _)
      rw [image, lifted'.resultAt_code solution]
      exact gTyped)
    (by
      change ContextualDependentNormalChecking.Normal (S := S) (Presentation.rename (lifted'.ren solution) bodyCode)
      rw [image]
      exact gNormal)
  let inner : Term ((kept.reindex (projectionHom Γ type)).reindex solution).target
      ((kept.reindex (projectionHom Γ type)).reindex solution).result := ⟨bodyCode, bodyTyped⟩
  have liftedEqual : Equal S.R ((lifted spine).reindex solution).target.raw
      (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution)).code
      (Presentation.rename (lifted'.ren solution) inner.code)
      ((lifted spine).reindex solution).result.code := by
    change Equal S.R _ _ (Presentation.rename (lifted'.ren solution) bodyCode) _
    rw [image]
    exact gSame
  -- Transport to the spines reindexed directly by the composite.
  let moved := transportTerm (kept.target_comp (projectionHom Γ type) solution)
    (kept.result_comp_heq (projectionHom Γ type) solution) inner
  refine ⟨moved, equal_transport (spine.target_comp (projectionHom Γ type) solution) ?_ ?_ ?_ liftedEqual⟩
  · exact code_heq (spine.target_comp (projectionHom Γ type) solution)
      (spine.result_comp_heq (projectionHom Γ type) solution)
      (openFunction_congr (type.reindex_comp solution (projectionHom Γ type)).symm
        (spine.reindex_comp_heq (projectionHom Γ type) solution) (Transport.cast_heq _ _).symm)
  · exact rename_heq (congrArg Context.arity (kept.target_comp (projectionHom Γ type) solution))
      (congrArg Context.arity (spine.target_comp (projectionHom Γ type) solution))
      (restriction.reindex_ren (projectionHom Γ type) solution)
      (code_heq (kept.target_comp (projectionHom Γ type) solution)
        (kept.result_comp_heq (projectionHom Γ type) solution)
        (transportTerm_heq _ _ inner).symm)
  · exact typeOver_code_heq (spine.target_comp (projectionHom Γ type) solution)
      (spine.result_comp_heq (projectionHom Γ type) solution)

include rigid complete normalizes facts algebra headTypingUnique roots heads declared in
/-- **Flex-flex forcing.** For `G ȳ ≐ f x̄` under a local telescope, every solution gives `G` a
value whose opening is a renaming of a body over the kept binders, for every restriction whose
kept binders include those `y` that occur among `x̄`. -/
theorem forced_flexFlex (pattern : Pattern spine scope) (app : Application scope)
    (sameType : app.spine.result.reindex app.map.hom = (lifted spine).result.reindex pattern.map.hom)
    {keptType : TypeOver Γ} {kept : Spine keptType} (restriction : Restriction spine kept)
    (covers : ∀ position : spine.Local, (∃ other, app.args other = pattern.args position) →
      ∃ chosen, restriction.keep chosen = position)
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type)
    (held : (pattern.constraint ((app.term).cast sameType)).Holds solution) :
    ∃ inner : Term (kept.reindex (solution ≫ projectionHom Γ type)).target
        (kept.reindex (solution ≫ projectionHom Γ type)).result,
      Equal S.R (spine.reindex (solution ≫ projectionHom Γ type)).target.raw
        ((spine.reindex (solution ≫ projectionHom Γ type)).openFunction (pulledNewest solution)).code
        (Presentation.rename (restriction.ren (solution ≫ projectionHom Γ type)) inner.code)
        (spine.reindex (solution ≫ projectionHom Γ type)).result.code := by
  -- The held equation, read through both argument maps.
  have heldEq : Equal S.R (scope.reindex solution).target.raw
      (Presentation.rename (pattern.reread solution)
        (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution)).code)
      (Presentation.rename (app.reread solution)
        ((app.spine.reindex solution).openFunction (app.function.reindex solution)).code)
      (Presentation.rename (pattern.reread solution) ((lifted spine).reindex solution).result.code) := by
    have opened := held
    rw [Pattern.constraint, Spine.toScoped_holds_iff] at opened
    change Equal S.R (scope.reindex solution).target.raw
      (subst (scope.map solution).substitution pattern.application.code)
      (subst (scope.map solution).substitution ((app.term).cast sameType).code)
      (subst (scope.map solution).substitution ((lifted spine).result.reindex pattern.map.hom).code) at opened
    rw [pattern.application_code, Term.cast_code, app.term_code, pattern.annotation_code] at opened
    exact opened
  have annotations : Presentation.rename (app.reread solution) (app.spine.reindex solution).result.code =
      Presentation.rename (pattern.reread solution) ((lifted spine).reindex solution).result.code := by
    rw [← app.annotation_code, ← pattern.annotation_code, sameType]
  -- Normal forms of both opened values.
  obtain ⟨gCode, gNormal, gSame⟩ := normalizes
    (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution))
  obtain ⟨fCode, fNormal, fSame⟩ := normalizes
    ((app.spine.reindex solution).openFunction (app.function.reindex solution))
  have gRenamed := gSame.rename (pattern.reread_compatible solution)
  have fRenamed := fSame.rename (app.reread_compatible solution)
  rw [annotations] at fRenamed
  have normalEqual : Equal S.R (scope.reindex solution).target.raw
      (Presentation.rename (app.reread solution) fCode) (Presentation.rename (pattern.reread solution) gCode)
      (Presentation.rename (pattern.reread solution) ((lifted spine).reindex solution).result.code) :=
    fRenamed.symm.trans (heldEq.symm.trans gRenamed)
  have common := ContextualDependentScopeConsequence.common_parameters_forced rigid complete
    (app.reread solution) (pattern.reread solution) (scope.reindex solution).target.formed fCode gCode _
    normalEqual fNormal gNormal
  exact forced_of_hits rigid complete facts algebra headTypingUnique roots heads declared pattern app
    restriction covers solution gCode gNormal gSame
    (fun index present => (ContextualDependentScopeConsequence.commonMask_iff _ _ _).mp (common index present))

include rigid complete normalizes facts algebra headTypingUnique roots heads declared in
/-- **Pruning to the intersection loses no solution.** A store whose solutions all satisfy a
flex-flex equation `G ȳ ≐ f x̄` is pruned to a restriction covering the intersection; the
whole store is instantiated with `G := λ ȳ. H (ȳ restricted)`. -/
def pruneFlexFlex (pattern : Pattern spine scope) (app : Application scope)
    (sameType : app.spine.result.reindex app.map.hom = (lifted spine).result.reindex pattern.map.hom)
    {keptType : TypeOver Γ} {kept : Spine keptType} (restriction : Restriction spine kept)
    (covers : ∀ position : spine.Local, (∃ other, app.args other = pattern.args position) →
      ∃ chosen, restriction.keep chosen = position)
    (problem : EquationStore (TotalTerm (extend Γ type)))
    (contains : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type), (frames S.levels).Models solution problem →
      (pattern.constraint ((app.term).cast sameType)).Holds solution) :
    Update S.levels problem :=
  prune S.levels restriction problem fun _ solution solved =>
    forced_flexFlex rigid complete normalizes facts algebra headTypingUnique roots heads declared
      pattern app sameType restriction covers solution (contains solution solved)

end Forcing

end ContextualDependentPrune
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
