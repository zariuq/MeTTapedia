import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlexReorder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEqualizerSelection

/-!
# Intersection: `λ x̄. G ȳ ≐ λ x̄. G z̄` for the newest metavariable

Both sides apply the newest metavariable `G` to distinct locals. Every solution gives `G` a value whose normal opening
`M` satisfies `M[ȳ] = M[z̄]`; two renamings of one normal term are typed-equal only when they agree on its support
(`ContextualDependentNormalEqualizer.equal_agreement`). So `M` mentions only the binders of `G` at which `ȳ` and `z̄`
agree, and every solution factors through `G := λ w̄. H (w̄ restricted to those binders)` (`forced_intersection`). The
**intersection update** prunes `G` to `H` (R76's `ContextualDependentPrune.prune`) and then drops the instantiated
equation, which the conversion test certifies (`intersectUpdate`).

**The rank.** The step keeps every declaration: `H` replaces `G`. It lowers the normal weight when no other equation
mentions `G` (`Weakened`): those equations are weakenings of equations over the older context, the pruning answer fixes
the older context (`ContextualDependentPrune.Restriction.answer_projection`), and a side read from the same older code
weighs the same past any newest declaration (`sideWeight_of_weakened`, `storeWeight_weakened`). The dropped equation
weighs at least one, so the weight rank drops (`tryIntersect`, carried in the progress type `Progress`).

The **intersection round** is the reorder round, and when that round is stuck, the intersection rule at the newest
declaration on the first equation (`intersectRound`). It is conservative over the reorder round, eventually constant,
and settles where it is not stuck.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersection

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope
open ContextualDependentPrune ContextualDependentPiSpine.Transport
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentEtaLong ContextualDependentConversionBudget
open ContextualDependentFlexReorder

/-! ## Weights past the newest declaration -/

section Weights

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Renaming keeps the weight.** -/
theorem weight_rename : ∀ {n m : Nat} (ρ : Ren n m) (t : Tm Head n),
    weight (Presentation.rename ρ t) = weight t
  | _, _, _, .var _ => rfl
  | _, _, _, .const _ => rfl
  | _, _, _, .head _ => rfl
  | _, _, ρ, .pi A B => by simp only [Presentation.rename, weight, weight_rename ρ A, weight_rename (liftRen ρ) B]
  | _, _, ρ, .sigma A B => by
      simp only [Presentation.rename, weight, weight_rename ρ A, weight_rename (liftRen ρ) B]
  | _, _, ρ, .id A a b => by
      simp only [Presentation.rename, weight, weight_rename ρ A, weight_rename ρ a, weight_rename ρ b]
  | _, _, ρ, .lam b => by simp only [Presentation.rename, weight, weight_rename (liftRen ρ) b]
  | _, _, ρ, .app f a => by simp only [Presentation.rename, weight, weight_rename ρ f, weight_rename ρ a]
  | _, _, ρ, .pair a b => by simp only [Presentation.rename, weight, weight_rename ρ a, weight_rename ρ b]
  | _, _, ρ, .fst p => by simp only [Presentation.rename, weight, weight_rename ρ p]
  | _, _, ρ, .snd p => by simp only [Presentation.rename, weight, weight_rename ρ p]
  | _, _, ρ, .refl z => by simp only [Presentation.rename, weight, weight_rename ρ z]

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra complete in
/-- **Sides read from the same older code weigh the same past any newest declaration.** Both are renamed into the
context with both newest declarations, where they are one term at one type; normal forms there are unique up to heads. -/
theorem sideWeight_of_weakened {Γ : Context S.R} (A B : TypeOver Γ) (side : TotalTerm (extend Γ A))
    (side' : TotalTerm (extend Γ B)) {code type : Tm Head Γ.arity}
    (codes : side.2.code = Presentation.rename wk code ∧ side.1.code = Presentation.rename wk type)
    (codes' : side'.2.code = Presentation.rename wk code ∧ side'.1.code = Presentation.rename wk type) :
    sideWeight facts roots heads algebra rigid complete side =
      sideWeight facts roots heads algebra rigid complete side' := by
  obtain ⟨v, normal⟩ := long_exists facts roots heads algebra rigid complete (extend Γ A).formed side.2.typed
  obtain ⟨v', normal'⟩ := long_exists facts roots heads algebra rigid complete (extend Γ B).formed side'.2.typed
  have isB : IsType S.R (.snoc Γ.raw A.code) (Presentation.rename wk B.code) :=
    IsType.rename ⟨B.level, B.universeWitness, B.formed⟩ (CtxRen.wk Γ.raw A.code)
  have formedΔ : CtxFormed S.R (.snoc (.snoc Γ.raw A.code) (Presentation.rename wk B.code)) :=
    (extend Γ A).formed.snoc isB
  have first := normal.rename facts (CtxRen.wk (.snoc Γ.raw A.code) (Presentation.rename wk B.code))
    (extend Γ A).formed formedΔ
  have second := normal'.rename facts (CtxRen.snoc (CtxRen.wk Γ.raw A.code) B.code) (extend Γ B).formed formedΔ
  have lifted : (fun i => liftRen (wk : Ren Γ.arity (Γ.arity + 1)) (wk i)) = fun i => wk (wk i) :=
    funext fun _ => rfl
  rw [codes.1, codes.2, rename_comp, rename_comp] at first
  rw [codes'.1, codes'.2, rename_comp, rename_comp, lifted] at second
  have same := long_unique facts roots heads algebra complete formedΔ second.1 first.1
    (.trans (.symm second.2) first.2)
  have weights := weight_of_same same
  rw [weight_rename, weight_rename] at weights
  rw [sideWeight_eq facts roots heads algebra rigid complete side normal,
    sideWeight_eq facts roots heads algebra rigid complete side' normal', weights]

/-- **An equation that does not mention the newest declaration**: its four codes are weakenings. -/
def Weakened {Γ : Context S.R} {A : TypeOver Γ} (equation : Equation (TotalTerm (extend Γ A))) : Prop :=
  ∃ c₁ t₁ c₂ t₂ : Tm Head Γ.arity,
    equation.1.2.code = Presentation.rename wk c₁ ∧ equation.1.1.code = Presentation.rename wk t₁ ∧
      equation.2.2.code = Presentation.rename wk c₂ ∧ equation.2.1.code = Presentation.rename wk t₂

/-- An answer that fixes the older context fixes every weakened code. -/
theorem subst_weakened {Γ : Context S.R} {A B : TypeOver Γ} (answer : extend Γ B ⟶ extend Γ A)
    (fixes : answer ≫ projectionHom Γ A = projectionHom Γ B) (code : Tm Head Γ.arity) :
    subst answer.substitution (Presentation.rename wk code) = Presentation.rename wk code := by
  have composite := congrArg (fun hom : extend Γ B ⟶ Γ => subst hom.substitution code) fixes
  rw [← subst_projection code, subst_subComp]
  exact composite

include facts roots heads algebra complete in
/-- **Weakened equations keep their weight** under an answer that fixes the older context. -/
theorem storeWeight_weakened {Γ : Context S.R} {A B : TypeOver Γ} (answer : extend Γ B ⟶ extend Γ A)
    (fixes : answer ≫ projectionHom Γ A = projectionHom Γ B) :
    ∀ (rest : EquationStore (TotalTerm (extend Γ A))), (∀ equation ∈ rest, Weakened equation) →
      storeWeight facts roots heads algebra rigid complete ((frames S.levels).applyStore answer rest) =
        storeWeight facts roots heads algebra rigid complete rest
  | [], _ => rfl
  | equation :: rest, weakened => by
      obtain ⟨c₁, t₁, c₂, t₂, e₁, f₁, e₂, f₂⟩ := weakened equation List.mem_cons_self
      have ih := storeWeight_weakened answer fixes rest (fun other member => weakened other (List.mem_cons_of_mem _ member))
      have left := sideWeight_of_weakened facts roots heads algebra rigid complete A B equation.1
        (equation.1.reindex answer) ⟨e₁, f₁⟩
        ⟨by
          change subst answer.substitution equation.1.2.code = _
          rw [e₁, subst_weakened answer fixes],
         by
          change subst answer.substitution equation.1.1.code = _
          rw [f₁, subst_weakened answer fixes]⟩
      have right := sideWeight_of_weakened facts roots heads algebra rigid complete A B equation.2
        (equation.2.reindex answer) ⟨e₂, f₂⟩
        ⟨by
          change subst answer.substitution equation.2.2.code = _
          rw [e₂, subst_weakened answer fixes],
         by
          change subst answer.substitution equation.2.1.code = _
          rw [f₂, subst_weakened answer fixes]⟩
      change equationWeight facts roots heads algebra rigid complete (equation.1.reindex answer, equation.2.reindex answer) +
          storeWeight facts roots heads algebra rigid complete ((frames S.levels).applyStore answer rest) =
        equationWeight facts roots heads algebra rigid complete equation +
          storeWeight facts roots heads algebra rigid complete rest
      rw [ih]
      unfold equationWeight
      dsimp only
      rw [← left, ← right]

end Weights

/-! ## Intersection forces the pruning -/

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

include rigid complete normalizes facts algebra headTypingUnique roots heads declared in
/-- **Intersection forcing.** For `G ȳ ≐ G z̄` under a local telescope, every solution gives `G` a value whose opening
is a renaming of a body over the kept binders, for every restriction that keeps the binders at which `ȳ` and `z̄`
agree. -/
theorem forced_intersection (first second : Pattern spine scope)
    (sameType : (lifted spine).result.reindex second.map.hom = (lifted spine).result.reindex first.map.hom)
    {keptType : TypeOver Γ} {kept : Spine keptType} (restriction : Restriction spine kept)
    (covers : ∀ position : (lifted spine).Local, second.liftedArgs position = first.liftedArgs position →
      ∃ chosen, restriction.keep chosen = spine.localReindexEquiv (projectionHom Γ type) position)
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type)
    (held : (first.constraint (second.application.cast sameType)).Holds solution) :
    ∃ inner : Term (kept.reindex (solution ≫ projectionHom Γ type)).target
        (kept.reindex (solution ≫ projectionHom Γ type)).result,
      Equal S.R (spine.reindex (solution ≫ projectionHom Γ type)).target.raw
        ((spine.reindex (solution ≫ projectionHom Γ type)).openFunction (pulledNewest solution)).code
        (Presentation.rename (restriction.ren (solution ≫ projectionHom Γ type)) inner.code)
        (spine.reindex (solution ≫ projectionHom Γ type)).result.code := by
  -- The held equation, read through both argument maps.
  have heldEq : Equal S.R (scope.reindex solution).target.raw
      (Presentation.rename (first.reread solution)
        (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution)).code)
      (Presentation.rename (second.reread solution)
        (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution)).code)
      (Presentation.rename (first.reread solution) ((lifted spine).reindex solution).result.code) := by
    have opened := held
    rw [Pattern.constraint, Spine.toScoped_holds_iff] at opened
    change Equal S.R (scope.reindex solution).target.raw
      (subst (scope.map solution).substitution first.application.code)
      (subst (scope.map solution).substitution (second.application.cast sameType).code)
      (subst (scope.map solution).substitution ((lifted spine).result.reindex first.map.hom).code) at opened
    rw [first.application_code, Term.cast_code, second.application_code, first.annotation_code] at opened
    exact opened
  have annotations : Presentation.rename (second.reread solution) ((lifted spine).reindex solution).result.code =
      Presentation.rename (first.reread solution) ((lifted spine).reindex solution).result.code := by
    rw [← second.annotation_code, ← first.annotation_code, sameType]
  -- The normal opening of `G`, and the agreement of the two argument maps on its support.
  obtain ⟨gCode, gNormal, gSame⟩ := normalizes
    (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution))
  have gFirst := gSame.rename (first.reread_compatible solution)
  have gSecond := gSame.rename (second.reread_compatible solution)
  rw [annotations] at gSecond
  have normalEqual : Equal S.R (scope.reindex solution).target.raw
      (Presentation.rename (first.reread solution) gCode) (Presentation.rename (second.reread solution) gCode)
      (Presentation.rename (first.reread solution) ((lifted spine).reindex solution).result.code) :=
    gFirst.symm.trans (heldEq.trans gSecond)
  have agree := ContextualDependentNormalEqualizer.equal_agreement rigid complete
    (scope.reindex solution).target.formed gCode (first.reread solution) (second.reread solution) normalEqual gNormal
  -- The support of `G`'s normal opening lies in the kept binders.
  let lifted' := restriction.reindex (projectionHom Γ type)
  have inside : ∀ index ∈ gCode.support, ∃ original, lifted'.ren solution original = index := by
    intro index present
    have hit := agree index present
    rcases ((lifted spine).reindex solution).variable_cases index with ⟨prior, rfl⟩ | ⟨position, rfl⟩
    · exact ⟨((kept.reindex (projectionHom Γ type)).reindex solution).outerRen prior,
        argRen_outer _ _ _ _ prior⟩
    · have hitLocal := hit
      change argRen ((lifted spine).reindex solution) (scope.reindex solution) idRen
          (reindexArgs (lifted spine) scope first.liftedArgs solution)
          (((lifted spine).reindex solution).localIndex position) =
        argRen ((lifted spine).reindex solution) (scope.reindex solution) idRen
          (reindexArgs (lifted spine) scope second.liftedArgs solution)
          (((lifted spine).reindex solution).localIndex position) at hitLocal
      rw [argRen_local, argRen_local] at hitLocal
      have sameLocal := (scope.reindex solution).localIndex_injective hitLocal
      unfold reindexArgs at sameLocal
      have sameArgument := (scope.localReindexEquiv solution).symm.injective sameLocal
      obtain ⟨chosen, chosenKeep⟩ :=
        covers ((spine.reindex (projectionHom Γ type)).localReindexEquiv solution position) sameArgument.symm
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
/-- **Pruning to the intersection loses no solution.** A store whose solutions all satisfy `G ȳ ≐ G z̄` is pruned to a
restriction that keeps the agreeing binders. -/
def pruneIntersection (first second : Pattern spine scope)
    (sameType : (lifted spine).result.reindex second.map.hom = (lifted spine).result.reindex first.map.hom)
    {keptType : TypeOver Γ} {kept : Spine keptType} (restriction : Restriction spine kept)
    (covers : ∀ position : (lifted spine).Local, second.liftedArgs position = first.liftedArgs position →
      ∃ chosen, restriction.keep chosen = spine.localReindexEquiv (projectionHom Γ type) position)
    (problem : EquationStore (TotalTerm (extend Γ type)))
    (contains : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type), (frames S.levels).Models solution problem →
      (first.constraint (second.application.cast sameType)).Holds solution) :
    Update S.levels problem :=
  prune S.levels restriction problem fun _ solution solved =>
    forced_intersection rigid complete normalizes facts algebra headTypingUnique roots heads declared
      first second sameType restriction covers solution (contains solution solved)

end Forcing

/-! ## Dropping a certified equation -/

section Drop

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Drop an equation that holds at every solution.** -/
def dropValid {Γ : Context S.R} (equation : Equation (TotalTerm Γ)) (rest : EquationStore (TotalTerm Γ))
    (valid : (frames S.levels).E equation.1 equation.2) : Update S.levels (equation :: rest) where
  target := Γ
  answer := 𝟙 Γ
  remaining := rest
  sound := by
    intro Δ residual solved
    rw [Category.comp_id]
    intro other member
    rcases List.mem_cons.mp member with same | later
    · rw [same]
      exact (frames S.levels).preserves residual valid
    · exact solved other later
  complete := by
    intro Δ solution solved
    refine ⟨solution, fun other member => solved other (List.mem_cons_of_mem _ member), fun term => ?_⟩
    rw [Category.comp_id]
    exact ((frames S.levels).equivalence Δ).refl _

end Drop

/-! ## The intersection rule -/

section Rule

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- **A progress of the weight rank**: an update whose residual store is below the store. -/
def Progress {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Type :=
  {update : Update S.levels problem //
    ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
    (weightRank facts roots heads algebra rigid complete problem)}

omit [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq] [DecidableRel S.R.cumulative] in
/-- **Isolation, read from the codes**: every equation strengthens past the newest declaration. -/
def isolatedCheck {Γ : Context S.R} {A : TypeOver Γ} :
    (rest : EquationStore (TotalTerm (extend Γ A))) → Option (PLift (∀ equation ∈ rest, Weakened equation))
  | [] => some ⟨fun _ member => absurd member List.not_mem_nil⟩
  | equation :: rest =>
      match ContextualDependentInPlace.strengthenCode (n := Γ.arity) equation.1.2.code,
          ContextualDependentInPlace.strengthenCode (n := Γ.arity) equation.1.1.code,
          ContextualDependentInPlace.strengthenCode (n := Γ.arity) equation.2.2.code,
          ContextualDependentInPlace.strengthenCode (n := Γ.arity) equation.2.1.code, isolatedCheck rest with
      | some c₁, some t₁, some c₂, some t₂, some later => some ⟨fun other member => by
          rcases List.mem_cons.mp member with same | inRest
          · rw [same]
            exact ⟨c₁.val, t₁.val, c₂.val, t₂.val, c₁.property.symm, t₁.property.symm, c₂.property.symm,
              t₂.property.symm⟩
          · exact later.down other inRest⟩
      | _, _, _, _, _ => none

/-- **Intersect one recognized pattern** `G ȳ` against `G z̄` on the right, and drop the instantiated equation. -/
def tryIntersect (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    {scopeType : TypeOver (extend Γ₀ newer)} (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend Γ₀ newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ₀ newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ₀ newer))) (isolated : ∀ other ∈ rest, Weakened other)
    (spine : Spine newer) (recognized : Recognized spine scope active) :
    Option (Progress facts roots heads algebra rigid complete (equation :: rest)) := by
  haveI := localDecidableEq scope
  haveI := localDecidableEq spine
  exact
  match readApplication recognized.right.code with
  | none => none
  | some (_, arguments) =>
    match arguments.mapM (localOf scope) with
    | none => none
    | some values =>
      match assigned : assign spine values with
      | none => none
      | some args =>
        if distinct : values.Nodup then
        if compatible : CtxRen (lifted spine).target.raw scope.target.raw
            (argRen (lifted spine) scope idRen (fun position => args (spine.localReindexEquiv _ position))) then
          let second : Pattern spine scope := ⟨args, assign_injective spine values args assigned distinct, compatible⟩
          if sameType : ((lifted spine).result.reindex second.map.hom).code =
              ((lifted spine).result.reindex recognized.pattern.map.hom).code ∧
              ((lifted spine).result.reindex second.map.hom).level =
              ((lifted spine).result.reindex recognized.pattern.map.hom).level then
          if rightSame : recognized.right.code = second.application.code then
            let mask := (locals spine).map fun position => decide (second.args position = recognized.pattern.args position)
            let keepList := (locals spine).filter fun position =>
              decide (second.args position = recognized.pattern.args position)
            match dropPis mask (fun index => some index) newer.code with
            | none => none
            | some keptCode =>
              match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ₀
                  keptCode with
              | none => none
              | some next =>
                match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer
                    fuel keepList.length next.val with
                | none => none
                | some kept =>
                  match keptAssigned : assign kept keepList with
                  | none => none
                  | some keep =>
                    if keptDistinct : keepList.Nodup then
                    if keptCompatible : CtxRen kept.target.raw spine.target.raw (argRen kept spine idRen keep) then
                    if keptResult : spine.result.code = Presentation.rename (argRen kept spine idRen keep) kept.result.code ∧
                        spine.result.level = kept.result.level then
                      let restriction : Restriction spine kept :=
                        ⟨keep, assign_injective kept keepList keep keptAssigned keptDistinct, keptCompatible,
                          keptResult.1, keptResult.2⟩
                      if covering : ∀ position ∈ locals spine,
                          second.args position = recognized.pattern.args position →
                            ∃ chosen ∈ locals kept, keep chosen = position then
                        let pruned := pruneIntersection rigid complete normalizes facts algebra headTypingUnique roots
                          heads declared recognized.pattern second (TypeOver.ext sameType.1 sameType.2) restriction
                          (fun position same => by
                            obtain ⟨chosen, _, hit⟩ := covering (spine.localReindexEquiv _ position)
                              (mem_locals spine _) same
                            exact ⟨chosen, hit⟩)
                          (equation :: rest)
                          (fun solution solved => by
                            have held := (recognized.holds_iff solution).mp ((view solution).mp
                              (fun other member => by
                                obtain rfl := List.mem_singleton.mp member
                                exact solved _ List.mem_cons_self))
                            have same : recognized.right = second.application.cast (TypeOver.ext sameType.1 sameType.2) :=
                              Term.ext (by rw [Term.cast_code]; exact rightSame)
                            rw [same] at held
                            exact held)
                        match Conversion.compare facts roots heads algebra reducer fuel
                            (equation.1.reindex restriction.answer) (equation.2.reindex restriction.answer) with
                        | none => none
                        | some certificate =>
                            some ⟨pruned.then (dropValid (equation.1.reindex restriction.answer,
                                equation.2.reindex restriction.answer)
                                ((frames S.levels).applyStore restriction.answer rest) certificate.down), by
                              change ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete
                                  ((frames S.levels).applyStore restriction.answer rest))
                                (weightRank facts roots heads algebra rigid complete (equation :: rest))
                              have kept := storeWeight_weakened facts roots heads algebra rigid complete
                                restriction.answer restriction.answer_projection rest isolated
                              have positive := equationWeight_pos facts roots heads algebra rigid complete equation
                              unfold weightRank ContextualDependentWorklist.Below
                              refine Prod.Lex.right _ ?_
                              change storeWeight facts roots heads algebra rigid complete
                                  ((frames S.levels).applyStore restriction.answer rest) <
                                equationWeight facts roots heads algebra rigid complete equation +
                                  storeWeight facts roots heads algebra rigid complete rest
                              omega⟩
                      else none
                    else none
                    else none
                    else none
          else none
          else none
        else none
        else none

/-- **The intersection rule on one store equation**: isolation of the others, the scoped reading, `G`'s spine and the
recognized pattern on the left. -/
def intersectEquation (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    (equation : Equation (TotalTerm (extend Γ₀ newer))) (rest : EquationStore (TotalTerm (extend Γ₀ newer))) :
    Option (Progress facts roots heads algebra rigid complete (equation :: rest)) :=
  match isolatedCheck rest with
  | none => none
  | some isolated =>
      match viewEquation facts roots heads algebra declared choices reducer root fuel equation with
      | none => none
      | some ⟨scope, active, view⟩ =>
          match readApplication active.left.code with
          | none => none
          | some (_, arguments) =>
              match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel
                  arguments.length newer with
              | none => none
              | some spine =>
                  match recognize spine scope active with
                  | none => none
                  | some recognized =>
                      tryIntersect facts roots heads algebra rigid complete declared choices reducer normalizes
                        headTypingUnique fuel newer scope active equation view rest isolated.down spine recognized

/-- Run a computation at the newest declaration. -/
def throughNewestProgress {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (solve : {Γ₀ : Context S.R} → (type : TypeOver Γ₀) → (stored : EquationStore (TotalTerm (extend Γ₀ type))) →
      Option (Progress facts roots heads algebra rigid complete stored)) :
    Option (Progress facts roots heads algebra rigid complete problem) := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact solve type problem

/-- **The intersection rule**: the first equation, at the newest declaration. -/
def intersectRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (Progress facts roots heads algebra rigid complete problem) :=
  match newestOf facts roots heads algebra declared choices reducer fuel Θ with
  | none => none
  | some view => throughNewestProgress facts roots heads algebra rigid complete view problem fun newer stored =>
      match stored with
      | [] => none
      | equation :: rest => intersectEquation facts roots heads algebra rigid complete declared choices reducer root
          normalizes headTypingUnique fuel newer equation rest

/-! ## The round -/

/-- **One intersection round**: the reorder round; when it is stuck, the intersection rule. -/
def intersectRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match intersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel problem with
      | some found => .progress found.val found.property
      | none => .stuck
  | other => other

/-- **The intersection family**, at the weight rank. -/
noncomputable def intersectFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

end Rule

end ContextualDependentIntersection
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
