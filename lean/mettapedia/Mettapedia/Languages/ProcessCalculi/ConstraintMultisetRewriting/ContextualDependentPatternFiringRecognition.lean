import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringStep

/-!
# Recognition of a pattern is complete when the argument types agree

Recognition reads `F x̄` from the left code of a scoped equation and builds the pattern data: the locals `x̄`,
assigned to the binders of `F`'s spine in order, distinct, with the declared type of each local equal to the
corresponding binder type of `F` (`CtxRen` compatibility), and the left code equal to the pattern application.

When the left code is the newest metavariable applied to distinct locals, one for each binder, the reading,
the assignment, distinctness and the identity of the left code with the application all hold
(`patternShape_some`); only the compatibility of declared types is a condition. Recognition up to conversion then
succeeds from the budget on which the type comparison accepts the annotation (`recognizeConv_eventually`).
Under cumulativity the compatibility can fail on a fragment equation: `x : U0` passed where `F` declares `U1`
(`ContextualDependentPatternFiring.Controls.cumulative_unread`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope

section Spines

variable {Head : Type} {rules : Rules Head}

/-- The binders of a nonempty spine: its first binder, then the binders of the rest. -/
theorem map_locals_bind {α : Type} {Γ : Context rules} (shape : ContextualDependentPiShape.Shape Γ)
    (rest : Spine shape.codomain) (f : (Spine.bind shape rest).Local → α) :
    (ContextualDependentPatternSolver.locals (Spine.bind shape rest)).map f =
      f (Sum.inl ()) :: (ContextualDependentPatternSolver.locals rest).map (fun position => f (Sum.inr position)) :=
  congrArg (List.cons (f (Sum.inl ()))) List.map_map

/-- **The opening of a function under a telescope** applies its renamed code to the locals, outermost first. -/
theorem openFunction_appSpine : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) (function : Term Γ type),
    (spine.openFunction function).code =
      appSpine (Presentation.rename spine.outerRen function.code)
        ((ContextualDependentPatternSolver.locals spine).map fun position => .var (spine.localIndex position))
  | _, _, .stop _, function => (rename_id function.code).symm
  | _, _, .bind shape rest, function => by
      rw [map_locals_bind]
      change (rest.openFunction (shape.fresh function)).code = _
      rw [openFunction_appSpine rest (shape.fresh function), appSpine_cons]
      congr 1
      change Tm.app (Presentation.rename rest.outerRen (Presentation.rename wk function.code))
          (.var (rest.outerRen 0)) =
        Tm.app (Presentation.rename (fun index => rest.outerRen index.succ) function.code)
          (.var ((Spine.bind shape rest).localIndex (Sum.inl ())))
      rw [Spine.localIndex_head, rename_comp]
      rfl

/-- Reading back a variable applied to variables. -/
theorem readApplication_appSpine {m : Nat} (head : Fin m) :
    ∀ arguments : List (Fin m),
      readApplication (appSpine (.var head : Tm Head m) (arguments.map Tm.var)) = some (head, arguments) := by
  intro arguments
  induction arguments using List.reverseRecOn with
  | nil => rfl
  | append_singleton rest last ih =>
      simp only [List.map_append, List.map_cons, List.map_nil, appSpine_concat, readApplication, ih, Option.map_some]

/-- The binders of a reindexed spine are the binders of the spine. -/
theorem locals_reindex : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {Δ : Context rules}
    (base : Δ ⟶ Γ),
    (ContextualDependentPatternSolver.locals (spine.reindex base)).map (spine.localReindexEquiv base) =
      ContextualDependentPatternSolver.locals spine
  | _, _, .stop _, _, _ => rfl
  | _, _, .bind shape rest, _, base => by
      have inner : List.map (fun position =>
            (Sum.inr (rest.localReindexEquiv (rawLift base shape.domain) position) : Unit ⊕ rest.Local))
          (ContextualDependentPatternSolver.locals (rest.reindex (rawLift base shape.domain))) =
          List.map Sum.inr (ContextualDependentPatternSolver.locals rest) := by
        rw [← locals_reindex rest (rawLift base shape.domain), List.map_map]
        rfl
      exact congrArg (List.cons (Sum.inl ())) (List.map_map.trans inner)

theorem length_locals : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type),
    (ContextualDependentPatternSolver.locals spine).length = spine.length
  | _, _, .stop _ => rfl
  | _, _, .bind shape rest => by
      have counted := congrArg List.length (map_locals_bind shape rest id)
      rw [List.map_id] at counted
      rw [counted, List.length_cons, List.length_map, length_locals rest]
      rfl

/-- **Assignment succeeds on lists of the spine's length**, and reads the list along the binders. -/
theorem assign_some {Local : Type} : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (values : List Local), values.length = spine.length →
      ∃ args, assign spine values = some args ∧ (ContextualDependentPatternSolver.locals spine).map args = values
  | _, _, .stop _, [], _ => ⟨Empty.elim, rfl, rfl⟩
  | _, _, .stop _, _ :: _, length => by simp [Spine.length] at length
  | _, _, .bind _ rest, [], length => by simp [Spine.length] at length
  | _, _, .bind shape rest, first :: others, length => by
      obtain ⟨later, assigned, read⟩ := assign_some rest others (by
        simp only [List.length_cons, Spine.length] at length
        omega)
      refine ⟨Sum.elim (fun _ => first) later, ?_, ?_⟩
      · change (assign rest others).map (fun later => Sum.elim (fun _ => first) later) = _
        rw [assigned]
        rfl
      · refine (map_locals_bind shape rest (Sum.elim (fun _ => first) later)).trans ?_
        change first :: (ContextualDependentPatternSolver.locals rest).map later = first :: others
        rw [read]

end Spines

section Shape

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable {Γ : Context S.R} {type : TypeOver Γ} {scopeType : TypeOver (extend Γ type)}

theorem localOf_localIndex (scope : Spine scopeType) (position : scope.Local) :
    localOf scope (scope.localIndex position) = some position := by
  unfold localOf Spine.localIndex
  rw [Equiv.symm_apply_apply]
  rfl

theorem mapM_localOf (scope : Spine scopeType) :
    ∀ positions : List scope.Local, (positions.map scope.localIndex).mapM (localOf scope) = some positions
  | [] => rfl
  | position :: rest => by
      simp only [List.map_cons, List.mapM_cons, localOf_localIndex, mapM_localOf scope rest]
      rfl

/-- The application of a pattern is the newest metavariable applied to its arguments, outermost first. -/
theorem application_code (spine : Spine type) (scope : Spine scopeType) (pattern : Pattern spine scope) :
    pattern.application.code = appSpine (.var (scope.outerRen 0))
      ((ContextualDependentPatternSolver.locals spine).map fun position =>
        .var (scope.localIndex (pattern.args position))) := by
  change subst (renSub pattern.map.forward) ((lifted spine).openFunction (newest Γ type)).code = _
  rw [subst_renSub, openFunction_appSpine, rename_appSpine]
  change appSpine (.var (pattern.map.forward ((lifted spine).outerRen 0))) _ = _
  have outer : pattern.map.forward ((lifted spine).outerRen 0) = scope.outerRen 0 :=
    argRen_outer (lifted spine) scope idRen pattern.liftedArgs 0
  rw [outer, List.map_map]
  congr 1
  rw [← locals_reindex spine (projectionHom Γ type), List.map_map]
  apply List.map_congr_left
  intro position _
  change Tm.var (pattern.map.forward ((lifted spine).localIndex position)) = _
  have local' : pattern.map.forward ((lifted spine).localIndex position) =
      scope.localIndex (pattern.liftedArgs position) :=
    argRen_local (lifted spine) scope idRen pattern.liftedArgs position
  rw [local']
  rfl

variable [DecidableEq Head]

/-- **Recognition reads every newest-metavariable pattern** whose argument types agree with the binder types. -/
theorem patternShape_some (spine : Spine type) (scope : Spine scopeType) (active : Active scope.target)
    (positions : List scope.Local)
    (left : active.left.code = appSpine (.var (scope.outerRen 0)) (positions.map fun position =>
      .var (scope.localIndex position)))
    (length : positions.length = spine.length) (distinct : positions.Nodup)
    (compatible : ∀ args : spine.Local → scope.Local, (ContextualDependentPatternSolver.locals spine).map args = positions →
      CtxRen (lifted spine).target.raw scope.target.raw
        (argRen (lifted spine) scope idRen (fun position => args (spine.localReindexEquiv _ position)))) :
    ∃ shape, ContextualDependentRecognitionConversion.patternShape spine scope active = some shape ∧
      (ContextualDependentPatternSolver.locals spine).map shape.pattern.args = positions := by
  obtain ⟨args, assigned, read⟩ := assign_some spine positions length
  have readLeft : readApplication active.left.code = some (scope.outerRen 0, positions.map scope.localIndex) := by
    rw [left]
    have same : (positions.map fun position => (Tm.var (scope.localIndex position) : Tm Head scope.target.arity)) =
        (positions.map scope.localIndex).map Tm.var := by rw [List.map_map]; rfl
    rw [same, readApplication_appSpine]
  unfold ContextualDependentRecognitionConversion.patternShape
  split
  · rename_i missing
    rw [readLeft] at missing
    cases missing
  · rename_i headIndex arguments found
    rw [readLeft] at found
    cases found
    split
    · rename_i missing
      rw [mapM_localOf] at missing
      cases missing
    · rename_i values found
      rw [mapM_localOf] at found
      cases found
      split
      · rename_i missing
        rw [assigned] at missing
        cases missing
      · rename_i chosen found
        rw [assigned] at found
        cases found
        rw [dif_pos distinct, dif_pos (compatible args read)]
        dsimp only
        rw [dif_pos]
        · exact ⟨_, rfl, read⟩
        · rw [application_code, left]
          conv_lhs => rw [← read]
          rw [List.map_map]
          rfl

end Shape

section Inversion

variable {Head : Type} {rules : Rules Head}

theorem mapRen_outer : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {Δ : Context rules}
    (base : Δ ⟶ Γ) (rho : Ren Γ.arity Δ.arity) (index : Fin Γ.arity),
    spine.mapRen base rho (spine.outerRen index) = (spine.reindex base).outerRen (rho index)
  | _, _, .stop _, _, _, _, _ => rfl
  | _, _, .bind shape rest, _, base, rho, index => by
      change rest.mapRen (rawLift base shape.domain) (liftRen rho) (rest.outerRen index.succ) =
        (rest.reindex (rawLift base shape.domain)).outerRen (rho index).succ
      rw [mapRen_outer rest (rawLift base shape.domain) (liftRen rho) index.succ]
      rfl

theorem mapRen_local : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {Δ : Context rules}
    (base : Δ ⟶ Γ) (rho : Ren Γ.arity Δ.arity) (position : spine.Local),
    spine.mapRen base rho (spine.localIndex position) =
      (spine.reindex base).localIndex ((spine.localReindexEquiv base).symm position)
  | _, _, .stop _, _, _, _, position => position.elim
  | _, _, .bind shape rest, _, base, rho, position => by
      change Unit ⊕ rest.Local at position
      rcases position with first | position
      · cases first
        have target : ((Spine.bind shape rest).reindex base).localIndex
            (((Spine.bind shape rest).localReindexEquiv base).symm (Sum.inl ())) =
            (rest.reindex (rawLift base shape.domain)).outerRen 0 :=
          Spine.localIndex_head (shape.reindex base) (rest.reindex (rawLift base shape.domain))
        rw [target, Spine.localIndex_head]
        change rest.mapRen (rawLift base shape.domain) (liftRen rho) (rest.outerRen 0) = _
        rw [mapRen_outer]
        rfl
      · rw [Spine.localIndex_tail]
        change rest.mapRen (rawLift base shape.domain) (liftRen rho) (rest.localIndex position) =
          (rest.reindex (rawLift base shape.domain)).localIndex
            ((rest.localReindexEquiv (rawLift base shape.domain)).symm position)
        rw [mapRen_local]

variable {Γ : Context rules} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}

theorem bodyRen_outer (pattern : Pattern spine scope) (prior : Fin Γ.arity) :
    pattern.bodyRen (spine.outerRen prior) = scope.outerRen prior.succ := by
  unfold Pattern.bodyRen
  rw [mapRen_outer]
  exact argRen_outer (lifted spine) scope idRen pattern.liftedArgs (wk prior)

theorem bodyRen_local (pattern : Pattern spine scope) (position : spine.Local) :
    pattern.bodyRen (spine.localIndex position) = scope.localIndex (pattern.args position) := by
  unfold Pattern.bodyRen
  rw [mapRen_local]
  change argRen (lifted spine) scope idRen pattern.liftedArgs ((lifted spine).localIndex _) = _
  rw [argRen_local]
  change scope.localIndex (pattern.args ((spine.localReindexEquiv _) ((spine.localReindexEquiv _).symm position))) = _
  rw [Equiv.apply_symm_apply]

/-- **The inversion map covers the outer variables other than `F` and the pattern arguments.** -/
theorem bodyRen_covers (pattern : Pattern spine scope) {positions : List scope.Local}
    (read : (ContextualDependentPatternSolver.locals spine).map pattern.args = positions)
    {index : Fin scope.target.arity}
    (covered : (∃ prior : Fin Γ.arity, scope.outerRen prior.succ = index) ∨
      ∃ position ∈ positions, scope.localIndex position = index) :
    ∃ original, pattern.bodyRen original = index := by
  rcases covered with ⟨prior, rfl⟩ | ⟨position, member, rfl⟩
  · exact ⟨spine.outerRen prior, bodyRen_outer pattern prior⟩
  · rw [← read] at member
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
    exact ⟨spine.localIndex source, bodyRen_local pattern source⟩

end Inversion

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
