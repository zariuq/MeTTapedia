import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringRecognition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentInstantiation

/-!
# Firing on the inversion row

**The inversion row of the census** (`InversionRow`), read from the store: the normal opening of the left side is
the newest metavariable `F` applied to distinct locals `x̄`; every variable of the normal opening of the right side
is an older metavariable or one of `x̄`; and the declared types agree: each local's declared type is the
corresponding binder type of `F`, and the annotation's result type is `F`'s result type at `x̄`, up to conversion.

When an equation of a store is in the dynamic pattern fragment and in this row, and the newest declaration is
normal, R94's conversion pattern rule decides the store from some budget on (`patternRuleConv_fires`), and the
firing round is not stuck there (`firingRound_fires_inversion`). The reading, the recognition and the pattern step
each eventually succeed: `viewEquation_eventually`, `patternShape_some` with `recognizeConv`, and
`step_solved_eventually`.

The agreement of declared types is a condition: in the cumulative tower a fragment equation can pass `x : U0` where
`F` declares `U1`, and recognition does not read it
(`ContextualDependentPatternFiring.Controls.cumulative_unread`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ExecutableChecking ContextualDependentExecutableJoin ContextualDependentExecutableConversion
open ContextualDependentExecutableChecking ContextualDependentExecutableDiscovery
open ContextualDependentPiSpine ContextualDependentDynamicFragment ContextualDependentScope ContextualDependentGeneralPattern

section General

variable {Head : Type}

theorem appsVar_eq_appSpine {m : Nat} (head : Fin m) :
    ∀ arguments : List (Fin m),
      appsVar (.var head : Tm Head m) arguments = appSpine (.var head) (arguments.reverse.map Tm.var)
  | [] => rfl
  | argument :: rest => by
      rw [List.reverse_cons, List.map_append, List.map_singleton, appSpine_concat, ← appsVar_eq_appSpine head rest]
      rfl

variable {rules : Rules Head}

/-- Opening is invariant under the cast of the number of locals. -/
theorem openCode_cast {n a b : Nat} (code : Tm Head n) (same : a = b) (cast : n + a = n + b) :
    rename (Fin.cast cast) (openCode a code) = openCode b code := by
  subst same
  exact (rename_ext (fun _ => Fin.ext rfl) _).trans (rename_id _)

theorem locals_of_rigid {Γ : Context rules} {type : TypeOver Γ} (scope : Spine type) :
    ∀ indices : List (Fin scope.target.arity), (∀ index ∈ indices, ∃ position, scope.localIndex position = index) →
      ∃ positions : List scope.Local, positions.map scope.localIndex = indices
  | [], _ => ⟨[], rfl⟩
  | index :: rest, locals => by
      obtain ⟨position, located⟩ := locals index List.mem_cons_self
      obtain ⟨positions, read⟩ := locals_of_rigid scope rest fun other member => locals other (List.mem_cons_of_mem _ member)
      exact ⟨position :: positions, by rw [List.map_cons, located, read]⟩

/-- **The inversion row of the census**, read from the store. -/
def InversionRow {Γ : Context rules} {type : TypeOver Γ} (equation : Equation (TotalTerm (extend Γ type))) : Prop :=
  ∀ left right,
    Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) left →
    Normal rules left →
    Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) right →
    Normal rules right →
    ∃ head arguments, readSpine left = some (head, arguments) ∧
      head.val = ContextualDependentPatternSolver.lamDepth equation.1.2.code ∧
      (∀ argument ∈ arguments, argument.val < ContextualDependentPatternSolver.lamDepth equation.1.2.code) ∧
      arguments.Nodup ∧
      (∀ index ∈ right.support,
        ContextualDependentPatternSolver.lamDepth equation.1.2.code < index.val ∨ index ∈ arguments) ∧
      ∀ (scope : Spine equation.1.1) (spine : Spine type)
        (same : scope.length = ContextualDependentPatternSolver.lamDepth equation.1.2.code)
        (args : spine.Local → scope.Local),
        (ContextualDependentPatternSolver.locals spine).map (fun position => scope.localIndex (args position)) =
            arguments.reverse.map (Fin.cast (by rw [scope.target_arity, same])) →
          CtxRen (lifted spine).target.raw scope.target.raw
            (argRen (lifted spine) scope idRen (fun position => args (spine.localReindexEquiv _ position))) ∧
          TypeEq rules scope.target.raw scope.result.code
            (Presentation.rename (fun index => argRen (lifted spine) scope idRen
              (fun position => args (spine.localReindexEquiv _ position))
              (spine.mapRen (projectionHom Γ type) wk index)) spine.result.code)

end General

variable {L : Type} [UniverseLevel.LevelOrder L]
variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative]

local instance settingHeadEqInversion (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.headEq :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).headEq)

local instance settingUniverseInversion (valuation : Nat → L) (head : LevelTower.Head L) :
    Decidable ((TowerModel.setting valuation).R.isUniverse head) :=
  inferInstanceAs (Decidable ((LevelTower.rules L).isUniverse head))

local instance settingCumulativeInversion (valuation : Nat → L) :
    DecidableRel (TowerModel.setting valuation).R.cumulative :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).cumulative)

variable (valuation : Nat → L)

/-- **The newest declaration of a context is read from some budget on** when it is normal. -/
theorem newestOf_stable {Θ : Context (TowerModel.setting valuation).R} (nonempty : 0 < Θ.arity)
    (normal : Normal (LevelTower.rules L) (Ctx.lookup Θ.raw ⟨0, nonempty⟩)) :
    ∃ (fuel : Nat) (view : ContextualDependentWorklist.Newest Θ), ∀ larger, fuel ≤ larger →
      ContextualDependentWorklist.newestOf (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots
        TowerModel.heads TowerModel.algebra declared tc red larger Θ = some view := by
  rcases Θ with ⟨arity, raw, formed⟩
  cases raw with
  | nil => exact absurd nonempty (Nat.lt_irrefl 0)
  | snoc raw code =>
      have codeNormal : Normal (LevelTower.rules L) code := normal_of_rename wk normal
      obtain ⟨fuel, found, stable⟩ := newestOf_eventually valuation formed codeNormal
      obtain ⟨view, computed⟩ := Option.isSome_iff_exists.mp found
      exact ⟨fuel, view, fun larger enough => (stable larger enough).trans computed⟩

variable (rigid : ∀ name, (TowerModel.setting valuation).roles name = .rigid)
  (complete : AlgorithmicComplete (TowerModel.setting valuation).R (TowerModel.setting valuation).roles)
  (normalizes : ∀ {Θ : Context (TowerModel.setting valuation).R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm (LevelTower.Head L) Θ.arity, ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation)
      code ∧ Equal (TowerModel.setting valuation).R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm (LevelTower.Head L) n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) term)))

/-- The conversion pattern rule's search decides a store when it decides one of its equations. -/
theorem searchStoreConv_isSome_of_mem (fuel : Nat) {Γ : Context (TowerModel.setting valuation).R}
    (type : TypeOver Γ) {equation : Equation (TotalTerm (extend Γ type))}
    (fires : ∀ rest, (ContextualDependentRecognitionConversion.tryEquationConv (S := TowerModel.setting valuation)
      TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red rigid complete
      (fun _ => none) normalizes certifyNormal fuel type equation rest).isSome) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)), equation ∈ problem →
      (ContextualDependentRecognitionConversion.searchStoreConv (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red rigid complete (fun _ => none) normalizes
        certifyNormal fuel type problem).isSome
  | [], member => absurd member List.not_mem_nil
  | first :: rest, member => by
      rcases List.mem_cons.mp member with same | later
      · subst same
        obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp (fires rest)
        simp only [ContextualDependentRecognitionConversion.searchStoreConv, computed]
        rfl
      · cases computed : ContextualDependentRecognitionConversion.tryEquationConv (S := TowerModel.setting valuation)
            TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red rigid complete
            (fun _ => none) normalizes certifyNormal fuel type first rest with
        | some found =>
            simp only [ContextualDependentRecognitionConversion.searchStoreConv, computed]
            rfl
        | none =>
            simp only [ContextualDependentRecognitionConversion.searchStoreConv, computed, Option.isSome_map]
            exact searchStoreConv_isSome_of_mem fuel type fires rest later

/-- **Firing of the conversion pattern rule on one equation of the inversion row**, for the newest metavariable
with a normal declaration. -/
theorem tryEquationConv_fires {Γ : Context (TowerModel.setting valuation).R} {type : TypeOver Γ}
    (equation : Equation (TotalTerm (extend Γ type))) (inside : InFragment equation) (row : InversionRow equation)
    (newestNormal : Normal (LevelTower.rules L) type.code) :
    ∃ bound, ∀ larger, bound ≤ larger → ∀ rest,
      (ContextualDependentRecognitionConversion.tryEquationConv (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red rigid complete (fun _ => none) normalizes
        certifyNormal larger type equation rest).isSome := by
  obtain ⟨types, normalAnnotation, deep, leftSide, _⟩ := inside
  obtain ⟨f₁, same, compared⟩ := compareTypes_eventually valuation equation.2.1 equation.1.1 (TypeEq.symm types)
  obtain ⟨f₂, scope, discovered⟩ := discover_eventually valuation
    (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.1 normalAnnotation
    (by rw [← piCount_eq_piDepth]; exact deep)
  have length : scope.length = ContextualDependentPatternSolver.lamDepth equation.1.2.code :=
    ContextualDependentPiSpineDiscovery.discovered_length (S := TowerModel.setting valuation) TowerModel.facts
      TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red f₂ _ equation.1.1 scope (discovered f₂ le_rfl)
  obtain ⟨f₃, leftCode, leftNormal, leftStar, leftStable⟩ :=
    normalizeAt_eventually valuation (scope.openFunction equation.1.2)
  obtain ⟨f₄, rightCode, rightNormal, rightStar, rightStable⟩ :=
    normalizeAt_eventually valuation (scope.openFunction (equation.2.2.convertType equation.1.1 same.down))
  obtain ⟨t₀, viewed⟩ := (ContextualDependentDecisiveFragment.viewEquation_const (S := TowerModel.setting valuation)
    TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red (fun _ => none) red_stable
    equation).spec
  -- The codes of the reading, renamed into the fragment's opening.
  have toScope : (extend Γ type).arity + ContextualDependentPatternSolver.lamDepth equation.1.2.code =
      scope.target.arity := by rw [scope.target_arity, length]
  have castBack : ∀ code : Tm (LevelTower.Head L) ((extend Γ type).arity + scope.length),
      rename (Fin.cast toScope.symm) (rename (Fin.cast scope.target_arity.symm) code) =
        rename (Fin.cast (by rw [length])) code := by
    intro code
    rw [rename_comp]
    exact rename_ext (fun _ => Fin.ext rfl) _
  have castThere : ∀ code : Tm (LevelTower.Head L) scope.target.arity,
      rename (Fin.cast toScope) (rename (Fin.cast toScope.symm) code) = code := by
    intro code
    rw [rename_comp]
    exact (rename_ext (fun _ => Fin.ext rfl) _).trans (rename_id _)
  have respects : ∀ i, outerFlexible scope (Fin.cast toScope i) =
      openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code) i := by
    intro i
    rw [outerFlexible_eq, length]
    rfl
  have injective : Function.Injective (Fin.cast toScope) := Fin.cast_injective _
  rw [openFunction_code] at leftStar rightStar
  have leftOpened : Star (R := LevelTower.rules L)
      (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code)
      (rename (Fin.cast toScope.symm) leftCode) := by
    have moved := star_rename (Fin.cast toScope.symm) leftStar
    rwa [castBack, openCode_cast _ length] at moved
  have rightOpened : Star (R := LevelTower.rules L)
      (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code)
      (rename (Fin.cast toScope.symm) rightCode) := by
    have moved := star_rename (Fin.cast toScope.symm) rightStar
    rwa [castBack, openCode_cast _ length] at moved
  have leftOpenedNormal := (ContextualDependentNormalizing.normal_rename_iff empty_root (Fin.cast toScope.symm)
    leftCode).mpr leftNormal
  have rightOpenedNormal := (ContextualDependentNormalizing.normal_rename_iff empty_root (Fin.cast toScope.symm)
    rightCode).mpr rightNormal
  obtain ⟨head, arguments, readLeft, headValue, argumentsLocal, distinctArguments, rightVariables, agreement⟩ :=
    row _ _ leftOpened leftOpenedNormal rightOpened rightOpenedNormal
  -- The left code of the reading is the newest metavariable applied to locals.
  have leftShape : leftCode = appsVar (.var (Fin.cast toScope head)) (arguments.map (Fin.cast toScope)) := by
    rw [← castThere leftCode, readSpine_spec readLeft, rename_appsVar]
    rfl
  have headOuter : Fin.cast toScope head = scope.outerRen 0 := by
    apply Fin.ext
    rw [outerRen_val, Fin.val_cast, headValue, length]
    simp
  have locals : ∀ index ∈ (arguments.map (Fin.cast toScope)).reverse, ∃ position, scope.localIndex position = index := by
    intro index member
    obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp member)
    apply local_of_rigid scope
    rw [respects]
    exact decide_eq_false (Nat.not_le.mpr (argumentsLocal argument inArguments))
  obtain ⟨positions, positionsRead⟩ := locals_of_rigid scope _ locals
  have leftForm : leftCode = appSpine (.var (scope.outerRen 0))
      (positions.map fun position => .var (scope.localIndex position)) := by
    rw [leftShape, appsVar_eq_appSpine, headOuter, ← positionsRead, List.map_map]
    rfl
  have positionsDistinct : positions.Nodup := by
    have mapped : (positions.map scope.localIndex).Nodup := by
      rw [positionsRead]
      exact List.nodup_reverse.mpr (distinctArguments.map injective)
    exact List.Nodup.of_map _ mapped
  have positionsLength : positions.length = arguments.length := by
    rw [← List.length_map (f := scope.localIndex), positionsRead, List.length_reverse, List.length_map]
  -- The spine of the newest declaration.
  have arity : arguments.length = piDepth type.code := by
    have inFragment := leftSide _ leftOpened leftOpenedNormal
    rw [readSpine_spec readLeft] at inFragment
    have flexibleHead : openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code) head = true :=
      decide_eq_true (by rw [headValue])
    have counted := arities_appsVar_length flexibleHead arguments inFragment.2
    rw [counted]
    unfold metaArity
    rw [dif_pos (by rw [headValue])]
    have index : (⟨head.val - ContextualDependentPatternSolver.lamDepth equation.1.2.code, by
        have := head.isLt; omega⟩ : Fin (extend Γ type).arity) = ⟨0, Nat.succ_pos _⟩ := Fin.ext (by
          simp [headValue])
    rw [index, ← piCount_eq_piDepth]
    exact piCount_rename wk type.code
  obtain ⟨f₅, spine, spineFound⟩ := discover_eventually valuation positions.length type newestNormal
    (by rw [positionsLength, arity])
  have spineLength : spine.length = positions.length :=
    ContextualDependentPiSpineDiscovery.discovered_length (S := TowerModel.setting valuation) TowerModel.facts
      TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red f₅ _ type spine (spineFound f₅ le_rfl)
  -- The reading at a budget from which every part is fixed.
  let reference := max (max (max f₁ f₂) (max f₃ f₄)) (max t₀ f₅)
  let active : Active scope.target :=
    ⟨scope.result,
      (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads (fun _ => none) reference (scope.openFunction equation.1.2)).1,
      (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads (fun _ => none) reference
        (scope.openFunction (equation.2.2.convertType equation.1.1 same.down))).1⟩
  have activeLeft : active.left.code = leftCode := leftStable reference (by omega)
  have activeRight : active.right.code = rightCode := rightStable reference (by omega)
  -- Recognition.
  obtain ⟨shape, shaped, shapeArgs⟩ := patternShape_some spine scope active positions
    (by rw [activeLeft, leftForm]) spineLength.symm positionsDistinct (fun args read => by
      refine (agreement scope spine length args ?_).1
      rw [show (ContextualDependentPatternSolver.locals spine).map (fun position => scope.localIndex (args position)) =
          ((ContextualDependentPatternSolver.locals spine).map args).map scope.localIndex from by
            rw [List.map_map]; rfl,
        read, positionsRead, List.map_reverse])
  have annotation : TypeEq (LevelTower.rules L) scope.target.raw active.type.code
      ((lifted spine).result.reindex shape.pattern.map.hom).code := by
    rw [pattern_type_code]
    refine (agreement scope spine length shape.pattern.args ?_).2
    rw [show (ContextualDependentPatternSolver.locals spine).map
          (fun position => scope.localIndex (shape.pattern.args position)) =
        ((ContextualDependentPatternSolver.locals spine).map shape.pattern.args).map scope.localIndex from
          by rw [List.map_map]; rfl, shapeArgs, positionsRead, List.map_reverse]
  obtain ⟨f₆, sameType, comparedType⟩ := compareTypes_eventually valuation active.type
    ((lifted spine).result.reindex shape.pattern.map.hom) annotation
  have recognizes : ∀ larger, f₆ ≤ larger →
      ContextualDependentRecognitionConversion.recognizeConv (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra red larger spine scope active =
        some ⟨shape.pattern, active.right.convertType _ sameType.down, fun solution =>
          ContextualDependentRecognitionConversion.conv_holds_iff shape sameType.down solution⟩ := by
    intro larger enough
    unfold ContextualDependentRecognitionConversion.recognizeConv
    rw [shaped, Option.bind_some]
    erw [comparedType larger enough]
    rfl
  have readActive : readApplication active.left.code = some (scope.outerRen 0, positions.map scope.localIndex) := by
    rw [activeLeft, leftForm]
    have same' : (positions.map fun position => (Tm.var (scope.localIndex position) : Tm (LevelTower.Head L) _)) =
        (positions.map scope.localIndex).map Tm.var := by rw [List.map_map]; rfl
    rw [same', readApplication_appSpine]
  have inside : ∀ index ∈ (active.right.convertType _ sameType.down).code.support,
      ∃ original, shape.pattern.bodyRen original = index := by
    intro index member
    rw [Term.convertType_code, activeRight, ← castThere rightCode, ContextualDependentSupport.support_rename] at member
    obtain ⟨variable', present, rfl⟩ := Finset.mem_image.mp member
    refine bodyRen_covers shape.pattern shapeArgs ?_
    rcases rightVariables variable' present with outside | inArguments
    · left
      rcases scope.variable_cases (Fin.cast toScope variable') with ⟨outer, hit⟩ | ⟨position, hit⟩
      · have value := congrArg Fin.val hit
        rw [outerRen_val, Fin.val_cast, length] at value
        refine ⟨⟨outer.val - 1, by have := outer.isLt; simp at this ⊢; omega⟩, ?_⟩
        rw [← hit]
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      · have value := congrArg Fin.val hit
        have below := localIndex_val scope position
        rw [Fin.val_cast] at value
        rw [length] at below
        omega
    · right
      have inImage : Fin.cast toScope variable' ∈ positions.map scope.localIndex := by
        rw [positionsRead]
        exact List.mem_reverse.mpr (List.mem_map_of_mem inArguments)
      obtain ⟨position, inPositions, hit⟩ := List.mem_map.mp inImage
      exact ⟨position, inPositions, hit⟩
  have rightNormal' : Normal (LevelTower.rules L) (active.right.convertType _ sameType.down).code := by
    rw [Term.convertType_code, activeRight]
    exact rightNormal
  obtain ⟨f₇, fires⟩ := tryActiveConv_solved_eventually valuation rigid complete normalizes certifyNormal scope active
    equation readActive (fun larger enough => by rw [List.length_map]; exact spineFound larger enough) recognizes
    rightNormal' inside
  refine ⟨max reference f₇, fun larger enough rest => ?_⟩
  unfold ContextualDependentRecognitionConversion.tryEquationConv
  rw [viewed larger (by omega), ← viewed reference (by omega)]
  unfold ContextualDependentPatternSolver.viewEquation
  simp only [Option.bind_eq_bind]
  erw [compared reference (by omega)]
  simp only [Option.bind_some]
  erw [discovered reference (by omega)]
  simp only [Option.bind_some, Option.pure_def]
  split
  · rfl
  · rename_i missing
    obtain ⟨update, smaller, computed⟩ := fires larger (by omega) rest _
    have conflict := computed.symm.trans missing
    cases conflict

/-- **Firing on the inversion row.** When an equation of a store is in the dynamic pattern fragment and in the
inversion row for the newest metavariable, and the newest declaration is normal, the conversion pattern rule decides
the store from some budget on. -/
theorem patternRuleConv_fires {Θ : Context (TowerModel.setting valuation).R} (problem : EquationStore (TotalTerm Θ))
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) (inside : InFragment equation)
    (nonempty : 0 < Θ.arity) (newestNormal : Normal (LevelTower.rules L) (Ctx.lookup Θ.raw ⟨0, nonempty⟩))
    (row : ∀ view : ContextualDependentWorklist.Newest Θ, InversionRow (view.same ▸ equation)) :
    ∃ bound, ∀ larger, bound ≤ larger →
      (ContextualDependentRecognitionConversion.patternRuleConv (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red rigid complete (fun _ => none) normalizes
        certifyNormal larger problem).isSome := by
  obtain ⟨f₀, view, newestStable⟩ := newestOf_stable valuation nonempty newestNormal
  have rowView := row view
  rcases view with ⟨base, type, same⟩
  subst same
  have typeNormal : Normal (LevelTower.rules L) type.code := normal_of_rename wk newestNormal
  obtain ⟨f₁, fires⟩ := tryEquationConv_fires valuation rigid complete normalizes certifyNormal equation inside rowView
    typeNormal
  refine ⟨max f₀ f₁, fun larger enough => ?_⟩
  unfold ContextualDependentRecognitionConversion.patternRuleConv
  rw [newestStable larger (by omega)]
  exact searchStoreConv_isSome_of_mem valuation rigid complete normalizes certifyNormal larger type
    (fires larger (by omega)) problem member

variable (headTypingUnique : ∀ {head first second : LevelTower.Head L},
  (TowerModel.setting valuation).R.headTyping head first → (TowerModel.setting valuation).R.headTyping head second →
    first = second)

/-- **The firing round fires on the inversion row**: from some budget on it is not stuck on a store with an equation
of the dynamic pattern fragment in the inversion row for the newest, normal declaration. -/
theorem firingRound_fires_inversion {Θ : Context (TowerModel.setting valuation).R}
    (problem : EquationStore (TotalTerm Θ)) {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem)
    (inside : InFragment equation) (nonempty : 0 < Θ.arity)
    (newestNormal : Normal (LevelTower.rules L) (Ctx.lookup Θ.raw ⟨0, nonempty⟩))
    (row : ∀ view : ContextualDependentWorklist.Newest Θ, InversionRow (view.same ▸ equation)) :
    ∃ bound, ∀ larger, bound ≤ larger →
      firingRound TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra rigid complete declared tc red
        (fun _ => none) normalizes certifyNormal headTypingUnique
        (ContextualDependentNormalizing.tower_rootComplete valuation) larger problem ≠ .stuck := by
  obtain ⟨bound, fires⟩ := patternRuleConv_fires valuation rigid complete normalizes certifyNormal problem member inside
    nonempty newestNormal row
  exact ⟨bound, fun larger enough => firingRound_not_stuck_of_pattern _ _ _ _ _ _ _ _ _ _ _ _ _ _ larger
    (fires larger enough)⟩

/-- **Firing on the inversion row at the head of a stratified store.** -/
theorem firingRound_fires_inversion_stratified {Θ : Context (TowerModel.setting valuation).R}
    {equation : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (stratified : ContextualDependentClosure.Stratified (TowerModel.setting valuation).levels (equation :: rest))
    (normal : Normal (LevelTower.rules L) equation.1.1.code)
    (depth : ContextualDependentPatternSolver.lamDepth equation.1.2.code ≤ piCount equation.1.1.code)
    (nonempty : 0 < Θ.arity) (newestNormal : Normal (LevelTower.rules L) (Ctx.lookup Θ.raw ⟨0, nonempty⟩))
    (row : ∀ view : ContextualDependentWorklist.Newest Θ, InversionRow (view.same ▸ equation)) :
    ∃ bound, ∀ larger, bound ≤ larger →
      firingRound TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra rigid complete declared tc red
        (fun _ => none) normalizes certifyNormal headTypingUnique
        (ContextualDependentNormalizing.tower_rootComplete valuation) larger (equation :: rest) ≠ .stuck :=
  firingRound_fires_inversion valuation rigid complete normalizes certifyNormal headTypingUnique (equation :: rest)
    List.mem_cons_self (stratified.head_inFragment normal depth) nonempty newestNormal row

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
