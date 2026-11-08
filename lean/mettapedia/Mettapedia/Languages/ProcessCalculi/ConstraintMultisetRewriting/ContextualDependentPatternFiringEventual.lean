import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringOpening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableDiscovery

/-!
# Completeness of the scoped reading, and firing on the rigid out-of-scope row

In the cumulative tower, with the actual normalizer and universe choices:

* **the scoped reading of an equation is complete** (`viewEquation_eventually`): an equation whose two
  annotations are equal types, whose left annotation is normal, and whose left side has at most as many leading
  abstractions as the annotation has leading Π binders, is read under its local telescope from some budget on;
* **the read codes are the fragment's normal forms** (`reading_codes_eventually`): from some budget on, the two
  codes of the reading are the normal forms of the fragment's openings of the two sides, renamed along the cast
  of the context length;
* **the rigid rule fires on its row** (`rigidRule_fires`): when an equation of the store is in the dynamic
  pattern fragment, the normal opening of its left side is a metavariable applied to locals, and the normal
  opening of its right side has in its rigid support a local outside those arguments, the rigid rule refutes the
  store from some budget on, and the firing round is not stuck there (`firingRound_fires`).
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
open ContextualDependentPiSpine ContextualDependentDynamicFragment ContextualDependentScope

variable {L : Type} [UniverseLevel.LevelOrder L]
variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative]

local instance settingHeadEq (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.headEq :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).headEq)

local instance settingUniverse (valuation : Nat → L) (head : LevelTower.Head L) :
    Decidable ((TowerModel.setting valuation).R.isUniverse head) :=
  inferInstanceAs (Decidable ((LevelTower.rules L).isUniverse head))

local instance settingCumulative (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.cumulative :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).cumulative)

variable (valuation : Nat → L)

/-! ## The scoped reading is complete -/

/-- **Completeness of the scoped reading.** -/
theorem viewEquation_eventually {Θ : Context (LevelTower.rules L)} (equation : Equation (TotalTerm Θ))
    (types : TypeEq (LevelTower.rules L) Θ.raw equation.2.1.code equation.1.1.code)
    (normal : Normal (LevelTower.rules L) equation.1.1.code)
    (deep : ContextualDependentPatternSolver.lamDepth equation.1.2.code ≤ piDepth equation.1.1.code) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      (ContextualDependentPatternSolver.viewEquation (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red (fun _ => none) larger equation).isSome := by
  obtain ⟨f₁, same, compared⟩ := compareTypes_eventually valuation equation.2.1 equation.1.1 types
  obtain ⟨f₂, spine, discovered⟩ := discover_eventually valuation
    (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.1 normal deep
  refine ⟨max f₁ f₂, fun larger enough => ?_⟩
  unfold ContextualDependentPatternSolver.viewEquation
  simp only [Option.bind_eq_bind]
  erw [compared larger (le_of_max_le_left enough)]
  simp only [Option.bind_some]
  erw [discovered larger (le_of_max_le_right enough)]
  rfl

/-! ## The read codes are normal forms -/

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
/-- A successful bounded normalization of a side returns the normalizer's result for its code. -/
theorem reduceTerm_code (fuel : Nat) {Γ : Context (TowerModel.setting valuation).R} (original : TotalTerm Γ)
    {reduced : ContextualDependentNormalization.Normalized (S := TowerModel.setting valuation) (fun _ => none) original}
    (computed : ContextualDependentNormalization.reduceTerm (S := TowerModel.setting valuation) (fun _ => none)
      TowerModel.facts TowerModel.roots TowerModel.heads fuel original = some reduced)
    {value : ExecutableReduction.Result (TowerModel.setting valuation).R original.2.code}
    (valueRun : ExecutableReduction.normalize (TowerModel.setting valuation).R (fun _ => none) fuel original.2.code =
      some value) :
    reduced.value.2.code = value.val := by
  unfold ContextualDependentNormalization.reduceTerm at computed
  split at computed
  · cases computed
  · split at computed
    · cases computed
    · rename_i _ _ found foundRun
      cases computed
      exact congrArg Subtype.val (Option.some.inj (foundRun.symm.trans valueRun))

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
/-- **Bounded normalization of a side eventually returns its normal form**, and keeps it. -/
theorem normalizeAt_eventually {C : Context (LevelTower.rules L)} {type : TypeOver C} (term : Term C type) :
    ∃ fuel result, Normal (LevelTower.rules L) result ∧ Star (R := LevelTower.rules L) term.code result ∧
      ∀ larger, fuel ≤ larger →
        (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation) TowerModel.facts
          TowerModel.roots TowerModel.heads (fun _ => none) larger term).1.code = result := by
  obtain ⟨f₁, annotation, _, _, typeStable⟩ := red_eventually_type C.formed type.isType
  obtain ⟨f₂, value, normalValue, toValue, valueStable⟩ := red_eventually C.formed term.typed
  refine ⟨max f₁ f₂, value.val, normalValue, toValue, fun larger enough => ?_⟩
  have typeRun := typeStable larger (le_of_max_le_left enough)
  have valueRun := valueStable larger (le_of_max_le_right enough)
  have success : (ContextualDependentNormalization.reduceTerm (S := TowerModel.setting valuation) (fun _ => none)
      TowerModel.facts TowerModel.roots TowerModel.heads larger ⟨type, term⟩).isSome = true :=
    (ContextualDependentNormalization.reduceTerm_success_iff _ _ _ _ larger _).mpr
      ⟨by change (red larger type.code).isSome = true; rw [typeRun]; rfl,
        by change (red larger term.code).isSome = true; rw [valueRun]; rfl⟩
  obtain ⟨reduced, computed⟩ := Option.isSome_iff_exists.mp success
  have atTerm : ContextualDependentNormalization.termAt (S := TowerModel.setting valuation) (fun _ => none)
      TowerModel.facts TowerModel.roots TowerModel.heads larger ⟨type, term⟩ = reduced.value := by
    unfold ContextualDependentNormalization.termAt
    rw [computed]
  change (ContextualDependentNormalization.termAt (S := TowerModel.setting valuation) (fun _ => none)
      TowerModel.facts TowerModel.roots TowerModel.heads larger ⟨type, term⟩).2.code = value.val
  rw [atTerm]
  exact reduceTerm_code valuation larger ⟨type, term⟩ computed valueRun

/-! ## The rigid out-of-scope row -/

omit [UniverseLevel.LevelOrder L] [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem piCount_eq_piDepth {n : Nat} : ∀ code : Tm (LevelTower.Head L) n, piCount code = piDepth code
  | .pi _ body => by simp only [piCount, piDepth, piCount_eq_piDepth body]
  | .var _ | .const _ | .head _ | .sigma _ _ | .id _ _ _ | .lam _ | .app _ _ | .pair _ _ | .fst _ | .snd _
  | .refl _ => rfl

omit [UniverseLevel.LevelOrder L] [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
variable {Head : Type} in
/-- **The rigid out-of-scope row of the census**, read from the store: the normal opening of the left side is a
metavariable applied to locals, and the normal opening of the right side has, in its rigid support, a local
outside those arguments. -/
def RigidOutside {rules : Rules Head} {Θ : Context rules} (equation : Equation (TotalTerm Θ)) : Prop :=
  ∀ left right,
    Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) left →
    Normal rules left →
    Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) right →
    Normal rules right →
    ∃ head arguments outside, readSpine left = some (head, arguments) ∧
      openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code) head = true ∧
      (∀ argument ∈ arguments,
        openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code) argument = false) ∧
      outside ∈ rigidSupport (openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code)) right ∧
      openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code) outside = false ∧
      outside ∉ arguments

omit [UniverseLevel.LevelOrder L] [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
variable {Head : Type} in
/-- **The row read on normal sides**: when both sides are normal, the row is a condition on their syntactic
openings, by confluence. -/
theorem rigidOutside_of_normal {rules : Rules Head} (empty : rules.computation = RootComputation.empty)
    {Θ : Context rules} {equation : Equation (TotalTerm Θ)}
    (leftNormal : Normal rules equation.1.2.code) (rightNormal : Normal rules equation.2.2.code)
    {head : Fin (Θ.arity + ContextualDependentPatternSolver.lamDepth equation.1.2.code)}
    {arguments : List (Fin (Θ.arity + ContextualDependentPatternSolver.lamDepth equation.1.2.code))}
    {outside : Fin (Θ.arity + ContextualDependentPatternSolver.lamDepth equation.1.2.code)}
    (read : readSpine (ContextualDependentCensus.openNormal (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.1.2.code) = some (head, arguments))
    (flexibleHead : openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code) head = true)
    (rigidArguments : ∀ argument ∈ arguments,
      openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code) argument = false)
    (occurs : outside ∈ rigidSupport (openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code))
      (ContextualDependentCensus.openNormal (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
        equation.2.2.code))
    (rigidOutside : openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code) outside = false)
    (notArgument : outside ∉ arguments) : RigidOutside equation := by
  intro left right toLeft normalLeft toRight normalRight
  rw [normal_reduct_unique empty (ContextualDependentCensus.openCode_star _ _)
    (ContextualDependentCensus.openNormal_normal empty leftNormal _) toLeft normalLeft]
  rw [normal_reduct_unique empty (ContextualDependentCensus.openCode_star _ _)
    (ContextualDependentCensus.openNormal_normal empty rightNormal _) toRight normalRight]
  exact ⟨head, arguments, outside, read, flexibleHead, rigidArguments, occurs, rigidOutside, notArgument⟩

variable (rigid : ∀ name, (TowerModel.setting valuation).roles name = .rigid)
  (complete : AlgorithmicComplete (TowerModel.setting valuation).R (TowerModel.setting valuation).roles)
  (normalizes : ∀ {Θ : Context (TowerModel.setting valuation).R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm (LevelTower.Head L) Θ.arity, ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation)
      code ∧ Equal (TowerModel.setting valuation).R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm (LevelTower.Head L) n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) term)))

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
/-- **The decision reads every reading of its row.** -/
theorem readingRefute_isSome {Γ : Context (TowerModel.setting valuation).R} {scopeType : TypeOver Γ}
    (scope : Spine scopeType) (active : Active scope.target)
    {head : Fin scope.target.arity} {arguments : List (Fin scope.target.arity)}
    (read : readSpine active.left.code = some (head, arguments))
    (flexibleHead : ContextualDependentGeneralPattern.outerFlexible scope head = true)
    (rigidArguments : ∀ argument ∈ arguments, ContextualDependentGeneralPattern.outerFlexible scope argument = false)
    {outside : Fin scope.target.arity}
    (occurs : outside ∈ rigidSupport (ContextualDependentGeneralPattern.outerFlexible scope) active.right.code)
    (rigidOutside : ContextualDependentGeneralPattern.outerFlexible scope outside = false)
    (notArgument : outside ∉ arguments) (certified : (certifyNormal active.right.code).isSome)
    (millerRight : miller (ContextualDependentGeneralPattern.outerFlexible scope) active.right.code = true) :
    (readingRefute TowerModel.facts TowerModel.roots TowerModel.heads rigid complete normalizes certifyNormal scope
      active).isSome := by
  unfold readingRefute
  split
  · rename_i missing
    rw [read] at missing
    cases missing
  · rename_i head' arguments' read'
    rw [read] at read'
    cases read'
    rw [dif_pos ⟨flexibleHead, List.all_eq_true.mpr fun argument member => by simp [rigidArguments argument member]⟩]
    split
    · rename_i missing
      have found : (outsideLocal scope arguments active.right.code).isSome :=
        List.find?_isSome.mpr ⟨outside, List.mem_finRange _, by simp [occurs, rigidOutside, notArgument]⟩
      rw [missing] at found
      cases found
    · split
      · rename_i missing
        have absent : certifyNormal active.right.code = none := missing
        rw [absent] at certified
        cases certified
      · rw [dif_pos millerRight]
        rfl

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem refuteReading_isSome {Θ : Context (TowerModel.setting valuation).R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) (reading : Reading (S := TowerModel.setting valuation) equation)
    (read : (readingRefute TowerModel.facts TowerModel.roots TowerModel.heads rigid complete normalizes certifyNormal
      reading.1 reading.2.1).isSome) :
    (refuteReading TowerModel.facts TowerModel.roots TowerModel.heads rigid complete normalizes certifyNormal equation
      rest (some reading)).isSome := by
  obtain ⟨scope, active, view⟩ := reading
  unfold refuteReading
  dsimp only
  split
  · rfl
  · rename_i missing
    have present : (readingRefute TowerModel.facts TowerModel.roots TowerModel.heads rigid complete normalizes
        certifyNormal scope active).isSome = true := read
    have gone : (readingRefute TowerModel.facts TowerModel.roots TowerModel.heads rigid complete normalizes
        certifyNormal scope active) = none := missing
    rw [gone] at present
    cases present

/-- The rigid rule refutes a store when it refutes one of its equations. -/
theorem rigidRule_isSome_of_mem (fuel : Nat) {Θ : Context (TowerModel.setting valuation).R}
    {equation : Equation (TotalTerm Θ)}
    (fires : ∀ rest, (tryEquationCode TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra rigid complete
      declared tc red (fun _ => none) normalizes certifyNormal fuel equation rest).isSome) :
    ∀ problem : EquationStore (TotalTerm Θ), equation ∈ problem →
      (rigidRule TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra rigid complete declared tc red
        (fun _ => none) normalizes certifyNormal fuel problem).isSome
  | [], member => absurd member List.not_mem_nil
  | first :: rest, member => by
      simp only [rigidRule, Option.isSome_or, Bool.or_eq_true]
      rcases List.mem_cons.mp member with same | later
      · subst same
        exact .inl (fires rest)
      · right
        simp only [Option.isSome_map]
        exact rigidRule_isSome_of_mem fuel fires rest later

/-- **Firing on the rigid out-of-scope row.** When an equation of a store is in the dynamic pattern fragment and in
the rigid out-of-scope row, the rigid rule refutes the store from some budget on. -/
theorem rigidRule_fires {Θ : Context (TowerModel.setting valuation).R} (problem : EquationStore (TotalTerm Θ))
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem)
    (inside : InFragment equation) (row : RigidOutside equation)
    (certifies : ∀ {n : Nat} (term : Tm (LevelTower.Head L) n), Normal (LevelTower.rules L) term →
      (certifyNormal term).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger →
      (rigidRule TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra rigid complete declared tc red
        (fun _ => none) normalizes certifyNormal larger problem).isSome := by
  obtain ⟨types, normalAnnotation, deep, _, rightSide⟩ := inside
  obtain ⟨f₁, same, compared⟩ := compareTypes_eventually valuation equation.2.1 equation.1.1 (TypeEq.symm types)
  obtain ⟨f₂, spine, discovered⟩ := discover_eventually valuation
    (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.1 normalAnnotation
    (by rw [← piCount_eq_piDepth]; exact deep)
  have length : spine.length = ContextualDependentPatternSolver.lamDepth equation.1.2.code :=
    ContextualDependentPiSpineDiscovery.discovered_length (S := TowerModel.setting valuation) TowerModel.facts
      TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red f₂ _ equation.1.1 spine (discovered f₂ le_rfl)
  obtain ⟨f₃, leftCode, leftNormal, leftStar, leftStable⟩ :=
    normalizeAt_eventually valuation (spine.openFunction equation.1.2)
  obtain ⟨f₄, rightCode, rightNormal, rightStar, rightStable⟩ :=
    normalizeAt_eventually valuation (spine.openFunction (equation.2.2.convertType equation.1.1 same.down))
  -- The codes of the reading are the renamed normal forms of the fragment's openings.
  have castBack : ∀ code : Tm (LevelTower.Head L) (Θ.arity + spine.length),
      rename (Fin.cast spine.target_arity) (rename (Fin.cast spine.target_arity.symm) code) = code := by
    intro code
    rw [rename_comp]
    exact (rename_ext (fun _ => Fin.ext rfl) _).trans (rename_id _)
  have castThere : ∀ code : Tm (LevelTower.Head L) spine.target.arity,
      rename (Fin.cast spine.target_arity.symm) (rename (Fin.cast spine.target_arity) code) = code := by
    intro code
    rw [rename_comp]
    exact (rename_ext (fun _ => Fin.ext rfl) _).trans (rename_id _)
  have respects : ∀ i, ContextualDependentGeneralPattern.outerFlexible spine (Fin.cast spine.target_arity.symm i) =
      openedFlexible spine.length i := outerFlexible_cast spine
  have injective : Function.Injective (Fin.cast spine.target_arity.symm) := Fin.cast_injective _
  rw [openFunction_code] at leftStar rightStar
  have leftOpened : Star (R := LevelTower.rules L) (openCode spine.length equation.1.2.code)
      (rename (Fin.cast spine.target_arity) leftCode) := by
    have moved := star_rename (Fin.cast spine.target_arity) leftStar
    rwa [castBack] at moved
  have rightOpened : Star (R := LevelTower.rules L) (openCode spine.length equation.2.2.code)
      (rename (Fin.cast spine.target_arity) rightCode) := by
    have moved := star_rename (Fin.cast spine.target_arity) rightStar
    rwa [castBack] at moved
  have leftOpenedNormal := (ContextualDependentNormalizing.normal_rename_iff empty_root (Fin.cast spine.target_arity)
    leftCode).mpr leftNormal
  have rightOpenedNormal := (ContextualDependentNormalizing.normal_rename_iff empty_root
    (Fin.cast spine.target_arity) rightCode).mpr rightNormal
  have row' := row
  unfold RigidOutside at row'
  rw [← length] at row' rightSide
  obtain ⟨head, arguments, outside, readLeft, flexibleHead, rigidArguments, occurs, rigidOutside, notArgument⟩ :=
    row' _ _ leftOpened leftOpenedNormal rightOpened rightOpenedNormal
  have millerRight := (rightSide _ rightOpened rightOpenedNormal).1
  -- Back in the telescope of the reading.
  have readScope : readSpine leftCode =
      some (Fin.cast spine.target_arity.symm head, arguments.map (Fin.cast spine.target_arity.symm)) := by
    rw [← castThere leftCode, readSpine_rename, readLeft]
    rfl
  have occursScope : Fin.cast spine.target_arity.symm outside ∈
      rigidSupport (ContextualDependentGeneralPattern.outerFlexible spine) rightCode := by
    rw [← castThere rightCode]
    exact rigidSupport_rename _ respects occurs
  have millerScope : miller (ContextualDependentGeneralPattern.outerFlexible spine) rightCode = true := by
    rw [← castThere rightCode]
    exact miller_rename _ injective respects millerRight
  refine ⟨max (max f₁ f₂) (max f₃ f₄), fun larger enough => ?_⟩
  have e₁ : f₁ ≤ larger := by omega
  have e₂ : f₂ ≤ larger := by omega
  have e₃ : f₃ ≤ larger := by omega
  have e₄ : f₄ ≤ larger := by omega
  refine rigidRule_isSome_of_mem valuation rigid complete normalizes certifyNormal larger (fun rest => ?_) problem member
  unfold tryEquationCode ContextualDependentPatternSolver.viewEquation
  simp only [Option.bind_eq_bind]
  erw [compared larger e₁]
  simp only [Option.bind_some]
  erw [discovered larger e₂]
  refine refuteReading_isSome valuation rigid complete normalizes certifyNormal equation rest _ ?_
  refine readingRefute_isSome valuation rigid complete normalizes certifyNormal spine _
    (head := Fin.cast spine.target_arity.symm head) (arguments := arguments.map (Fin.cast spine.target_arity.symm))
    (outside := Fin.cast spine.target_arity.symm outside) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · change readSpine (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation) TowerModel.facts
      TowerModel.roots TowerModel.heads (fun _ => none) larger (spine.openFunction equation.1.2)).1.code = _
    rw [leftStable larger e₃]
    exact readScope
  · rw [respects]
    exact flexibleHead
  · intro argument inArguments
    obtain ⟨source, inSource, rfl⟩ := List.mem_map.mp inArguments
    rw [respects]
    exact rigidArguments source inSource
  · change Fin.cast spine.target_arity.symm outside ∈ rigidSupport _
      (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads (fun _ => none) larger
        (spine.openFunction (equation.2.2.convertType equation.1.1 same.down))).1.code
    rw [rightStable larger e₄]
    exact occursScope
  · rw [respects]
    exact rigidOutside
  · intro inArguments
    obtain ⟨source, inSource, hit⟩ := List.mem_map.mp inArguments
    exact notArgument (injective hit ▸ inSource)
  · change (certifyNormal (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation)
      TowerModel.facts TowerModel.roots TowerModel.heads (fun _ => none) larger
      (spine.openFunction (equation.2.2.convertType equation.1.1 same.down))).1.code).isSome = true
    rw [rightStable larger e₄]
    exact certifies rightCode rightNormal
  · change miller _ (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation) TowerModel.facts
      TowerModel.roots TowerModel.heads (fun _ => none) larger
      (spine.openFunction (equation.2.2.convertType equation.1.1 same.down))).1.code = true
    rw [rightStable larger e₄]
    exact millerScope

omit [UniverseLevel.LevelOrder L] [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
variable {Head : Type} in
/-- **The rigid out-of-scope row, with the metavariable on the right**: the normal opening of the right side is a
metavariable applied to locals, and the normal opening of the left side has, in its rigid support, a local outside
those arguments. -/
def RigidOutsideRight {rules : Rules Head} {Θ : Context rules} (equation : Equation (TotalTerm Θ)) : Prop :=
  ∀ left right,
    Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) left →
    Normal rules left →
    Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) right →
    Normal rules right →
    ∃ head arguments outside, readSpine right = some (head, arguments) ∧
      openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code) head = true ∧
      (∀ argument ∈ arguments,
        openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code) argument = false) ∧
      outside ∈ rigidSupport (openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code)) left ∧
      openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code) outside = false ∧
      outside ∉ arguments

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem refuteReading_isSome_swap {Θ : Context (TowerModel.setting valuation).R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) (reading : Reading (S := TowerModel.setting valuation) equation)
    (read : (readingRefute TowerModel.facts TowerModel.roots TowerModel.heads rigid complete normalizes certifyNormal
      reading.1 ⟨reading.2.1.type, reading.2.1.right, reading.2.1.left⟩).isSome) :
    (refuteReading TowerModel.facts TowerModel.roots TowerModel.heads rigid complete normalizes certifyNormal equation
      rest (some reading)).isSome := by
  obtain ⟨scope, active, view⟩ := reading
  unfold refuteReading
  dsimp only
  split
  · rfl
  · simp only [Option.isSome_map]
    exact read

/-- **Firing on the rigid out-of-scope row, with the metavariable on the right.** -/
theorem rigidRule_fires_right {Θ : Context (TowerModel.setting valuation).R} (problem : EquationStore (TotalTerm Θ))
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem)
    (inside : InFragment equation) (row : RigidOutsideRight equation)
    (certifies : ∀ {n : Nat} (term : Tm (LevelTower.Head L) n), Normal (LevelTower.rules L) term →
      (certifyNormal term).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger →
      (rigidRule TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra rigid complete declared tc red
        (fun _ => none) normalizes certifyNormal larger problem).isSome := by
  obtain ⟨types, normalAnnotation, deep, leftSide, _⟩ := inside
  obtain ⟨f₁, same, compared⟩ := compareTypes_eventually valuation equation.2.1 equation.1.1 (TypeEq.symm types)
  obtain ⟨f₂, spine, discovered⟩ := discover_eventually valuation
    (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.1 normalAnnotation
    (by rw [← piCount_eq_piDepth]; exact deep)
  have length : spine.length = ContextualDependentPatternSolver.lamDepth equation.1.2.code :=
    ContextualDependentPiSpineDiscovery.discovered_length (S := TowerModel.setting valuation) TowerModel.facts
      TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red f₂ _ equation.1.1 spine (discovered f₂ le_rfl)
  obtain ⟨f₃, leftCode, leftNormal, leftStar, leftStable⟩ :=
    normalizeAt_eventually valuation (spine.openFunction equation.1.2)
  obtain ⟨f₄, rightCode, rightNormal, rightStar, rightStable⟩ :=
    normalizeAt_eventually valuation (spine.openFunction (equation.2.2.convertType equation.1.1 same.down))
  have castBack : ∀ code : Tm (LevelTower.Head L) (Θ.arity + spine.length),
      rename (Fin.cast spine.target_arity) (rename (Fin.cast spine.target_arity.symm) code) = code := by
    intro code
    rw [rename_comp]
    exact (rename_ext (fun _ => Fin.ext rfl) _).trans (rename_id _)
  have castThere : ∀ code : Tm (LevelTower.Head L) spine.target.arity,
      rename (Fin.cast spine.target_arity.symm) (rename (Fin.cast spine.target_arity) code) = code := by
    intro code
    rw [rename_comp]
    exact (rename_ext (fun _ => Fin.ext rfl) _).trans (rename_id _)
  have respects : ∀ i, ContextualDependentGeneralPattern.outerFlexible spine (Fin.cast spine.target_arity.symm i) =
      openedFlexible spine.length i := outerFlexible_cast spine
  have injective : Function.Injective (Fin.cast spine.target_arity.symm) := Fin.cast_injective _
  rw [openFunction_code] at leftStar rightStar
  have leftOpened : Star (R := LevelTower.rules L) (openCode spine.length equation.1.2.code)
      (rename (Fin.cast spine.target_arity) leftCode) := by
    have moved := star_rename (Fin.cast spine.target_arity) leftStar
    rwa [castBack] at moved
  have rightOpened : Star (R := LevelTower.rules L) (openCode spine.length equation.2.2.code)
      (rename (Fin.cast spine.target_arity) rightCode) := by
    have moved := star_rename (Fin.cast spine.target_arity) rightStar
    rwa [castBack] at moved
  have leftOpenedNormal := (ContextualDependentNormalizing.normal_rename_iff empty_root (Fin.cast spine.target_arity)
    leftCode).mpr leftNormal
  have rightOpenedNormal := (ContextualDependentNormalizing.normal_rename_iff empty_root
    (Fin.cast spine.target_arity) rightCode).mpr rightNormal
  have row' := row
  unfold RigidOutsideRight at row'
  rw [← length] at row' leftSide
  obtain ⟨head, arguments, outside, readRight, flexibleHead, rigidArguments, occurs, rigidOutside, notArgument⟩ :=
    row' _ _ leftOpened leftOpenedNormal rightOpened rightOpenedNormal
  have millerLeft := (leftSide _ leftOpened leftOpenedNormal).1
  have readScope : readSpine rightCode =
      some (Fin.cast spine.target_arity.symm head, arguments.map (Fin.cast spine.target_arity.symm)) := by
    rw [← castThere rightCode, readSpine_rename, readRight]
    rfl
  have occursScope : Fin.cast spine.target_arity.symm outside ∈
      rigidSupport (ContextualDependentGeneralPattern.outerFlexible spine) leftCode := by
    rw [← castThere leftCode]
    exact rigidSupport_rename _ respects occurs
  have millerScope : miller (ContextualDependentGeneralPattern.outerFlexible spine) leftCode = true := by
    rw [← castThere leftCode]
    exact miller_rename _ injective respects millerLeft
  refine ⟨max (max f₁ f₂) (max f₃ f₄), fun larger enough => ?_⟩
  have e₁ : f₁ ≤ larger := by omega
  have e₂ : f₂ ≤ larger := by omega
  have e₃ : f₃ ≤ larger := by omega
  have e₄ : f₄ ≤ larger := by omega
  refine rigidRule_isSome_of_mem valuation rigid complete normalizes certifyNormal larger (fun rest => ?_) problem member
  unfold tryEquationCode ContextualDependentPatternSolver.viewEquation
  simp only [Option.bind_eq_bind]
  erw [compared larger e₁]
  simp only [Option.bind_some]
  erw [discovered larger e₂]
  refine refuteReading_isSome_swap valuation rigid complete normalizes certifyNormal equation rest _ ?_
  refine readingRefute_isSome valuation rigid complete normalizes certifyNormal spine _
    (head := Fin.cast spine.target_arity.symm head) (arguments := arguments.map (Fin.cast spine.target_arity.symm))
    (outside := Fin.cast spine.target_arity.symm outside) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · change readSpine (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation) TowerModel.facts
      TowerModel.roots TowerModel.heads (fun _ => none) larger
      (spine.openFunction (equation.2.2.convertType equation.1.1 same.down))).1.code = _
    rw [rightStable larger e₄]
    exact readScope
  · rw [respects]
    exact flexibleHead
  · intro argument inArguments
    obtain ⟨source, inSource, rfl⟩ := List.mem_map.mp inArguments
    rw [respects]
    exact rigidArguments source inSource
  · change Fin.cast spine.target_arity.symm outside ∈ rigidSupport _
      (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads (fun _ => none) larger (spine.openFunction equation.1.2)).1.code
    rw [leftStable larger e₃]
    exact occursScope
  · rw [respects]
    exact rigidOutside
  · intro inArguments
    obtain ⟨source, inSource, hit⟩ := List.mem_map.mp inArguments
    exact notArgument (injective hit ▸ inSource)
  · change (certifyNormal (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation)
      TowerModel.facts TowerModel.roots TowerModel.heads (fun _ => none) larger
      (spine.openFunction equation.1.2)).1.code).isSome = true
    rw [leftStable larger e₃]
    exact certifies leftCode leftNormal
  · change miller _ (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation) TowerModel.facts
      TowerModel.roots TowerModel.heads (fun _ => none) larger (spine.openFunction equation.1.2)).1.code = true
    rw [leftStable larger e₃]
    exact millerScope

variable (headTypingUnique : ∀ {head first second : LevelTower.Head L},
  (TowerModel.setting valuation).R.headTyping head first → (TowerModel.setting valuation).R.headTyping head second →
    first = second)

/-- **The firing round fires on the rigid out-of-scope row**, in either orientation: from some budget on it is not
stuck on a store with an equation of the dynamic pattern fragment in that row. -/
theorem firingRound_fires {Θ : Context (TowerModel.setting valuation).R} (problem : EquationStore (TotalTerm Θ))
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem)
    (inside : InFragment equation) (row : RigidOutside equation ∨ RigidOutsideRight equation)
    (certifies : ∀ {n : Nat} (term : Tm (LevelTower.Head L) n), Normal (LevelTower.rules L) term →
      (certifyNormal term).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger →
      firingRound TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra rigid complete declared tc red
        (fun _ => none) normalizes certifyNormal headTypingUnique
        (ContextualDependentNormalizing.tower_rootComplete valuation) larger problem ≠ .stuck := by
  obtain ⟨bound, fires⟩ := row.elim
    (fun left => rigidRule_fires valuation rigid complete normalizes certifyNormal problem member inside left certifies)
    (fun right => rigidRule_fires_right valuation rigid complete normalizes certifyNormal problem member inside right
      certifies)
  exact ⟨bound, fun larger enough => firingRound_not_stuck_of_rigid _ _ _ _ _ _ _ _ _ _ _ _ _ _ larger
    (fires larger enough)⟩

/-- **Firing at the head of a stratified store**: when the first equation of a stratified store has a normal
annotation with a Π binder for every abstraction of its left side, and lies in the rigid out-of-scope row, the
firing round is not stuck from some budget on. -/
theorem firingRound_fires_stratified {Θ : Context (TowerModel.setting valuation).R}
    {equation : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (stratified : ContextualDependentClosure.Stratified (TowerModel.setting valuation).levels (equation :: rest))
    (normal : Normal (LevelTower.rules L) equation.1.1.code)
    (depth : ContextualDependentPatternSolver.lamDepth equation.1.2.code ≤ piCount equation.1.1.code)
    (row : RigidOutside equation ∨ RigidOutsideRight equation)
    (certifies : ∀ {n : Nat} (term : Tm (LevelTower.Head L) n), Normal (LevelTower.rules L) term →
      (certifyNormal term).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger →
      firingRound TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra rigid complete declared tc red
        (fun _ => none) normalizes certifyNormal headTypingUnique
        (ContextualDependentNormalizing.tower_rootComplete valuation) larger (equation :: rest) ≠ .stuck :=
  firingRound_fires valuation rigid complete normalizes certifyNormal headTypingUnique (equation :: rest)
    List.mem_cons_self (stratified.head_inFragment normal depth) row certifies

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
