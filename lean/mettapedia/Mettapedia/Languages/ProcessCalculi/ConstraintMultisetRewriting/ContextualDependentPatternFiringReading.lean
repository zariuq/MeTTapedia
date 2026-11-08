import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringRigid

/-!
# The rigid out-of-scope refutation, read on the codes of a scoped equation

A scoped equation `λ x̄. l ≐ λ x̄. r` is read under its local telescope as two codes over the metavariables
followed by the locals. When the left code is a metavariable `F` applied to locals and the right code, normal
with Miller occurrences, has in its rigid support a local that is not among those arguments, the equation has
no solution in any future context (`reading_refuted`).

Unlike the general pattern step, the rule reads codes only: `F` need not be the newest metavariable, the
arguments need not be distinct, and no pattern is recognized, so nothing depends on the declared type of `F`.
Every solution is typed-equal to one with normal components. Its instance of `F ȳ` reduces to a normal term
whose variables are those of the instance of `F`, outer ones, and the instances of `ȳ`
(`applied_normalizes_support`); its instance of `r` reduces to a normal term that keeps the local
(`miller_instance`). Equal normal terms have the same support.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentEta ContextualDependentScope
open ContextualDependentDynamicFragment
open ContextualDependentGeneralPattern

section Applied

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid)

local notation "Normal" => ContextualDependentNormalChecking.Normal (S := S)

include rigid in
/-- **A normal term applied to variables reduces to a normal term** whose variables are those of the term and
the arguments. -/
theorem applied_normalizes_support {m : Nat} (function : Tm Head m) (normal : Normal function) :
    ∀ arguments : List (Fin m), ∃ result, Reduces S.R (appsVar function arguments) result ∧ Normal result ∧
      ∀ index ∈ result.support, index ∈ function.support ∨ index ∈ arguments
  | [] => ⟨function, .refl, normal, fun _ member => .inl member⟩
  | argument :: rest => by
      obtain ⟨inner, reduced, innerNormal, bound⟩ := applied_normalizes_support function normal rest
      have toApp : Reduces S.R (appsVar function (argument :: rest)) (.app inner (.var argument)) :=
        reduces_app reduced .refl
      by_cases isLambda : ∃ body, inner = .lam body
      · obtain ⟨body, rfl⟩ := isLambda
        refine ⟨inst0 (.var argument) body, toApp.tail (StepCore.betaPi body (.var argument)), ?_, ?_⟩
        · rw [inst0_var]
          exact ContextualDependentNormalObservations.normal_rename rigid _
            (ContextualDependentNormalObservations.normal_lam innerNormal)
        · intro index member
          rw [inst0_var, ContextualDependentSupport.support_rename] at member
          obtain ⟨source, inBody, mapped⟩ := Finset.mem_image.mp member
          cases source using Fin.cases with
          | zero =>
              simp only [Fin.cases_zero] at mapped
              subst mapped
              exact .inr List.mem_cons_self
          | succ previous =>
              simp only [Fin.cases_succ] at mapped
              subst mapped
              have outer : previous ∈ (Tm.lam body).support := by
                simp only [Tm.support, mem_outerSupport]
                exact inBody
              rcases bound previous outer with found | found
              · exact .inl found
              · exact .inr (List.mem_cons_of_mem _ found)
      · refine ⟨.app inner (.var argument), toApp, ContextualDependentNormalObservations.normal_app rigid innerNormal
          (ContextualDependentNormalObservations.normal_var rigid argument) (fun body same => isLambda ⟨body, same⟩),
          fun index member => ?_⟩
        simp only [Tm.support, Finset.mem_union, Finset.mem_singleton] at member
        rcases member with member | rfl
        · rcases bound index member with found | found
          · exact .inl found
          · exact .inr (List.mem_cons_of_mem _ found)
        · exact .inr List.mem_cons_self

/-- Substituting into a variable spine whose arguments go to variables, with the images read back. -/
theorem subst_apps_images {n m : Nat} (σ : Sub Head n m) (head : Fin n) :
    ∀ arguments : List (Fin n), (∀ argument ∈ arguments, ∃ image, σ argument = .var image) →
      ∃ images : List (Fin m), subst σ (appsVar (.var head) arguments) = appsVar (σ head) images ∧
        ∀ image ∈ images, ∃ argument ∈ arguments, σ argument = .var image
  | [], _ => ⟨[], rfl, fun _ member => absurd member List.not_mem_nil⟩
  | argument :: rest, onVariables => by
      obtain ⟨images, same, back⟩ := subst_apps_images σ head rest
        fun other member => onVariables other (List.mem_cons_of_mem _ member)
      obtain ⟨image, mapped⟩ := onVariables argument List.mem_cons_self
      refine ⟨image :: images, ?_, fun found member => ?_⟩
      · simp only [appsVar, subst]
        rw [same, mapped]
      · rcases List.mem_cons.mp member with rfl | later
        · exact ⟨argument, List.mem_cons_self, mapped⟩
        · obtain ⟨other, inRest, hit⟩ := back found later
          exact ⟨other, List.mem_cons_of_mem _ inRest, hit⟩

end Applied

section Scopes

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)

theorem outer_of_flexible {index : Fin scope.target.arity} (flexible : outerFlexible scope index = true) :
    ∃ outer, scope.outerRen outer = index := by
  cases origin : scope.originEquiv.symm index with
  | inl outer => exact ⟨outer, by rw [← scope.outer_origin, ← origin, Equiv.apply_symm_apply]⟩
  | inr position => simp [outerFlexible, origin] at flexible

theorem local_of_rigid {index : Fin scope.target.arity} (rigidIndex : outerFlexible scope index = false) :
    ∃ position, scope.localIndex position = index := by
  cases origin : scope.originEquiv.symm index with
  | inl outer => simp [outerFlexible, origin] at rigidIndex
  | inr position =>
      exact ⟨position, by unfold Spine.localIndex; rw [← origin, Equiv.apply_symm_apply]⟩

end Scopes

section Refutation

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
variable (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
  ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
    Equal S.R Θ.raw term.code code type.code)

include facts roots heads rigid complete normalizes in
/-- **A rigid out-of-scope local refutes a scoped equation**: the left code is a metavariable applied to
locals, and the right code, normal with Miller occurrences, has in its rigid support a local that is not
among them. -/
theorem reading_refuted {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) {head : Fin scope.target.arity} {arguments : List (Fin scope.target.arity)}
    (read : readSpine active.left.code = some (head, arguments)) (flexibleHead : outerFlexible scope head = true)
    (rigidArguments : ∀ argument ∈ arguments, outerFlexible scope argument = false)
    {outside : Fin scope.target.arity} (occurs : outside ∈ rigidSupport (outerFlexible scope) active.right.code)
    (rigidOutside : outerFlexible scope outside = false) (notArgument : outside ∉ arguments)
    (millerRight : miller (outerFlexible scope) active.right.code = true)
    (normal : ContextualDependentNormalChecking.Normal (S := S) active.right.code)
    {Δ : Context S.R} (solution : Δ ⟶ Γ) : ¬ (scope.toScoped active).Holds solution := by
  intro solved
  obtain ⟨normalSolution, same, componentsNormal⟩ := exists_normal_solution normalizes solution
  have moved := (Scoped.holds_iff_of_same S.levels (scope.toScoped active) solution normalSolution
    (act_equal_of_substEq S.levels same)).mp solved
  rw [Spine.toScoped_holds_iff] at moved
  change Equal S.R (scope.reindex normalSolution).target.raw
      (subst (scope.map normalSolution).substitution active.left.code)
      (subst (scope.map normalSolution).substitution active.right.code)
      (subst (scope.map normalSolution).substitution active.type.code) at moved
  have formed := (scope.reindex normalSolution).target.formed
  have admissible := admissible_map rigid scope normalSolution componentsNormal
  -- The instance of the flexible spine.
  obtain ⟨outer, outerHead⟩ := outer_of_flexible scope flexibleHead
  subst outerHead
  obtain ⟨images, substituted, imagesBack⟩ := subst_apps_images (scope.map normalSolution).substitution
    (scope.outerRen outer) arguments fun argument member => (admissible argument).2 (rigidArguments argument member)
  rw [readSpine_spec read, substituted] at moved
  obtain ⟨leftResult, leftReduced, leftNormal, leftBound⟩ := applied_normalizes_support rigid
    ((scope.map normalSolution).substitution (scope.outerRen outer))
    ((admissible (scope.outerRen outer)).1 flexibleHead) images
  -- The instance of the right side.
  obtain ⟨rightResult, rightReduced, rightNormal, _, keeps⟩ := miller_instance rigid active.right.code
    (outerFlexible scope) (scope.map normalSolution).substitution normal millerRight admissible
  have typedLeft := (Equal.typed (S := S) moved formed).1
  have typedRight := (Equal.typed (S := S) moved formed).2
  have toLeft := (Reduces.preserve facts roots heads formed leftReduced typedLeft).2
  have toRight := (Reduces.preserve facts roots heads formed rightReduced typedRight).2
  have supports := ContextualDependentNormalSupport.equal_support rigid complete formed
    (toLeft.symm.trans (moved.trans toRight)) leftNormal rightNormal
  -- The outside local survives on the right.
  obtain ⟨position, located⟩ := local_of_rigid scope rigidOutside
  subst located
  have member := keeps (scope.localIndex position) (localRead scope normalSolution position (scope.localIndex position))
    occurs (map_localRead scope normalSolution position position)
  rw [← supports] at member
  rcases leftBound _ member with inHead | inImages
  · rw [scope.map_outer, ContextualDependentSupport.support_rename] at inHead
    obtain ⟨source, _, hit⟩ := Finset.mem_image.mp inHead
    rw [localRead_local] at hit
    exact (scope.reindex normalSolution).outer_ne_local source _ hit
  · obtain ⟨argument, inArguments, hit⟩ := imagesBack _ inImages
    obtain ⟨argumentPosition, argumentLocated⟩ := local_of_rigid scope (rigidArguments argument inArguments)
    subst argumentLocated
    rw [map_localRead scope normalSolution argumentPosition argumentPosition] at hit
    have sameIndex := Tm.var.inj hit
    rw [localRead_local, localRead_local] at sameIndex
    have samePosition := (scope.localReindexEquiv normalSolution).symm.injective
      ((scope.reindex normalSolution).localIndex_injective sameIndex)
    exact notArgument (samePosition ▸ inArguments)

variable (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
  Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))

/-- A local of the rigid support of a code outside a list of arguments. -/
def outsideLocal {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (arguments : List (Fin scope.target.arity)) (right : Tm Head scope.target.arity) : Option (Fin scope.target.arity) :=
  (List.finRange _).find? fun index =>
    decide (index ∈ rigidSupport (outerFlexible scope) right) && !outerFlexible scope index && !decide (index ∈ arguments)

omit facts roots heads rigid complete normalizes in
theorem outsideLocal_spec {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    {arguments : List (Fin scope.target.arity)} {right : Tm Head scope.target.arity} {index : Fin scope.target.arity}
    (found : outsideLocal scope arguments right = some index) :
    index ∈ rigidSupport (outerFlexible scope) right ∧ outerFlexible scope index = false ∧ index ∉ arguments := by
  have selected := List.find?_some found
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    at selected
  exact ⟨selected.1.1, selected.1.2, selected.2⟩

/-- **The rigid out-of-scope refutation of a scoped reading**: a metavariable applied to locals on the left, and on
the right a certified normal code with Miller occurrences and a local of its rigid support outside the arguments. -/
def readingRefute {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType) (active : Active scope.target) :
    Option (PLift (∀ {Δ : Context S.R} (solution : Δ ⟶ Γ), ¬ (scope.toScoped active).Holds solution)) :=
  match read : readSpine active.left.code with
  | none => none
  | some (head, arguments) =>
      if shape : outerFlexible scope head = true ∧ arguments.all (fun argument => !outerFlexible scope argument) = true
      then
        match found : outsideLocal scope arguments active.right.code with
        | none => none
        | some _ =>
            match certifyNormal active.right.code with
            | none => none
            | some normal =>
                if millerRight : miller (outerFlexible scope) active.right.code = true then
                  some ⟨fun solution => by
                    obtain ⟨occurs, rigidOutside, notArgument⟩ := outsideLocal_spec scope found
                    have rigidArguments : ∀ argument ∈ arguments, outerFlexible scope argument = false := by
                      intro argument member
                      have each := List.all_eq_true.mp shape.2 argument member
                      simpa using each
                    exact reading_refuted facts roots heads rigid complete normalizes scope active read shape.1
                      rigidArguments occurs rigidOutside notArgument millerRight normal.down solution⟩
                else none
      else none

end Refutation

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
