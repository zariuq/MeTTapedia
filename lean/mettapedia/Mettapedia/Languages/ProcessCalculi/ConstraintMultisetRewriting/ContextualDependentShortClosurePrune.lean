import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentShortClosureClosed

/-!
# The stratified Miller class under pruning and intersection

R76's pruning answer `G := λ z̄. H (z̄ restricted)` (`ContextualDependentPrune.Restriction.answer`) is a pattern answer
in the sense of hereditary substitution (`pruneAnswer`): its value is the abstraction, over `G`'s binders, of the
newest metavariable `H` applied to the kept binders through the restriction's injective binder map. That value is
normal and has Miller occurrences: `H` is a metavariable applied to distinct binders (`pruneValue_miller`). Its code
is read from the spine machinery (`abstractBody_code`, with R107's `openFunction_code`).

So the Miller class is closed under every **pruning update** (`stratifiedMiller_prune`: the whole store instantiated
by the answer), and under the **intersection progress** (`stratifiedMiller_intersect`: prune, then drop the
instantiated intersection equation, certified valid), whatever the other equations of the store are and whether or
not they mention `G`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentShortClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta ContextualDependentClosure ContextualDependentHereditary
open ContextualDependentPiSpine ContextualDependentPrune ContextualDependentGeneralPattern

/-! ## Codes of abstractions over a spine -/

section Codes

variable {Head : Type} {rules : Rules Head}

theorem lam_lamsVar {n : Nat} : ∀ (k : Nat) (c : Tm Head (n + 1 + k)),
    Tm.lam (lamsVar k c) = lamsVar (k + 1) (Presentation.rename (Fin.cast (by omega)) c)
  | 0, c => by
      change Tm.lam c = Tm.lam (Presentation.rename (Fin.cast _) c)
      exact congrArg Tm.lam (((rename_ext (fun _ => Fin.ext rfl) c).trans (rename_id c)).symm)
  | k + 1, c => by
      change Tm.lam (lamsVar k (.lam c)) = lamsVar (k + 1) (.lam (Presentation.rename (Fin.cast _) c))
      rw [lam_lamsVar k (.lam c)]
      change lamsVar (k + 1) (.lam (Presentation.rename (liftRen (Fin.cast _)) c)) = _
      congr 2
      apply rename_ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Fin.ext rfl
      · exact Fin.ext rfl

/-- **The code of an abstraction over a spine**: one abstraction per binder. -/
theorem abstractBody_code : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (body : Term spine.target spine.result),
    (spine.abstractBody body).code =
      lamsVar spine.length (Presentation.rename (Fin.cast spine.target_arity) body.code)
  | _, _, .stop _, body => ((rename_ext (fun _ => Fin.ext rfl) _).trans (rename_id _)).symm
  | _, _, .bind shape rest, body => by
      change Tm.lam (rest.abstractBody body).code = _
      rw [abstractBody_code rest body, lam_lamsVar, rename_comp]
      change lamsVar (rest.length + 1) _ = lamsVar (rest.length + 1) _
      congr 1

/-- The marking of a spine's context: the outer variables flexible, the binders rigid. -/
def spineMark {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) : Fin spine.target.arity → Bool :=
  fun i => decide (spine.length ≤ i.val)

theorem spineMark_outer {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) (prior : Fin Γ.arity) :
    spineMark spine (spine.outerRen prior) = true := by
  simp [spineMark, ContextualDependentPatternFiring.outerRen_val]

theorem spineMark_local {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) (position : spine.Local) :
    spineMark spine (spine.localIndex position) = false := by
  have := ContextualDependentPatternFiring.localIndex_val spine position
  simp only [spineMark, decide_eq_false_iff_not, not_le]
  exact this

/-- **A pattern map respects the markings** when its outer map does: outer variables to outer variables, binders to
binders. -/
theorem argRen_respects {Γ Δ : Context rules} {type : TypeOver Γ} {scopeType : TypeOver Δ}
    (spine : Spine type) (scope : Spine scopeType) (outer : Ren Γ.arity Δ.arity) (args : spine.Local → scope.Local) :
    ∀ i, spineMark scope (argRen spine scope outer args i) = spineMark spine i := by
  intro i
  rcases spine.variable_cases i with ⟨prior, rfl⟩ | ⟨position, rfl⟩
  · rw [argRen_outer, spineMark_outer, spineMark_outer]
  · rw [argRen_local, spineMark_local, spineMark_local]

end Codes

/-! ## The pruning answer is a pattern answer -/

section Answer

variable {Head : Type} {rules : Rules Head} (empty : rules.computation = RootComputation.empty)
include empty

/-- The newest variable opened at `count` fresh locals: a metavariable applied to distinct rigid locals. -/
theorem openNewest_miller {n : Nat} (count : Nat) :
    miller (openedFlexible count) (openCode count (Tm.var (0 : Fin (n + 1)) : Tm Head (n + 1))) = true ∧
      Normal rules (openCode count (Tm.var (0 : Fin (n + 1)) : Tm Head (n + 1))) := by
  rw [openCode_eq_appsFwd]
  have spine : appsFwd (Presentation.rename (wkK count) (Tm.var (0 : Fin (n + 1)) : Tm Head (n + 1)))
      (localsFwd count) = appsVar (.var (wkK count 0)) ((localsFwd count).reverse ++ []) :=
    appsFwd_appsVar (.var (wkK count 0)) (localsFwd count) []
  rw [spine]
  refine ⟨miller_appsVar ?_ _ ?_ ?_, normal_appsVar empty _ _⟩
  · simp [openedFlexible, wkK_val]
  · intro y member
    rw [List.append_nil, List.mem_reverse] at member
    have := localsFwd_lt count y member
    simp only [openedFlexible, decide_eq_false_iff_not, not_le]
    exact this
  · rw [List.append_nil]
    exact List.nodup_reverse.mpr (localsFwd_nodup count)

variable {Γ : Context rules} {type keptType : TypeOver Γ} {spine : Spine type} {kept : Spine keptType}

omit empty in
theorem answer_zero (restriction : Restriction spine kept) :
    restriction.answer.substitution 0 =
      (restriction.restrict (projectionHom Γ keptType) (newest Γ keptType)).code := rfl

/-- **The value of the pruning answer is normal with Miller occurrences**, every free variable read as a
metavariable. -/
theorem pruneValue_miller (restriction : Restriction spine kept) :
    miller (fun _ => true) (restriction.restrict (projectionHom Γ keptType) (newest Γ keptType)).code = true ∧
      Normal rules (restriction.restrict (projectionHom Γ keptType) (newest Γ keptType)).code := by
  let base := projectionHom Γ keptType
  have code : (restriction.restrict base (newest Γ keptType)).code =
      lamsVar (spine.reindex base).length (Presentation.rename (Fin.cast (spine.reindex base).target_arity)
        (Presentation.rename (restriction.ren base) (Presentation.rename
          (Fin.cast (kept.reindex base).target_arity.symm)
          (openCode (kept.reindex base).length (newest Γ keptType).code)))) := by
    rw [Restriction.restrict, abstractBody_code, Restriction.body_code,
      ContextualDependentPatternFiring.openFunction_code]
  rw [code]
  obtain ⟨opened, openedNormal⟩ := openNewest_miller (rules := rules) empty (n := Γ.arity) (kept.reindex base).length
  refine ⟨?_, normal_lamsVar empty _ _ ?_⟩
  · rw [miller_lamsVar]
    have marking : bodyFlexible (o := Γ.arity + 1) (spine.reindex base).length =
        openedFlexible (spine.reindex base).length :=
      funext fun index => bodyFlexible_eq _ index
    rw [marking]
    refine miller_rename _ (Fin.cast_injective _) (flexible := spineMark (spine.reindex base))
      (fun i => by simp [spineMark, openedFlexible]) ?_
    refine miller_rename _ (restriction.ren_injective base) (flexible := spineMark (kept.reindex base))
      (argRen_respects _ _ _ _) ?_
    refine miller_rename _ (Fin.cast_injective _) (flexible := openedFlexible (kept.reindex base).length)
      (fun i => by simp [spineMark, openedFlexible]) ?_
    exact opened
  · rw [ContextualDependentNormalizing.normal_rename_iff empty, ContextualDependentNormalizing.normal_rename_iff empty,
      ContextualDependentNormalizing.normal_rename_iff empty]
    exact openedNormal

/-- **R76's pruning answer is a pattern answer** for the newest metavariable, every other variable fixed. -/
def pruneAnswer (restriction : Restriction spine kept) :
    PatternAnswer rules (bodyFlexible (o := Γ.arity + 1) 0) (bodyFlexible (o := Γ.arity + 1) 0)
      restriction.answer.substitution where
  target := 0
  flexibleTarget := rfl
  rename i _ := i
  injective := fun _ _ _ _ same => same
  respects := fun _ _ => rfl
  others := by
    intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨prior, rfl⟩
    · exact absurd rfl hi
    · rfl
  outerArity := Γ.arity + 1
  outer := idRen
  outerInjective := fun _ _ same => same
  outerFlexible := fun _ => rfl
  value := (restriction.restrict (projectionHom Γ keptType) (newest Γ keptType)).code
  solution := (rename_id _).symm
  valueMiller := (pruneValue_miller empty restriction).1
  valueNormal := (pruneValue_miller empty restriction).2

end Answer

/-! ## Pruning and intersection keep the Miller class -/

section Store

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
variable {Γ : Context rules} {type keptType : TypeOver Γ} {spine : Spine type} {kept : Spine keptType}

/-- **Every pruning update keeps the Miller class**: the whole store is instantiated by `G := λ z̄. H (z̄ restricted)`,
other equations mentioning `G` included. -/
theorem stratifiedMiller_prune (empty : rules.computation = RootComputation.empty)
    (restriction : Restriction spine kept) {problem : EquationStore (TotalTerm (extend Γ type))}
    (stratified : StratifiedMiller levels problem)
    (normalizes : ∀ equation ∈ problem,
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
          Normal rules opened) ∧
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
          Normal rules opened)) :
    StratifiedMiller levels ((frames levels).applyStore restriction.answer problem) :=
  stratifiedMiller_applyStore empty restriction.answer (pruneAnswer empty restriction) stratified normalizes

/-- **The intersection progress keeps the Miller class**: prune the first equation's metavariable to the intersection,
instantiate the whole store, and drop the instantiated first equation, which the answer makes valid. -/
theorem stratifiedMiller_intersect (empty : rules.computation = RootComputation.empty)
    (restriction : Restriction spine kept) {first : Equation (TotalTerm (extend Γ type))}
    {rest : EquationStore (TotalTerm (extend Γ type))} (stratified : StratifiedMiller levels (first :: rest))
    (normalizes : ∀ equation ∈ first :: rest,
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
          Normal rules opened) ∧
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
          Normal rules opened))
    (valid : (frames levels).E (first.1.reindex restriction.answer) (first.2.reindex restriction.answer)) :
    StratifiedMiller levels ((frames levels).applyStore restriction.answer rest) :=
  stratifiedMiller_answer_drop empty restriction.answer (pruneAnswer empty restriction) stratified normalizes
    fun τ => (frames levels).preserves τ valid

end Store

end ContextualDependentShortClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
