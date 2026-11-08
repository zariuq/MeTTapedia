import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentClosure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentInstantiation

/-!
# The stratified fragment under an answer for the newest metavariable

A pattern answer for the newest metavariable `F` of `Γ, F` instantiates the rest of the store along
`F ↦ λ z̄. u` and drops the solved equation. When `u` is normal, with Miller occurrences and the arities of the
older metavariables, and `F` has one Π binder for each `z`, the instantiated store is again stratified
(`stratified_instantiate_newest`):

* **fragment sides**: each opened side, instantiated and normalized, is again in the fragment
  (`ContextualDependentDynamicFragment.instantiated_side_in_fragment`), provided the instantiation keeps the
  number of leading abstractions of the left side;
* **stratified annotations**: a solution of the instantiated equations before an equation is, composed with the
  answer, a solution of the original equations before it, the solved one included; so the annotations stay equal.

Only the newest metavariable is instantiated, so no declaration changes and every arity is read as before. The
condition on leading abstractions is explicit: instantiating a bare `F` on the left of another equation by an
abstraction adds abstractions, and the fragment opens such a side at a different depth.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentStratifiedClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta ContextualDependentClosure

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} (levels : LevelModel rules L)

/-- Every equation of a stratified store has fragment sides. -/
theorem Stratified.sides_of_mem {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (stratified : Stratified levels problem) {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) :
    FragmentSides equation := by
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  exact (stratified before after equation split).1

variable {levels}

/-- **The stratified fragment is closed under an answer for the newest metavariable**, removing the solved
equation, when the answer is a pattern solution and keeps the leading abstractions of every left side. -/
theorem stratified_instantiate_newest (empty : rules.computation = RootComputation.empty) {Γ : Context rules}
    {type : TypeOver Γ} (value : Term Γ type) {arity : Nat} {body : Tm Head (Γ.arity + arity)}
    (valueCode : value.code = lamsVar arity body) (normal : Normal rules body)
    (millerBody : miller (bodyFlexible arity) body = true) (arityOf : piCount type.code = arity)
    (aritiesBody : arities (bodyFlexible arity) (liftArityK arity fun j => piCount (Ctx.lookup Γ.raw j)) body = true)
    {before after : EquationStore (TotalTerm (extend Γ type))} {solved : Equation (TotalTerm (extend Γ type))}
    (stratified : Stratified levels (before ++ solved :: after))
    (solves : ∀ {Δ : Context rules} (τ : Δ ⟶ Γ),
      (frames levels).Solves (τ ≫ Elimination.instantiate Γ value) solved)
    (depths : ∀ equation ∈ before ++ after,
      ContextualDependentPatternSolver.lamDepth
          (subst (Elimination.instantiate Γ value).substitution equation.1.2.code) =
        ContextualDependentPatternSolver.lamDepth equation.1.2.code)
    (normalizes : ∀ equation ∈ before ++ after,
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
          Normal rules opened) ∧
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
          Normal rules opened)) :
    Stratified levels ((frames levels).applyStore (Elimination.instantiate Γ value) (before ++ after)) := by
  intro before' after' later split
  change (before ++ after).map (fun equation => (equation.1.reindex (Elimination.instantiate Γ value),
    equation.2.reindex (Elimination.instantiate Γ value))) = before' ++ later :: after' at split
  obtain ⟨prefix', rest, hsplit, rfl, mapped⟩ := List.map_eq_append_iff.mp split
  obtain ⟨equation, suffix, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
  have member : equation ∈ before ++ after := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have inOriginal : equation ∈ before ++ solved :: after := by
    rcases List.mem_append.mp member with inBefore | inAfter
    · exact List.mem_append_left _ inBefore
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ inAfter)
  have sides := Stratified.sides_of_mem levels stratified inOriginal
  refine ⟨?_, ?_⟩
  · -- fragment sides of the instantiated equation
    unfold FragmentSides
    change (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth
          (subst (Elimination.instantiate Γ value).substitution equation.1.2.code))
          (subst (Elimination.instantiate Γ value).substitution equation.1.2.code)) code → Normal rules code →
        InFragmentCode Γ.raw (ContextualDependentPatternSolver.lamDepth
          (subst (Elimination.instantiate Γ value).substitution equation.1.2.code)) code) ∧
      (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth
          (subst (Elimination.instantiate Γ value).substitution equation.1.2.code))
          (subst (Elimination.instantiate Γ value).substitution equation.2.2.code)) code → Normal rules code →
        InFragmentCode Γ.raw (ContextualDependentPatternSolver.lamDepth
          (subst (Elimination.instantiate Γ value).substitution equation.1.2.code)) code)
    rw [depths equation member]
    exact ⟨instantiated_side_in_fragment empty value valueCode normal millerBody arityOf aritiesBody _ sides.1
        (normalizes equation member).1,
      instantiated_side_in_fragment empty value valueCode normal millerBody arityOf aritiesBody _ sides.2
        (normalizes equation member).2⟩
  · -- stratified annotations
    intro Δ τ solvedPrefix
    have pulled : (frames levels).Models (τ ≫ Elimination.instantiate Γ value) prefix' :=
      (Frames.models_applyStore (X := frames levels) (Elimination.instantiate Γ value) τ prefix').mp solvedPrefix
    have annotations : TypeEq rules Δ.raw
        (subst (τ ≫ Elimination.instantiate Γ value).substitution equation.1.1.code)
        (subst (τ ≫ Elimination.instantiate Γ value).substitution equation.2.1.code) := by
      rcases List.append_eq_append_iff.mp hsplit with ⟨middle, prefixEq, afterEq⟩ | ⟨middle, beforeEq, restEq⟩
      · -- the equation was after the solved one
        have atOriginal : StratifiedAt levels (before ++ solved :: middle) equation :=
          (stratified (before ++ solved :: middle) suffix equation (by
          rw [afterEq]; simp)).2
        refine atOriginal _ ?_
        rw [prefixEq, ContextualDependentClosure.models_append_iff] at pulled
        rw [ContextualDependentClosure.models_append_iff]
        refine ⟨pulled.1, ?_⟩
        intro other inOther
        rcases List.mem_cons.mp inOther with same | inMiddle
        · rw [same]
          exact solves τ
        · exact pulled.2 other inMiddle
      · rcases middle with _ | ⟨first, middle⟩
        · -- the equation is the first one of `after`
          rw [List.nil_append] at restEq
          rw [List.append_nil] at beforeEq
          have atOriginal : StratifiedAt levels (prefix' ++ [solved]) equation :=
            (stratified (prefix' ++ [solved]) suffix equation (by
            rw [beforeEq, ← restEq]; simp)).2
          refine atOriginal _ ?_
          rw [ContextualDependentClosure.models_append_iff]
          refine ⟨pulled, ?_⟩
          intro other inOther
          rw [List.mem_singleton.mp inOther]
          exact solves τ
        · -- the equation was before the solved one
          rw [List.cons_append, List.cons.injEq] at restEq
          obtain ⟨headEq, _⟩ := restEq
          have atOriginal : StratifiedAt levels prefix' equation :=
            (stratified prefix' (middle ++ solved :: after) equation (by
            rw [beforeEq, headEq]; simp)).2
          exact atOriginal _ pulled
    have leftSame : subst τ.substitution (equation.1.reindex (Elimination.instantiate Γ value)).1.code =
        subst (τ ≫ Elimination.instantiate Γ value).substitution equation.1.1.code :=
      (congrArg TypeOver.code (TypeOver.reindex_comp equation.1.1 τ (Elimination.instantiate Γ value))).symm
    have rightSame : subst τ.substitution (equation.2.reindex (Elimination.instantiate Γ value)).1.code =
        subst (τ ≫ Elimination.instantiate Γ value).substitution equation.2.1.code :=
      (congrArg TypeOver.code (TypeOver.reindex_comp equation.2.1 τ (Elimination.instantiate Γ value))).symm
    change TypeEq rules Δ.raw (subst τ.substitution (equation.1.reindex (Elimination.instantiate Γ value)).1.code)
      (subst τ.substitution (equation.2.reindex (Elimination.instantiate Γ value)).1.code)
    rw [leftSame, rightSame]
    exact annotations

end ContextualDependentStratifiedClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
