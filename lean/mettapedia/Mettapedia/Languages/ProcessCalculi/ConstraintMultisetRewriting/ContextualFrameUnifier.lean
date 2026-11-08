import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFamilies
import Mettapedia.OSLF.Syntax.ContextualFamilyComposition

/-!
# Principal unifiers between contextual declaration frames

A solver answer may replace declarations and introduce fresh helpers.
Soundness and factorization are stated on the original frame, with images in
any subsequent declaration family. Sequential solving maps the residual
equations explicitly; it does not discard their contexts or sides.

Equations still use the existing binding terms. This file introduces no proof
syntax, evaluator, or assumption that every problem has a principal answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUnifier

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W X Y : Type}
  {source : V → MetaArity S} {middle : W → MetaArity S}
  {target : X → MetaArity S} {next : Y → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

def Models (assignment : Assignment source middle)
    (problem : EquationStore (Term (signature S source) Γ sort)) : Prop :=
  ∀ equation ∈ problem, instantiate assignment equation.1 = instantiate assignment equation.2

/-- Contextual solvability permits the fresh helper declarations that a
principal solution may require. An endomorphic solution is a special case. -/
def Solvable (problem : EquationStore (Term (signature S source) Γ sort)) : Prop :=
  ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment source future),
    Models candidate problem

theorem solvable_of_model {problem : EquationStore (Term (signature S source) Γ sort)}
    {candidate : Assignment source middle} (model : Models candidate problem) : Solvable problem :=
  ⟨_, middle, candidate, model⟩

def mapProblem (assignment : Assignment source middle)
    (problem : EquationStore (Term (signature S source) Γ sort)) :
    EquationStore (Term (signature S middle) Γ sort) :=
  problem.map fun equation => (instantiate assignment equation.1, instantiate assignment equation.2)

theorem models_append (assignment : Assignment source middle)
    (first second : EquationStore (Term (signature S source) Γ sort)) :
    Models assignment (first ++ second) ↔ Models assignment first ∧ Models assignment second := by
  simp only [Models, List.forall_mem_append]

theorem models_compose {first : Assignment source middle}
    {problem : EquationStore (Term (signature S source) Γ sort)}
    (solved : Models first problem) (second : Assignment middle target) :
    Models (Assignment.compose second first) problem := by
  intro equation member
  simpa only [Assignment.instantiate_compose] using congrArg (instantiate second) (solved equation member)

/-- A model in the original declaration frame is also a future-frame model. -/
theorem solvable_of_consistent {problem : EquationStore (Term (signature S source) Γ sort)}
    (consistent : (ContextualFamilies.action source Γ sort).Consistent problem) : Solvable problem := by
  obtain ⟨candidate, model⟩ := consistent
  exact solvable_of_model model

/-- Ground terms for every sort collapse any future model back into the
original frame. This condition belongs to the one-frame comparison, not to
general contextual admission. -/
theorem solvable_iff_consistent
    (ground : ∀ result, Term (signature S source) [] result)
    (problem : EquationStore (Term (signature S source) Γ sort)) :
    Solvable problem ↔ (ContextualFamilies.action source Γ sort).Consistent problem := by
  constructor
  · rintro ⟨Future, future, candidate, model⟩
    let close : Assignment future source := fun name =>
      rename (S := signature S source) (Γ := []) (Δ := (future name).1) (fun _ impossible => nomatch impossible) (ground (future name).2)
    exact ⟨Assignment.compose close candidate, models_compose model close⟩
  · exact solvable_of_consistent

theorem models_mapProblem (first : Assignment source middle) (second : Assignment middle target)
    (problem : EquationStore (Term (signature S source) Γ sort)) :
    Models second (mapProblem first problem) ↔ Models (Assignment.compose second first) problem := by
  constructor
  · intro solved equation member
    simpa only [Assignment.instantiate_compose] using
      solved _ (List.mem_map.mpr ⟨equation, member, rfl⟩)
  · intro solved equation member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    simpa only [Assignment.instantiate_compose] using solved original present

theorem factor_terms (candidate : Assignment source target) (answer : Assignment source middle)
    (residual : Assignment middle target)
    (components : ∀ identity, candidate identity = instantiate residual (answer identity))
    {context : Ctx S} {result : S.Srt} (term : Term (signature S source) context result) :
    instantiate candidate term = instantiate residual (instantiate answer term) := by
  rw [instantiate_comp]
  exact congrArg (fun assignment => instantiate assignment term) (funext components)

structure Principal (problem : EquationStore (Term (signature S source) Γ sort))
    (answer : Assignment source middle) : Prop where
  sound : Models answer problem
  factors : ∀ {Variables : Type} (declaration : Variables → MetaArity S)
    (candidate : Assignment source declaration), Models candidate problem →
      ∃ residual : Assignment middle declaration,
        ∀ identity, candidate identity = instantiate residual (answer identity)

/-- The second solver sees the actual residual new equations. Factorization
is pointwise at every original declaration, including those outside the
conclusion's vocabulary. -/
theorem Principal.compose {old extra : EquationStore (Term (signature S source) Γ sort)}
    {first : Assignment source middle} {second : Assignment middle target}
    (oldPrincipal : Principal old first)
    (residualPrincipal : Principal (mapProblem first extra) second) :
    Principal (old ++ extra) (Assignment.compose second first) := by
  constructor
  · exact (models_append _ _ _).mpr
      ⟨models_compose oldPrincipal.sound second,
        (models_mapProblem first second extra).mp residualPrincipal.sound⟩
  · intro Variables declaration candidate solved
    obtain ⟨oldSolved, extraSolved⟩ := (models_append _ _ _).mp solved
    obtain ⟨throughFirst, firstComponents⟩ := oldPrincipal.factors declaration candidate oldSolved
    have residualSolved : Models throughFirst (mapProblem first extra) := by
      intro equation member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact (factor_terms candidate first throughFirst firstComponents original.1).symm.trans
        ((extraSolved original present).trans (factor_terms candidate first throughFirst firstComponents original.2))
    obtain ⟨throughSecond, secondComponents⟩ :=
      residualPrincipal.factors declaration throughFirst residualSolved
    refine ⟨throughSecond, ?_⟩
    intro identity
    calc
      candidate identity = instantiate throughFirst (first identity) := firstComponents identity
      _ = instantiate throughSecond (instantiate second (first identity)) :=
        factor_terms throughFirst second throughSecond secondComponents (first identity)
      _ = instantiate throughSecond (Assignment.compose second first identity) := rfl

/-- A principal answer presents exactly the original solutions in every
subsequent declaration family, including the original caller variables. -/
theorem Principal.models_iff_factors
    {problem : EquationStore (Term (signature S source) Γ sort)}
    {answer : Assignment source middle} (principal : Principal problem answer)
    (candidate : Assignment source target) :
    Models candidate problem ↔ ∃ residual : Assignment middle target,
      ∀ identity, candidate identity = instantiate residual (answer identity) := by
  constructor
  · exact principal.factors target candidate
  · rintro ⟨residual, components⟩ equation member
    exact (factor_terms candidate answer residual components equation.1).trans
      ((congrArg (instantiate residual) (principal.sound equation member)).trans
        (factor_terms candidate answer residual components equation.2).symm)

/-- Reordering equations does not change principality. This concerns the
equation problem, not the order at which an interaction observes its guards. -/
theorem Principal.of_perm
    {first second : EquationStore (Term (signature S source) Γ sort)}
    {answer : Assignment source middle} (principal : Principal first answer)
    (permutation : first.Perm second) : Principal second answer := by
  refine ⟨fun equation member => principal.sound equation (permutation.mem_iff.mpr member), ?_⟩
  intro Future future candidate model
  exact principal.factors future candidate
    (fun equation member => model equation (permutation.mem_iff.mp member))

/-- Two principal answers can use different helper declarations. Each
factors through the other on all original terms; an isomorphism of their
entire private declaration families is neither assumed nor concluded. -/
theorem Principal.mutual_factorization
    {problem : EquationStore (Term (signature S source) Γ sort)}
    {left : Assignment source middle} {right : Assignment source target}
    (leftPrincipal : Principal problem left) (rightPrincipal : Principal problem right) :
    ∃ toRight : Assignment middle target, ∃ toLeft : Assignment target middle,
      (∀ {context : Ctx S} {result : S.Srt} (term : Term (signature S source) context result),
        instantiate toRight (instantiate left term) = instantiate right term) ∧
      (∀ {context : Ctx S} {result : S.Srt} (term : Term (signature S source) context result),
        instantiate toLeft (instantiate right term) = instantiate left term) := by
  obtain ⟨toRight, rightComponents⟩ := leftPrincipal.factors target right rightPrincipal.sound
  obtain ⟨toLeft, leftComponents⟩ := rightPrincipal.factors middle left leftPrincipal.sound
  exact ⟨toRight, toLeft,
    fun term => (factor_terms right left toRight rightComponents term).symm,
    fun term => (factor_terms left right toLeft leftComponents term).symm⟩

/-- Sequential principal solving in either order preserves the complete
original interface. The second solve in each order receives the actual
residual equations. No claim that every problem has a principal answer is
made, and this does not commute effectful publication or guard admission. -/
theorem Principal.solve_orders
    {Other Result : Type} {other : Other → MetaArity S} {result : Result → MetaArity S}
    {first second : EquationStore (Term (signature S source) Γ sort)}
    {leftFirst : Assignment source middle} {leftSecond : Assignment middle target}
    {rightFirst : Assignment source other} {rightSecond : Assignment other result}
    (lf : Principal first leftFirst)
    (ls : Principal (mapProblem leftFirst second) leftSecond)
    (rf : Principal second rightFirst)
    (rs : Principal (mapProblem rightFirst first) rightSecond) :
    ∃ toRight : Assignment target result, ∃ toLeft : Assignment result target,
      (∀ {context : Ctx S} {sort : S.Srt} (term : Term (signature S source) context sort),
        instantiate toRight (instantiate (Assignment.compose leftSecond leftFirst) term) =
          instantiate (Assignment.compose rightSecond rightFirst) term) ∧
      (∀ {context : Ctx S} {sort : S.Srt} (term : Term (signature S source) context sort),
        instantiate toLeft (instantiate (Assignment.compose rightSecond rightFirst) term) =
          instantiate (Assignment.compose leftSecond leftFirst) term) :=
  (lf.compose ls).mutual_factorization ((rf.compose rs).of_perm (List.perm_append_comm))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUnifier
