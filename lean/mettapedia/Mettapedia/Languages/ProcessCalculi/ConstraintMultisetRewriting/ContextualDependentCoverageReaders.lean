import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCoverage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosurePermuted

/-!
# The census in the permuted class

In `StratifiedMiller` the census starts from the first equation of the store (`StratifiedMiller.head_typeEq`,
`StratifiedMiller.head_kind`). In the corrected class (`ContextualDependentMillerClosure.PermutedMiller`) the store's
first equation may be a twin whose annotations differ, so the census starts from the first equation **in the stratified
order**, which may sit anywhere in the store: every nonempty store of the class has an equation with equal annotations
whose pairs of normal forms of opened sides are all census kinds (`PermutedMiller.exists_head`).

R110's readers (`ContextualDependentAcceptance2.last_reads_*`) search the whole prepared store, so they read such an
equation wherever it sits. That each census kind meets its reader's hypothesis on the prepared store is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentMillerClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta ContextualDependentClosure ContextualDependentShortClosure

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **A nonempty store of the permuted class has a census head**: an equation with equal annotations, every pair of
normal forms of whose opened sides is a census kind. -/
theorem PermutedMiller.exists_head [DecidableEq Head] {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller levels problem) (nonempty : problem ≠ []) :
    ∃ equation ∈ problem, TypeEq rules Θ.raw equation.1.1.code equation.2.1.code ∧
      ∀ {left right : Tm Head (Θ.arity + ContextualDependentPatternSolver.lamDepth equation.1.2.code)},
        Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
          equation.1.2.code) left → Normal rules left →
        Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
          equation.2.2.code) right → Normal rules right →
        Kind (openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code)) left right := by
  obtain ⟨ordered, perm, stratified⟩ := permuted
  cases ordered with
  | nil => exact absurd (List.Perm.nil_eq perm).symm nonempty
  | cons equation rest =>
      exact ⟨equation, perm.subset List.mem_cons_self, StratifiedMiller.head_typeEq stratified,
        fun toLeft normalLeft toRight normalRight =>
          StratifiedMiller.head_kind stratified toLeft normalLeft toRight normalRight⟩

end ContextualDependentMillerClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
