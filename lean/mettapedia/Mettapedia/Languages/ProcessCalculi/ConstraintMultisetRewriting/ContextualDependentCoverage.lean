import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentShortClosurePieces

/-!
# The census of the first equation of a stratified Miller store

The classification half of coverage starts from the first equation of a store, which is the one the rounds read.
In the corrected class (`ContextualDependentShortClosure.StratifiedMiller`):

* its two annotations are equal types (`StratifiedMiller.head_typeEq`), since no equation precedes it;
* every pair of normal forms of its opened sides is one of R86's census kinds (`StratifiedMiller.head_kind`): a Miller
  pattern on the left or on the right against any side (flex–flex included), or two rigid sides with equal or with
  distinct spine heads.

This is the shape half only. That each kind meets the hypothesis of the reader that handles it, on the store the
rounds actually read (after preparation and twin collapse), is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentShortClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta ContextualDependentClosure

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **The first equation of a store in the Miller class has equal annotations.** -/
theorem StratifiedMiller.head_typeEq {Θ : Context rules} {equation : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (stratified : StratifiedMiller levels (equation :: rest)) :
    TypeEq rules Θ.raw equation.1.1.code equation.2.1.code := by
  have atHead := (stratified [] rest equation rfl).2 (𝟙 Θ) (fun _ member => absurd member List.not_mem_nil)
  change TypeEq rules Θ.raw (subst ids equation.1.1.code) (subst ids equation.2.1.code) at atHead
  rwa [subst_ids, subst_ids] at atHead

/-- **The first equation of a store in the Miller class is in the census**: every pair of normal forms of its
opened sides is a pattern equation or a rigid–rigid equation with equal or distinct heads. -/
theorem StratifiedMiller.head_kind [DecidableEq Head] {Θ : Context rules} {equation : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (stratified : StratifiedMiller levels (equation :: rest))
    {left right : Tm Head (Θ.arity + ContextualDependentPatternSolver.lamDepth equation.1.2.code)}
    (toLeft : Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.1.2.code) left) (normalLeft : Normal rules left)
    (toRight : Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.2.2.code) right) (normalRight : Normal rules right) :
    Kind (openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code)) left right := by
  have sides := (stratified [] rest equation rfl).1
  exact classification (sides.1 left toLeft normalLeft) (sides.2 right toRight normalRight)

end ContextualDependentShortClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
