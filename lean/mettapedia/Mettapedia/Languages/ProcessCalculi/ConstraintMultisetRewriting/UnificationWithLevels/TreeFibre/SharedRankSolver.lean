import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.UnionSolver

/-!
# One solver of the tree's driver for the pieces whose rank counts equations

The solvers of the glb join, of flex–rigid equations with unknowns at codomains, and of glb groups share one rank: the
number of equations (`storeRank`). For pieces that share a rank the piece can be read again at every round.

* **The round** (`sharedRound`): the first of the three pieces whose fragment holds at the current store, and that
  piece's round. Every round of every piece lowers the shared rank.
* **The union of the three fragments is a fragment of this one solver** (`sharedFragment`): a round of the chosen piece
  keeps that piece's fragment, so the store stays in the union; and on the union the chosen round is never stuck.
* **Decided** (`shared_decided`): the tree's own driver with this one solver reaches, from some budget on, a fixed
  outcome, a principal answer or a certified refutation, on every store of the union.

The Miller solver's rank (weight, then equations) and the arrow solver's (unknowns, then size) are pairs that the
equation count does not dominate, so those two pieces join through the combined run of `UnionSolver`, which reads the
piece once.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

section Shared

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
  (declared : DeclaredTypesFormed S.R)
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- **The union of the three pieces whose rank counts equations.** -/
def InShared {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  InGlbJoinFragmentK problem ∨ InFlexCod choices problem ∨ InGlbFragment problem

/-- **The round**: the first piece whose fragment holds at the current store, and its round. -/
noncomputable def sharedRound {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    Round S.levels storeRank problem := by
  classical
  exact if InGlbJoinFragmentK problem then
      glbJoinRoundK facts roots heads algebra rigid complete headsTyped join joinSound glb spec problem
    else if InFlexCod choices problem then
      flexCodRound choices glb spec facts roots heads algebra rigid complete headsTyped declared problem
    else if InGlbFragment problem then
      glbGroupRound facts roots heads algebra rigid complete headsTyped glb spec problem
    else .stuck

/-- **One solver of the tree's driver** for the three pieces. -/
noncomputable def sharedSolver : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := fun problem =>
    sharedRound choices facts roots heads algebra rigid complete headsTyped declared join joinSound glb spec problem

/-- **The rounds keep the union**: the chosen piece's round keeps its own fragment. -/
theorem sharedRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (progressed : sharedRound choices facts roots heads algebra rigid complete headsTyped declared join joinSound glb spec
      problem = .progress update smaller) :
    InShared choices update.remaining := by
  unfold sharedRound at progressed
  split_ifs at progressed with h1 h2 h3
  · exact .inl (glbJoinRoundK_stable facts roots heads algebra rigid complete headsTyped join joinSound glb spec h1
      progressed)
  · exact .inr (.inl (flexCodRound_stable choices glb spec facts roots heads algebra rigid complete headsTyped declared
      h2 progressed))
  · exact .inr (.inr (glbGroupRound_stable facts roots heads algebra rigid complete headsTyped glb spec h3
      progressed))

variable (joinTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)
  (glbTotal : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include joinTotal glbTotal in
/-- **Progress on the union**: the chosen round is never stuck before the store is empty. -/
theorem sharedRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InShared choices problem) (nonempty : problem ≠ []) :
    sharedRound choices facts roots heads algebra rigid complete headsTyped declared join joinSound glb spec problem ≠
      .stuck := by
  unfold sharedRound
  split_ifs with h1 h2 h3
  · exact glbJoinRoundK_ne_stuck facts roots heads algebra rigid complete headsTyped join joinSound glb spec joinTotal
      glbTotal h1 nonempty
  · exact flexCodRound_ne_stuck choices glb spec facts roots heads algebra rigid complete headsTyped declared glbTotal
      h2 nonempty
  · exact glbGroupRound_ne_stuck facts roots heads algebra rigid complete headsTyped glb spec glbTotal h3 nonempty
  · rcases inside with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3

include joinTotal glbTotal in
/-- **The union of the three pieces is a fragment of the one solver.** -/
noncomputable def sharedFragment :
    ContextualDependentWorklist.Fragment
      (sharedSolver choices facts roots heads algebra rigid complete headsTyped declared join joinSound glb spec) where
  holds := InShared choices
  stable := fun _ progressed =>
    sharedRound_stable choices facts roots heads algebra rigid complete headsTyped declared join joinSound glb spec progressed
  decisive := fun inside nonempty =>
    sharedRound_ne_stuck choices facts roots heads algebra rigid complete headsTyped declared join joinSound glb spec joinTotal
      glbTotal inside nonempty

include facts roots heads algebra rigid complete headsTyped declared joinSound spec joinTotal glbTotal in
/-- **Decided by one solver**: on the union of the glb join, flex–rigid equations with codomains and glb groups,
the tree's driver reaches, at some budget and at every larger one, a principal answer or a certified refutation. -/
theorem shared_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InShared choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (sharedSolver choices facts roots heads algebra rigid complete headsTyped declared join joinSound glb spec) original
          larger =
        run (sharedSolver choices facts roots heads algebra rigid complete headsTyped declared join joinSound glb spec)
          original fuel ∧
        ((∃ state finished,
            run (sharedSolver choices facts roots heads algebra rigid complete headsTyped declared join joinSound glb spec)
                original larger = .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (sharedSolver choices facts roots heads algebra rigid complete headsTyped declared join joinSound glb spec)
              original larger = .refuted absent)) :=
  (sharedFragment choices facts roots heads algebra rigid complete headsTyped declared join joinSound glb spec joinTotal
    glbTotal).decided inside

end Shared

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
