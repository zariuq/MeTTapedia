import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.UnionSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerRunInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroupsInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrowsInitial

/-!
# Initial solutions on the union of the decided fragments

Every piece of the union has its initiality theorem: Miller patterns with the glb round (`millerGlb_initial`), glb
groups (`glbGroup_initial`), the glb join (`glbJoin_initial`), flex–rigid stores with codomains (`flexCod_initial`) and
equations between arrow codes with codomains (`arrowsCod_initial`). Together (`union_initial`): **every solvable store
of the union, over a telescope of universe families, has an initial solution**, the trimmed answer of its piece's
solver.
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

section Union

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Miller.Inhabitants S.R)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
  (declared : DeclaredTypesFormed S.R)
  (strengthening : ContextualDependentIntersectionGeneral.EqualStrengthening S.R)
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
  (joinTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)
  (glbTotal : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening joinSound spec
  joinTotal glbTotal in
/-- **Every solvable store of the union of the decided fragments, over a telescope of universe families, has an
initial solution.** -/
theorem union_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : ∃ k, InPiece choices k original) (families : Miller.Families Θ)
    (solvable : (frames S.levels).Solvable original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer := by
  obtain ⟨k, inPiece⟩ := inside
  cases k with
  | miller =>
      rcases Miller.millerGlb_initial facts roots heads algebra rigid complete normalizes inh headsTyped glb spec
          glbTotal inPiece with found | absent
      · exact found
      · exact absurd solvable absent
  | arrows =>
      exact arrowsCod_initial choices glb spec facts roots heads algebra rigid complete headsTyped declared
        strengthening inh glbTotal inPiece families solvable
  | flexRigid =>
      exact flexCod_initial choices glb spec facts roots heads algebra rigid complete headsTyped declared inh glbTotal
        inPiece families solvable
  | glbGroups =>
      exact glbGroup_initial facts roots heads algebra rigid complete headsTyped glb spec inPiece inh families glbTotal
  | glbJoin =>
      exact glbJoin_initial facts roots heads algebra rigid complete headsTyped join joinSound glb spec inh joinTotal
        glbTotal inPiece

end Union

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
