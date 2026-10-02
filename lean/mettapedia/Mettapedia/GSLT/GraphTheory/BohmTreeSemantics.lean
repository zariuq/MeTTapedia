import Mettapedia.GSLT.GraphTheory.BohmSearchApproximation
import Mettapedia.GSLT.GraphTheory.BohmObservationControls
import Mettapedia.GSLT.GraphTheory.BetaEtaConfluence

/-!
# Exact Böhm observations and qualified execution

The coherent uncapped observation family defines exact tree equivalence.
Finite evaluators agree eventually at each fixed depth, rather than at the
same arbitrary budget. Exact equivalence contains β-conversion, is closed
under abstraction, preserves solvability and separates identity from its eta
expansion. It is not packaged as a lambda theory: closure under application
is not proved here; graph realization and maximality are not asserted.

The distinction from extensional observational theories follows the taxonomy
of Intrigila, Manzonetto and Polonsky, "Degrees of extensionality in the
theory of Böhm trees and Sallé's conjecture", LMCS 15(1):6 (2019).
-/

namespace Mettapedia.GSLT.GraphTheory

/-- Add one binder to the root node; bottom stays bottom. -/
def BohmTree.abstract : BohmTree → BohmTree
  | .bot => .bot
  | .node numLams head children => .node (numLams + 1) head children

namespace BohmObservation

/-- The exact observation of an abstraction is the exact observation of its
body with one more binder at the root. -/
theorem tree_lam (depth : Nat) (term : LambdaTerm) :
    tree depth (.lam term) = (tree depth term).abstract := by
  classical
  cases depth with
  | zero => rw [tree_zero, tree_zero]; rfl
  | succ depth =>
      by_cases solvable : term.Solvable
      · obtain ⟨hnf, path, head⟩ := solvable
        have headSome := (extractHNF_isSome_eq_isHNF hnf).trans head
        cases headForm : extractHNF hnf with
        | none => simp only [headForm, Option.isSome_none, Bool.false_eq_true] at headSome
        | some value =>
            rcases value with ⟨numLams, headVar, arguments⟩
            have lamPath : (LambdaTerm.lam term) ⇛* (LambdaTerm.lam hnf) :=
              parRedStar_iterate_lam 1 path
            rw [tree_node_of_reaches path headForm depth,
              tree_node_of_reaches lamPath (extractHNF_lam_some headForm) depth]
            rfl
      · rw [(tree_bot_iff depth term).mpr solvable,
          (tree_bot_iff depth (.lam term)).mpr (LambdaTerm.Unsolvable.lam solvable)]
        rfl

/-- Equality of the coherent mathematical trees, independently of search fuel. -/
def Equivalent (first second : LambdaTerm) : Prop := family first = family second

theorem equivalent_iff (first second : LambdaTerm) :
    Equivalent first second ↔ ∀ depth, tree depth first = tree depth second :=
  family_eq_iff first second

theorem equivalent_equivalence : Equivalence Equivalent :=
  ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩

theorem equivalent_of_reduction {term result : LambdaTerm} (path : term ⇛* result) :
    Equivalent term result := family_reduction_eq path

theorem beta_equivalent (body argument : LambdaTerm) :
    Equivalent (.app (.lam body) argument) (argument.subst 0 body) := family_beta_eq _ _

/-- β-convertible terms have the same exact observations. -/
theorem equivalent_of_conversion {first second : LambdaTerm}
    (convertible : Relation.EqvGen ParRed first second) : Equivalent first second :=
  equivalent_equivalence.eqvGen_iff.mp
    (Relation.EqvGen.mono
      (fun _ _ step => equivalent_of_reduction (Relation.ReflTransGen.single step)) _ _
      convertible)

/-- Exact equivalence is closed under abstraction. -/
theorem Equivalent.lam {first second : LambdaTerm} (same : Equivalent first second) :
    Equivalent (.lam first) (.lam second) :=
  (equivalent_iff _ _).mpr fun depth => by
    rw [tree_lam, tree_lam, (equivalent_iff first second).mp same depth]

theorem equivalent_iff_eventual_agreement (first second : LambdaTerm) :
    Equivalent first second ↔ ∀ depth, ∃ threshold, ∀ fuel, threshold ≤ fuel →
      BohmSearch.observe (fun _ => fuel) depth first =
        BohmSearch.observe (fun _ => fuel) depth second :=
  BohmSearch.family_eq_iff_eventual_agreement first second

theorem Equivalent.unsolvable_iff {first second : LambdaTerm} (same : Equivalent first second) :
    first.Unsolvable ↔ second.Unsolvable := by
  rw [← tree_bot_iff 0 first, ← tree_bot_iff 0 second]
  rw [(equivalent_iff first second).mp same 1]

theorem unsolvables_equivalent {first second : LambdaTerm}
    (firstBottom : first.Unsolvable) (secondBottom : second.Unsolvable) :
    Equivalent first second := by
  apply (equivalent_iff first second).mpr
  intro depth
  cases depth with
  | zero =>
      exact ((tree_eq_iff 0 first .bot).mpr (.zero first)).trans
        ((tree_eq_iff 0 second .bot).mpr (.zero second)).symm
  | succ depth =>
      rw [(tree_bot_iff depth first).mpr firstBottom,
        (tree_bot_iff depth second).mpr secondBottom]

/-- Actual head observations distinguish the standard combinators. -/
theorem identity_not_equivalent_constant : ¬Equivalent LambdaTerm.I LambdaTerm.K := by
  intro same
  have head := (equivalent_iff _ _).mp same 1
  have constant : tree 1 LambdaTerm.K = .node 2 1 [] :=
    tree_node_of_reaches (term := LambdaTerm.K) (hnf := LambdaTerm.K)
      (arguments := []) Relation.ReflTransGen.refl rfl 0
  rw [identity_mathematical_observation, constant] at head
  cases head

end BohmObservation

/-- The eta expansion λf.λx.f x is extensionally related to identity. -/
def etaExpandedIdentity : LambdaTerm := .lam (.lam (.app (.var 1) (.var 0)))

theorem etaExpandedIdentity_contracts :
    BetaEta.EtaStep etaExpandedIdentity LambdaTerm.I :=
  BetaEta.EtaStep.lam (BetaEta.EtaStep.eta (.var 0))

/-- Exact trees retain the extra binder and argument; eta conversion is a
different observation contract, even on closed normal forms. -/
theorem identity_not_equivalent_etaExpandedIdentity :
    ¬BohmObservation.Equivalent LambdaTerm.I etaExpandedIdentity := by
  intro same
  have head := (BohmObservation.equivalent_iff _ _).mp same 1
  have expanded : BohmObservation.tree 1 etaExpandedIdentity = .node 2 1 [.bot] := by
    have equation := BohmObservation.tree_node_of_reaches
      (term := etaExpandedIdentity) (hnf := etaExpandedIdentity)
      (arguments := [.var 0]) Relation.ReflTransGen.refl rfl 0
    simpa only [List.map_cons, List.map_nil, BohmObservation.tree_zero] using equation
  rw [identity_mathematical_observation, expanded] at head
  cases head

end Mettapedia.GSLT.GraphTheory
