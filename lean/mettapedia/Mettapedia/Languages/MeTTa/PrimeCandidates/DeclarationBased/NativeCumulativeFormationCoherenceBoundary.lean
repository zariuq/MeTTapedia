import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeRelatorCompatibility
import Mettapedia.TypeTheory.TarskiCumulativeCodeCoherenceBoundary

/-!
# A native cumulative formation diamond and its semantic code obstruction

In the actual refined judgment, the open dependent type `Pi x : A, B x`
can be formed and then raised, or formed after raising both premises. The
context retains the arbitrary family variable `B : Pi x : A, U_l`. Both
constructions have the same raw term and the same upper displayed universe.

A strict code interpretation of proof-carrying native terms identifies those
two admitted terms. If its formation and cumulativity clauses are the supplied
enclosing-tower operations, their two code routes must therefore agree. The
existing tag-adapted operator refutes that agreement while retaining all its
dependent closure and decoding equivalences.

This is an obstruction for the explicitly stated interpretation equations,
not native unsoundness or a native definition of a semantic tag test. No
global interpretation, unbounded host existence, quotient policy, or identity
principle is asserted or selected. The enclosing operator is independently
supplied throughout; the obstruction is not a construction of that operator.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeCumulativeFormationCoherenceBoundary

open Presentation Presentation.Declaration
open Presentation.FormationSensitive (Typing Judgment ContextFormation)
open OpaqueRelatorExtension (rules)
open Mettapedia.TypeTheory
open UniverseClosureProfiles TarskiUniverseCapabilities
open TarskiCumulativeCodeCoherenceBoundary

universe u

/-! ## Two actual refined derivations at the same displayed universe -/

/-- The family variable has its full dependent function type. -/
def context (level : LevelExpr) : Tower.Ctx 2 :=
  .snoc (.snoc .nil (sortTm level)) (.pi (.var 0) (sortTm level))

/-- In the body scope, index 1 is the family and index 0 its argument. -/
def dependentPi : Tower.Tm 2 := .pi (.var 1) (.app (.var 1) (.var 0))

def lowerLevel (level : LevelExpr) : LevelExpr := .max level level

def upperLevel (level : LevelExpr) : LevelExpr := .max (.succ level) (.succ level)

variable (signature : Signature Tower.Head) (level : LevelExpr)

theorem context_formed : ContextFormation (rules signature) (context level) := by
  apply ContextFormation.snoc (u := Tower.Head.sort (.max level (.succ level)))
  · exact .snoc .nil (.headType (.sort level)) (.sort (.succ level))
  · exact .piForm (.var 0) (.sort level) (.headType (.sort level))
      (.sort (.succ level)) (.sorts level (.succ level))
  · exact .sort _

theorem family_application_formed :
    Typing (rules signature) (.snoc (context level) (.var 1))
      (.app (.var 1) (.var 0)) (sortTm level) := by
  have familyTyped : Typing (rules signature) (.snoc (context level) (.var 1))
      (.var 1) (.pi (.var 2) (sortTm level)) := .var 1
  have argumentTyped : Typing (rules signature) (.snoc (context level) (.var 1))
      (.var 0) (.var 2) := .var 0
  simpa only [sortTm, inst0, subst] using Typing.appElim familyTyped argumentTyped

theorem lower_formation :
    Judgment (rules signature) (context level) dependentPi (sortTm (lowerLevel level)) :=
  ⟨context_formed signature level,
    .piForm (.var 1) (.sort level) (family_application_formed signature level)
      (.sort level) (.sorts level level)⟩

/-- First use native Pi formation at the lower premises, then the native
cumulativity rule. Neither formation nor the cumulative edge is assumed. -/
theorem form_then_lift :
    Judgment (rules signature) (context level) dependentPi (sortTm (upperLevel level)) := by
  refine ⟨context_formed signature level, .cumul (lower_formation signature level).typing ?_⟩
  intro valuation
  simp only [lowerLevel, upperLevel, LevelExpr.eval, Nat.max_self]
  exact Nat.le_succ _

/-- Raise the domain and the full dependent codomain formation separately,
then apply the same native Pi constructor at their actual joined level. -/
theorem lift_then_form :
    Judgment (rules signature) (context level) dependentPi (sortTm (upperLevel level)) := by
  have raisedDomain : Typing (rules signature) (context level) (.var 1)
      (sortTm (.succ level)) := by
    refine .cumul (.var 1) ?_
    intro valuation
    exact Nat.le_succ _
  have raisedCodomain : Typing (rules signature) (.snoc (context level) (.var 1))
      (.app (.var 1) (.var 0)) (sortTm (.succ level)) := by
    refine .cumul (family_application_formed signature level) ?_
    intro valuation
    exact Nat.le_succ _
  exact ⟨context_formed signature level,
    .piForm raisedDomain (.sort (.succ level)) raisedCodomain (.sort (.succ level))
      (.sorts (.succ level) (.succ level))⟩

/-- The first construction as an actual proof-carrying admitted native code. -/
def formedByLift :
    { term : Tower.Tm 2 //
      Judgment (rules signature) (context level) term (sortTm (upperLevel level)) } :=
  ⟨dependentPi, form_then_lift signature level⟩

/-- The second construction has the same carrier, scope, and displayed type. -/
def formedByUpper :
    { term : Tower.Tm 2 //
      Judgment (rules signature) (context level) term (sortTm (upperLevel level)) } :=
  ⟨dependentPi, lift_then_form signature level⟩

/-- The existing refined judgment lives in Prop. These proof-carrying native
terms retain no separate formation-route identity. -/
theorem native_routes_equal : formedByLift signature level = formedByUpper signature level :=
  Subtype.ext rfl

/-- The diamond uses the actual mixed HOL/List/J/relator/wire rule package;
it does not require changing any declaration or choosing an opaque model. -/
theorem common_formations :
    Judgment HOLNativeRelatorCompatibility.rules (context level)
        dependentPi (sortTm (lowerLevel level)) ∧
      Judgment HOLNativeRelatorCompatibility.rules (context level)
        dependentPi (sortTm (upperLevel level)) :=
  ⟨lower_formation HOLNativeRelatorCompatibility.signature level,
    form_then_lift HOLNativeRelatorCompatibility.signature level⟩

/-- The actual formation is available after any refined typed substitution
into any formed ambient context; the existing capture-avoiding syntax is used. -/
theorem formation_substitute {n : Nat} {target : Tower.Ctx n}
    {substitution : Sub Tower.Head 2 n}
    (formed : ContextFormation (rules signature) target)
    (typed : FormationSensitive.CtxMor (rules signature) (context level) target substitution) :
    Judgment (rules signature) target (subst substitution dependentPi)
      (sortTm (upperLevel level)) :=
  (form_then_lift signature level).substitute formed typed

/-! ## Matching the semantic route indices to actual native levels -/

@[simp] theorem eval_lowerLevel (valuation : Nat → Nat) :
    LevelExpr.eval valuation (lowerLevel level) = LevelExpr.eval valuation level := by
  simp [lowerLevel, LevelExpr.eval]

@[simp] theorem eval_upperLevel (valuation : Nat → Nat) :
    LevelExpr.eval valuation (upperLevel level) = LevelExpr.eval valuation level + 1 := by
  simp [upperLevel, LevelExpr.eval]

/-- The common upper display is genuinely higher under every native level
valuation, not a relabeling of the lower formation level. -/
theorem evaluated_level_strict (valuation : Nat → Nat) :
    LevelExpr.eval valuation (lowerLevel level) < LevelExpr.eval valuation (upperLevel level) := by
  rw [eval_lowerLevel, eval_upperLevel]
  exact Nat.lt_succ_self _

/-- The source genuinely applies its dependent-family variable to the bound
argument; it is not a constant codomain substituted for the native family. -/
theorem dependentPi_not_constant_codomain :
    dependentPi ≠ (.pi (.var 1) (.var 1) : Tower.Tm 2) := by decide

/-! ## Independent code operations and their required agreement -/

variable (operator : SmallFamilyEnclosingUniverseOperator.{u})
variable (A : Type u) (B : A → Type u) (valuation : Nat → Nat)

/-- At a fixed semantic valuation of the native context's two fields,
strict interpretation forces the supplied cumulative and Pi equations to
agree. The equations specify each independent operation, not their equality. -/
theorem strict_equations_force_code_coherence
    (domain : (FamilyEnclosingUniverseTower.family operator A B).Code
      (LevelExpr.eval valuation level))
    (codomain : (FamilyEnclosingUniverseTower.family operator A B).El
        (LevelExpr.eval valuation level) domain →
      (FamilyEnclosingUniverseTower.family operator A B).Code
        (LevelExpr.eval valuation level))
    (interpret :
      { term : Tower.Tm 2 //
        Judgment (rules signature) (context level) term (sortTm (upperLevel level)) } →
      (FamilyEnclosingUniverseTower.family operator A B).Code
        (LevelExpr.eval valuation level + 1))
    (cumulativeEquation : interpret (formedByLift signature level) =
      Routes.liftedPi operator A B (LevelExpr.eval valuation level) domain codomain)
    (formationEquation : interpret (formedByUpper signature level) =
      (Routes.upperPi operator A B (LevelExpr.eval valuation level)).code domain codomain) :
    Routes.liftedPi operator A B (LevelExpr.eval valuation level) domain codomain =
      (Routes.upperPi operator A B (LevelExpr.eval valuation level)).code domain codomain :=
  cumulativeEquation.symm.trans
    ((congrArg interpret (native_routes_equal signature level)).trans formationEquation)

/-- Decoded dependent function spaces agree without assuming or obtaining
the code equality demanded by a strict interpretation. -/
def decoded_routes_agree
    (domain : (FamilyEnclosingUniverseTower.family operator A B).Code
      (LevelExpr.eval valuation level))
    (codomain : (FamilyEnclosingUniverseTower.family operator A B).El
        (LevelExpr.eval valuation level) domain →
      (FamilyEnclosingUniverseTower.family operator A B).Code
        (LevelExpr.eval valuation level)) :
    (FamilyEnclosingUniverseTower.family operator A B).El
        (LevelExpr.eval valuation level + 1)
        (Routes.liftedPi operator A B (LevelExpr.eval valuation level) domain codomain) ≃
      (FamilyEnclosingUniverseTower.family operator A B).El
        (LevelExpr.eval valuation level + 1)
        ((Routes.upperPi operator A B (LevelExpr.eval valuation level)).code domain codomain) :=
  Routes.piAgreement operator A B (LevelExpr.eval valuation level) domain codomain

/-- For the existing full-interface tag adapter, no function on actual
admitted native codes satisfies both supplied interpretation equations.
The domain and entire dependent codomain are arbitrary. -/
theorem tagged_route_equations_incompatible
    (domain : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code
      (LevelExpr.eval valuation level))
    (codomain : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).El
        (LevelExpr.eval valuation level) domain →
      (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code
        (LevelExpr.eval valuation level)) :
    ¬ ∃ interpret :
        { term : Tower.Tm 2 //
          Judgment (rules signature) (context level) term (sortTm (upperLevel level)) } →
        (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code
          (LevelExpr.eval valuation level + 1),
      interpret (formedByLift signature level) =
          Routes.liftedPi (tagOperator operator) A B (LevelExpr.eval valuation level)
            domain codomain ∧
        interpret (formedByUpper signature level) =
          (Routes.upperPi (tagOperator operator) A B (LevelExpr.eval valuation level)).code
            domain codomain := by
  rintro ⟨interpret, cumulativeEquation, formationEquation⟩
  exact TarskiCumulativeCodeCoherenceBoundary.pi_routes_ne operator A B
    (LevelExpr.eval valuation level) domain codomain
    (strict_equations_force_code_coherence signature level (tagOperator operator) A B valuation
      domain codomain interpret cumulativeEquation formationEquation)

/-- The actual shared native judgment is inhabited on both displays and
the semantic dependent products are equivalent, yet the supplied tagged
formation equations have no strict meaning on those native codes. -/
theorem common_native_boundary
    (domain : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code
      (LevelExpr.eval valuation level))
    (codomain : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).El
        (LevelExpr.eval valuation level) domain →
      (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code
        (LevelExpr.eval valuation level)) :
    let family := FamilyEnclosingUniverseTower.family (tagOperator operator) A B
    let lowerCode := Routes.liftedPi (tagOperator operator) A B
      (LevelExpr.eval valuation level) domain codomain
    let upperCode := (Routes.upperPi (tagOperator operator) A B
      (LevelExpr.eval valuation level)).code domain codomain
    Judgment HOLNativeRelatorCompatibility.rules (context level)
        dependentPi (sortTm (lowerLevel level)) ∧
      Judgment HOLNativeRelatorCompatibility.rules (context level)
        dependentPi (sortTm (upperLevel level)) ∧
      Nonempty (family.El (LevelExpr.eval valuation level + 1) lowerCode ≃
        family.El (LevelExpr.eval valuation level + 1) upperCode) ∧
      ¬ ∃ interpret :
          { term : Tower.Tm 2 //
            Judgment HOLNativeRelatorCompatibility.rules (context level) term
              (sortTm (upperLevel level)) } →
          family.Code (LevelExpr.eval valuation level + 1),
        interpret (formedByLift HOLNativeRelatorCompatibility.signature level) = lowerCode ∧
          interpret (formedByUpper HOLNativeRelatorCompatibility.signature level) = upperCode := by
  exact ⟨(common_formations level).1, (common_formations level).2,
    ⟨decoded_routes_agree level (tagOperator operator) A B valuation domain codomain⟩,
    tagged_route_equations_incompatible HOLNativeRelatorCompatibility.signature level
      operator A B valuation domain codomain⟩

#print axioms context_formed
#print axioms lower_formation
#print axioms form_then_lift
#print axioms lift_then_form
#print axioms native_routes_equal
#print axioms common_formations
#print axioms formation_substitute
#print axioms evaluated_level_strict
#print axioms strict_equations_force_code_coherence
#print axioms decoded_routes_agree
#print axioms tagged_route_equations_incompatible
#print axioms common_native_boundary

end NativeCumulativeFormationCoherenceBoundary
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
