import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeRelatorCompatibility
import Mettapedia.TypeTheory.TarskiUniverseEmbedding
import Mettapedia.TypeTheory.FamilyEnclosingUniverseTower
import Mettapedia.TypeTheory.TarskiDecodedFamilyCoherence
import Mettapedia.TypeTheory.TarskiClosureRankObstruction

/-!
# Universe formation required by the common native judgments

The native List/J/relator/HOL environment admits every successive universe
formation, in its formation-sensitive judgment. A realization of just these
heads must code each lower code carrier at the next semantic level. This is
stronger than merely preserving decoded types along a cumulative lift.

No finite family of predicatively separated semantic levels realizes all
these formations. In particular, the existing two-level set-family model
does not interpret the full native tower. Conversely, a concrete infinite
finite-rank family realizes the heads but fails dependent-product closure.
Thus neither a two-level model nor an infinite level supply is by itself a
model of the actual dependent language.

An independently supplied small family-enclosing operator now provides a
single conditional family with formation, cumulative paths, and mixed-level
Pi/Sigma decoding. Its interpretation respects the actual successor/max
level expressions and their substitution. Full Pi/Sigma closure and a
Boolean code now derive predicative ranks by Cantor's obstruction, rather
than requiring rank separation as another model assumption. This does not
construct the operator or interpret all native judgments.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeUniverseModelBoundary

open Presentation Presentation.FormationSensitive
open Mettapedia.TypeTheory
open TarskiUniverseCapabilities UniverseClosureProfiles TarskiUniverseEmbedding

universe uLevel u

/-- These are actual formed judgments of the shared declaration package,
not just an external order on universe labels. -/
theorem sort_judgment {n : Nat} {context : Tower.Ctx n}
    (formed : ContextFormation HOLNativeRelatorCompatibility.rules context)
    (level : LevelExpr) :
    Judgment HOLNativeRelatorCompatibility.rules context
      (sortTm level) (sortTm (.succ level)) :=
  ⟨formed, .headType (Tower.HeadTyping.sort level)⟩

/-- Iterating the very successor constructor used by the native head rule. -/
def successive (base : LevelExpr) : Nat → LevelExpr
  | 0 => base
  | step + 1 => .succ (successive base step)

/-- Necessary data for interpreting universe-formation heads. This omits
Pi/Sigma/identity, declarations, and conversion coherence, so inhabiting it
is deliberately not named a model of the dependent language. -/
structure FormationRealization (family : TarskiCodeFamily.{uLevel, u, u}) where
  onLevel : LevelExpr → family.Level
  formation : ∀ level, UniverseEmbedding
    (universeAt family (onLevel (.succ level)))
    (universeAt family (onLevel level))

namespace FormationRealization

variable {family : TarskiCodeFamily.{uLevel, u, u}}

/-- Consecutive native formations compose using the actual universe-code
and decoded-type components of their semantic embeddings. -/
theorem later_embeds (realization : FormationRealization family)
    (base : LevelExpr) {lower upper : Nat} (below : lower < upper) :
    Nonempty (UniverseEmbedding
      (universeAt family (realization.onLevel (successive base upper)))
      (universeAt family (realization.onLevel (successive base lower)))) := by
  induction upper generalizing lower with
  | zero => omega
  | succ upper inductionHypothesis =>
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ below) with shorter | same
      · obtain ⟨earlier⟩ := inductionHypothesis shorter
        exact ⟨compose earlier (realization.formation (successive base upper))⟩
      · subst lower
        exact ⟨realization.formation (successive base upper)⟩

/-- Predicative rank separation forces every finite successor stage to use
a distinct semantic level. No level-expression equality assumption is used. -/
theorem successive_injective (realization : FormationRealization family)
    (predicative : family.PredicativeRanks) (base : LevelExpr) :
    Function.Injective (fun step => realization.onLevel (successive base step)) := by
  intro lower upper equal
  change realization.onLevel (successive base lower) =
    realization.onLevel (successive base upper) at equal
  by_contra distinct
  rcases lt_or_gt_of_ne distinct with below | above
  · obtain ⟨embedding⟩ := realization.later_embeds base below
    rw [equal] at embedding
    exact no_self_embedding family predicative _ ⟨embedding⟩
  · obtain ⟨embedding⟩ := realization.later_embeds base above
    rw [equal] at embedding
    exact no_self_embedding family predicative _ ⟨embedding⟩

/-- For full set-family products and sums with a Boolean code, distinct
native successor stages are forced by the closure operations themselves.
This does not apply to restricted Henkin function domains. -/
theorem successive_injective_of_closure (realization : FormationRealization family)
    (products : family.PiClosed) (sums : family.SigmaClosed)
    (booleans : ∀ level, ∃ code : family.Code level,
      Nonempty (family.El level code ≃ Bool)) (base : LevelExpr) :
    Function.Injective (fun step => realization.onLevel (successive base step)) :=
  realization.successive_injective
    (TarskiClosureRankObstruction.predicativeRanks_of_pi_sigma_bool
      family products sums booleans) base

/-- An unbounded semantic level supply follows from actual formation and
full dependent closure; predicativity is not a separate input here. -/
theorem infinite_levels_of_closure (realization : FormationRealization family)
    (products : family.PiClosed) (sums : family.SigmaClosed)
    (booleans : ∀ level, ∃ code : family.Code level,
      Nonempty (family.El level code ≃ Bool)) : Infinite family.Level :=
  Infinite.of_injective
    (fun step => realization.onLevel (successive (.const 0) step))
    (realization.successive_injective_of_closure products sums booleans (.const 0))

end FormationRealization

/-- A finite semantic level family cannot host the whole actual native
successor chain under the separately stated predicative-rank condition. -/
theorem no_finite_formation_realization (family : TarskiCodeFamily.{uLevel, u, u})
    [Finite family.Level] (predicative : family.PredicativeRanks) :
    ¬ Nonempty (FormationRealization family) := by
  rintro ⟨realization⟩
  have : Infinite family.Level := Infinite.of_injective
    (fun step => realization.onLevel (successive (.const 0) step))
    (realization.successive_injective predicative (.const 0))
  exact not_finite family.Level

/-- A finite level family with these full meanings cannot interpret all
native formation heads. Unlike the more general ranked theorem above,
this conclusion requires no independently assumed rank separation. -/
theorem no_finite_full_closure_realization (family : TarskiCodeFamily.{uLevel, u, u})
    [Finite family.Level] (products : family.PiClosed) (sums : family.SigmaClosed)
    (booleans : ∀ level, ∃ code : family.Code level,
      Nonempty (family.El level code ≃ Bool)) :
    ¬ Nonempty (FormationRealization family) := by
  rintro ⟨realization⟩
  have : Infinite family.Level :=
    realization.infinite_levels_of_closure products sums booleans
  exact not_finite family.Level

/-- The concrete two-level set-family hierarchy is excluded by its actual
code-carrier rank theorem, not by calling it a bounded presentation. -/
theorem twoLevel_cannot_realize_tower :
    ¬ Nonempty (FormationRealization
      CwfTarskiUniverseHierarchy.TwoLevelSetFamilies.externalFamily.{u}) := by
  have : Finite CwfTarskiUniverseHierarchy.TwoLevelSetFamilies.externalFamily.{u}.Level := by
    change Finite Bool
    infer_instance
  exact no_finite_formation_realization _
    CwfTarskiUniverseHierarchy.TwoLevelSetFamilies.predicativeRanks

/-- A concrete positive realization of all formation heads, including level
parameters and maxima, in the existing finite-rank code family. -/
def finiteRankFormation (valuation : Nat → Nat) : FormationRealization FiniteRank.family where
  onLevel := LevelExpr.eval valuation
  formation level := finiteRankSuccessor (LevelExpr.eval valuation level)

/-- The positive control also respects actual native universe-head
conversion. Its formation alone did not assume this additional property. -/
theorem finiteRank_headEq (valuation : Nat → Nat) {left right : LevelExpr}
    (equal : Tower.HeadEq (.sort left) (.sort right)) :
    (finiteRankFormation valuation).onLevel left =
      (finiteRankFormation valuation).onLevel right :=
  equal valuation

/-- Level instantiation commutes with the positive control's interpretation. -/
theorem finiteRank_level_substitution (valuation : Nat → Nat)
    (substitution : Nat → LevelExpr) (level : LevelExpr) :
    (finiteRankFormation valuation).onLevel (LevelExpr.subst substitution level) =
      (finiteRankFormation (fun index => LevelExpr.eval valuation (substitution index))).onLevel
        level :=
  LevelExpr.eval_subst valuation substitution level

/-- Unlimited formation heads do not establish dependent-product semantics.
The exhibited realization fails already at the rank-three function space. -/
theorem formation_does_not_supply_products :
    Nonempty (FormationRealization FiniteRank.family) ∧
      ¬ FiniteRank.family.PiClosedAt 3 :=
  ⟨⟨finiteRankFormation (fun _ => 0)⟩, FiniteRank.not_piClosedAt_three⟩

/-! ## One conditional family for formation and dependent closure -/

namespace Enclosed

open TarskiDecodedFamilyCoherence

variable (operator : SmallFamilyEnclosingUniverseOperator.{u})
variable (A : Type u) (B : A → Type u)

/-- Actual native levels index the iterated enclosing family. The operator
is independent semantic input; existence is not inferred from these laws. -/
def formation (valuation : Nat → Nat) :
    FormationRealization (FamilyEnclosingUniverseTower.family operator A B) where
  onLevel := LevelExpr.eval valuation
  formation level := FamilyEnclosingUniverseTower.successorEmbedding operator A B
    (LevelExpr.eval valuation level)

/-- Every formation path in the supplied enclosing tower is separated.
The rank theorem is derived from its actual full closure operations. -/
theorem successive_injective (valuation : Nat → Nat) (base : LevelExpr) :
    Function.Injective (fun step =>
      (formation operator A B valuation).onLevel (successive base step)) :=
  (formation operator A B valuation).successive_injective
    (TarskiClosureRankObstruction.tower_predicativeRanks operator A B) base

theorem headEq (valuation : Nat → Nat) {left right : LevelExpr}
    (equal : Tower.HeadEq (.sort left) (.sort right)) :
    (formation operator A B valuation).onLevel left =
      (formation operator A B valuation).onLevel right := equal valuation

theorem level_substitution (valuation : Nat → Nat)
    (substitution : Nat → LevelExpr) (level : LevelExpr) :
    (formation operator A B valuation).onLevel (LevelExpr.subst substitution level) =
      (formation operator A B
        (fun index => LevelExpr.eval valuation (substitution index))).onLevel level :=
  LevelExpr.eval_subst valuation substitution level

/-- A native cumulative edge uses the canonical path in this very family. -/
def cumulativeLift (valuation : Nat → Nat) {left right : LevelExpr}
    (below : Tower.Cumulative (.sort left) (.sort right))
    (code : (FamilyEnclosingUniverseTower.family operator A B).Code
      (LevelExpr.eval valuation left)) :
    (FamilyEnclosingUniverseTower.family operator A B).Code
      (LevelExpr.eval valuation right) :=
  FamilyEnclosingUniverseTower.liftCode operator A B (below valuation) code

def decodeCumulativeLift (valuation : Nat → Nat) {left right : LevelExpr}
    (below : Tower.Cumulative (.sort left) (.sort right))
    (code : (FamilyEnclosingUniverseTower.family operator A B).Code
      (LevelExpr.eval valuation left)) :
    (FamilyEnclosingUniverseTower.family operator A B).El
        (LevelExpr.eval valuation right) (cumulativeLift operator A B valuation below code) ≃
      (FamilyEnclosingUniverseTower.family operator A B).El
        (LevelExpr.eval valuation left) code :=
  FamilyEnclosingUniverseTower.decodeLift operator A B (below valuation) code

theorem cumulativeLift_id (valuation : Nat → Nat) (level : LevelExpr)
    (code : (FamilyEnclosingUniverseTower.family operator A B).Code
      (LevelExpr.eval valuation level)) :
    cumulativeLift operator A B valuation (fun _ => Nat.le_refl _) code = code :=
  FamilyEnclosingUniverseTower.liftCode_refl operator A B _ code

theorem cumulativeLift_comp (valuation : Nat → Nat) {first middle last : LevelExpr}
    (firstBelow : Tower.Cumulative (.sort first) (.sort middle))
    (secondBelow : Tower.Cumulative (.sort middle) (.sort last))
    (code : (FamilyEnclosingUniverseTower.family operator A B).Code
      (LevelExpr.eval valuation first)) :
    cumulativeLift operator A B valuation
        (fun value => (firstBelow value).trans (secondBelow value)) code =
      cumulativeLift operator A B valuation secondBelow
        (cumulativeLift operator A B valuation firstBelow code) :=
  FamilyEnclosingUniverseTower.liftCode_trans operator A B
    (firstBelow valuation) (secondBelow valuation) code

/-- Lift the two inputs independently before closing their product. The
codomain argument is transported by the actual domain decoding equivalence. -/
def piAt (left right : Nat) :
    PiCoding (FamilyEnclosingUniverseTower.family operator A B) left right (Nat.max left right) :=
  (show PiCoding (FamilyEnclosingUniverseTower.family operator A B)
      (Nat.max left right) (Nat.max left right) (Nat.max left right) from
    ⟨FamilyEnclosingUniverseTower.piCode operator A B (max left right),
      FamilyEnclosingUniverseTower.decodePi operator A B (max left right)⟩).mapInputs
    (FamilyEnclosingUniverseTower.liftCode operator A B (Nat.le_max_left left right))
    (FamilyEnclosingUniverseTower.decodeLift operator A B (Nat.le_max_left left right))
    (FamilyEnclosingUniverseTower.liftCode operator A B (Nat.le_max_right left right))
    (FamilyEnclosingUniverseTower.decodeLift operator A B (Nat.le_max_right left right))

def sigmaAt (left right : Nat) :
    SigmaCoding (FamilyEnclosingUniverseTower.family operator A B) left right (Nat.max left right) :=
  (show SigmaCoding (FamilyEnclosingUniverseTower.family operator A B)
      (Nat.max left right) (Nat.max left right) (Nat.max left right) from
    ⟨FamilyEnclosingUniverseTower.sigmaCode operator A B (max left right),
      FamilyEnclosingUniverseTower.decodeSigma operator A B (max left right)⟩).mapInputs
    (FamilyEnclosingUniverseTower.liftCode operator A B (Nat.le_max_left left right))
    (FamilyEnclosingUniverseTower.decodeLift operator A B (Nat.le_max_left left right))
    (FamilyEnclosingUniverseTower.liftCode operator A B (Nat.le_max_right left right))
    (FamilyEnclosingUniverseTower.decodeLift operator A B (Nat.le_max_right left right))

/-- The output level is the actual maximum used by Tower.Join.sorts. -/
def pi (valuation : Nat → Nat) (left right : LevelExpr) :
    PiCoding (FamilyEnclosingUniverseTower.family operator A B)
      (LevelExpr.eval valuation left) (LevelExpr.eval valuation right)
      (LevelExpr.eval valuation (.max left right)) :=
  piAt operator A B (LevelExpr.eval valuation left) (LevelExpr.eval valuation right)

def sigma (valuation : Nat → Nat) (left right : LevelExpr) :
    SigmaCoding (FamilyEnclosingUniverseTower.family operator A B)
      (LevelExpr.eval valuation left) (LevelExpr.eval valuation right)
      (LevelExpr.eval valuation (.max left right)) :=
  sigmaAt operator A B (LevelExpr.eval valuation left) (LevelExpr.eval valuation right)

/-- Substitution changes the indices, so equality of the actual code/decode
records is heterogeneous. No equality is postulated between decoded types. -/
theorem pi_level_substitution (valuation : Nat → Nat)
    (substitution : Nat → LevelExpr) (left right : LevelExpr) :
    HEq (pi operator A B valuation (LevelExpr.subst substitution left)
      (LevelExpr.subst substitution right))
      (pi operator A B (fun index => LevelExpr.eval valuation (substitution index)) left right) := by
  have congruent (i i' j j' : Nat) (hi : i = i') (hj : j = j') :
      HEq (piAt operator A B i j) (piAt operator A B i' j') := by
    subst i'
    subst j'
    rfl
  exact congruent _ _ _ _ (LevelExpr.eval_subst valuation substitution left)
    (LevelExpr.eval_subst valuation substitution right)

theorem sigma_level_substitution (valuation : Nat → Nat)
    (substitution : Nat → LevelExpr) (left right : LevelExpr) :
    HEq (sigma operator A B valuation (LevelExpr.subst substitution left)
      (LevelExpr.subst substitution right))
      (sigma operator A B (fun index => LevelExpr.eval valuation (substitution index)) left right) := by
  have congruent (i i' j j' : Nat) (hi : i = i') (hj : j = j') :
      HEq (sigmaAt operator A B i j) (sigmaAt operator A B i' j') := by
    subst i'
    subst j'
    rfl
  exact congruent _ _ _ _ (LevelExpr.eval_subst valuation substitution left)
    (LevelExpr.eval_subst valuation substitution right)

/-- Shared-family qualification of this boundary only: actual formation
heads and mixed-level products/sums, plus identity closure at every level.
Native motives, declarations, and conversion soundness are not conclusions. -/
theorem formation_and_closure (valuation : Nat → Nat) :
    Nonempty (FormationRealization (FamilyEnclosingUniverseTower.family operator A B)) ∧
      (∀ left right : LevelExpr,
        Nonempty (PiCoding (FamilyEnclosingUniverseTower.family operator A B)
          (LevelExpr.eval valuation left) (LevelExpr.eval valuation right)
          (LevelExpr.eval valuation (.max left right))) ∧
        Nonempty (SigmaCoding (FamilyEnclosingUniverseTower.family operator A B)
          (LevelExpr.eval valuation left) (LevelExpr.eval valuation right)
          (LevelExpr.eval valuation (.max left right)))) ∧
      (∀ (level : Nat) (domain : (FamilyEnclosingUniverseTower.family operator A B).Code level)
        (left right : (FamilyEnclosingUniverseTower.family operator A B).El level domain),
        ∃ code : (FamilyEnclosingUniverseTower.family operator A B).Code level,
        Nonempty ((FamilyEnclosingUniverseTower.family operator A B).El level code ≃
          (left = right))) :=
  ⟨⟨formation operator A B valuation⟩,
    fun left right => ⟨⟨pi operator A B valuation left right⟩,
      ⟨sigma operator A B valuation left right⟩⟩,
    FamilyEnclosingUniverseTower.identityClosed operator A B⟩

end Enclosed

#print axioms sort_judgment
#print axioms FormationRealization.later_embeds
#print axioms FormationRealization.successive_injective
#print axioms FormationRealization.successive_injective_of_closure
#print axioms FormationRealization.infinite_levels_of_closure
#print axioms no_finite_formation_realization
#print axioms no_finite_full_closure_realization
#print axioms twoLevel_cannot_realize_tower
#print axioms finiteRankFormation
#print axioms finiteRank_headEq
#print axioms finiteRank_level_substitution
#print axioms formation_does_not_supply_products
#print axioms Enclosed.formation
#print axioms Enclosed.successive_injective
#print axioms Enclosed.headEq
#print axioms Enclosed.level_substitution
#print axioms Enclosed.cumulativeLift_comp
#print axioms Enclosed.decodeCumulativeLift
#print axioms Enclosed.pi
#print axioms Enclosed.sigma
#print axioms Enclosed.pi_level_substitution
#print axioms Enclosed.sigma_level_substitution
#print axioms Enclosed.formation_and_closure

end NativeUniverseModelBoundary
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
