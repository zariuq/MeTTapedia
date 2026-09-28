import Mettapedia.OSLF.Syntax.LambdaRuleDerivationPolynomial
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraMorphisms
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraCategory
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Morphisms and coherence for proof-relevant rule interpretations

An indexed rule polynomial presents one constructor for each firing rule and
one recursive position for each premise. The interpretation of derivation
trees into a rule algebra is its fold. Here algebra morphisms compose and the
fold is natural in the target algebra, including every premise position.

The concrete lambda interpretation maps a full rule history to its number
of firings. It covers a root beta step and a step under a binder. Counting
deliberately forgets rule names; the full history algebra remains available
to consumers that require those observations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.Algebra

universe uBase uIndex uShape uPosition uSource uMiddle uTarget uFourth

variable {Base : Type uBase} {Index : Base → Type uIndex}
variable {polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
    Base Index}
variable {source : (base : Base) → Index base → Type uSource}
variable {middle : (base : Base) → Index base → Type uMiddle}
variable {target : (base : Base) → Index base → Type uTarget}
variable {fourth : (base : Base) → Index base → Type uFourth}

/-- Folding a derivation and then mapping evidence is the same as folding
directly into the target interpretation. This is the morphism coherence law
needed by an operational model and its interpretation maps. -/
theorem fold_natural {A : Algebra polynomial source}
    {B : Algebra polynomial target} (f : Hom A B)
    (base : Base) (index : Index base)
    (tree : polynomial.Fix base index) :
    f.toFun base index
      (IndexedPolynomial.Fix.fold polynomial A.act base index tree) =
    IndexedPolynomial.Fix.fold polynomial B.act base index tree := by
  let composite := Hom.comp (foldHom A) f
  exact hom_eq_fold B composite base index tree

#print axioms fold_natural

end Mettapedia.TypeTheory.IndexedPolynomial.Algebra

namespace Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.OperationalRuleModels

/-- The exact four-rule lambda system is an instance of the general
proof-relevant free rule model. -/
noncomputable def lambdaFreeRuleModelInitial :
    _root_.CategoryTheory.Limits.IsInitial
      (OperationalRuleModels.free rules) :=
  OperationalRuleModels.freeIsInitial rules

/-- Each retained rule application contributes one unit, including an
application of congruence beneath a binder. -/
def countAlgebra : rules.Algebra (fun _ _ => Nat) where
  act := by
    intro base index layer
    rcases layer with ⟨shape, children⟩
    change RuleShape index at shape
    cases shape with
    | beta _ _ => exact 1
    | appCongL _ _ _ => exact children () + 1
    | appCongR _ _ _ => exact children () + 1
    | lamCong _ _ => exact children () + 1

/-- List length is a homomorphism from the complete rule-history algebra to
the counting algebra. It preserves all four constructor actions. -/
def historyToCount : IndexedPolynomial.Algebra.Hom historyAlgebra countAlgebra where
  toFun := fun _ _ history => history.length
  commutes := by
    intro base index layer
    rcases layer with ⟨shape, children⟩
    change RuleShape index at shape
    cases shape <;> rfl

/-- Counting through the history interpretation agrees with interpreting
the same proof-relevant tree directly in the counting model. -/
theorem count_via_history (j : Judgment) (tree : rules.Fix () j) :
    (history tree).length =
      IndexedPolynomial.Fix.fold rules countAlgebra.act () j tree := by
  exact IndexedPolynomial.Algebra.fold_natural historyToCount () j tree

theorem open_firing_count :
    IndexedPolynomial.Fix.fold rules countAlgebra.act () _ openBetaTree = 1 := by
  rw [← count_via_history]
  exact congrArg List.length open_history

theorem binder_firing_count :
    IndexedPolynomial.Fix.fold rules countAlgebra.act () _ closedLamTree = 2 := by
  rw [← count_via_history]
  exact congrArg List.length closed_history

/-- A legal rule-model map can forget the identity of a firing. Therefore
history preservation is an additional property of an interpretation, not a
consequence of constructor preservation alone. -/
theorem count_map_forgets_rule_name (j : Judgment) :
    (historyToCount.toFun () j [.beta] =
      historyToCount.toFun () j [.lamCong]) ∧
    ([.beta] : List RuleTag) ≠ [.lamCong] := by
  constructor
  · rfl
  · decide

#print axioms lambdaFreeRuleModelInitial
#print axioms count_via_history
#print axioms binder_firing_count
#print axioms count_map_forgets_rule_name

end Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial
