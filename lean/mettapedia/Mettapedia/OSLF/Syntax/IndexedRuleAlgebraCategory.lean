import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Categories of proof-relevant rule algebras

At a fixed indexed rule polynomial, a model interprets each rule constructor
as an action on the chosen evidence family. Morphisms preserve those actions
at every premise position. Constructor trees form the initial model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.OperationalRuleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.TypeTheory

universe uBase uIndex uShape uPosition

variable {Base : Type uBase} {Index : Base → Type uIndex}
variable (P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)

/-- A proof-relevant interpretation of every rule shape and its recursively
interpreted premises, over a fixed family of judgment indices. -/
structure Model where
  carrier : (base : Base) → Index base →
    Type (max uIndex uShape uPosition)
  rules : P.Algebra carrier

/-- A rule-model map preserves each rule constructor and all premise inputs. -/
instance modelCategory : CategoryTheory.Category (Model P) where
  Hom A B := IndexedPolynomial.Algebra.Hom A.rules B.rules
  id A := IndexedPolynomial.Algebra.Hom.id A.rules
  comp f g := IndexedPolynomial.Algebra.Hom.comp f g
  id_comp := by
    intro A B f
    exact IndexedPolynomial.Algebra.Hom.id_comp f
  comp_id := by
    intro A B f
    exact IndexedPolynomial.Algebra.Hom.comp_id f
  assoc := by
    intro A B C D f g h
    exact IndexedPolynomial.Algebra.Hom.comp_assoc f g h

/-- Constructor trees are the free interpretation of the rule polynomial. -/
def free : Model P where
  carrier := P.Fix
  rules := IndexedPolynomial.Algebra.initial P

/-- The rule-tree interpretation into any model is the unique map preserving
all rule constructors, including each recursive premise position. -/
noncomputable def freeIsInitial :
    IsInitial (free P) :=
  IsInitial.ofUniqueHom
    (fun target => IndexedPolynomial.Algebra.foldHom target.rules)
    (fun target f => by
      apply IndexedPolynomial.Algebra.Hom.ext
      intro base index tree
      exact IndexedPolynomial.Algebra.hom_eq_fold target.rules f base index tree)

#print axioms freeIsInitial

end Mettapedia.OSLF.Binding.OperationalRuleModels
