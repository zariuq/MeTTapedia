import Mettapedia.Languages.Agda.Structural.RuleInterpretation

/-!
# Proof-relevant correspondence of root constructors

The authored root polynomial has exactly the structural root constructors,
at each scoped endpoint pair. Both inverse laws retain the chosen declaration
and the full local valuation. This comparison concerns root constructors;
compatible closure adds the separately generated congruence constructors.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Authored

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

def shapeOfRootAt : {j : Judgment algebra} → RootAt j → Shape roots algebra j
  | ⟨_, _, _, _⟩, root => shapeOfRoot root

private def instanceOfRootAt {j : Judgment algebra} (root : RootAt j) : Instance roots algebra :=
  (shapeOfRootAt root).1

private theorem instanceOfRootAt_transport {first second : Judgment algebra}
    (same : first = second) (root : RootAt first) :
    instanceOfRootAt (same ▸ root) = instanceOfRootAt root := by
  cases same
  rfl

private theorem instanceOfRootAt_mpr {first second : Judgment algebra}
    (same : first = second) (root : RootAt second) :
    instanceOfRootAt ((congrArg RootAt same).mpr root) = instanceOfRootAt root := by
  cases same
  rfl

private theorem instanceOfRootAt_rootFromValues {Γ : Ctx sig} (index : Fin roots.length)
    (values : Val (roots.get index).1 Γ) :
    instanceOfRootAt (rootFromValues index values) = occurrence index values := by
  rcases index with ⟨i, bound⟩
  match i with
  | 0 =>
      change instanceOfRootAt ((congrArg RootAt (beta_conclusion values)).mpr
        (Root.beta (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))) = _
      exact (instanceOfRootAt_mpr (beta_conclusion values)
        (Root.beta (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))).trans
        (congrArg (occurrence betaIndex) (betaValues_recover values))
  | 1 =>
      change instanceOfRootAt ((congrArg RootAt (noAbs_conclusion values)).mpr
        (Root.betaNoAbs (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))) = _
      exact (instanceOfRootAt_mpr (noAbs_conclusion values)
        (Root.betaNoAbs (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))).trans
        (congrArg (occurrence noAbsIndex) (noAbsValues_recover values))
  | 2 =>
      change instanceOfRootAt ((congrArg RootAt (empty_conclusion values)).mpr
        (Root.eliminateEmpty (values (0 : Fin 1)))) = _
      exact (instanceOfRootAt_mpr (empty_conclusion values)
        (Root.eliminateEmpty (values (0 : Fin 1)))).trans
        (congrArg (occurrence emptyIndex) (emptyValues_recover values))
  | 3 =>
      change instanceOfRootAt ((congrArg RootAt (elimAppend_conclusion values)).mpr
        (Root.eliminateAppend (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))) = _
      exact (instanceOfRootAt_mpr (elimAppend_conclusion values)
        (Root.eliminateAppend (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))).trans
        (congrArg (occurrence elimAppendIndex) (elimAppendValues_recover values))
  | 4 =>
      change instanceOfRootAt ((congrArg RootAt (appendEmpty_conclusion values)).mpr
        (Root.appendEmpty (values (0 : Fin 1)))) = _
      exact (instanceOfRootAt_mpr (appendEmpty_conclusion values)
        (Root.appendEmpty (values (0 : Fin 1)))).trans
        (congrArg (occurrence appendEmptyIndex) (appendEmptyValues_recover values))
  | 5 =>
      change instanceOfRootAt ((congrArg RootAt (appendCons_conclusion values)).mpr
        (Root.appendCons (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))) = _
      exact (instanceOfRootAt_mpr (appendCons_conclusion values)
        (Root.appendCons (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))).trans
        (congrArg (occurrence appendConsIndex) (appendConsValues_recover values))
  | n + 6 =>
      exfalso
      simp only [roots, List.length_cons, List.length_nil] at bound
      omega

private theorem instanceOfRootAt_rootOfOccurrence (event : Instance roots algebra) :
    instanceOfRootAt (rootOfOccurrence event) = event := by
  unfold rootOfOccurrence
  rw [instanceOfRootAt_transport, instanceOfRootAt_rootFromValues]
  exact (occurrence_complete event).symm

theorem shapeOfRootAt_rootOfShape {j : Judgment algebra} (shape : Shape roots algebra j) :
    shapeOfRootAt (rootOfShape shape) = shape := by
  apply Subtype.ext
  change instanceOfRootAt (rootOfShape shape) = shape.1
  unfold rootOfShape
  rw [instanceOfRootAt_transport, instanceOfRootAt_rootOfOccurrence]

theorem rootOfShape_shapeOfRootAt {j : Judgment algebra} (root : RootAt j) :
    rootOfShape (shapeOfRootAt root) = root := by
  rcases j with ⟨Γ, resultSort, source, target⟩
  exact rootOfShape_shapeOfRoot root

/-- Exact equality of the proof-relevant root fibres, including declarations
and all local parameters, rather than mere equality of endpoint predicates. -/
def rootShapeEquiv (j : Judgment algebra) : Shape roots algebra j ≃ RootAt j where
  toFun := rootOfShape
  invFun := shapeOfRootAt
  left_inv := shapeOfRootAt_rootOfShape
  right_inv := rootOfShape_shapeOfRootAt

#print axioms shapeOfRootAt_rootOfShape
#print axioms rootShapeEquiv

end Mettapedia.Languages.Agda.Structural.Authored
