import Mettapedia.OSLF.Framework.InstrumentEquationDecomposition

/-!
# Reconstruction of actual equation classes by a complete first-order kit

The independent labelled bisimulation matches all actual equation-class
openings. A least-count representative supplies the left-hand decomposition;
the matching right-hand decomposition may be any representative. Projection
exposes its exact component classes. Hereditary least-count descent therefore
earns equality by strong induction, including nontrivial cross-root equations.

No raw-view equation admission, operational soundness field or global
reconstruction hypothesis is used. Minimal-context/runtime correspondence
and binding remain separate obligations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentEquations

open InstrumentObservations

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}
variable (generators : Tree Symbols arity → Tree Symbols arity → Prop)

theorem related_bundle_children (opened : Policy Symbols)
    {relation : ClassState generators → ClassState generators → Prop}
    (bisimulation : IsClassBisimulation generators opened relation)
    (constructor : Symbols) (permission : opened constructor)
    (first second : Fin (arity constructor) → TermClass generators)
    (related : relation (.bundle constructor first) (.bundle constructor second))
    (position : Fin (arity constructor)) :
    relation (.term (first position)) (.term (second position)) := by
  obtain ⟨matched, response, nextRelated⟩ :=
    bisimulation.forward related (label := .get constructor position)
      ⟨ClassEvent.get constructor first permission position⟩
  have shape := get_target generators opened constructor second position response
  rw [shape] at nextRelated
  exact nextRelated

theorem isClassBisimulation_reconstruction (opened : Policy Symbols)
    (complete : ∀ constructor, opened constructor)
    {relation : ClassState generators → ClassState generators → Prop}
    (bisimulation : IsClassBisimulation generators opened relation)
    {first second : TermClass generators}
    (related : relation (.term first) (.term second)) : first = second := by
  have reconstruction : ∀ bound (left right : TermClass generators),
      measure generators left = bound → relation (.term left) (.term right) → left = right := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound inductionHypothesis =>
      intro left right measured relatedTerms
      obtain ⟨representative, represents, lean⟩ := lean_representative generators left
      cases representative with
      | node constructor arguments =>
        obtain ⟨matched, response, relatedBundles⟩ :=
          bisimulation.forward relatedTerms (label := .ask constructor)
            ⟨ClassEvent.ask constructor arguments (complete constructor) left represents⟩
        obtain ⟨compared, shape, otherRepresents⟩ :=
          ask_target_supplied generators opened right constructor response
        rw [shape] at relatedBundles
        have children : ∀ position,
            classOf generators (arguments position) = classOf generators (compared position) := by
          intro position
          have childRelated := related_bundle_children generators opened bisimulation constructor
            (complete constructor) (fun index => classOf generators (arguments index))
            (fun index => classOf generators (compared index)) relatedBundles position
          have smaller := (lean_child_descent generators constructor arguments lean position).2
          rw [represents, measured] at smaller
          exact inductionHypothesis _ smaller _ _ rfl childRelated
        exact represents.symm.trans
          ((nodeClass_of_component_classes generators constructor arguments compared children).trans
            otherRepresents)
  exact reconstruction (measure generators first) first second rfl related

theorem complete_class_kit_reconstruction (opened : Policy Symbols)
    (complete : ∀ constructor, opened constructor) (first second : TermClass generators) :
    ClassBisimilar generators opened (.term first) (.term second) ↔ first = second := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact isClassBisimulation_reconstruction generators opened complete bisimulation related
  · rintro rfl
    exact class_bisimilar_refl generators opened _

theorem complete_raw_equation_reconstruction (opened : Policy Symbols)
    (complete : ∀ constructor, opened constructor) (first second : Tree Symbols arity) :
    ClassBisimilar generators opened (.term (classOf generators first))
      (.term (classOf generators second)) ↔ Equation generators first second :=
  (complete_class_kit_reconstruction generators opened complete _ _).trans
    (classOf_eq_iff generators first second)

end Mettapedia.OSLF.Framework.InstrumentEquations
