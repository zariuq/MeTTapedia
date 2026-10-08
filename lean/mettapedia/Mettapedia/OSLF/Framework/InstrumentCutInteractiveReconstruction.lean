import Mettapedia.OSLF.Framework.InstrumentCutKitReactions
import Mettapedia.OSLF.Framework.PartialStructuralObservers

/-!
# Full reactive bisimulation determines admitted structural observations

Actual ask/get IPOs, in the complete proper-plus-kit rule family, determine
each opened constructor and its supplied children. The resulting necessary
partial-view and logical readings concern full literal-label bisimilarity,
not the separately defined sampled probe relation. Fully opened source trees
are reconstructed exactly. No converse is asserted for arbitrary partial
views in the presence of proper reactions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} (arity : Symbols → Nat)

theorem embedded_original_inversion (constructor : Symbols)
    (arguments : Fin (arity constructor) → Value arity .base)
    (source : InstrumentObservations.Tree Symbols arity)
    (read : embedSource arity source = original arity constructor arguments) :
    ∃ supplied : Fin (arity constructor) → InstrumentObservations.Tree Symbols arity,
      source = .node constructor supplied ∧
        arguments = fun position => embedSource arity (supplied position) := by
  cases source with
  | node other supplied =>
    rw [embedSource_node] at read
    have same : other = constructor := Constructor.original.inj
      (Term.head_eq (signature := signature arity) _ _ read)
    subst other
    exact ⟨supplied, rfl, (Term.node.inj read).symm⟩

set_option backward.isDefEq.respectTransparency false in
theorem kit_bundle_children_related {Origins : Type w} (origin : Origins)
    (opened : InstrumentObservations.Policy Symbols) (proper : SourceRule arity → Prop)
    (constructor : Symbols) (permission : opened constructor)
    (first second : Fin (arity constructor) → Value arity .base)
    (related : IPOBisimilar (kitRules arity Origins opened proper)
      (termArrow (signature arity) (bundle arity constructor first))
      (termArrow (signature arity) (bundle arity constructor second)))
    (position : Fin (arity constructor)) :
    IPOBisimilar (kitRules arity Origins opened proper)
      (termArrow (signature arity) (first position))
      (termArrow (signature arity) (second position)) := by
  have step : ActIPO (kitRules arity Origins opened proper)
      (contextArrow (signature arity) (probeContext arity (.get constructor position)))
      (termArrow (signature arity) (bundle arity constructor first))
      (termArrow (signature arity) (first position)) :=
    (kit_probe_step_iff arity Origins opened proper (.get constructor position) _ _).mpr
      ⟨⟨origin, .get constructor position first⟩, permission, rfl, rfl⟩
  obtain ⟨matched, response, successors⟩ := ipoBisimilar_forward related step
  cases matched with
  | value target =>
    obtain ⟨occurrence, _, sourceRead, targetRead⟩ :=
      (kit_probe_step_iff arity Origins opened proper (.get constructor position) _ _).mp response
    rcases occurrence with ⟨occurrenceOrigin, instance_⟩
    cases instance_ with
    | get _ _ supplied =>
      have argumentsRead : second = supplied := Term.node.inj sourceRead
      have resultRead : target = second position := targetRead.trans (congrFun argumentsRead position).symm
      rw [resultRead] at successors
      exact successors

set_option backward.isDefEq.respectTransparency false in
theorem kit_opened_constructor_related {Origins : Type w} (origin : Origins)
    (opened : InstrumentObservations.Policy Symbols) (proper : SourceRule arity → Prop)
    (constructor : Symbols) (permission : opened constructor)
    (arguments : Fin (arity constructor) → InstrumentObservations.Tree Symbols arity)
    (other : InstrumentObservations.Tree Symbols arity)
    (related : IPOBisimilar (kitRules arity Origins opened proper)
      (termArrow (signature arity) (embedSource arity (.node constructor arguments)))
      (termArrow (signature arity) (embedSource arity other))) :
    ∃ compared : Fin (arity constructor) → InstrumentObservations.Tree Symbols arity,
      other = .node constructor compared ∧
        IPOBisimilar (kitRules arity Origins opened proper)
          (termArrow (signature arity)
            (bundle arity constructor (fun position => embedSource arity (arguments position))))
          (termArrow (signature arity)
            (bundle arity constructor (fun position => embedSource arity (compared position)))) := by
  have step : ActIPO (kitRules arity Origins opened proper)
      (contextArrow (signature arity) (probeContext arity (.ask constructor)))
      (termArrow (signature arity) (embedSource arity (.node constructor arguments)))
      (termArrow (signature arity)
        (bundle arity constructor (fun position => embedSource arity (arguments position)))) :=
    (kit_probe_step_iff arity Origins opened proper (.ask constructor) _ _).mpr
      ⟨⟨origin, .ask constructor (fun position => embedSource arity (arguments position))⟩,
        permission, rfl, rfl⟩
  obtain ⟨matched, response, successors⟩ := ipoBisimilar_forward related step
  cases matched with
  | value target =>
    obtain ⟨occurrence, _, sourceRead, targetRead⟩ :=
      (kit_probe_step_iff arity Origins opened proper (.ask constructor) _ _).mp response
    rcases occurrence with ⟨occurrenceOrigin, instance_⟩
    cases instance_ with
    | ask _ supplied =>
      obtain ⟨compared, otherRead, argumentsRead⟩ :=
        embedded_original_inversion arity constructor supplied other sourceRead
      rw [targetRead, argumentsRead] at successors
      exact ⟨compared, otherRead, successors⟩

theorem kit_interactive_view {Origins : Type w} (origin : Origins)
    (opened : InstrumentObservations.Policy Symbols) (proper : SourceRule arity → Prop)
    (first second : InstrumentObservations.Tree Symbols arity)
    (related : IPOBisimilar (kitRules arity Origins opened proper)
      (termArrow (signature arity) (embedSource arity first))
      (termArrow (signature arity) (embedSource arity second))) :
    InstrumentObservations.view opened first = InstrumentObservations.view opened second := by
  classical
  induction first generalizing second with
  | node constructor arguments inductionHypothesis =>
    by_cases permission : opened constructor
    · obtain ⟨compared, rfl, bundles⟩ := kit_opened_constructor_related arity origin opened proper
        constructor permission arguments second related
      simp only [InstrumentObservations.view, if_pos permission]
      congr 1
      funext position
      exact inductionHypothesis position (compared position)
        (kit_bundle_children_related arity origin opened proper constructor permission _ _ bundles position)
    · cases second with
      | node other compared =>
        by_cases otherPermission : opened other
        · obtain ⟨supplied, shape, _⟩ := kit_opened_constructor_related arity origin opened proper
            other otherPermission compared (.node constructor arguments) (ipoBisimilar_symm related)
          have same : constructor = other := congrArg
            (fun tree : InstrumentObservations.Tree Symbols arity => match tree with | .node head _ => head) shape
          exact (permission (same ▸ otherPermission)).elim
        · simp only [InstrumentObservations.view, if_neg permission, if_neg otherPermission]

def FullyOpened (opened : InstrumentObservations.Policy Symbols) :
    InstrumentObservations.Tree Symbols arity → Prop
  | .node constructor arguments => opened constructor ∧ ∀ position, FullyOpened opened (arguments position)

theorem kit_interactive_reconstruction {Origins : Type w} (origin : Origins)
    (opened : InstrumentObservations.Policy Symbols) (proper : SourceRule arity → Prop)
    (first second : InstrumentObservations.Tree Symbols arity) (complete : FullyOpened arity opened first)
    (related : IPOBisimilar (kitRules arity Origins opened proper)
      (termArrow (signature arity) (embedSource arity first))
      (termArrow (signature arity) (embedSource arity second))) : first = second := by
  induction first generalizing second with
  | node constructor arguments inductionHypothesis =>
    obtain ⟨compared, rfl, bundles⟩ := kit_opened_constructor_related arity origin opened proper
      constructor complete.1 arguments second related
    congr 1
    funext position
    exact inductionHypothesis position (compared position) (complete.2 position)
      (kit_bundle_children_related arity origin opened proper constructor complete.1 _ _ bundles position)

theorem kit_interactive_iff_equal (Origins : Type w) [Nonempty Origins]
    (opened : InstrumentObservations.Policy Symbols) (proper : SourceRule arity → Prop)
    (first second : InstrumentObservations.Tree Symbols arity) (complete : FullyOpened arity opened first) :
    IPOBisimilar (kitRules arity Origins opened proper)
      (termArrow (signature arity) (embedSource arity first))
      (termArrow (signature arity) (embedSource arity second)) ↔ first = second := by
  constructor
  · exact kit_interactive_reconstruction arity (Classical.choice inferInstance) opened proper first second complete
  · intro same
    subst second
    exact ipoBisimilar_refl _ _

theorem kit_interactive_partial_tests (Origins : Type w) [Nonempty Origins]
    (kit : List Symbols) (proper : SourceRule arity → Prop)
    (first second : InstrumentObservations.Tree Symbols arity)
    (related : IPOBisimilar (kitRules arity Origins (fun constructor => constructor ∈ kit) proper)
      (termArrow (signature arity) (embedSource arity first))
      (termArrow (signature arity) (embedSource arity second))) :
    InstrumentObservations.LogicallyEquivalent (fun constructor => constructor ∈ kit) first second :=
  (InstrumentObservations.logicallyEquivalent_iff_view kit first second).mpr
    (kit_interactive_view arity (Classical.choice inferInstance) _ proper first second related)

end Mettapedia.OSLF.Framework.InstrumentCutContexts
