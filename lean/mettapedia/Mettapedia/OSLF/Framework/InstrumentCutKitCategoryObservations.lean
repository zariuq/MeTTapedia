import Mettapedia.OSLF.Framework.InstrumentCutKitMonotonicity
import Mettapedia.OSLF.Framework.InstrumentCutInteractiveReconstruction

/-!
# Independent structural observations of the complete kit category

Every selected ask/get is an actual permitted arrow of the kit category. Its
full IPO matches recover the supplied original constructor and exact children.
This earns necessary partial tests and exact reconstruction on the fully
opened source subalgebra, with arbitrary proper source reactions retained.
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

local instance instrumentCutKitCategoryObservationsQuiver : Quiver (Srt Symbols arity) :=
  frameQuiver (signature arity)

theorem kit_probeFrame_supported (opened : InstrumentObservations.Policy Symbols)
    (instrument : Probe Symbols arity) (permission : opened (instrumentConstructor arity instrument)) :
    KitFrame arity opened (probeFrame arity instrument) := by
  refine ⟨.cut instrument permission, ?_⟩
  intro other different
  fin_cases other
  · exact kitSupported_probe arity opened instrument permission
  · exact (different rfl).elim

def kitProbeContext (opened : InstrumentObservations.Policy Symbols)
    (instrument : Probe Symbols arity) (permission : opened (instrumentConstructor arity instrument)) :
    kitInterface arity opened (receiver arity instrument) ⟶ kitInterface arity opened (result arity instrument) :=
  kitContext arity (probeContext arity instrument)
    (.cons (.nil _) (kit_probeFrame_supported arity opened instrument permission))

def kitSource (opened : InstrumentObservations.Policy Symbols)
    (source : InstrumentObservations.Tree Symbols arity) : kitOrigin arity opened ⟶ kitInterface arity opened .base :=
  kitValue arity (embedSource arity source) (embedSource_kitSupported arity opened source)

def kitBundle (opened : InstrumentObservations.Policy Symbols) (constructor : Symbols)
    (permission : opened constructor) (children : Fin (arity constructor) → InstrumentObservations.Tree Symbols arity) :
    kitOrigin arity opened ⟶ kitInterface arity opened (.arguments constructor) :=
  kitValue arity (bundle arity constructor (fun position => embedSource arity (children position)))
    (kitSupported_bundle arity opened constructor permission _
      (fun position => embedSource_kitSupported arity opened (children position)))

theorem kit_category_probe_step_iff (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (proper : SourceRule arity → Prop) (instrument : Probe Symbols arity)
    (permission : opened (instrumentConstructor arity instrument))
    (source : Value arity (receiver arity instrument)) (sourceSupported : KitSupported arity opened source)
    (target : Value arity (result arity instrument)) (targetSupported : KitSupported arity opened target) :
    ActIPO (kitCategoryRules arity Origins opened proper) (kitProbeContext arity opened instrument permission)
      (kitValue arity source sourceSupported) (kitValue arity target targetSupported) ↔
      ∃ occurrence : AdministrativeOccurrence arity Origins instrument,
        opened (instrumentConstructor arity instrument) ∧
          source = occurrence.instance_.body ∧ target = occurrence.instance_.output :=
  (kit_category_step_iff arity Origins opened proper _ _ _).trans
    (kit_probe_step_iff arity Origins opened proper instrument source target)

set_option backward.isDefEq.respectTransparency false in
theorem kit_category_bundle_children_related {Origins : Type w} (origin : Origins)
    (opened : InstrumentObservations.Policy Symbols) (proper : SourceRule arity → Prop)
    (constructor : Symbols) (permission : opened constructor)
    (first second : Fin (arity constructor) → InstrumentObservations.Tree Symbols arity)
    (related : IPOBisimilar (kitCategoryRules arity Origins opened proper)
      (kitBundle arity opened constructor permission first) (kitBundle arity opened constructor permission second))
    (position : Fin (arity constructor)) :
    IPOBisimilar (kitCategoryRules arity Origins opened proper)
      (kitSource arity opened (first position)) (kitSource arity opened (second position)) := by
  have step : ActIPO (kitCategoryRules arity Origins opened proper)
      (kitProbeContext arity opened (.get constructor position) permission)
      (kitBundle arity opened constructor permission first) (kitSource arity opened (first position)) :=
    (kit_category_probe_step_iff arity Origins opened proper (.get constructor position) permission _ _ _ _).mpr
      ⟨⟨origin, .get constructor position (fun index => embedSource arity (first index))⟩, permission, rfl, rfl⟩
  obtain ⟨matched, response, successors⟩ := ipoBisimilar_forward related step
  rcases matched with ⟨matchedArrow, matchedSupport⟩
  cases matchedArrow with
  | value target =>
    cases matchedSupport with
    | value targetSupported =>
      obtain ⟨occurrence, _, sourceRead, targetRead⟩ :=
        (kit_category_probe_step_iff arity Origins opened proper (.get constructor position)
          permission _ _ target targetSupported).mp response
      rcases occurrence with ⟨occurrenceOrigin, instance_⟩
      cases instance_ with
      | get _ _ supplied =>
        have argumentRead : (fun index => embedSource arity (second index)) = supplied := Term.node.inj sourceRead
        have resultRead : target = embedSource arity (second position) :=
          targetRead.trans (congrFun argumentRead position).symm
        cases resultRead
        exact successors

set_option backward.isDefEq.respectTransparency false in
theorem kit_category_opened_constructor_related {Origins : Type w} (origin : Origins)
    (opened : InstrumentObservations.Policy Symbols) (proper : SourceRule arity → Prop)
    (constructor : Symbols) (permission : opened constructor)
    (arguments : Fin (arity constructor) → InstrumentObservations.Tree Symbols arity)
    (other : InstrumentObservations.Tree Symbols arity)
    (related : IPOBisimilar (kitCategoryRules arity Origins opened proper)
      (kitSource arity opened (.node constructor arguments)) (kitSource arity opened other)) :
    ∃ compared : Fin (arity constructor) → InstrumentObservations.Tree Symbols arity,
      other = .node constructor compared ∧
        IPOBisimilar (kitCategoryRules arity Origins opened proper)
          (kitBundle arity opened constructor permission arguments) (kitBundle arity opened constructor permission compared) := by
  have step : ActIPO (kitCategoryRules arity Origins opened proper)
      (kitProbeContext arity opened (.ask constructor) permission)
      (kitSource arity opened (.node constructor arguments)) (kitBundle arity opened constructor permission arguments) :=
    (kit_category_probe_step_iff arity Origins opened proper (.ask constructor) permission _ _ _ _).mpr
      ⟨⟨origin, .ask constructor (fun position => embedSource arity (arguments position))⟩, permission, rfl, rfl⟩
  obtain ⟨matched, response, successors⟩ := ipoBisimilar_forward related step
  rcases matched with ⟨matchedArrow, matchedSupport⟩
  cases matchedArrow with
  | value target =>
    cases matchedSupport with
    | value targetSupported =>
      obtain ⟨occurrence, _, sourceRead, targetRead⟩ :=
        (kit_category_probe_step_iff arity Origins opened proper (.ask constructor)
          permission _ _ target targetSupported).mp response
      rcases occurrence with ⟨occurrenceOrigin, instance_⟩
      cases instance_ with
      | ask _ supplied =>
        obtain ⟨compared, otherRead, argumentRead⟩ := embedded_original_inversion arity constructor supplied other sourceRead
        cases targetRead
        cases argumentRead
        exact ⟨compared, otherRead, successors⟩

theorem kit_category_interactive_view {Origins : Type w} (origin : Origins)
    (opened : InstrumentObservations.Policy Symbols) (proper : SourceRule arity → Prop)
    (first second : InstrumentObservations.Tree Symbols arity)
    (related : IPOBisimilar (kitCategoryRules arity Origins opened proper)
      (kitSource arity opened first) (kitSource arity opened second)) :
    InstrumentObservations.view opened first = InstrumentObservations.view opened second := by
  classical
  induction first generalizing second with
  | node constructor arguments inductionHypothesis =>
    by_cases permission : opened constructor
    · obtain ⟨compared, rfl, bundles⟩ := kit_category_opened_constructor_related arity origin opened proper
        constructor permission arguments second related
      simp only [InstrumentObservations.view, if_pos permission]
      congr 1
      funext position
      exact inductionHypothesis position (compared position)
        (kit_category_bundle_children_related arity origin opened proper constructor permission _ _ bundles position)
    · cases second with
      | node other compared =>
        by_cases otherPermission : opened other
        · obtain ⟨supplied, shape, _⟩ := kit_category_opened_constructor_related arity origin opened proper
            other otherPermission compared (.node constructor arguments) (ipoBisimilar_symm related)
          have same : constructor = other := congrArg
            (fun tree : InstrumentObservations.Tree Symbols arity => match tree with | .node head _ => head) shape
          exact (permission (same ▸ otherPermission)).elim
        · simp only [InstrumentObservations.view, if_neg permission, if_neg otherPermission]

theorem kit_category_interactive_reconstruction {Origins : Type w} (origin : Origins)
    (opened : InstrumentObservations.Policy Symbols) (proper : SourceRule arity → Prop)
    (first second : InstrumentObservations.Tree Symbols arity) (complete : FullyOpened arity opened first)
    (related : IPOBisimilar (kitCategoryRules arity Origins opened proper)
      (kitSource arity opened first) (kitSource arity opened second)) : first = second := by
  induction first generalizing second with
  | node constructor arguments inductionHypothesis =>
    obtain ⟨compared, rfl, bundles⟩ := kit_category_opened_constructor_related arity origin opened proper
      constructor complete.1 arguments second related
    congr 1
    funext position
    exact inductionHypothesis position (compared position) (complete.2 position)
      (kit_category_bundle_children_related arity origin opened proper constructor complete.1 _ _ bundles position)

theorem kit_category_interactive_iff_equal (Origins : Type w) [Nonempty Origins]
    (opened : InstrumentObservations.Policy Symbols) (proper : SourceRule arity → Prop)
    (first second : InstrumentObservations.Tree Symbols arity) (complete : FullyOpened arity opened first) :
    IPOBisimilar (kitCategoryRules arity Origins opened proper)
      (kitSource arity opened first) (kitSource arity opened second) ↔ first = second := by
  constructor
  · exact kit_category_interactive_reconstruction arity (Classical.choice inferInstance) opened proper first second complete
  · intro same
    subst second
    exact ipoBisimilar_refl _ _

theorem kit_category_interactive_partial_tests (Origins : Type w) [Nonempty Origins]
    (kit : List Symbols) (proper : SourceRule arity → Prop)
    (first second : InstrumentObservations.Tree Symbols arity)
    (related : IPOBisimilar (kitCategoryRules arity Origins (fun constructor => constructor ∈ kit) proper)
      (kitSource arity (fun constructor => constructor ∈ kit) first)
      (kitSource arity (fun constructor => constructor ∈ kit) second)) :
    InstrumentObservations.LogicallyEquivalent (fun constructor => constructor ∈ kit) first second :=
  (InstrumentObservations.logicallyEquivalent_iff_view kit first second).mpr
    (kit_category_interactive_view arity (Classical.choice inferInstance) _ proper first second related)

end Mettapedia.OSLF.Framework.InstrumentCutContexts
