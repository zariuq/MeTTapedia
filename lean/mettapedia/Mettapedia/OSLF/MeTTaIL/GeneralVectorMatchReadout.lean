import Mettapedia.OSLF.MeTTaIL.GeneralVectorMatchInstance
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderReadout
import Mathlib.Data.List.Perm.Basic

/-! Root-context readback for constructors and fixed vectors. Bag selection
retains a permutation decomposition and the actual captured remainder, so
equal resource values do not become reusable occurrences. These statements
consume the independent scoped matching judgment, not an enumerator. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax RuleBinding GeneralScopedMatch Match

mutual
  theorem vector_matching_readout {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {initial final chosen : ScopedRuleMatching.Assignment}
      {schema target : Pattern} (shape : VectorFirstOrder schema)
      (matched : Matches rule spec ambient site path 0 initial schema target final)
      (later : Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
      applyBindings (ordinary chosen) schema = target := by
    cases shape with
    | metavariable name =>
      cases matched with
      | capture stored =>
        have found := capture_ordinary_compatible stored later roots (name, target) (by simp)
        rw [apply_variable, found]
        rfl
    | constructor label arguments children =>
      cases matched with
      | constructor matchedArguments =>
        have read := vector_arguments_readout children matchedArguments later roots
        simpa only [applyBindings] using congrArg (Pattern.apply label) read
    | vector arguments children =>
      cases matched with
      | bag nonvector _ => exact (nonvector rfl).elim
      | vector matchedArguments =>
        have read := vector_arguments_readout children matchedArguments later roots
        simpa only [applyBindings, List.append_nil] using
          congrArg (fun values => Pattern.collection .vec values none) read
  termination_by sizeOf schema

  theorem vector_arguments_readout {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat}
      {site : RulePatternSite} {path : List Nat} {initial final chosen : ScopedRuleMatching.Assignment}
      {schemas targets : List Pattern} (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema)
      (matched : Arguments rule spec ambient site path 0 initial index schemas targets final)
      (later : Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
      schemas.map (applyBindings (ordinary chosen)) = targets := by
    cases schemas with
    | nil => cases matched; rfl
    | cons schema schemas =>
      cases matched with
      | cons head tail =>
        have first := vector_matching_readout (shapes schema List.mem_cons_self)
          head (tail.extends.trans later) roots
        have rest := vector_arguments_readout
          (fun child member => shapes child (List.mem_cons_of_mem schema member)) tail later roots
        simp only [List.map_cons, first, rest]
  termination_by sizeOf schemas
end

theorem named_arguments_readout {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final chosen : ScopedRuleMatching.Assignment}
    (names : List String) (values : List Pattern)
    (matched : Arguments rule spec ambient site path 0 initial index (names.map Pattern.fvar) values final)
    (later : Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    List.Forall₂ (fun name value => (ordinary chosen).lookup name = some value) names values := by
  induction names generalizing values initial index with
  | nil => cases matched; exact .nil
  | cons name names ih =>
    cases matched with
    | @cons _ _ _ _ _ _ value _ middle _ first rest =>
      cases first with
      | capture stored =>
        have read := capture_ordinary_compatible stored (rest.extends.trans later) roots
          (name, value) List.mem_cons_self
        exact .cons read (ih _ rest)

theorem fixed_vector_arguments {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    {schemas targets : List Pattern}
    (matched : Matches rule spec ambient site path 0 initial
      (.collection .vec schemas none) (.collection .vec targets none) final) :
    Arguments rule spec ambient site path 0 initial 0 schemas targets final := by
  cases matched with
  | vector children => exact children
  | bag nonvector _ => exact (nonvector rfl).elim

/-- Matching fixed-vector/constructor heads into a bag consumes distinct
positions and reads its true residual in the retained final assignment. -/
theorem vector_bag_selection_readout {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final chosen : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
    {kind : CollType} {restName : String}
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema)
    (matched : Bag rule spec ambient site path 0 initial index schemas (some restName) kind targets final)
    (later : Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ residual,
      targets.Perm (schemas.map (applyBindings (ordinary chosen)) ++ residual) ∧
      (ordinary chosen).lookup restName = some (.collection kind residual none) := by
  induction schemas generalizing initial index targets with
  | nil =>
    cases matched with
    | rest captured =>
      have read := capture_ordinary_compatible captured later roots
        (restName, .collection kind targets none) (by simp)
      exact ⟨targets, by simp, read⟩
  | cons schema schemas ih =>
    cases matched with
    | cons selected within head tail =>
      obtain ⟨residual, conserved, restRead⟩ := ih
        (fun child member => shapes child (List.mem_cons_of_mem schema member)) tail
      have first := vector_matching_readout (shapes schema List.mem_cons_self)
        head (tail.extends.trans later) roots
      refine ⟨residual, ?_, restRead⟩
      rw [List.map_cons, List.cons_append, first]
      exact (List.getElem_cons_eraseIdx_perm within).symm.trans (conserved.cons _)

#print axioms vector_matching_readout
#print axioms vector_bag_selection_readout

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
