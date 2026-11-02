import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClauseDictionary
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderReadout

/-! Pool readback is derived from the actual scoped match of InferSnapshot.
Later premise bindings retain those reads, so the source atom interpretation
uses the same relation and literal references as the native request. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.RequestReading

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch
open GeneralFirstOrderProjection

private theorem named_arguments {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final chosen : ScopedRuleMatching.Assignment}
    (names : List String) (values : List Pattern)
    (matched : Arguments rule spec ambient site path 0 initial index (names.map Pattern.fvar) values final)
    (later : GeneralScopedMatch.Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    List.Forall₂ (fun name value => (ordinary chosen).lookup name = some value) names values := by
  induction names generalizing values initial index with
  | nil =>
    cases matched
    exact .nil
  | cons name names ih =>
    cases matched with
    | @cons _ _ _ _ _ _ value _ middle _ first rest =>
      cases first with
      | capture stored =>
        have head := capture_ordinary_compatible stored (rest.extends.trans later) roots (name,value) List.mem_cons_self
        exact .cons head (ih _ rest)

private theorem vector_arguments {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    {schemas values : List Pattern}
    (matched : Matches rule spec ambient site path 0 initial
      (.collection .vec schemas none) (.collection .vec values none) final) :
    Arguments rule spec ambient site path 0 initial 0 schemas values final := by
  cases matched with
  | vector children => exact children
  | bag nonvector _ => exact (nonvector rfl).elim

theorem physical_pools (pools : Join.Pools) {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {captured completed : ScopedRuleMatching.Assignment}
    (matched : Matches rule spec ambient .left [] 0 []
      (.apply "InferSnapshot" [Join.poolPattern (Join.relationSlots pools),Join.poolPattern (Join.literalSlots pools)])
      (Executable.request pools) captured)
    (later : GeneralScopedMatch.Extends captured completed)
    (roots : GeneralPremise.RootValues ambient completed) :
    (∀ index, index < pools.relations.length →
      (ordinary completed).lookup (Join.relationSlot index) = some (Executable.relationRef index)) ∧
    (∀ index, index < pools.literals.length →
      (ordinary completed).lookup (Join.literalSlot index) = some (Executable.valueRef index)) := by
  change Matches rule spec ambient .left [] 0 []
    (.apply "InferSnapshot" [Join.vector ((Join.relationSlots pools).map Pattern.fvar),
      Join.vector ((Join.literalSlots pools).map Pattern.fvar)])
    (.apply "InferSnapshot" [Join.vector ((List.range pools.relations.length).map Executable.relationRef),
      Join.vector ((List.range pools.literals.length).map Executable.valueRef)]) captured at matched
  cases matched with
  | constructor arguments =>
    cases arguments with
    | cons relationMatch remaining =>
      cases remaining with
      | cons literalMatch last =>
        cases last
        have relationValues := named_arguments (Join.relationSlots pools)
          ((List.range pools.relations.length).map Executable.relationRef)
          (vector_arguments relationMatch) (literalMatch.extends.trans later) roots
        have literalValues := named_arguments (Join.literalSlots pools)
          ((List.range pools.literals.length).map Executable.valueRef)
          (vector_arguments literalMatch) later roots
        constructor
        · intro index bound
          have selected := relationValues.get (by simpa [Join.relationSlots] using bound) (by simpa using bound)
          simpa [Join.relationSlots] using selected
        · intro index bound
          have selected := literalValues.get (by simpa [Join.literalSlots] using bound) (by simpa using bound)
          simpa [Join.literalSlots] using selected

theorem request_pools (pools : Join.Pools) {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {captured completed : ScopedRuleMatching.Assignment}
    (matched : Matches rule spec ambient .left [] 0 []
      (.apply "InferSnapshot" [Join.poolPattern (Join.relationSlots pools),Join.poolPattern (Join.literalSlots pools)])
      (Executable.request pools) captured)
    (later : GeneralScopedMatch.Extends captured completed)
    (roots : GeneralPremise.RootValues ambient completed) :
    ClauseReading.PoolsRead pools (ClauseDictionary.expand pools (ordinary completed)) := by
  obtain ⟨relations,literals⟩ := physical_pools pools matched later roots
  exact ClauseDictionary.pools_read pools (ordinary completed)
    (fun index _ present => relations index (List.getElem?_eq_some_iff.mp present).1)
    (fun index _ present => literals index (List.getElem?_eq_some_iff.mp present).1)

#print axioms physical_pools
#print axioms request_pools

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.RequestReading
