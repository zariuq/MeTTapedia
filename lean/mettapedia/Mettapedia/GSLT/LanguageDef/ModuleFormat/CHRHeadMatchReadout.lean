import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompiledHeadShape

/-! Actual scoped CHR request matches conserve the physical store's resource
occurrences. The selected terms are reconstructed from the compiled rule and
one retained assignment; the remainder is its captured bag, not a fresh
enumeration of equal values. Source value interpretation is a further law. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.HeadMatchReadout

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

theorem request_store_conservation (vocabulary : Vocabulary) (query activeSlot activeId : Nat)
    (source : Rule) (rule : RewriteRule) (known : List Pattern)
    (compiled : compileRule? vocabulary query activeSlot source = some rule)
    {spec : RuleBindingSpec} {ambient : Nat} {captured chosen : ScopedRuleMatching.Assignment}
    (matched : Matches rule spec ambient .left [] 0 [] rule.left
      (request vocabulary query activeId known) captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ selected residual,
      rule.left = .apply (queryLabel query) (poolPatterns vocabulary ++
        [.fvar "chr:active", .apply "ChrStore" [.collection .hashBag selected (some "chr:rest")]]) ∧
      known.Perm (selected.map (applyBindings (ordinary chosen)) ++ residual) ∧
      (ordinary chosen).lookup "chr:rest" = some (.collection .hashBag residual none) := by
  obtain ⟨selected, left, shapes⟩ := HeadShape.compiled_rule_heads vocabulary query activeSlot source rule compiled
  rw [left] at matched
  simp only [poolPatterns, request, List.cons_append, List.nil_append] at matched
  cases matched with
  | constructor arguments =>
    cases arguments with
    | cons predicates afterPredicates =>
      cases afterPredicates with
      | cons scalars afterScalars =>
        cases afterScalars with
        | cons active afterActive =>
          cases afterActive with
          | cons storeMatch endArgs =>
            cases endArgs
            cases storeMatch with
            | constructor storeArguments =>
              cases storeArguments with
              | cons bagMatch endArgs =>
                cases endArgs
                cases bagMatch with
                | bag _ bag =>
                  obtain ⟨residual, conserved, restRead⟩ := vector_bag_selection_readout shapes bag later roots
                  exact ⟨selected, residual, left, conserved, restRead⟩

#print axioms request_store_conservation

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.HeadMatchReadout
