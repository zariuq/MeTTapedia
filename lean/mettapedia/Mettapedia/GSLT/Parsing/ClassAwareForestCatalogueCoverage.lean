import Mettapedia.GSLT.Parsing.ClassAwareForestCatalogue

/-! The selected catalogue covers the original ParserPack certificates
present in a complete forest. All family premises and child seams come from
the original replay relation, independently of catalogue execution. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareForestCatalogue

open ClassAwarePackedForest ClassAwarePackedForestKBest
open ClassAwareParserPackCertificate ClassAwareParserPackCorrespondence
open PackedForestCatalogue ParserProfileSemantics PresentationExprSemantics

mutual
  theorem replay_unfolds {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {sort : String} {start stop : Nat} {tree : CST} {certificate : Certificate}
      (forest : Forest) (allow : Family → Bool)
      (replayed : Replays profile plan input certificate sort start stop tree)
      (present : ∀ family ∈ certificateFamilies sort certificate, family ∈ forest.families)
      (selected : ∀ family ∈ certificateFamilies sort certificate, allow family = true) :
      PackedForestCatalogue.Unfolds (familiesAt forest) (fun family => nodeChildren family.children) allow
        ⟨sort, start, stop⟩ (ofCertificate sort certificate) :=
    match replayed with
    | .lexical position valid matcherExact sortExact labelExact matched => by
      simp only [ofCertificate]
      apply PackedForestCatalogue.Unfolds.node
      · apply (family_at_iff _ _ _).mpr
        exact ⟨present _ (by simp [certificateFamilies]), rfl⟩
      · exact selected _ (by simp [certificateFamilies])
      · exact .nil
    | .structural position valid sortExact labelExact body => by
      simp only [ofCertificate]
      apply PackedForestCatalogue.Unfolds.node
      · apply (family_at_iff _ _ _).mpr
        exact ⟨present _ (by simp [certificateFamilies]), rfl⟩
      · exact selected _ (by simp [certificateFamilies])
      · exact replay_items forest allow body
          (fun family member => present family (by simpa [certificateFamilies] using Or.inr member))
          (fun family member => selected family (by simpa [certificateFamilies] using Or.inr member))
    termination_by structural replayed

  theorem replay_items {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {items : List PackItem} {start stop : Nat} {values : List CST} {body : ItemsCertificate}
      (forest : Forest) (allow : Family → Bool)
      (replayed : ItemsReplays profile plan input body items start stop values)
      (present : ∀ family ∈ itemsFamilies body, family ∈ forest.families)
      (selected : ∀ family ∈ itemsFamilies body, allow family = true) :
      ChildrenUnfold (familiesAt forest) (fun family => nodeChildren family.children) allow
        (nodeChildren (itemsChildRefs body)) (ofItems body) :=
    match replayed with
    | .nil => .nil
    | .terminal matched rest => by
      simp only [itemsChildRefs, nodeChildren, ofItems, List.filterMap_cons]
      exact replay_items forest allow rest present selected
    | .nonterminal head rest => by
      simp only [itemsChildRefs, nodeChildren, ofItems, List.filterMap_cons]
      apply ChildrenUnfold.cons
      · exact replay_unfolds forest allow head
          (fun family member => present family (by simp only [itemsFamilies, List.mem_append]; exact Or.inl member))
          (fun family member => selected family (by simp only [itemsFamilies, List.mem_append]; exact Or.inl member))
      · exact replay_items forest allow rest
          (fun family member => present family (by simp only [itemsFamilies, List.mem_append]; exact Or.inr member))
          (fun family member => selected family (by simp only [itemsFamilies, List.mem_append]; exact Or.inr member))
    termination_by structural replayed
end

theorem certificate_covered {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {sort : String} {start stop : Nat} {tree : CST} {certificate : Certificate}
    (forest : Forest) (allow : Family → Bool) (rounds : Nat) (store : Store)
    (finished : catalogue? forest allow rounds = some store)
    (replayed : Replays profile plan input certificate sort start stop tree)
    (present : ClassAwarePackedForest.Unfolds forest sort certificate)
    (selected : ∀ family ∈ certificateFamilies sort certificate, allow family = true) :
    certificate ∈ (lookup store ⟨sort, start, stop⟩).filterMap restore := by
  apply List.mem_filterMap.mpr
  exact ⟨ofCertificate sort certificate,
    (catalogue?_exact forest allow rounds store finished _ _).mpr (replay_unfolds forest allow replayed present selected),
    restore_replayed replayed⟩

#print axioms replay_unfolds
#print axioms certificate_covered

end Mettapedia.GSLT.Parsing.ClassAwareForestCatalogue
