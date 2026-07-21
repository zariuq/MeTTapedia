import Mettapedia.GSLT.Parsing.GroundedChart

/-!
# Certified packed-backend correspondence

The grounded chart is a complete finite reference scheduler.  Optimized GLL
and GLR engines may use different descriptor orders, GSS layouts, and local
packing strategies.  Their trust boundary is therefore extensional: every
root and family in the complete reference forest must occur in the emitted
backend forest.

Extra backend data is harmless because accepted results still require
independent certificate replay against the compiled presentation.  Missing
reference data is rejected because it could lose a source parse.
-/

namespace Mettapedia.GSLT.Parsing.BackendCorrespondence

open CompilerCorrespondence GuardCorrespondence PackedForest GroundedChart
open Mettapedia.Logic.LP

/-- A backend forest retains every root and packed family of a reference
forest.  It may contain additional administrative or unreachable data. -/
structure ForestCovers (reference backend : Forest) : Prop where
  roots : ∀ root, root ∈ reference.roots → root ∈ backend.roots
  families : ∀ family, family ∈ reference.families → family ∈ backend.families

def familyChildNodes (family : Family) : List NodeKey :=
  family.children.filterMap fun child =>
    match child with
    | .terminal _ _ _ => none
    | .node key => some key

def reachabilityRule (parent child : NodeKey) : PropRule NodeKey :=
  { premises := {parent}, head := child }

def reachabilityProgram (forest : Forest) : PropProgram NodeKey :=
  (forest.families.flatMap fun family =>
    (familyChildNodes family).map (reachabilityRule family.parent)).toFinset

def reachableNodes (forest : Forest) : Finset NodeKey :=
  FiniteHornSaturation.saturate
    (reachabilityProgram forest) forest.roots.toFinset

/-- Remove chart families that cannot occur below any accepted root. -/
def rootReachableForest (forest : Forest) : Forest :=
  { roots := forest.roots
    families := forest.families.filter
      fun family => family.parent ∈ reachableNodes forest }

theorem root_mem_reachableNodes
    {forest : Forest} {root : NodeKey}
    (member : root ∈ forest.roots) :
    root ∈ reachableNodes forest := by
  apply FiniteHornSaturation.saturate_contains_facts
    (program := reachabilityProgram forest) (facts := forest.roots.toFinset)
  simpa using member

theorem child_mem_reachableNodes
    {forest : Forest} {family : Family} {child : NodeKey}
    (familyMember : family ∈ forest.families)
    (parentReachable : family.parent ∈ reachableNodes forest)
    (childMember : child ∈ familyChildNodes family) :
    child ∈ reachableNodes forest := by
  apply FiniteHornSaturation.saturate_rule_closed
    (program := reachabilityProgram forest) (facts := forest.roots.toFinset)
    (rule := reachabilityRule family.parent child)
  · unfold reachabilityProgram
    simp only [List.mem_toFinset]
    apply List.mem_flatMap.mpr
    refine ⟨family, familyMember, ?_⟩
    exact List.mem_map.mpr ⟨child, childMember, rfl⟩
  · intro premise premiseMember
    have premiseEq : premise = family.parent := by
      simpa [reachabilityRule] using premiseMember
    subst premise
    exact parentReachable

theorem certificate_unfolds_rootReachable
    {forest : Forest} {certificate : Certificate} {key : NodeKey}
    (keyEq : certificateKey certificate = some key)
    (keyReachable : key ∈ reachableNodes forest)
    (unfolds : Unfolds forest certificate) :
    Unfolds (rootReachableForest forest) certificate := by
  let CertMotive : Certificate → Prop := fun current =>
    ∀ currentKey,
      certificateKey current = some currentKey →
      currentKey ∈ reachableNodes forest →
      Unfolds forest current →
      Unfolds (rootReachableForest forest) current
  let ChildrenMotive : List Certificate → Prop := fun currentChildren =>
    ∀ child, child ∈ currentChildren → CertMotive child
  have terminalCase : ∀ codepoint start stop,
      CertMotive (.terminal codepoint start stop) := by
    intro codepoint start stop currentKey currentKeyEq
    simp [certificateKey] at currentKeyEq
  have nodeCase : ∀ sourceRule category start stop children,
      ChildrenMotive children →
      CertMotive (.node sourceRule category start stop children) := by
    intro sourceRule category start stop children childrenComplete
      currentKey currentKeyEq currentKeyReachable currentUnfolds
    simp only [certificateKey, Option.some.injEq] at currentKeyEq
    subst currentKey
    let parent : NodeKey :=
      { category := category, start := start, stop := stop }
    let rootFamily : Family :=
      { parent := parent, sourceRule := sourceRule,
        children := children.map certificateRef }
    have rootFamilyMember : rootFamily ∈ forest.families := by
      apply currentUnfolds
      simp [certificateFamilies, certificateFamily, rootFamily, parent]
    have childUnfolds : ∀ child, child ∈ children → Unfolds forest child := by
      intro child childMember family familyMember
      apply currentUnfolds family
      simp only [certificateFamilies, certificateFamily, Option.toList_some,
        List.singleton_append, List.mem_cons]
      right
      exact mem_certificatesFamilies_iff.mpr
        ⟨child, childMember, familyMember⟩
    intro family familyMember
    simp only [certificateFamilies, certificateFamily, Option.toList_some,
      List.singleton_append, List.mem_cons] at familyMember
    rcases familyMember with rootEq | descendant
    · subst family
      simp only [rootReachableForest, List.mem_filter]
      exact ⟨rootFamilyMember,
        by simpa [rootFamily, parent] using currentKeyReachable⟩
    · obtain ⟨child, childMember, childFamilyMember⟩ :=
        mem_certificatesFamilies_iff.mp descendant
      cases child with
      | terminal codepoint childStart childStop =>
          simp [certificateFamilies] at childFamilyMember
      | node childRule childCategory childStart childStop grandchildren =>
          let childKey : NodeKey :=
            { category := childCategory, start := childStart,
              stop := childStop }
          have childInFamily : childKey ∈ familyChildNodes rootFamily := by
            apply List.mem_filterMap.mpr
            refine ⟨.node childKey, ?_, rfl⟩
            apply List.mem_map.mpr
            exact ⟨.node childRule childCategory childStart childStop grandchildren,
              childMember, by simp [certificateRef, childKey]⟩
          have childReachable := child_mem_reachableNodes rootFamilyMember
            (by simpa [parent] using currentKeyReachable) childInFamily
          have childPruned := childrenComplete
            (.node childRule childCategory childStart childStop grandchildren)
            childMember childKey rfl childReachable
            (childUnfolds _ childMember)
          exact childPruned _ childFamilyMember
  have nilCase : ChildrenMotive [] := by
    intro child childMember
    simp at childMember
  have consCase : ∀ childHead tail,
      CertMotive childHead → ChildrenMotive tail →
      ChildrenMotive (childHead :: tail) := by
    intro childHead tail headComplete tailComplete requested requestedMember
    simp only [List.mem_cons] at requestedMember
    rcases requestedMember with rfl | tailMember
    · exact headComplete
    · exact tailComplete requested tailMember
  exact Certificate.rec
    (motive_1 := CertMotive) (motive_2 := ChildrenMotive)
    terminalCase nodeCase nilCase consCase certificate
    key keyEq keyReachable unfolds

theorem rootUnfolds_rootReachable
    {forest : Forest} {certificate : Certificate}
    (unfolds : RootUnfolds forest certificate) :
    RootUnfolds (rootReachableForest forest) certificate := by
  obtain ⟨key, keyEq, rootMember, familyUnfolds⟩ := unfolds
  have reachable := root_mem_reachableNodes rootMember
  exact ⟨key, keyEq, by simpa [rootReachableForest] using rootMember,
    certificate_unfolds_rootReachable keyEq reachable familyUnfolds⟩

theorem rootReachable_complete
    {forest : Forest}
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint}
    (complete : Complete forest presentation input) :
    Complete (rootReachableForest forest) presentation input := by
  intro tree derivation
  obtain ⟨certificate, replay⟩ := complete tree derivation
  exact ⟨certificate, rootUnfolds_rootReachable replay.1, replay.2⟩

theorem rootReachable_grammar_complete
    {forest : Forest} {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint}
    (complete : GrammarComplete forest grammar input) :
    GrammarComplete (rootReachableForest forest) grammar input := by
  intro tree derivation
  obtain ⟨certificate, replay⟩ := complete tree derivation
  exact ⟨certificate, rootUnfolds_rootReachable replay.1, replay.2⟩

def validateForestCovers (reference backend : Forest) : Bool :=
  reference.roots.all (· ∈ backend.roots) &&
    reference.families.all (· ∈ backend.families)

theorem validateForestCovers_sound
    {reference backend : Forest}
    (accepted : validateForestCovers reference backend = true) :
    ForestCovers reference backend := by
  simp only [validateForestCovers, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at accepted
  exact ⟨accepted.1, accepted.2⟩

theorem validateForestCovers_complete
    {reference backend : Forest}
    (covers : ForestCovers reference backend) :
    validateForestCovers reference backend = true := by
  simp only [validateForestCovers, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  exact ⟨covers.roots, covers.families⟩

theorem validateForestCovers_iff
    {reference backend : Forest} :
    validateForestCovers reference backend = true ↔
      ForestCovers reference backend :=
  ⟨validateForestCovers_sound, validateForestCovers_complete⟩

theorem unfolds_of_covers
    {reference backend : Forest}
    (covers : ForestCovers reference backend)
    {certificate : Certificate}
    (unfolds : Unfolds reference certificate) :
    Unfolds backend certificate := by
  intro family familyMember
  exact covers.families family (unfolds family familyMember)

theorem rootUnfolds_of_covers
    {reference backend : Forest}
    (covers : ForestCovers reference backend)
    {certificate : Certificate}
    (unfolds : RootUnfolds reference certificate) :
    RootUnfolds backend certificate := by
  obtain ⟨key, keyEq, rootMember, families⟩ := unfolds
  exact ⟨key, keyEq, covers.roots key rootMember,
    unfolds_of_covers covers families⟩

theorem packedReplays_of_covers
    {reference backend : Forest}
    (covers : ForestCovers reference backend)
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint} {certificate : Certificate} {tree : ParseTree}
    (replay : PackedReplays reference presentation input certificate tree) :
    PackedReplays backend presentation input certificate tree :=
  ⟨rootUnfolds_of_covers covers replay.1, replay.2⟩

theorem complete_of_covers
    {reference backend : Forest}
    (covers : ForestCovers reference backend)
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint}
    (complete : Complete reference presentation input) :
    Complete backend presentation input := by
  intro tree derivation
  obtain ⟨certificate, replay⟩ := complete tree derivation
  exact ⟨certificate, packedReplays_of_covers covers replay⟩

theorem grammarComplete_of_covers
    {reference backend : Forest}
    (covers : ForestCovers reference backend)
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint}
    (complete : GrammarComplete reference grammar input) :
    GrammarComplete backend grammar input := by
  intro tree derivation
  obtain ⟨certificate, rootUnfolds, replay⟩ := complete tree derivation
  exact ⟨certificate, rootUnfolds_of_covers covers rootUnfolds, replay⟩

theorem backend_grammar_complete_of_chart_coverage
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {backend : Forest}
    (covers : ForestCovers
      (rootReachableForest (GroundedChart.chartForest grammar input))
      backend) :
    GrammarComplete backend grammar input :=
  grammarComplete_of_covers covers
    (rootReachable_grammar_complete
      (GroundedChart.chartForest_grammar_complete grammar input))

theorem backend_grammar_result_set_agreement
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {backend : Forest}
    (covers : ForestCovers
      (rootReachableForest (GroundedChart.chartForest grammar input))
      backend) :
    grammarPackedResults backend grammar input =
      GuardCorrespondence.grammarResults grammar input :=
  grammar_complete_result_set_agreement
    (backend_grammar_complete_of_chart_coverage covers)

theorem backend_grammar_ambiguity_agreement
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {backend : Forest}
    (covers : ForestCovers
      (rootReachableForest (GroundedChart.chartForest grammar input))
      backend) :
    PackedForest.Ambiguous (grammarPackedResults backend grammar input) ↔
      PackedForest.Ambiguous
        (GuardCorrespondence.grammarResults grammar input) :=
  grammar_complete_ambiguity_agreement
    (backend_grammar_complete_of_chart_coverage covers)

theorem backend_complete_of_chart_coverage
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint} {backend : Forest}
    (covers : ForestCovers
      (rootReachableForest
        (GroundedChart.chartForest
          (GuardCorrespondence.compile presentation) input))
      backend) :
    Complete backend presentation input :=
  complete_of_covers covers
    (rootReachable_complete
      (GroundedChart.chartForest_complete presentation input))

theorem backend_result_set_agreement
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint} {backend : Forest}
    (covers : ForestCovers
      (rootReachableForest
        (GroundedChart.chartForest
          (GuardCorrespondence.compile presentation) input))
      backend) :
    packedResults backend presentation input =
      GuardCorrespondence.sourceResults presentation input :=
  complete_result_set_agreement
    (backend_complete_of_chart_coverage covers)

theorem backend_ambiguity_agreement
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint} {backend : Forest}
    (covers : ForestCovers
      (rootReachableForest
        (GroundedChart.chartForest
          (GuardCorrespondence.compile presentation) input))
      backend) :
    PackedForest.Ambiguous (packedResults backend presentation input) ↔
      PackedForest.Ambiguous
        (GuardCorrespondence.sourceResults presentation input) :=
  complete_ambiguity_agreement
    (backend_complete_of_chart_coverage covers)

/-- Any two packed engines covering the same complete chart agree on the
entire parse-tree may-set, even if their internal forest layouts differ. -/
theorem backends_result_set_agree
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint} {left right : Forest}
    (leftCovers : ForestCovers
      (rootReachableForest
        (GroundedChart.chartForest
          (GuardCorrespondence.compile presentation) input))
      left)
    (rightCovers : ForestCovers
      (rootReachableForest
        (GroundedChart.chartForest
          (GuardCorrespondence.compile presentation) input))
      right) :
    packedResults left presentation input =
      packedResults right presentation input :=
  complete_forests_result_set_agreement
    (backend_complete_of_chart_coverage leftCovers)
    (backend_complete_of_chart_coverage rightCovers)

/-! ## Executable controls -/

def controlReference : Forest :=
  rootReachableForest
    (GroundedChart.chartForest GroundedChart.controlGrammar [97])

def controlBackend : Forest :=
  { roots := controlReference.roots
    families := controlReference.families.reverse }

def missingAlternativeBackend : Forest :=
  { roots := controlReference.roots
    families := controlReference.families.take 1 }

theorem reordered_backend_covers :
    validateForestCovers controlReference controlBackend = true := by
  decide

theorem missing_alternative_rejected :
    validateForestCovers controlReference missingAlternativeBackend = false := by
  decide

theorem reordered_backend_result_set_agrees :
    packedResults controlBackend GroundedChart.controlPresentation [97] =
      GuardCorrespondence.sourceResults GroundedChart.controlPresentation [97] :=
  backend_result_set_agreement
    (validateForestCovers_sound reordered_backend_covers)

end Mettapedia.GSLT.Parsing.BackendCorrespondence
