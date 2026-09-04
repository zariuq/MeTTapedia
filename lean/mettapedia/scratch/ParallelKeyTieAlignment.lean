import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

namespace Mettapedia.OSLF.MeTTaIL.PatternCode

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem sortPatternsBy_forall₂_of_key_perm_of_cross_ties
    {Key : Type} [LinearOrder Key]
    {relation : Pattern → Pattern → Prop}
    (key : Pattern → Key) {left right : List Pattern}
    (keyPermutation : List.Perm (left.map key) (right.map key))
    (ties : ∀ {leftPattern rightPattern}, leftPattern ∈ left →
      rightPattern ∈ right → key leftPattern = key rightPattern →
        relation leftPattern rightPattern) :
    List.Forall₂ relation (sortPatternsBy key left)
      (sortPatternsBy key right) := by
  have sortedKeys :
      (sortPatternsBy key left).map key =
        (sortPatternsBy key right).map key := by
    have leftMap :
        (sortPatternsBy key left).map key =
          (left.map key).mergeSort (fun first second => decide (first ≤ second)) := by
      unfold sortPatternsBy
      rw [List.map_mergeSort]
      intro first _ second _
      rfl
    have rightMap :
        (sortPatternsBy key right).map key =
          (right.map key).mergeSort
            (fun first second => decide (first ≤ second)) := by
      unfold sortPatternsBy
      rw [List.map_mergeSort]
      intro first _ second _
      rfl
    rw [leftMap, rightMap]
    let ordered : Key → Key → Prop := fun first second => first ≤ second
    letI : Std.Total ordered := ⟨fun first second => le_total first second⟩
    letI : IsTrans Key ordered := ⟨fun _ _ _ => le_trans⟩
    letI : Std.Antisymm ordered := ⟨fun _ _ => le_antisymm⟩
    apply List.Perm.eq_of_pairwise' (r := ordered)
    · simpa [ordered] using
        (List.pairwise_mergeSort' ordered (left.map key))
    · simpa [ordered] using
        (List.pairwise_mergeSort' ordered (right.map key))
    · exact (List.mergeSort_perm (left.map key) _).trans
        (keyPermutation.trans (List.mergeSort_perm (right.map key) _).symm)
  have leftMembership : ∀ pattern ∈ sortPatternsBy key left,
      pattern ∈ left := by
    intro pattern membership
    exact (sortPatternsBy_perm key left).mem_iff.mp membership
  have rightMembership : ∀ pattern ∈ sortPatternsBy key right,
      pattern ∈ right := by
    intro pattern membership
    exact (sortPatternsBy_perm key right).mem_iff.mp membership
  have build : ∀ (leftSorted rightSorted : List Pattern),
      leftSorted.map key = rightSorted.map key →
      (∀ pattern ∈ leftSorted, pattern ∈ left) →
      (∀ pattern ∈ rightSorted, pattern ∈ right) →
      List.Forall₂ relation leftSorted rightSorted := by
    intro leftSorted
    induction leftSorted with
    | nil =>
        intro rightSorted keyEq _ _
        cases rightSorted with
        | nil => exact .nil
        | cons rightHead rightTail => simp at keyEq
    | cons leftHead leftTail inductionHypothesis =>
        intro rightSorted keyEq leftMem rightMem
        cases rightSorted with
        | nil => simp at keyEq
        | cons rightHead rightTail =>
            simp only [List.map_cons, List.cons.injEq] at keyEq
            exact .cons
              (ties (leftMem leftHead (by simp))
                (rightMem rightHead (by simp)) keyEq.1)
              (inductionHypothesis rightTail keyEq.2
                (fun pattern membership => leftMem pattern (by
                  simp [membership]))
                (fun pattern membership => rightMem pattern (by
                  simp [membership])))
  exact build _ _ sortedKeys leftMembership rightMembership

theorem sortPatternsBy_forall₂_of_perm_of_cross_ties
    {Key : Type} [LinearOrder Key]
    {relation : Pattern → Pattern → Prop}
    (key : Pattern → Key) {left right : List Pattern}
    (permutation : List.Perm left right)
    (ties : ∀ {leftPattern rightPattern}, leftPattern ∈ left →
      rightPattern ∈ right → key leftPattern = key rightPattern →
        relation leftPattern rightPattern) :
    List.Forall₂ relation (sortPatternsBy key left)
      (sortPatternsBy key right) := by
  apply sortPatternsBy_forall₂_of_key_perm_of_cross_ties key
    (permutation.map key)
  exact ties

end Mettapedia.OSLF.MeTTaIL.PatternCode

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace CostStaticAtomKeyCospan

theorem CommonRestorationApex.Permutation.semanticKey_perm
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl} {depth : Nat}
    {left right : List Pattern}
    (alignment : CommonRestorationApex.Permutation
      (source := source) cospan declaration depth left right) :
    List.Perm
      (left.map (cospan.commonSemanticPatternKeyAt source depth))
      (right.map (cospan.commonSemanticPatternKeyAt source depth)) := by
  have restored := alignment.restored_perm
  have coded := restored.map
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
  unfold commonSemanticPatternKeyAt
  simpa only [List.map_map, Function.comp_def] using coded

theorem substituteAt_collapseParallel_sortPatternsBy_eq_of_perm_of_cross_ties
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (keyDepth restorationDepth : Nat) {left right : List Pattern}
    (keyPermutation : List.Perm
      (left.map (cospan.commonSemanticPatternKeyAt source keyDepth))
      (right.map (cospan.commonSemanticPatternKeyAt source keyDepth)))
    (ties : ∀ {leftPattern rightPattern}, leftPattern ∈ left →
      rightPattern ∈ right →
      cospan.commonSemanticPatternKeyAt source keyDepth leftPattern =
        cospan.commonSemanticPatternKeyAt source keyDepth rightPattern →
      ReflectiveContextSupport.RestoresTogether
        source.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment leftPattern rightPattern) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment restorationDepth
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel declaration
          (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
            (cospan.commonSemanticPatternKeyAt source keyDepth) left)) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment restorationDepth
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel declaration
          (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
            (cospan.commonSemanticPatternKeyAt source keyDepth) right)) := by
  let key := cospan.commonSemanticPatternKeyAt source keyDepth
  let relation := ReflectiveContextSupport.RestoresTogether
    source.costWholeReflectionProfile cospan.commonSupport
      cospan.commonAssignment
  have aligned : List.Forall₂ relation
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key left)
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key right) :=
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_forall₂_of_key_perm_of_cross_ties
      key (by simpa [key] using keyPermutation) (by
        intro leftPattern rightPattern leftMem rightMem keyEq
        exact ties leftMem rightMem (by simpa [key] using keyEq))
  have restoreAligned : ∀ {leftPatterns rightPatterns : List Pattern},
      List.Forall₂ relation leftPatterns rightPatterns →
      leftPatterns.map
          (ReflectiveContextSupport.substituteAt
            source.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment restorationDepth) =
        rightPatterns.map
          (ReflectiveContextSupport.substituteAt
            source.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment restorationDepth) := by
    intro leftPatterns rightPatterns related
    induction related with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        exact congrArg₂ List.cons (head restorationDepth) inductionHypothesis
  have restored :
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key left).map
          (ReflectiveContextSupport.substituteAt
            source.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment restorationDepth) =
        (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key right).map
          (ReflectiveContextSupport.substituteAt
            source.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment restorationDepth) := by
    exact restoreAligned aligned
  rw [cospan.substituteAt_collapseParallel source restorationDepth declaration,
    cospan.substituteAt_collapseParallel source restorationDepth declaration]
  exact congrArg
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel declaration)
    (by simpa [key] using restored)

theorem CommonRestorationApex.parallel_at_keyDepth_of_perm_of_cross_ties
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (keyDepth restorationDepth : Nat) {leftElements rightElements : List Pattern}
    (keyPermutation : List.Perm
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents declaration
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt source)
          declaration keyDepth leftElements)).map
            (cospan.commonSemanticPatternKeyAt source keyDepth))
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents declaration
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt source)
          declaration keyDepth rightElements)).map
            (cospan.commonSemanticPatternKeyAt source keyDepth)))
    (ties : ∀ {leftPattern rightPattern},
      leftPattern ∈ Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt source)
          declaration keyDepth leftElements) →
      rightPattern ∈ Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt source)
          declaration keyDepth rightElements) →
      cospan.commonSemanticPatternKeyAt source keyDepth leftPattern =
        cospan.commonSemanticPatternKeyAt source keyDepth rightPattern →
      ReflectiveContextSupport.RestoresTogether
        source.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment leftPattern rightPattern) :
    CommonRestorationApex source cospan declaration restorationDepth
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (cospan.commonSemanticPatternKeyAt source)
        declaration keyDepth
        (.collection declaration.parallelCollection leftElements none))
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (cospan.commonSemanticPatternKeyAt source)
        declaration keyDepth
        (.collection declaration.parallelCollection rightElements none)) := by
  apply CommonRestorationApex.leafAligned
  apply PatternLeafAligned.leaf
  intro depth
  simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt,
    beq_self_eq_true, if_true]
  exact
    substituteAt_collapseParallel_sortPatternsBy_eq_of_perm_of_cross_ties
      cospan declaration keyDepth depth keyPermutation ties

end CostStaticAtomKeyCospan
end Mettapedia.GSLT.LanguageDef
