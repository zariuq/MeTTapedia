import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorQuadrantCanary

/-!
# Q6: the dual-nonempty-boundary cospan canary

Pair: `A = @b(*b(@w{0w}))` (one wrapped boundary) versus
`B = @b(*b(@b(*b(@w{0w}))))` (same wrapped boundary, one base shell deeper).
Both roots collapse at the base declaration; both boundary tables are
non-empty.  This is the smallest same-view-colour dual-nonempty cospan.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ClaudeDualBoundary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderCrossColorReachedCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorQuadrantCanary

/-- `B`'s well-sortedness at the shared Name sort. -/
theorem deepWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [] nameType leftPattern := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [leftPattern, reachedPattern, rightPattern, binderSafeAt,
    binderSafeListAt]

/-- Canonical equality at the base declaration: the extra base shell
evaporates. -/
theorem dual_pair_canonical :
    canonicalize declaration reachedPattern =
      canonicalize declaration leftPattern := by decide

/-- Both roots collapse at the base declaration. -/
theorem dual_collapsing_left : CollapsingRoot declaration reachedPattern :=
  Or.inl ⟨_, rfl⟩

theorem dual_collapsing_right : CollapsingRoot declaration leftPattern :=
  Or.inl ⟨_, rfl⟩

/-- The deep endpoint's built tree. -/
noncomputable def deepTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty [] [] leftPattern
      nameType :=
  (CostRegionTree.build? [] [] leftPattern nameType).get
    (CostRegionTree.build?_isSome_of_wellSorted deepWellSorted)

theorem deepTree_rootIsStatic : deepTree.rootIsStatic = true := by decide

noncomputable def deepViewPair : Σ color, deepTree.StaticRootView color :=
  deepTree.staticRootView_of_rootIsStatic deepTree_rootIsStatic

/-- Same view colour on both sides: base. -/
theorem deepViewPair_color : deepViewPair.1 = .base := by decide

/-- The deep side's semantic atom environment. -/
noncomputable def deepEnv :=
  CostStaticAtomEnvironment.ofInventory
    (deepViewPair.2.node.semanticAtomEnvironment
      (deepViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

/-- One boundary entry on the deep side too. -/
theorem deepEntries_length :
    deepViewPair.2.node.finiteBoundaryTable.entries.length = 1 := by decide

noncomputable def deepBoundaryEntry :=
  deepViewPair.2.node.finiteBoundaryTable.entries[0]'(by
    rw [deepEntries_length]; decide)

noncomputable def deepBoundaryVarName : String :=
  costRegionBoundaryVariableName deepBoundaryEntry.boundary

/-- The deep skeleton is the double Quote/Drop spine over one boundary
variable. -/
theorem deepSkeleton_shape :
    deepViewPair.2.node.skeleton.1 =
      .apply "NQuote" [.apply "PDrop" [.apply "NQuote" [.apply "PDrop"
        [.fvar deepBoundaryVarName]]]] := by rfl

noncomputable def deepOccurrence :
    CostStaticFVarOccurrence deepViewPair.2.node.skeleton.1 where
  name := deepBoundaryVarName
  context := .apply "NQuote" [] (.apply "PDrop" []
    (.apply "NQuote" [] (.apply "PDrop" [] .hole []) []) []) []
  selected := by
    rw [deepSkeleton_shape]
    exact .apply (.apply (.apply (.apply .here)))

theorem deepSlot_exists :
    (deepEnv.slotOfName? deepBoundaryVarName).isSome = true :=
  deepEnv.slotOfName?_isSome_of_occurrence deepOccurrence

noncomputable def deepSlot : Fin deepEnv.atomCount :=
  (deepEnv.slotOfName? deepBoundaryVarName).get deepSlot_exists

/-- **The cospan is dual-nonempty**: both boundary inventories carry a
semantic atom.  This is the configuration no prior fixture exercised. -/
theorem dual_nonempty_boundaries :
    0 < leftEnv.atomCount ∧ 0 < deepEnv.atomCount :=
  ⟨leftSlot.2.trans_le' (Nat.zero_le _) |>.trans_le (Nat.le_refl _),
    deepSlot.2.trans_le' (Nat.zero_le _) |>.trans_le (Nat.le_refl _)⟩

theorem deepSlot_selected :
    deepEnv.slotOfName? deepBoundaryVarName = some deepSlot :=
  (Option.some_get deepSlot_exists).symm

/-- The deep reified frame: the double Quote/Drop spine over the atom. -/
theorem deepReifiedFrame :
    (deepViewPair.2.node.reifiedSourceFrame deepEnv).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.apply rhoReflectivePresentation.quoteConstructor
            [.apply rhoReflectivePresentation.dropConstructor
              [.fvar (deepEnv.atomName deepSlot)]]]] := by
  have spineReify :
      deepEnv.reify (.apply "NQuote" [.apply "PDrop" [.apply "NQuote"
          [.apply "PDrop" [.fvar deepBoundaryVarName]]]]) =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.apply rhoReflectivePresentation.quoteConstructor
              [.apply rhoReflectivePresentation.dropConstructor
                [.fvar (deepEnv.atomName deepSlot)]]]] := by
    simp [Pattern.renameFVars, CostStaticAtomEnvironment.reifyName,
      deepSlot_selected, rhoReflectivePresentation]
  exact (deepViewPair.2.node.reifiedSourceFrame_pattern _).trans
    ((congrArg deepEnv.reify deepSkeleton_shape).trans spineReify)

/-- The deep frame at the base declaration. -/
noncomputable def deepFrame : Pattern :=
  deepViewPair.2.node.canonicalizeReifiedTargetFrame deepEnv
    (costStaticReflectivePresentationDecl rhoCIGSLT .base
      rhoReflectivePresentation)

/-- **The deep side also degenerates to its single semantic atom**: the
double shell is an atom shell, so the canonical frame is the atom's name. -/
theorem deepFrame_is_atom : deepFrame = .fvar (deepEnv.atomName deepSlot) :=
  CostStaticRegionNode.canonicalizeReifiedTargetFrame_atomShell
    deepViewPair.2.node deepEnv deepSlot
    (RhoCanonicalAtomShell.quoteDrop (RhoCanonicalAtomShell.quoteDrop
      RhoCanonicalAtomShell.hole))
    (by
      rw [deepReifiedFrame]
      rfl)

/-- Key agreement across the dual cospan? -/
theorem dual_keys_agree :
    (leftEnv.atomValue leftSlot).key = (deepEnv.atomValue deepSlot).key := by
  decide

end ClaudeDualBoundary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
