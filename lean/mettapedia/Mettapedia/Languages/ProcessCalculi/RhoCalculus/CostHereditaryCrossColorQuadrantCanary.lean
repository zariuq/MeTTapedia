import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderCrossColorReachedCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

/-!
# Cross-colour application/application quadrant canary

Verdict probe for the central semantic question of the rho Cost₁ audit:
can a built cross-colour collapsing pair reach two colour-decodable
application frames?  The pair here is the smallest one, in both colour
orientations:

* base declaration: `@b(*b(@w{0w}))` against `@w{0w}`; only the left side
  collapses; both are static root views of the shared `Name` sort.
* wrapped declaration: `@w(*w(@b{0b}))` against `@b{0b}`.

Every fact is kernel-checked: by `decide` for the decidable patterns
(well-sortedness, collapsing, canonical equality, static root shape, view
colours, table structure), and equationally by theorem for the frame shapes
and the normalization equation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostHereditaryCrossColorQuadrantCanary

open CostHereditaryProviderCrossColorReachedCanary

/-- The shared Name sort expression. -/
def nameType : TypeExpr := .base (costBaseSortName "Name")

/-! ## Base orientation: left = `@b(*b(@w{0w}))` collapses, right = `@w{0w}` -/

/-- Well-sortedness of the wrapped endpoint, restated here (the reached
canary keeps its own copy private). -/
theorem endpointWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [] nameType rightPattern := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [rightPattern, binderSafeAt, binderSafeListAt]

/-- Well-sortedness of the collapsing base pattern. -/
theorem reachedWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [] nameType reachedPattern := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [reachedPattern, rightPattern, binderSafeAt, binderSafeListAt]

/-- The canonical equality of the minimal pair, kernel-computed. -/
theorem pair_canonical :
    canonicalize declaration reachedPattern =
      canonicalize declaration rightPattern := by
  decide

/-- Only the left side collapses. -/
theorem pair_collapsing_left :
    CollapsingRoot declaration reachedPattern :=
  Or.inl ⟨_, rfl⟩

theorem pair_not_collapsing_right :
    ¬ CollapsingRoot declaration rightPattern := by
  intro collapsing
  rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩
  · have headEq := (Pattern.apply.inj shape).1
    unfold declaration at headEq
    rw [rhoDecl_quoteConstructor .base] at headEq
    exact absurd headEq (by decide)
  · cases shape

/-- The two trees actually built by the executable builder. -/
noncomputable def leftTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty [] [] reachedPattern
      nameType :=
  (CostRegionTree.build? [] [] reachedPattern nameType).get
    (CostRegionTree.build?_isSome_of_wellSorted reachedWellSorted)

noncomputable def rightTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty [] [] rightPattern
      nameType :=
  (CostRegionTree.build? [] [] rightPattern nameType).get
    (CostRegionTree.build?_isSome_of_wellSorted endpointWellSorted)

theorem leftTree_rootIsStatic : leftTree.rootIsStatic = true := by
  decide

theorem rightTree_rootIsStatic : rightTree.rootIsStatic = true := by
  decide

/-- Root views as packed (colour, view) pairs straight from the builder. -/
noncomputable def leftViewPair : Σ color, leftTree.StaticRootView color :=
  leftTree.staticRootView_of_rootIsStatic leftTree_rootIsStatic

noncomputable def rightViewPair : Σ color, rightTree.StaticRootView color :=
  rightTree.staticRootView_of_rootIsStatic rightTree_rootIsStatic

/-- The builder picks the expected colours on the two static roots. -/
theorem leftViewPair_color : leftViewPair.1 = .base := by
  decide

theorem rightViewPair_color : rightViewPair.1 = .wrapped := by
  decide

/-- The semantic atom environments of the two built roots. -/
noncomputable def leftEnv :=
  CostStaticAtomEnvironment.ofInventory
    (leftViewPair.2.node.semanticAtomEnvironment
      (leftViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

noncomputable def rightEnv :=
  CostStaticAtomEnvironment.ofInventory
    (rightViewPair.2.node.semanticAtomEnvironment
      (rightViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

/-- Each side's canonical frame at its own colour's declaration. -/
noncomputable def leftFrame : Pattern :=
  leftViewPair.2.node.canonicalizeReifiedTargetFrame leftEnv
    (costStaticReflectivePresentationDecl rhoCIGSLT leftViewPair.1
      rhoReflectivePresentation.toReflectivePresentationDecl)

noncomputable def rightFrame : Pattern :=
  rightViewPair.2.node.canonicalizeReifiedTargetFrame rightEnv
    (costStaticReflectivePresentationDecl rhoCIGSLT rightViewPair.1
      rhoReflectivePresentation.toReflectivePresentationDecl)

/-- The collapsing side's canonical frame.  Extract the leaf name from the
frame itself so the statement stays robust under renaming. -/
noncomputable def leftFrameFvarName : String :=
  match leftFrame with
  | .fvar name => name
  | _ => ""

/-- The single retained boundary entry, extracted from the (kernel-checked)
finite boundary table. -/
theorem leftEntries_length :
    leftViewPair.2.node.finiteBoundaryTable.entries.length = 1 := by
  decide

noncomputable def leftBoundaryEntry :=
  leftViewPair.2.node.finiteBoundaryTable.entries[0]'(by
    rw [leftEntries_length]; decide)

/-- The boundary variable name selected by the built plan: the canonical
placeholder of the single retained boundary entry. -/
noncomputable def leftBoundaryVarName : String :=
  costRegionBoundaryVariableName leftBoundaryEntry.boundary

/-- The built plan's authored skeleton is exactly the Quote/Drop spine over
one boundary variable, kernel-computed. -/
theorem leftSkeleton_shape :
    leftViewPair.2.node.skeleton.1 =
      .apply "NQuote" [.apply "PDrop" [.fvar leftBoundaryVarName]] := by
  rfl

/-- The authored occurrence of the boundary variable in the left skeleton. -/
noncomputable def leftOccurrence :
    CostStaticFVarOccurrence leftViewPair.2.node.skeleton.1 where
  name := leftBoundaryVarName
  context := .apply "NQuote" [] (.apply "PDrop" [] .hole []) []
  selected := by
    rw [leftSkeleton_shape]
    exact .apply (.apply .here)

/-- The environment resolves the boundary name to a slot. -/
theorem leftSlot_exists :
    (leftEnv.slotOfName? leftBoundaryVarName).isSome = true :=
  leftEnv.slotOfName?_isSome_of_occurrence leftOccurrence

noncomputable def leftSlot : Fin leftEnv.atomCount :=
  (leftEnv.slotOfName? leftBoundaryVarName).get leftSlot_exists

theorem leftSlot_selected :
    leftEnv.slotOfName? leftBoundaryVarName = some leftSlot :=
  (Option.some_get leftSlot_exists).symm

/-- The left reified source frame is the Quote/Drop spine over the selected
semantic atom.  This is the frame-shape premise of the atom-collapse
theorem; it is proved structurally, not by kernel evaluation. -/
theorem leftReifiedFrame :
    (leftViewPair.2.node.reifiedSourceFrame leftEnv).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.fvar (leftEnv.atomName leftSlot)]] := by
  have spineReify :
      leftEnv.reify (.apply "NQuote" [.apply "PDrop" [.fvar leftBoundaryVarName]]) =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (leftEnv.atomName leftSlot)]] := by
    simp [Pattern.renameFVars, CostStaticAtomEnvironment.reifyName,
      leftSlot_selected, rhoReflectivePresentation]
  exact (leftViewPair.2.node.reifiedSourceFrame_pattern _).trans
    ((congrArg leftEnv.reify leftSkeleton_shape).trans spineReify)

/-- **Quadrant verdict, base orientation: the collapsing side degenerates to
a single semantic atom.**  Its canonical frame is the boundary atom's free
name, not an application. -/
theorem leftFrame_is_atom : leftFrame = .fvar (leftEnv.atomName leftSlot) :=
  CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
    leftViewPair.2.node leftEnv leftSlot leftReifiedFrame

/-- **The application/application quadrant is empty here.**  At least one of
the two canonical frames is a leaf, so the refuted configuration (two
colour-decodable application frames) never arises. -/
theorem quadrant_unreachable :
    ¬ (∃ wire arguments, leftFrame = .apply wire arguments) ∨
      ¬ (∃ wire arguments, rightFrame = .apply wire arguments) := by
  left
  rintro ⟨wire, arguments, shape⟩
  rw [leftFrame_is_atom] at shape
  cases shape

/-- The partner plan skeleton is the wrapped quotation of the wrapped
parallel unit, kernel-computed. -/
theorem rightSkeleton_shape :
    rightViewPair.2.node.skeleton.1 =
      .apply "NQuote" [.apply "PZero" []] := by
  rfl

/-- The partner reified frame: no atoms, so reification is literal. -/
theorem rightReifiedFrame :
    (rightViewPair.2.node.reifiedSourceFrame rightEnv).1 =
      .apply "NQuote" [.apply "PZero" []] := by
  have spineReify :
      rightEnv.reify (.apply "NQuote" [.apply "PZero" []]) =
        .apply "NQuote" [.apply "PZero" []] := by
    simp [Pattern.renameFVars]
  exact (rightViewPair.2.node.reifiedSourceFrame_pattern _).trans
    ((congrArg rightEnv.reify rightSkeleton_shape).trans spineReify)

/-- **The partner side's canonical frame is a genuine application**: its own
colour's quotation of the parallel unit — the exact built pattern. -/
theorem rightFrame_is_application : rightFrame = rightPattern := by
  have closed : rightViewPair.2.node.targetBound = [] := by
    decide
  unfold rightFrame
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
    rightViewPair.2.node rightEnv]
  rw [CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
    _ closed]
  have targetDepth : rightViewPair.2.node.targetBound.length = 0 := by
    simp [closed]
  rw [targetDepth, rightReifiedFrame]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    rhoReflectivePresentation, mapPattern, mapPatternList_eq_map,
    CostStaticColor.symbols_constructor, CostStaticColor.constructorTag,
    costWrappedConstructorName, rightPattern]
  rw [rightViewPair_color]

/-- The partner frame's head decodes at its own colour. -/
theorem rightFrame_head_decoded :
    decodeCostStaticConstructor rightViewPair.1
        (costWrappedConstructorName "NQuote") = some "NQuote" := by
  rw [rightViewPair_color]
  exact decodeCostStaticConstructor_symbols rhoCIGSLT .wrapped "NQuote"

/-- The partner tree hereditary-normalizes to its own pattern: no atoms, no
collapse, the frame is the pattern. -/
theorem rightTree_normalize :
    (rightTree.normalize (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      rightPattern := by
  rw [rightViewPair.2.normalize_pattern]
  change ((CostStaticRegionNode.normalizeHereditary rightViewPair.2.node
    (rightViewPair.2.children.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))).1 = rightPattern)
  have raw := CostStaticRegionNode.normalizeHereditaryRawWithInventory_eq_sourceAction
    rightViewPair.2.node
    (rightViewPair.2.children.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))
    (rightViewPair.2.node.semanticAtomEnvironment
      (rightViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  rw [show CostStaticRegionNode.normalizeHereditary rightViewPair.2.node
      (rightViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)) =
        CostStaticRegionNode.normalizeHereditaryWithInventory rightViewPair.2.node
          (rightViewPair.2.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))
          (rightViewPair.2.node.semanticAtomEnvironment
            (rightViewPair.2.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1 from rfl,
    CostStaticRegionNode.normalizeHereditaryWithInventory_pattern]
  rw [raw]
  have side : rightEnv.restore rightViewPair.2.node.targetBound
      (rightViewPair.2.node.canonicalizeReifiedTargetFrame rightEnv
        (costStaticReflectivePresentationDecl rhoCIGSLT rightViewPair.1
          rhoReflectivePresentation.toReflectivePresentationDecl)) =
    CostCanonicalLaws.rhoCostStaticActionAt rightViewPair.2.node.thinning
      rightEnv.restorationSupportedOpenAssignment []
      rightViewPair.2.node.targetBound
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt rightViewPair.2.node
          rightEnv)
        rhoReflectivePresentation rightViewPair.2.node.targetBound.length 0
        (rightViewPair.2.node.reifiedSourceFrame rightEnv).1) := by
    rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
      rightViewPair.2.node rightEnv]
    rfl
  unfold rightEnv at side
  rw [← side]
  have frame' := rightFrame_is_application
  rw [rightFrame, rightEnv] at frame'
  rw [frame']
  have closed : rightViewPair.2.node.targetBound = [] := by
    decide
  simp only [CostStaticAtomEnvironment.restore, closed]
  simp [CostStaticAtomEnvironment.restoreAt,
    ReflectiveContextSupport.substituteAt, rightPattern]

/-- Kernel-spelled variant of `rightTree_normalize` (structure projection; no
tree unfolding). -/
theorem rightTree_normalizeK :
    (rightTree.normalize (normalizeStatic :=
      rhoHereditaryNormalizationKernel.normalize)).pattern = rightPattern :=
  rightTree_normalize

/-- Local finite index of the single retained boundary entry. -/
noncomputable def leftEntryIndex :
    Fin leftViewPair.2.node.finiteBoundaryTable.entries.length :=
  ⟨0, by rw [leftEntries_length]; decide⟩

/-- Opaque screen for the collapsing side's finite boundary table. -/
noncomputable def leftKernelTable :
    TypedCostRegionBoundaryTable rhoCIGSLT leftViewPair.1
      FreeTypeContext.empty leftViewPair.2.node.plan.occurrences :=
  leftViewPair.2.node.finiteBoundaryTable

/-- Opaque screen for the kernel-spelled normalized finite values of the
collapsing side: every proof goal below mentions only this constant, never
the proof-carrying `normalizeValues` term itself. -/
noncomputable def leftKernelValues :
    TypedCostRegionBoundaryTable.Values rhoCIGSLT leftViewPair.1
      FreeTypeContext.empty leftKernelTable :=
  leftViewPair.2.children.normalizeValues
    (normalizeStatic := rhoHereditaryNormalizationKernel.normalize)

/-- Opaque screen for the unique boundary entry's stable key. -/
noncomputable def leftKernelEntryName : String :=
  costRegionBoundaryVariableName
    ((leftViewPair.2.children.getEntry leftEntryIndex).boundary.boundary)

/-- The resolve chain for the collapsing fixture's unique boundary value,
packaged with its normalized-value identity, stated over the opaque
kernel-spelled screens so downstream goals stay small. -/
theorem leftResolved_obtain :
    ∃ resolved : TypedCostRegionBoundaryTable.Values.Resolved rhoCIGSLT
        leftViewPair.1 FreeTypeContext.empty,
      leftKernelValues.resolve leftKernelTable leftKernelEntryName =
        some resolved ∧
      resolved.2.1 =
        (((leftViewPair.2.children.getEntry leftEntryIndex)
          ).tree.normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 := by
  obtain ⟨resolved, resolution, _resolvedBoundary, resolvedNormal⟩ :=
    leftViewPair.2.children.exists_resolve_normalizedValue_eq_getEntry
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition leftEntryIndex
  exact ⟨resolved, resolution, resolvedNormal⟩

/-- Normalize agreement between the collapsing fixture's boundary child and
the partner's own built tree — the unambiguity step only. -/
theorem leftEntryTree_normalize_eq :
    ((leftViewPair.2.children.getEntry leftEntryIndex).tree.normalize
        (normalizeStatic := rhoHereditaryNormalizationKernel.normalize)).pattern =
      (rightTree.normalize
        (normalizeStatic := rhoHereditaryNormalizationKernel.normalize)).pattern := by
  have object : WellSorted.isObjectPattern rightPattern = true := by
    decide
  exact CostRegionTree.normalize_pattern_eq_of_unambiguous
    CostCanonicalLaws.rho_unambiguousStaticDecomposition
    rhoHereditaryNormalizationKernel
    (leftViewPair.2.children.getEntry leftEntryIndex).tree rightTree object

/-- The stored boundary entry at the unique slot is the hand-spelled
single-entry boundary. -/
theorem leftStoredEntry_eq_leftBoundaryEntry :
    (leftViewPair.2.children.getEntry leftEntryIndex).boundary =
      leftBoundaryEntry := by
  rfl

/-- Assignment computed for the unique boundary slot: every goal is
microscopic because the values/table carry only the opaque screen
constants. -/
theorem leftAtom_assignment_resolved :
    leftKernelValues.assignment leftKernelTable leftOccurrence.name =
      (((leftViewPair.2.children.getEntry leftEntryIndex)
        ).tree.normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 := by
  obtain ⟨resolved, resolution, resolvedNormal⟩ := leftResolved_obtain
  rw [← resolvedNormal]
  rw [TypedCostRegionBoundaryTable.Values.assignment.eq_unfold]
  dsimp only []
  rw [show leftOccurrence.name =
      costRegionBoundaryVariableName leftBoundaryEntry.boundary from rfl]
  rw [decodeCostRegionSourceVariableName_boundary]
  rw [show costRegionBoundaryVariableName leftBoundaryEntry.boundary =
      leftKernelEntryName from by
    rw [leftKernelEntryName,
      congrArg costRegionBoundaryVariableName
        (congrArg (·.boundary) leftStoredEntry_eq_leftBoundaryEntry)]
  ]
  rw [resolution]

/-- **The boundary atom's compact normal value is the partner's pattern.**
The semantic mechanism of the cross-colour restoration. -/
theorem leftAtom_normal : (leftEnv.atomValue leftSlot).key.normal = rightPattern := by
  have viaAssignment := leftEnv.atomValue_normal_eq_of_slotOfName?_eq_some
    (values := leftKernelValues) leftOccurrence leftSlot leftSlot_selected
  rw [viaAssignment]
  rw [leftAtom_assignment_resolved]
  rw [CostRegionTree.normalizedBoundaryValue_pattern]
  rw [leftEntryTree_normalize_eq]
  rw [rightTree_normalizeK]

/-- The boundary atom's target support is empty: the slot is a boundary
parameter, not a nested name. -/
theorem leftAtomKey_targetSupport :
    (leftEnv.atomValue leftSlot).key.targetSupport = [] := by
  rw [leftEnv.atomValue_targetSupport_eq_of_slotOfName?_eq_some
    leftOccurrence leftSlot leftSlot_selected]
  rw [show leftOccurrence.name =
    costRegionBoundaryVariableName leftBoundaryEntry.boundary from rfl]
  have entriesShape : leftViewPair.2.node.boundaryTable.entries =
      [leftBoundaryEntry] := by
    rfl
  rw [TypedCostRegionBoundaryTable.restorationSupport_boundaryVariable
    leftViewPair.2.node.boundaryTable leftBoundaryEntry
    (entriesShape ▸ List.mem_singleton_self leftBoundaryEntry)]
  rfl

/-- Opaque screen for the common semantic quotient of the two viewed
environments. -/
noncomputable def pairCospan := leftEnv.semanticKeyCospan rightEnv

/-- The unique common slot's normalized value is the partner's pattern:
the common quotient carries the endpoint key's normal verbatim. -/
theorem pairCospan_commonNormal :
    (pairCospan.commonKeys.get (pairCospan.leftSlot leftSlot)).normal =
      rightPattern := by
  rw [show pairCospan.commonKeys.get (pairCospan.leftSlot leftSlot) =
    (leftEnv.atomValue leftSlot).key from pairCospan.leftCommutes leftSlot]
  exact leftAtom_normal

/-- The unique common slot's normalized value, at the assignment spelling. -/
theorem pairCospan_commonAssignment :
    pairCospan.commonAssignment
        (pairCospan.commonAtomName (pairCospan.leftSlot leftSlot)) =
      rightPattern := by
  rw [CostStaticAtomKeyCospan.commonAssignment_commonAtomName]
  exact pairCospan_commonNormal

/-- The unique common slot's support is empty. -/
theorem pairCospan_commonSupport :
    pairCospan.commonSupport
        (pairCospan.commonAtomName (pairCospan.leftSlot leftSlot)) = [] := by
  rw [CostStaticAtomKeyCospan.commonSupport_commonAtomName]
  rw [show pairCospan.commonKeys.get (pairCospan.leftSlot leftSlot) =
    (leftEnv.atomValue leftSlot).key from pairCospan.leftCommutes leftSlot]
  exact leftAtomKey_targetSupport

/-- Reifying the collapsing side's atom frame through the common quotient
selects the unique common slot's atom name. -/
theorem pairReify_left :
    pairCospan.reifyWith leftEnv.lookupAtom? pairCospan.leftSlot leftFrame =
      .fvar (pairCospan.commonAtomName (pairCospan.leftSlot leftSlot)) := by
  rw [leftFrame_is_atom]
  rw [CostStaticAtomKeyCospan.reifyWith_fvar]
  rw [CostStaticAtomKeyCospan.reifyNameWith,
    CostStaticAtomEnvironment.lookupAtom?_atomName]

/-- Reifying the partner's rigid frame through the common quotient is the
identity: the application tower contains no free variables. -/
theorem pairReify_right :
    pairCospan.reifyWith rightEnv.lookupAtom? pairCospan.rightSlot
        rightPattern = rightPattern := by
  simp [rightPattern, Pattern.renameFVars]

/-- The partner's application tower carries no bound indices, so every bound
lift is invisible. -/
theorem liftBVars_rightPattern (shift : Nat) :
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 shift rightPattern =
      rightPattern := by
  simp [rightPattern,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

/-- Restoring the partner's rigid frame under the common environment at any
ambient depth is the identity: every fvar-branch is unreachable. -/
theorem pairSubstituteAt_right (depth : Nat) :
    ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile pairCospan.commonSupport
        pairCospan.commonAssignment depth rightPattern =
      rightPattern := by
  simp [rightPattern, ReflectiveContextSupport.substituteAt]

/-- **The fixture's two frames restore together**: the collapsing side's
semantic atom, reified to the common quotient, restores at every depth to
the partner's own rigid frame — which is already the common normalized
value of that atom. -/
theorem pair_framesRestorationAligned :
    RhoStaticFramesRestorationAligned leftViewPair.2 rightViewPair.2 := by
  refine RhoStaticFramesRestorationAligned.ofFramesRestoreTogether
    leftViewPair.2 rightViewPair.2 ?_
  show ReflectiveContextSupport.RestoresTogether
    rhoCIGSLT.costWholeReflectionProfile pairCospan.commonSupport
    pairCospan.commonAssignment
    (pairCospan.reifyWith leftEnv.lookupAtom? pairCospan.leftSlot leftFrame)
    (pairCospan.reifyWith rightEnv.lookupAtom? pairCospan.rightSlot rightFrame)
  intro depth
  rw [rightFrame_is_application, pairReify_left, pairReify_right]
  rw [ReflectiveContextSupport.substituteAt_fvar,
    pairCospan_commonSupport, pairCospan_commonAssignment]
  rw [pairSubstituteAt_right]
  simp only [List.length_nil, Nat.sub_zero]
  exact liftBVars_rightPattern depth

/-! ## Wrapped orientation: `@w(*w(@b{0b}))` collapses, `@b{0b}` stays -/

/-- The base-colour endpoint of the mirrored pair. -/
def partnerBase : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PZero") []]

/-- The mirrored collapsing pattern. -/
def collapsingWrapped : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [partnerBase]]

/-- The wrapped declaration. -/
def wrappedDeclaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl

theorem partnerBaseWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [] nameType partnerBase := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [partnerBase, binderSafeAt, binderSafeListAt]

theorem collapsingWrappedWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [] nameType collapsingWrapped := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [collapsingWrapped, partnerBase, binderSafeAt, binderSafeListAt]

/-- The canonical equality of the mirrored pair, kernel-computed. -/
theorem mirror_canonical :
    canonicalize wrappedDeclaration collapsingWrapped =
      canonicalize wrappedDeclaration partnerBase := by
  decide

/-- Only the right side collapses. -/
theorem mirror_collapsing_right :
    CollapsingRoot wrappedDeclaration collapsingWrapped :=
  Or.inl ⟨_, rfl⟩

theorem mirror_not_collapsing_left :
    ¬ CollapsingRoot wrappedDeclaration partnerBase := by
  intro collapsing
  rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩
  · unfold partnerBase at shape
    have headEq := (Pattern.apply.inj shape).1
    unfold wrappedDeclaration at headEq
    rw [rhoDecl_quoteConstructor .wrapped] at headEq
    exact absurd headEq (by decide)
  · cases shape

noncomputable def mLeftTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty [] [] partnerBase
      nameType :=
  (CostRegionTree.build? [] [] partnerBase nameType).get
    (CostRegionTree.build?_isSome_of_wellSorted partnerBaseWellSorted)

noncomputable def mRightTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty [] [] collapsingWrapped
      nameType :=
  (CostRegionTree.build? [] [] collapsingWrapped nameType).get
    (CostRegionTree.build?_isSome_of_wellSorted collapsingWrappedWellSorted)

theorem mLeftTree_rootIsStatic : mLeftTree.rootIsStatic = true := by
  decide

theorem mRightTree_rootIsStatic : mRightTree.rootIsStatic = true := by
  decide

noncomputable def mLeftViewPair : Σ color, mLeftTree.StaticRootView color :=
  mLeftTree.staticRootView_of_rootIsStatic mLeftTree_rootIsStatic

noncomputable def mRightViewPair : Σ color, mRightTree.StaticRootView color :=
  mRightTree.staticRootView_of_rootIsStatic mRightTree_rootIsStatic

theorem mLeftViewPair_color : mLeftViewPair.1 = .base := by
  decide

theorem mRightViewPair_color : mRightViewPair.1 = .wrapped := by
  decide

noncomputable def mRightEnv :=
  CostStaticAtomEnvironment.ofInventory
    (mRightViewPair.2.node.semanticAtomEnvironment
      (mRightViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

theorem mRightEntries_length :
    mRightViewPair.2.node.finiteBoundaryTable.entries.length = 1 := by
  decide

noncomputable def mRightBoundaryEntry :=
  mRightViewPair.2.node.finiteBoundaryTable.entries[0]'(by
    rw [mRightEntries_length]; decide)

/-- The mirrored boundary variable name. -/
noncomputable def mRightBoundaryVarName : String :=
  costRegionBoundaryVariableName mRightBoundaryEntry.boundary

/-- The mirrored skeleton is the same Quote/Drop spine over one boundary
variable, kernel-computed. -/
theorem mRightSkeleton_shape :
    mRightViewPair.2.node.skeleton.1 =
      .apply "NQuote" [.apply "PDrop" [.fvar mRightBoundaryVarName]] := by
  rfl

/-- The authored occurrence of the mirrored boundary variable. -/
noncomputable def mRightOccurrence :
    CostStaticFVarOccurrence mRightViewPair.2.node.skeleton.1 where
  name := mRightBoundaryVarName
  context := .apply "NQuote" [] (.apply "PDrop" [] .hole []) []
  selected := by
    rw [mRightSkeleton_shape]
    exact .apply (.apply .here)

theorem mRightSlot_exists :
    (mRightEnv.slotOfName? mRightBoundaryVarName).isSome = true :=
  mRightEnv.slotOfName?_isSome_of_occurrence mRightOccurrence

noncomputable def mRightSlot : Fin mRightEnv.atomCount :=
  (mRightEnv.slotOfName? mRightBoundaryVarName).get mRightSlot_exists

theorem mRightSlot_selected :
    mRightEnv.slotOfName? mRightBoundaryVarName = some mRightSlot :=
  (Option.some_get mRightSlot_exists).symm

theorem mRightReifiedFrame :
    (mRightViewPair.2.node.reifiedSourceFrame mRightEnv).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.fvar (mRightEnv.atomName mRightSlot)]] := by
  have spineReify :
      mRightEnv.reify (.apply "NQuote" [.apply "PDrop"
          [.fvar mRightBoundaryVarName]]) =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (mRightEnv.atomName mRightSlot)]] := by
    simp [Pattern.renameFVars, CostStaticAtomEnvironment.reifyName,
      mRightSlot_selected, rhoReflectivePresentation]
  exact (mRightViewPair.2.node.reifiedSourceFrame_pattern _).trans
    ((congrArg mRightEnv.reify mRightSkeleton_shape).trans spineReify)

/-- **Quadrant verdict, wrapped orientation: the collapsing side again
degenerates to a single semantic atom.** -/
theorem mRightFrame_is_atom :
    mRightViewPair.2.node.canonicalizeReifiedTargetFrame mRightEnv
        (costStaticReflectivePresentationDecl rhoCIGSLT mRightViewPair.1
          rhoReflectivePresentation.toReflectivePresentationDecl) =
      .fvar (mRightEnv.atomName mRightSlot) :=
  CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
    mRightViewPair.2.node mRightEnv mRightSlot mRightReifiedFrame

/-- The partner-side environment of the mirrored pair. -/
noncomputable def mLeftEnv :=
  CostStaticAtomEnvironment.ofInventory
    (mLeftViewPair.2.node.semanticAtomEnvironment
      (mLeftViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

/-- The mirrored partner skeleton decodes to the source `Quote (PZero)`
spine. -/
theorem mLeftSkeleton_shape :
    mLeftViewPair.2.node.skeleton.1 =
      .apply "NQuote" [.apply "PZero" []] := by
  rfl

/-- The mirrored partner's reified frame: no atoms, so reification is
literal. -/
theorem mLeftReifiedFrame :
    (mLeftViewPair.2.node.reifiedSourceFrame mLeftEnv).1 =
      .apply "NQuote" [.apply "PZero" []] := by
  have spineReify :
      mLeftEnv.reify (.apply "NQuote" [.apply "PZero" []]) =
        .apply "NQuote" [.apply "PZero" []] := by
    simp [Pattern.renameFVars]
  exact (mLeftViewPair.2.node.reifiedSourceFrame_pattern _).trans
    ((congrArg mLeftEnv.reify mLeftSkeleton_shape).trans spineReify)

/-- The mirrored partner's canonical frame (opaque screen). -/
noncomputable def mLeftFrame : Pattern :=
  mLeftViewPair.2.node.canonicalizeReifiedTargetFrame mLeftEnv
    (costStaticReflectivePresentationDecl rhoCIGSLT mLeftViewPair.1
      rhoReflectivePresentation.toReflectivePresentationDecl)

/-- The mirrored collapsing side's canonical frame (opaque screen). -/
noncomputable def mRightFrame : Pattern :=
  mRightViewPair.2.node.canonicalizeReifiedTargetFrame mRightEnv
    (costStaticReflectivePresentationDecl rhoCIGSLT mRightViewPair.1
      rhoReflectivePresentation.toReflectivePresentationDecl)

/-- **The mirrored partner side's canonical frame is a genuine
application**: the base quotation of the parallel unit. -/
theorem mLeftFrame_is_application : mLeftFrame = partnerBase := by
  have closed : mLeftViewPair.2.node.targetBound = [] := by
    decide
  unfold mLeftFrame
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
    mLeftViewPair.2.node mLeftEnv]
  rw [CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
    _ closed]
  have targetDepth : mLeftViewPair.2.node.targetBound.length = 0 := by
    simp [closed]
  rw [targetDepth, mLeftReifiedFrame]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    rhoReflectivePresentation, mapPattern, mapPatternList_eq_map,
    CostStaticColor.symbols_constructor, CostStaticColor.constructorTag,
    costBaseConstructorName, partnerBase]
  rw [mLeftViewPair_color]

/-- The mirrored partner tree hereditary-normalizes to its own pattern. -/
theorem mLeftTree_normalize :
    (mLeftTree.normalize (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      partnerBase := by
  rw [mLeftViewPair.2.normalize_pattern]
  change ((CostStaticRegionNode.normalizeHereditary mLeftViewPair.2.node
    (mLeftViewPair.2.children.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))).1 = partnerBase)
  have raw := CostStaticRegionNode.normalizeHereditaryRawWithInventory_eq_sourceAction
    mLeftViewPair.2.node
    (mLeftViewPair.2.children.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))
    (mLeftViewPair.2.node.semanticAtomEnvironment
      (mLeftViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  rw [show CostStaticRegionNode.normalizeHereditary mLeftViewPair.2.node
      (mLeftViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)) =
        CostStaticRegionNode.normalizeHereditaryWithInventory mLeftViewPair.2.node
          (mLeftViewPair.2.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))
          (mLeftViewPair.2.node.semanticAtomEnvironment
            (mLeftViewPair.2.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1 from rfl,
    CostStaticRegionNode.normalizeHereditaryWithInventory_pattern]
  rw [raw]
  have side : mLeftEnv.restore mLeftViewPair.2.node.targetBound
      (mLeftViewPair.2.node.canonicalizeReifiedTargetFrame mLeftEnv
        (costStaticReflectivePresentationDecl rhoCIGSLT mLeftViewPair.1
          rhoReflectivePresentation.toReflectivePresentationDecl)) =
    CostCanonicalLaws.rhoCostStaticActionAt mLeftViewPair.2.node.thinning
      mLeftEnv.restorationSupportedOpenAssignment []
      mLeftViewPair.2.node.targetBound
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt mLeftViewPair.2.node
          mLeftEnv)
        rhoReflectivePresentation mLeftViewPair.2.node.targetBound.length 0
        (mLeftViewPair.2.node.reifiedSourceFrame mLeftEnv).1) := by
    rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
      mLeftViewPair.2.node mLeftEnv]
    rfl
  unfold mLeftEnv at side
  rw [← side]
  have frame' := mLeftFrame_is_application
  rw [mLeftFrame, mLeftEnv] at frame'
  rw [frame']
  have closed : mLeftViewPair.2.node.targetBound = [] := by
    decide
  simp only [CostStaticAtomEnvironment.restore, closed]
  simp [CostStaticAtomEnvironment.restoreAt,
    ReflectiveContextSupport.substituteAt, partnerBase]

/-- Kernel-spelled variant of `mLeftTree_normalize`. -/
theorem mLeftTree_normalizeK :
    (mLeftTree.normalize (normalizeStatic :=
      rhoHereditaryNormalizationKernel.normalize)).pattern = partnerBase :=
  mLeftTree_normalize

/-- **Mirror verdict.** In the wrapped orientation the application half of
the quadrant would have to live on the `@b{0b}` side; the collapsing wrapped
side degenerates, so the two-application quadrant is empty here too. -/
theorem quadrant_unreachable_mirror :
    ¬ (∃ wire arguments,
        mRightViewPair.2.node.canonicalizeReifiedTargetFrame mRightEnv
          (costStaticReflectivePresentationDecl rhoCIGSLT mRightViewPair.1
            rhoReflectivePresentation.toReflectivePresentationDecl) =
          .apply wire arguments) := by
  rintro ⟨wire, arguments, shape⟩
  rw [mRightFrame_is_atom] at shape
  cases shape

/-! ### The mirrored semantic mechanism -/

/-- Local finite index of the mirrored single boundary entry. -/
noncomputable def mRightEntryIndex :
    Fin mRightViewPair.2.node.finiteBoundaryTable.entries.length :=
  ⟨0, by rw [mRightEntries_length]; decide⟩

/-- Opaque screen for the mirrored finite boundary table. -/
noncomputable def mRightKernelTable :
    TypedCostRegionBoundaryTable rhoCIGSLT mRightViewPair.1
      FreeTypeContext.empty mRightViewPair.2.node.plan.occurrences :=
  mRightViewPair.2.node.finiteBoundaryTable

/-- Opaque screen for the mirrored kernel-spelled values. -/
noncomputable def mRightKernelValues :
    TypedCostRegionBoundaryTable.Values rhoCIGSLT mRightViewPair.1
      FreeTypeContext.empty mRightKernelTable :=
  mRightViewPair.2.children.normalizeValues
    (normalizeStatic := rhoHereditaryNormalizationKernel.normalize)

/-- Opaque screen for the mirrored boundary entry's stable key. -/
noncomputable def mRightKernelEntryName : String :=
  costRegionBoundaryVariableName
    ((mRightViewPair.2.children.getEntry mRightEntryIndex).boundary.boundary)

/-- The resolve chain for the mirrored boundary value. -/
theorem mRightResolved_obtain :
    ∃ resolved : TypedCostRegionBoundaryTable.Values.Resolved rhoCIGSLT
        mRightViewPair.1 FreeTypeContext.empty,
      mRightKernelValues.resolve mRightKernelTable mRightKernelEntryName =
        some resolved ∧
      resolved.2.1 =
        (((mRightViewPair.2.children.getEntry mRightEntryIndex)
          ).tree.normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 := by
  obtain ⟨resolved, resolution, _resolvedBoundary, resolvedNormal⟩ :=
    mRightViewPair.2.children.exists_resolve_normalizedValue_eq_getEntry
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition mRightEntryIndex
  exact ⟨resolved, resolution, resolvedNormal⟩

/-- Normalize agreement between the mirrored boundary child and the partner
tree — the unambiguity step only. -/
theorem mRightEntryTree_normalize_eq :
    ((mRightViewPair.2.children.getEntry mRightEntryIndex).tree.normalize
        (normalizeStatic := rhoHereditaryNormalizationKernel.normalize)).pattern =
      (mLeftTree.normalize
        (normalizeStatic := rhoHereditaryNormalizationKernel.normalize)).pattern := by
  have object : WellSorted.isObjectPattern partnerBase = true := by
    decide
  exact CostRegionTree.normalize_pattern_eq_of_unambiguous
    CostCanonicalLaws.rho_unambiguousStaticDecomposition
    rhoHereditaryNormalizationKernel
    (mRightViewPair.2.children.getEntry mRightEntryIndex).tree mLeftTree object

/-- The mirrored stored boundary entry is its hand-spelled single entry. -/
theorem mRightStoredEntry_eq :
    (mRightViewPair.2.children.getEntry mRightEntryIndex).boundary =
      mRightBoundaryEntry := by
  rfl

/-- Assignment computed for the mirrored unique boundary slot. -/
theorem mRightAtom_assignment_resolved :
    mRightKernelValues.assignment mRightKernelTable mRightOccurrence.name =
      (((mRightViewPair.2.children.getEntry mRightEntryIndex)
        ).tree.normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 := by
  obtain ⟨resolved, resolution, resolvedNormal⟩ := mRightResolved_obtain
  rw [← resolvedNormal]
  rw [TypedCostRegionBoundaryTable.Values.assignment.eq_unfold]
  dsimp only []
  rw [show mRightOccurrence.name =
      costRegionBoundaryVariableName mRightBoundaryEntry.boundary from rfl]
  rw [decodeCostRegionSourceVariableName_boundary]
  rw [show costRegionBoundaryVariableName mRightBoundaryEntry.boundary =
      mRightKernelEntryName from by
    rw [mRightKernelEntryName,
      congrArg costRegionBoundaryVariableName
        (congrArg (·.boundary) mRightStoredEntry_eq)]
  ]
  rw [resolution]

/-- **The mirrored boundary atom's compact normal value is the partner's
pattern.**  The restoration of the wrapped orientation. -/
theorem mRightAtom_normal :
    (mRightEnv.atomValue mRightSlot).key.normal = partnerBase := by
  have viaAssignment := mRightEnv.atomValue_normal_eq_of_slotOfName?_eq_some
    (values := mRightKernelValues) mRightOccurrence mRightSlot
    mRightSlot_selected
  rw [viaAssignment]
  rw [mRightAtom_assignment_resolved]
  rw [CostRegionTree.normalizedBoundaryValue_pattern]
  rw [mRightEntryTree_normalize_eq]
  rw [mLeftTree_normalizeK]

/-- The mirrored boundary atom's target support is empty. -/
theorem mRightAtomKey_targetSupport :
    (mRightEnv.atomValue mRightSlot).key.targetSupport = [] := by
  rw [mRightEnv.atomValue_targetSupport_eq_of_slotOfName?_eq_some
    mRightOccurrence mRightSlot mRightSlot_selected]
  rw [show mRightOccurrence.name =
    costRegionBoundaryVariableName mRightBoundaryEntry.boundary from rfl]
  have entriesShape : mRightViewPair.2.node.boundaryTable.entries =
      [mRightBoundaryEntry] := by
    rfl
  rw [TypedCostRegionBoundaryTable.restorationSupport_boundaryVariable
    mRightViewPair.2.node.boundaryTable mRightBoundaryEntry
    (entriesShape ▸ List.mem_singleton_self mRightBoundaryEntry)]
  rfl

/-- Opaque screen for the mirrored common semantic quotient. -/
noncomputable def mPairCospan := mLeftEnv.semanticKeyCospan mRightEnv

/-- The mirrored common slot's normalized value is the partner's pattern
(this time the substantive slot comes in through the right leg). -/
theorem mPairCospan_commonNormal :
    (mPairCospan.commonKeys.get (mPairCospan.rightSlot mRightSlot)).normal =
      partnerBase := by
  rw [show mPairCospan.commonKeys.get (mPairCospan.rightSlot mRightSlot) =
    (mRightEnv.atomValue mRightSlot).key from mPairCospan.rightCommutes mRightSlot]
  exact mRightAtom_normal

/-- The mirrored common slot's normalized value, at the assignment spelling. -/
theorem mPairCospan_commonAssignment :
    mPairCospan.commonAssignment
        (mPairCospan.commonAtomName (mPairCospan.rightSlot mRightSlot)) =
      partnerBase := by
  rw [CostStaticAtomKeyCospan.commonAssignment_commonAtomName]
  exact mPairCospan_commonNormal

/-- The mirrored common slot's support is empty. -/
theorem mPairCospan_commonSupport :
    mPairCospan.commonSupport
        (mPairCospan.commonAtomName (mPairCospan.rightSlot mRightSlot)) = [] := by
  rw [CostStaticAtomKeyCospan.commonSupport_commonAtomName]
  rw [show mPairCospan.commonKeys.get (mPairCospan.rightSlot mRightSlot) =
    (mRightEnv.atomValue mRightSlot).key from mPairCospan.rightCommutes mRightSlot]
  exact mRightAtomKey_targetSupport

/-- Reifying the mirrored partner's rigid frame through the quotient is the
identity. -/
theorem mPairReify_left :
    mPairCospan.reifyWith mLeftEnv.lookupAtom? mPairCospan.leftSlot
        partnerBase = partnerBase := by
  simp [partnerBase, Pattern.renameFVars]

/-- Reifying the mirrored collapsing atom frame selects the common slot. -/
theorem mPairReify_right :
    mPairCospan.reifyWith mRightEnv.lookupAtom? mPairCospan.rightSlot
        mRightFrame =
      .fvar (mPairCospan.commonAtomName (mPairCospan.rightSlot mRightSlot)) := by
  rw [show mRightFrame =
      .fvar (mRightEnv.atomName mRightSlot) from mRightFrame_is_atom]
  rw [CostStaticAtomKeyCospan.reifyWith_fvar]
  rw [CostStaticAtomKeyCospan.reifyNameWith,
    CostStaticAtomEnvironment.lookupAtom?_atomName]

/-- Restoring the mirrored partner's rigid frame at any depth is the
identity. -/
theorem mPairSubstituteAt_left (depth : Nat) :
    ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile mPairCospan.commonSupport
        mPairCospan.commonAssignment depth partnerBase =
      partnerBase := by
  simp [partnerBase, ReflectiveContextSupport.substituteAt]

/-- The mirrored partner carries no bound indices. -/
theorem liftBVars_partnerBase (shift : Nat) :
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 shift partnerBase =
      partnerBase := by
  simp [partnerBase,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

/-- **The mirrored fixture's two frames restore together.**  Both
orientations of the minimal cross-colour collapsing pair satisfy the leaf
restoration alignment. -/
theorem mirror_framesRestorationAligned :
    RhoStaticFramesRestorationAligned mLeftViewPair.2 mRightViewPair.2 := by
  refine RhoStaticFramesRestorationAligned.ofFramesRestoreTogether
    mLeftViewPair.2 mRightViewPair.2 ?_
  show ReflectiveContextSupport.RestoresTogether
    rhoCIGSLT.costWholeReflectionProfile mPairCospan.commonSupport
    mPairCospan.commonAssignment
    (mPairCospan.reifyWith mLeftEnv.lookupAtom? mPairCospan.leftSlot mLeftFrame)
    (mPairCospan.reifyWith mRightEnv.lookupAtom? mPairCospan.rightSlot
      mRightFrame)
  intro depth
  rw [mLeftFrame_is_application, mPairReify_left, mPairReify_right]
  rw [ReflectiveContextSupport.substituteAt_fvar,
    mPairCospan_commonSupport, mPairCospan_commonAssignment]
  rw [mPairSubstituteAt_left]
  simp only [List.length_nil, Nat.sub_zero]
  exact (liftBVars_partnerBase depth).symm

end CostHereditaryCrossColorQuadrantCanary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
