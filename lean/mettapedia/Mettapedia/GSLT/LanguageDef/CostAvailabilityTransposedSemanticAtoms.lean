import Mettapedia.GSLT.LanguageDef.CostAvailabilityTransposedRestoration
import Mettapedia.GSLT.LanguageDef.CostCanonicalOccurrenceTraceRecursive
import Mettapedia.GSLT.LanguageDef.CostHereditaryTransportAtoms
import Mettapedia.GSLT.LanguageDef.CostStructuralSelection

/-!
# Semantic atoms across an availability transposition

The authoritative boundary-value relation is positional, while restoration
uses the finite semantic-atom quotient.  This module connects those two
views without comparing serialized boundary names.  Corresponding atoms may
have different complete keys: only target support and normalized value are
the restoration data transported here.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace CostStaticFVarOccurrence

/-- Map one exact zipper occurrence through structural free-variable
renaming.  The zipper is transformed together with the selected payload, so
duplicate occurrences remain positionally distinct even when the renaming
coalesces their names. -/
def renameFVars {root : Pattern} (rename : String → String)
    (occurrence : CostStaticFVarOccurrence root) :
    CostStaticFVarOccurrence (Pattern.renameFVars rename root) where
  name := rename occurrence.name
  context := StructuralPatternAction.renameFVarsContext rename
    occurrence.context
  selected := by
    simpa only [StructuralPatternAction.freeVariableRenaming_map,
      StructuralPatternAction.freeVariableRenaming_mapContext,
      Pattern.renameFVars] using
      (StructuralPatternAction.freeVariableRenaming rename).mapSelection ()
        occurrence.selected

@[simp]
theorem renameFVars_name {root : Pattern} (rename : String → String)
    (occurrence : CostStaticFVarOccurrence root) :
    (occurrence.renameFVars rename).name = rename occurrence.name :=
  rfl

@[simp]
theorem renameFVars_context {root : Pattern} (rename : String → String)
    (occurrence : CostStaticFVarOccurrence root) :
    (occurrence.renameFVars rename).context =
      StructuralPatternAction.renameFVarsContext rename occurrence.context :=
  rfl

end CostStaticFVarOccurrence

/-- The exact semantic-atom fields needed by restoration when an ambient
binder suffix moves from outer context into active availability. -/
structure TypedCostStaticAtom.RestorationAvailabilitySuffix
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (ambient : List TypeExpr)
    (small large : TypedCostStaticAtom source color targetFree) : Prop where
  targetSupport : CostStaticAvailabilitySuffix ambient
    small.key.targetSupport large.key.targetSupport
  normal_eq : small.key.normal = large.key.normal

namespace TypedCostStaticAtom.RestorationAvailabilitySuffix

/-- An exposed atom retains the moved ambient suffix in its target support. -/
theorem exposed
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {small large : TypedCostStaticAtom source color targetFree}
    (support_eq : large.key.targetSupport =
      small.key.targetSupport ++ ambient)
    (normal_eq : small.key.normal = large.key.normal) :
    RestorationAvailabilitySuffix ambient small large :=
  ⟨Or.inl support_eq, normal_eq⟩

/-- A sealed atom retains both its target support and normalized value. -/
theorem sealed
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {small large : TypedCostStaticAtom source color targetFree}
    (support_eq : large.key.targetSupport = small.key.targetSupport)
    (normal_eq : small.key.normal = large.key.normal) :
    RestorationAvailabilitySuffix ambient small large :=
  ⟨Or.inr support_eq, normal_eq⟩

/-- A support pair outside both permitted regimes cannot be accepted merely
because its normalized values happen to agree. -/
theorem not_of_support_ne_append_of_ne
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {small large : TypedCostStaticAtom source color targetFree}
    (notExposed : large.key.targetSupport ≠
      small.key.targetSupport ++ ambient)
    (notSealed : large.key.targetSupport ≠ small.key.targetSupport) :
    ¬ RestorationAvailabilitySuffix ambient small large := by
  intro related
  exact CostStaticAvailabilitySuffix.not_of_ne_append_of_ne
    notExposed notSealed related.targetSupport

/-- Corresponding boundary values induce corresponding restoration atoms.
Source support and the rest of the semantic key are deliberately irrelevant
to this conclusion. -/
theorem ofBoundaryValue
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {smallBoundary largeBoundary :
      TypedCostRegionBoundary source color targetFree}
    {smallValue : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      smallBoundary.boundary.targetSupport smallBoundary.boundary.targetType}
    {largeValue : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      largeBoundary.boundary.targetSupport largeBoundary.boundary.targetType}
    (boundary : TypedCostRegionBoundary.AvailabilitySuffix ambient
      smallBoundary largeBoundary)
    (normal_eq : smallValue.1 = largeValue.1) :
    RestorationAvailabilitySuffix ambient
      (TypedCostStaticAtom.ofBoundaryValue smallBoundary smallValue)
      (TypedCostStaticAtom.ofBoundaryValue largeBoundary largeValue) :=
  ⟨boundary.targetSupport, normal_eq⟩

end TypedCostStaticAtom.RestorationAvailabilitySuffix

namespace TypedCostRegionBoundaryTable.ValuesAvailabilitySuffix

/-- Positionally related value vectors have equal finite lengths. -/
theorem entries_length_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {occurrences : List CostRegionOccurrence}
    {smallTable largeTable : TypedCostRegionBoundaryTable source color
      targetFree occurrences}
    {smallValues : TypedCostRegionBoundaryTable.Values source color targetFree
      smallTable}
    {largeValues : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable}
    (_related : ValuesAvailabilitySuffix ambient smallTable largeTable
      smallValues largeValues) :
    smallTable.entries.length = largeTable.entries.length := by
  rw [TypedCostRegionBoundaryTable.entries_length,
    TypedCostRegionBoundaryTable.entries_length]

/-- Every exact small-table position selects the corresponding large-table
position and produces restoration-related semantic atoms.  No boundary-name
lookup occurs, so duplicate or coalesced names cannot redirect the witness. -/
theorem getEntry
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {occurrences : List CostRegionOccurrence}
    {smallTable largeTable : TypedCostRegionBoundaryTable source color
      targetFree occurrences}
    {smallValues : TypedCostRegionBoundaryTable.Values source color targetFree
      smallTable}
    {largeValues : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable}
    (related : ValuesAvailabilitySuffix ambient smallTable largeTable
      smallValues largeValues)
    (index : Fin smallTable.entries.length) :
    let largeIndex : Fin largeTable.entries.length :=
      Fin.cast (entries_length_eq related) index
    TypedCostStaticAtom.RestorationAvailabilitySuffix ambient
      (TypedCostStaticAtom.ofBoundaryValue
        (TypedCostRegionBoundaryTable.Values.getEntry smallTable smallValues
          index).1
        (TypedCostRegionBoundaryTable.Values.getEntry smallTable smallValues
          index).2)
      (TypedCostStaticAtom.ofBoundaryValue
        (TypedCostRegionBoundaryTable.Values.getEntry largeTable largeValues
          largeIndex).1
        (TypedCostRegionBoundaryTable.Values.getEntry largeTable largeValues
          largeIndex).2) := by
  induction related with
  | nil => exact Fin.elim0 index
  | @cons occurrence occurrences smallBoundary largeBoundary smallContent
      largeContent smallTail largeTail smallValue largeValue smallValues
      largeValues head normal_eq tail inductionHypothesis =>
      induction index using Fin.cases with
      | zero =>
          exact
            TypedCostStaticAtom.RestorationAvailabilitySuffix.ofBoundaryValue
              head normal_eq
      | succ previous =>
          exact inductionHypothesis previous

end TypedCostRegionBoundaryTable.ValuesAvailabilitySuffix

namespace ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned

/-- Restoration-related semantic atoms yield a leaf alignment between their
endpoint-local internal names.  The support certificate chooses the unique
regime needed by the leaf proof; no global name equality is required. -/
theorem atomNames
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    {smallValues : TypedCostRegionBoundaryTable.Values source color targetFree
      smallTable}
    {largeValues : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable}
    {smallRoot largeRoot : Pattern}
    {smallInventory : CostStaticParameterInventory source color targetFree
      smallTable smallValues smallRoot}
    {largeInventory : CostStaticParameterInventory source color targetFree
      largeTable largeValues largeRoot}
    (smallEnvironment : CostStaticAtomEnvironment source color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment source color targetFree
      largeInventory)
    {ambient : List TypeExpr}
    (smallSlot : Fin smallEnvironment.atomCount)
    (largeSlot : Fin largeEnvironment.atomCount)
    (related : TypedCostStaticAtom.RestorationAvailabilitySuffix ambient
      (smallEnvironment.atomValue smallSlot)
      (largeEnvironment.atomValue largeSlot))
    (reexposes :
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
        profile
        smallEnvironment.restorationSupport
        smallEnvironment.restorationAssignment
        largeEnvironment.restorationSupport
        largeEnvironment.restorationAssignment ambient
        CostStaticAvailabilityRegime.exposed
        (.fvar (smallEnvironment.atomName smallSlot))
        (.fvar (largeEnvironment.atomName largeSlot))) :
    ∃ regime,
      _root_.Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
        profile
        smallEnvironment.restorationSupport
        smallEnvironment.restorationAssignment
        largeEnvironment.restorationSupport
        largeEnvironment.restorationAssignment ambient regime
        (.fvar (smallEnvironment.atomName smallSlot))
        (.fvar (largeEnvironment.atomName largeSlot)) := by
  rcases related.targetSupport with exposed | sealed
  · refine ⟨CostStaticAvailabilityRegime.exposed,
      .fvar (smallEnvironment.atomName smallSlot)
        (largeEnvironment.atomName largeSlot) ?_ ?_⟩
    intro depth
    simp only [ReflectiveContextSupport.substituteAt,
      CostStaticAvailabilityRegime.largeDepth]
    simp only [CostStaticAtomEnvironment.restorationSupport_atomName,
      CostStaticAtomEnvironment.restorationAssignment_atomName]
    rw [exposed, related.normal_eq, List.length_append]
    congr 1
    omega
    intro impossible
    cases impossible
  · refine ⟨CostStaticAvailabilityRegime.sealed,
      .fvar (smallEnvironment.atomName smallSlot)
        (largeEnvironment.atomName largeSlot) ?_ (fun _ => reexposes)⟩
    intro depth
    simp only [ReflectiveContextSupport.substituteAt,
      CostStaticAvailabilityRegime.largeDepth]
    simp only [CostStaticAtomEnvironment.restorationSupport_atomName,
      CostStaticAtomEnvironment.restorationAssignment_atomName]
    rw [sealed, related.normal_eq]

/-- Exact-regime form of `atomNames`.  The planner chooses the regime at the
selected positional boundary, so clients need not recover it from the older
disjunctive suffix relation. -/
theorem atomNamesAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    {smallValues : TypedCostRegionBoundaryTable.Values source color targetFree
      smallTable}
    {largeValues : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable}
    {smallRoot largeRoot : Pattern}
    {smallInventory : CostStaticParameterInventory source color targetFree
      smallTable smallValues smallRoot}
    {largeInventory : CostStaticParameterInventory source color targetFree
      largeTable largeValues largeRoot}
    (smallEnvironment : CostStaticAtomEnvironment source color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment source color targetFree
      largeInventory)
    {ambient : List TypeExpr} {regime : CostStaticAvailabilityRegime}
    (smallSlot : Fin smallEnvironment.atomCount)
    (largeSlot : Fin largeEnvironment.atomCount)
    (supportAt : CostStaticAvailabilityAt ambient regime
      (smallEnvironment.atomValue smallSlot).key.targetSupport
      (largeEnvironment.atomValue largeSlot).key.targetSupport)
    (normalEq : (smallEnvironment.atomValue smallSlot).key.normal =
      (largeEnvironment.atomValue largeSlot).key.normal)
    (reexposes : regime = .sealed →
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether profile
        smallEnvironment.restorationSupport
        smallEnvironment.restorationAssignment
        largeEnvironment.restorationSupport
        largeEnvironment.restorationAssignment ambient .exposed
        (.fvar (smallEnvironment.atomName smallSlot))
        (.fvar (largeEnvironment.atomName largeSlot))) :
    _root_.Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      profile smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient regime
      (.fvar (smallEnvironment.atomName smallSlot))
      (.fvar (largeEnvironment.atomName largeSlot)) := by
  cases regime with
  | exposed =>
      refine .fvar (smallEnvironment.atomName smallSlot)
        (largeEnvironment.atomName largeSlot) ?_ ?_
      · intro depth
        simp only [ReflectiveContextSupport.substituteAt,
          CostStaticAvailabilityRegime.largeDepth]
        simp only [CostStaticAtomEnvironment.restorationSupport_atomName,
          CostStaticAtomEnvironment.restorationAssignment_atomName]
        rw [supportAt, normalEq, List.length_append]
        congr 1
        omega
      · intro impossible
        cases impossible
  | sealed =>
      refine .fvar (smallEnvironment.atomName smallSlot)
        (largeEnvironment.atomName largeSlot) ?_ (fun _ => reexposes rfl)
      intro depth
      simp only [ReflectiveContextSupport.substituteAt,
        CostStaticAvailabilityRegime.largeDepth]
      simp only [CostStaticAtomEnvironment.restorationSupport_atomName,
        CostStaticAtomEnvironment.restorationAssignment_atomName]
      rw [supportAt, normalEq]

/-- A pair of semantic slots carrying the same rigid source free variable is
aligned in either availability regime.  Its normalized value has no bound
indices, so this source-variable case does not require a support-suffix
equation and remains valid when a quote-sealed path is re-exposed. -/
theorem atomNamesRigid
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    {smallValues : TypedCostRegionBoundaryTable.Values source color targetFree
      smallTable}
    {largeValues : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable}
    {smallRoot largeRoot : Pattern}
    {smallInventory : CostStaticParameterInventory source color targetFree
      smallTable smallValues smallRoot}
    {largeInventory : CostStaticParameterInventory source color targetFree
      largeTable largeValues largeRoot}
    (smallEnvironment : CostStaticAtomEnvironment source color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment source color targetFree
      largeInventory)
    {ambient : List TypeExpr} (regime : CostStaticAvailabilityRegime)
    (smallSlot : Fin smallEnvironment.atomCount)
    (largeSlot : Fin largeEnvironment.atomCount)
    (valueName : String)
    (smallValue : (smallEnvironment.atomValue smallSlot).key.normal =
      .fvar valueName)
    (largeValue : (largeEnvironment.atomValue largeSlot).key.normal =
      .fvar valueName) :
    _root_.Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      profile
      smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient regime
      (.fvar (smallEnvironment.atomName smallSlot))
      (.fvar (largeEnvironment.atomName largeSlot)) := by
  refine .fvar (smallEnvironment.atomName smallSlot)
    (largeEnvironment.atomName largeSlot) ?_ ?_
  · apply ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.fvar_rigid
    · simpa only [CostStaticAtomEnvironment.restorationAssignment_atomName]
        using smallValue
    · simpa only [CostStaticAtomEnvironment.restorationAssignment_atomName]
        using largeValue
  · intro _sealed
    apply ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.fvar_rigid
    · simpa only [CostStaticAtomEnvironment.restorationAssignment_atomName]
        using smallValue
    · simpa only [CostStaticAtomEnvironment.restorationAssignment_atomName]
        using largeValue

/-- Equal closed semantic-atom values align in either regime and remain
aligned if a surrounding quotation is later eliminated.  Support equality is
intentionally absent: closed values cannot observe either endpoint depth. -/
theorem atomNamesClosed
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    {smallValues : TypedCostRegionBoundaryTable.Values source color targetFree
      smallTable}
    {largeValues : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable}
    {smallRoot largeRoot : Pattern}
    {smallInventory : CostStaticParameterInventory source color targetFree
      smallTable smallValues smallRoot}
    {largeInventory : CostStaticParameterInventory source color targetFree
      largeTable largeValues largeRoot}
    (smallEnvironment : CostStaticAtomEnvironment source color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment source color targetFree
      largeInventory)
    {ambient : List TypeExpr} (regime : CostStaticAvailabilityRegime)
    (smallSlot : Fin smallEnvironment.atomCount)
    (largeSlot : Fin largeEnvironment.atomCount)
    (normalEq : (smallEnvironment.atomValue smallSlot).key.normal =
      (largeEnvironment.atomValue largeSlot).key.normal)
    (closed : (smallEnvironment.atomValue smallSlot).key.normal.isWellScopedAt
      0 = true) :
    _root_.Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      profile
      smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient regime
      (.fvar (smallEnvironment.atomName smallSlot))
      (.fvar (largeEnvironment.atomName largeSlot)) := by
  refine .fvar (smallEnvironment.atomName smallSlot)
    (largeEnvironment.atomName largeSlot) ?_ ?_
  · apply ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.fvar_closed
      (value := (smallEnvironment.atomValue smallSlot).key.normal)
    · simp only [CostStaticAtomEnvironment.restorationAssignment_atomName]
    · simpa only [CostStaticAtomEnvironment.restorationAssignment_atomName]
        using normalEq.symm
    · exact closed
  · intro _sealed
    apply ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.fvar_closed
      (value := (smallEnvironment.atomValue smallSlot).key.normal)
    · simp only [CostStaticAtomEnvironment.restorationAssignment_atomName]
    · simpa only [CostStaticAtomEnvironment.restorationAssignment_atomName]
        using normalEq.symm
    · exact closed

/-- An atom stored in the empty target-support fibre is closed, so equal
compact endpoint values supply both the selected regime and its possible
quote-cancellation re-exposure without an additional callback. -/
theorem atomNamesAt_of_smallTargetSupport_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    {smallValues : TypedCostRegionBoundaryTable.Values source color targetFree
      smallTable}
    {largeValues : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable}
    {smallRoot largeRoot : Pattern}
    {smallInventory : CostStaticParameterInventory source color targetFree
      smallTable smallValues smallRoot}
    {largeInventory : CostStaticParameterInventory source color targetFree
      largeTable largeValues largeRoot}
    (smallEnvironment : CostStaticAtomEnvironment source color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment source color targetFree
      largeInventory)
    {ambient : List TypeExpr} (regime : CostStaticAvailabilityRegime)
    (smallSlot : Fin smallEnvironment.atomCount)
    (largeSlot : Fin largeEnvironment.atomCount)
    (smallSupport : (smallEnvironment.atomValue smallSlot).key.targetSupport =
      [])
    (normalEq : (smallEnvironment.atomValue smallSlot).key.normal =
      (largeEnvironment.atomValue largeSlot).key.normal) :
    _root_.Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      profile
      smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient regime
      (.fvar (smallEnvironment.atomName smallSlot))
      (.fvar (largeEnvironment.atomName largeSlot)) := by
  have closed := (smallEnvironment.atomValue smallSlot).normalTyped.isWellScopedAt
  rw [smallSupport] at closed
  exact atomNamesClosed smallEnvironment largeEnvironment regime smallSlot
    largeSlot normalEq closed

mutual
  /-- Structural free-variable renaming preserves availability-transposed
  alignment when each exact source occurrence supplies the leaf certificate
  selected by its quote path.  The callback is occurrence-indexed: neither
  its name nor its regime can vary independently of the token. -/
  noncomputable def renameFVars
      {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
      {smallSupport largeSupport : ContextSupport.Support}
      {smallAssignment largeAssignment : ContextSupport.Assignment}
      {ambient : List TypeExpr} {regime : CostStaticAvailabilityRegime}
      (smallRename largeRename : String → String) (pattern : Pattern)
      (leaf : ∀ occurrence : CostStaticFVarOccurrence pattern,
        _root_.Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
          profile smallSupport smallAssignment largeSupport largeAssignment
            ambient
              (CostStaticAvailabilityRegime.atContext profile regime
                occurrence.context)
              (.fvar (smallRename occurrence.name))
              (.fvar (largeRename occurrence.name))) :
      _root_.Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
        profile smallSupport smallAssignment largeSupport largeAssignment
          ambient regime (Pattern.renameFVars smallRename pattern)
            (Pattern.renameFVars largeRename pattern) :=
    match pattern with
    | .bvar index => by
        simpa only [Pattern.renameFVars] using
          (AvailabilityTransposedPatternAligned.bvar
            (profile := profile) (smallSupport := smallSupport)
            (smallAssignment := smallAssignment)
            (largeSupport := largeSupport)
            (largeAssignment := largeAssignment) (ambient := ambient)
            regime index)
    | .fvar name => by
        let occurrence : CostStaticFVarOccurrence (.fvar name) :=
          { name := name
            context := .hole
            selected := .here }
        simpa [Pattern.renameFVars, occurrence,
          CostStaticAvailabilityRegime.atContext] using leaf occurrence
    | .apply constructor arguments =>
        by
          simpa only [Pattern.renameFVars] using
            (.apply regime constructor
              (renameFVarsList smallRename largeRename arguments
                (if ReflectiveContextSupport.isQuoteConstructor profile constructor
                  then .sealed else regime)
                (fun occurrence => by
                  simpa [CostStaticFVarListOccurrence.inApply,
                    CostStaticAvailabilityRegime.atContext_comp,
                    CostStaticAvailabilityRegime.atContext] using
                    leaf (occurrence.inApply constructor))))
    | .lambda binder body =>
        by
          simpa only [Pattern.renameFVars] using
            (.lambda regime binder
              (renameFVars smallRename largeRename body (fun occurrence => by
                simpa [CostStaticFVarOccurrence.inContext,
                  CostStaticAvailabilityRegime.atContext_comp,
                  CostStaticAvailabilityRegime.atContext] using
                  leaf (occurrence.inContext (.lambda binder .hole)))))
    | .multiLambda arity binders body =>
        by
          simpa only [Pattern.renameFVars] using
            (.multiLambda regime arity binders
              (renameFVars smallRename largeRename body (fun occurrence => by
                simpa [CostStaticFVarOccurrence.inContext,
                  CostStaticAvailabilityRegime.atContext_comp,
                  CostStaticAvailabilityRegime.atContext] using
                  leaf (occurrence.inContext
                    (.multiLambda arity binders .hole)))))
    | .subst body replacement =>
        by
          simpa only [Pattern.renameFVars] using
            (.subst regime
              (renameFVars smallRename largeRename body (fun occurrence => by
                simpa [CostStaticFVarOccurrence.inContext,
                  CostStaticAvailabilityRegime.atContext_comp,
                  CostStaticAvailabilityRegime.atContext] using
                  leaf (occurrence.inContext
                    (.substBody .hole replacement))))
              (renameFVars smallRename largeRename replacement
                (fun occurrence => by
                  simpa [CostStaticFVarOccurrence.inContext,
                    CostStaticAvailabilityRegime.atContext_comp,
                    CostStaticAvailabilityRegime.atContext] using
                    leaf (occurrence.inContext
                      (.substReplacement body .hole)))))
    | .collection collectionType elements rest =>
        by
          simpa only [Pattern.renameFVars] using
            (.collection regime collectionType rest
              (renameFVarsList smallRename largeRename elements regime
                (fun occurrence => by
                  simpa [CostStaticFVarListOccurrence.inCollection,
                    CostStaticAvailabilityRegime.atContext_comp,
                    CostStaticAvailabilityRegime.atContext] using
                    leaf (occurrence.inCollection collectionType rest))))
  termination_by 3 * sizeOf pattern + 2

  /-- Positional list companion of occurrence-indexed structural renaming. -/
  noncomputable def renameFVarsList
      {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
      {smallSupport largeSupport : ContextSupport.Support}
      {smallAssignment largeAssignment : ContextSupport.Assignment}
      {ambient : List TypeExpr}
      (smallRename largeRename : String → String) :
      (patterns : List Pattern) → (regime : CostStaticAvailabilityRegime) →
      (leaf : ∀ occurrence : CostStaticFVarListOccurrence patterns,
        _root_.Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
          profile smallSupport smallAssignment largeSupport largeAssignment
            ambient
              (CostStaticAvailabilityRegime.atContext profile regime
                occurrence.occurrence.context)
              (.fvar (smallRename occurrence.occurrence.name))
              (.fvar (largeRename occurrence.occurrence.name))) →
      _root_.Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAlignedList
        profile smallSupport smallAssignment largeSupport largeAssignment
          ambient regime (patterns.map (Pattern.renameFVars smallRename))
            (patterns.map (Pattern.renameFVars largeRename))
    | [], regime, _ => .nil regime
    | head :: tail, regime, leaf =>
        .cons regime
          (renameFVars smallRename largeRename head (fun occurrence => by
            let selected : CostStaticFVarListOccurrence (head :: tail) :=
              { position := ⟨0, by simp⟩
                occurrence := by simpa using occurrence }
            simpa [selected, CostStaticAvailabilityRegime.atContext] using
              leaf selected))
          (renameFVarsList smallRename largeRename tail regime
            (fun occurrence => by
              let selected : CostStaticFVarListOccurrence (head :: tail) :=
                { position := Fin.succ occurrence.position
                  occurrence := by simpa using occurrence.occurrence }
              simpa [selected, CostStaticAvailabilityRegime.atContext] using
                leaf selected))
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_wf <;> omega
end

end ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned

namespace CostStaticAtomEnvironment

/-- Reifying one authored frame in two endpoint atom environments preserves
availability-transposed alignment when every exact authored occurrence supplies
its path-selected semantic-atom certificate. -/
theorem reify_availabilityTransposedAligned
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    {smallValues : TypedCostRegionBoundaryTable.Values source color targetFree
      smallTable}
    {largeValues : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable}
    {smallRoot largeRoot : Pattern}
    {smallInventory : CostStaticParameterInventory source color targetFree
      smallTable smallValues smallRoot}
    {largeInventory : CostStaticParameterInventory source color targetFree
      largeTable largeValues largeRoot}
    (smallEnvironment : CostStaticAtomEnvironment source color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment source color targetFree
      largeInventory)
    {ambient : List TypeExpr} {regime : CostStaticAvailabilityRegime}
    {pattern : Pattern}
    (leaf : ∀ occurrence : CostStaticFVarOccurrence pattern,
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
        source.costWholeReflectionProfile
        smallEnvironment.restorationSupport
        smallEnvironment.restorationAssignment
        largeEnvironment.restorationSupport
        largeEnvironment.restorationAssignment ambient
        (CostStaticAvailabilityRegime.atContext
          source.costWholeReflectionProfile regime occurrence.context)
        (.fvar (smallEnvironment.reifyName occurrence.name))
        (.fvar (largeEnvironment.reifyName occurrence.name))) :
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      source.costWholeReflectionProfile
      smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient regime
      (smallEnvironment.reify pattern) (largeEnvironment.reify pattern) := by
  rw [smallEnvironment.reify_eq_renameFVars,
    largeEnvironment.reify_eq_renameFVars]
  exact
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.renameFVars
      smallEnvironment.reifyName largeEnvironment.reifyName pattern leaf

end CostStaticAtomEnvironment

end Mettapedia.GSLT.LanguageDef
