import Mettapedia.Languages.Metamath.InferenceProjection
import Metamath.WellFormedness

/-!
# Parser invariants for the Metamath inference projection

This file connects `mm-lean4`'s propositional parser invariants to the
executable symbol-declaration and DV-orientation gates used by the inference
projection.  The projection's `List.mergeSort_perm` bridge supplies the
membership theorem needed to prove that its deterministic `objectEntries`
list is extensionally exact with respect to the runtime object map.

No prefix-completeness or runtime-step correspondence claim is made here.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjectionParserBridge

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection

/-- Exact extensional correspondence between an inspectable entry list and
the live runtime object map.  Both directions are retained so the hypothesis
cannot hide missing or fabricated entries. -/
def ObjectEntriesExact (db : RuntimeDB)
    (entries : List (String × Metamath.Verify.Object)) : Prop :=
  ∀ label object,
    (label, object) ∈ entries ↔ db.find? label = some object

/-- The unsorted runtime map enumeration has the exact correspondence needed
by the bridge. -/
theorem rawObjectEntries_exact (db : RuntimeDB) :
    ObjectEntriesExact db db.objects.toList := by
  intro label object
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
  rfl

/-- The projection's deterministic ordering preserves the exact runtime map
correspondence by the library theorem that merge sort is a permutation. -/
theorem objectEntries_exact (db : RuntimeDB) :
    ObjectEntriesExact db (objectEntries db) := by
  intro label object
  rw [mem_objectEntries_iff]
  exact rawObjectEntries_exact db label object

private theorem declaredConstantNames_mem_of_isConst
    (db : RuntimeDB) (entries : List (String × Metamath.Verify.Object))
    (hexact : ObjectEntriesExact db entries)
    (hembedded : entries.all fun entry =>
      objectEmbeddedNameMatches entry.1 entry.2)
    (constantName : String) (hconstant : db.isConst constantName = true) :
    constantName ∈ declaredConstantNames entries := by
  unfold Metamath.Verify.DB.isConst at hconstant
  cases hfind : db.find? constantName with
  | none => simp [hfind] at hconstant
  | some object =>
      cases object with
      | const embeddedName =>
          have hmem : (constantName, .const embeddedName) ∈ entries :=
            (hexact constantName (.const embeddedName)).2 hfind
          have hmatch :=
            (List.all_eq_true.mp hembedded)
              (constantName, .const embeddedName) hmem
          have heq : embeddedName = constantName := by
            simpa [objectEmbeddedNameMatches] using hmatch
          apply List.mem_filterMap.mpr
          exact ⟨(constantName, .const embeddedName), hmem, by simp [heq]⟩
      | var _ => simp [hfind] at hconstant
      | hyp _ _ _ => simp [hfind] at hconstant
      | assert _ _ _ => simp [hfind] at hconstant

private theorem declaredVariableNames_mem_of_isVar
    (db : RuntimeDB) (entries : List (String × Metamath.Verify.Object))
    (hexact : ObjectEntriesExact db entries)
    (hembedded : entries.all fun entry =>
      objectEmbeddedNameMatches entry.1 entry.2)
    (variableName : String) (hvariable : db.isVar variableName = true) :
    variableName ∈ declaredVariableNames entries := by
  unfold Metamath.Verify.DB.isVar at hvariable
  cases hfind : db.find? variableName with
  | none => simp [hfind] at hvariable
  | some object =>
      cases object with
      | var embeddedName =>
          have hmem : (variableName, .var embeddedName) ∈ entries :=
            (hexact variableName (.var embeddedName)).2 hfind
          have hmatch :=
            (List.all_eq_true.mp hembedded)
              (variableName, .var embeddedName) hmem
          have heq : embeddedName = variableName := by
            simpa [objectEmbeddedNameMatches] using hmatch
          apply List.mem_filterMap.mpr
          exact ⟨(variableName, .var embeddedName), hmem, by simp [heq]⟩
      | const _ => simp [hfind] at hvariable
      | hyp _ _ _ => simp [hfind] at hvariable
      | assert _ _ _ => simp [hfind] at hvariable

/-- `FormulaSymbolsDeclared` implies the executable declaration gate for any
entry list that exactly reflects the runtime object map and passes the same
embedded-name check used by `projectPrefix?`. -/
theorem formulaSymbolsRespectDeclarations_of_formulaSymbolsDeclared
    (db : RuntimeDB) (entries : List (String × Metamath.Verify.Object))
    (runtimeFormula : RuntimeFormula) (formula : ConstantHeadedFormula)
    (hexact : ObjectEntriesExact db entries)
    (hembedded : entries.all fun entry =>
      objectEmbeddedNameMatches entry.1 entry.2)
    (hdeclared : Metamath.WF.FormulaSymbolsDeclared db runtimeFormula)
    (hview : ConstantHeadedFormula.ofRuntime? runtimeFormula = some formula) :
    formulaSymbolsRespectDeclarations
      (declaredConstantNames entries) (declaredVariableNames entries) formula = true := by
  have hruntime : runtimeFormula = formula.toRuntime :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff runtimeFormula formula).mp hview
  rw [hruntime] at hdeclared
  unfold formulaSymbolsRespectDeclarations
  simp only [Bool.and_eq_true]
  constructor
  · apply List.contains_iff_mem.mpr
    apply declaredConstantNames_mem_of_isConst db entries hexact hembedded
    exact hdeclared (.const formula.typecode) (by
      simp [ConstantHeadedFormula.toRuntime])
  · apply List.all_eq_true.mpr
    intro symbol hsymbol
    cases symbol with
    | const constantName =>
        apply List.contains_iff_mem.mpr
        apply declaredConstantNames_mem_of_isConst db entries hexact hembedded
        exact hdeclared (.const constantName) (by
          simp [ConstantHeadedFormula.toRuntime, hsymbol])
    | var variableName =>
        apply List.contains_iff_mem.mpr
        apply declaredVariableNames_mem_of_isVar db entries hexact hembedded
        exact hdeclared (.var variableName) (by
          simp [ConstantHeadedFormula.toRuntime, hsymbol])

/-- The object-entry specialization needed by the executable projection. -/
theorem formulaSymbolsRespectObjectDeclarations
    (db : RuntimeDB) (runtimeFormula : RuntimeFormula)
    (formula : ConstantHeadedFormula)
    (hembedded : (objectEntries db).all fun entry =>
      objectEmbeddedNameMatches entry.1 entry.2)
    (hdeclared : Metamath.WF.FormulaSymbolsDeclared db runtimeFormula)
    (hview : ConstantHeadedFormula.ofRuntime? runtimeFormula = some formula) :
    formulaSymbolsRespectDeclarations
      (declaredConstantNames (objectEntries db))
      (declaredVariableNames (objectEntries db)) formula = true := by
  exact formulaSymbolsRespectDeclarations_of_formulaSymbolsDeclared
    db (objectEntries db) runtimeFormula formula (objectEntries_exact db)
      hembedded hdeclared hview

/-- `WellScopedDB` records declaration correctness for every stored assertion
formula, independently of the projection's entry enumeration. -/
theorem assertion_formulaSymbolsDeclared_of_wellScopedDB
    (db : RuntimeDB) (label embeddedLabel : String)
    (runtimeFormula : RuntimeFormula) (frame : RuntimeFrame)
    (hscoped : Metamath.WF.WellScopedDB db)
    (hfind : db.find? label = some (.assert runtimeFormula frame embeddedLabel)) :
    Metamath.WF.FormulaSymbolsDeclared db runtimeFormula :=
  (hscoped.2 label (.assert runtimeFormula frame embeddedLabel) hfind).2.2

/-- `WellScopedDB` records the same global declaration correctness for every
stored hypothesis formula. -/
theorem hypothesis_formulaSymbolsDeclared_of_wellScopedDB
    (db : RuntimeDB) (label embeddedLabel : String) (essential : Bool)
    (runtimeFormula : RuntimeFormula)
    (hscoped : Metamath.WF.WellScopedDB db)
    (hfind : db.find? label = some (.hyp essential runtimeFormula embeddedLabel)) :
    Metamath.WF.FormulaSymbolsDeclared db runtimeFormula :=
  (hscoped.2 label (.hyp essential runtimeFormula embeddedLabel) hfind).2

/-- A stored assertion inherits the executable declaration gate directly from
`WellScopedDB` once its runtime formula is decoded. -/
theorem assertion_formulaSymbolsRespectObjectDeclarations
    (db : RuntimeDB) (label embeddedLabel : String)
    (runtimeFormula : RuntimeFormula) (frame : RuntimeFrame)
    (formula : ConstantHeadedFormula)
    (hembedded : (objectEntries db).all fun entry =>
      objectEmbeddedNameMatches entry.1 entry.2)
    (hscoped : Metamath.WF.WellScopedDB db)
    (hfind : db.find? label = some (.assert runtimeFormula frame embeddedLabel))
    (hview : ConstantHeadedFormula.ofRuntime? runtimeFormula = some formula) :
    formulaSymbolsRespectDeclarations
      (declaredConstantNames (objectEntries db))
      (declaredVariableNames (objectEntries db)) formula = true := by
  have hdeclared : Metamath.WF.FormulaSymbolsDeclared db runtimeFormula :=
    assertion_formulaSymbolsDeclared_of_wellScopedDB
      db label embeddedLabel runtimeFormula frame hscoped hfind
  exact formulaSymbolsRespectObjectDeclarations
    db runtimeFormula formula hembedded hdeclared hview

/-- A stored hypothesis likewise inherits the declaration gate from
`WellScopedDB`; activity in the current frame is not needed for this global
symbol-declaration fact. -/
theorem hypothesis_formulaSymbolsRespectObjectDeclarations
    (db : RuntimeDB) (label embeddedLabel : String) (essential : Bool)
    (runtimeFormula : RuntimeFormula) (formula : ConstantHeadedFormula)
    (hembedded : (objectEntries db).all fun entry =>
      objectEmbeddedNameMatches entry.1 entry.2)
    (hscoped : Metamath.WF.WellScopedDB db)
    (hfind : db.find? label = some (.hyp essential runtimeFormula embeddedLabel))
    (hview : ConstantHeadedFormula.ofRuntime? runtimeFormula = some formula) :
    formulaSymbolsRespectDeclarations
      (declaredConstantNames (objectEntries db))
      (declaredVariableNames (objectEntries db)) formula = true := by
  have hdeclared : Metamath.WF.FormulaSymbolsDeclared db runtimeFormula :=
    hypothesis_formulaSymbolsDeclared_of_wellScopedDB
      db label embeddedLabel essential runtimeFormula hscoped hfind
  exact formulaSymbolsRespectObjectDeclarations
    db runtimeFormula formula hembedded hdeclared hview

/-- The strict canonical orientation component of `frameDVValid` is already a
parser invariant: every stored DV pair in a well-scoped frame satisfies
`left < right`. -/
theorem frameDVStrictOrder_of_wellScopedFrame
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hscoped : Metamath.WF.WellScopedFrame db frame) :
    frame.dj.toList.all (fun pair => decide (pair.1 < pair.2)) = true := by
  apply List.all_eq_true.mpr
  intro pair hpair
  exact decide_eq_true (hscoped.2 pair.1 pair.2 hpair).1

/-- The current parser frame has strict canonical DV orientation whenever the
runtime database satisfies `WellScopedDB`. -/
theorem currentFrameDVStrictOrder_of_wellScopedDB
    (db : RuntimeDB) (hscoped : Metamath.WF.WellScopedDB db) :
    db.frame.dj.toList.all (fun pair => decide (pair.1 < pair.2)) = true :=
  frameDVStrictOrder_of_wellScopedFrame db db.frame hscoped.1

/-- Every stored assertion frame has strict canonical DV orientation under
the same parser invariant. -/
theorem assertionFrameDVStrictOrder_of_wellScopedDB
    (db : RuntimeDB) (label embeddedLabel : String)
    (runtimeFormula : RuntimeFormula) (frame : RuntimeFrame)
    (hscoped : Metamath.WF.WellScopedDB db)
    (hfind : db.find? label = some (.assert runtimeFormula frame embeddedLabel)) :
    frame.dj.toList.all (fun pair => decide (pair.1 < pair.2)) = true := by
  have hframe : Metamath.WF.WellScopedFrame db frame :=
    (hscoped.2 label (.assert runtimeFormula frame embeddedLabel) hfind).1
  exact frameDVStrictOrder_of_wellScopedFrame db frame hframe

section DeclarationGateExamples

private def declaredExampleFormula : ConstantHeadedFormula :=
  ⟨"wff", [.var "ph"]⟩

/-- Positive fixture: source names and embedded names coincide. -/
example :
    formulaSymbolsRespectDeclarations
      (declaredConstantNames [("wff", .const "wff")])
      (declaredVariableNames [("ph", .var "ph")])
      declaredExampleFormula = true := by
  decide

/-- Negative fixture: a mismatched embedded constant name must not certify the
source spelling used as the formula typecode. -/
example :
    formulaSymbolsRespectDeclarations
      (declaredConstantNames [("wff", .const "not-wff")])
      (declaredVariableNames [("ph", .var "ph")])
      declaredExampleFormula = false := by
  decide

end DeclarationGateExamples

end Mettapedia.Languages.Metamath.InferenceProjectionParserBridge
