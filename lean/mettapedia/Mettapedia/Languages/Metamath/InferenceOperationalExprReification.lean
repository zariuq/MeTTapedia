import Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness

/-!
# Canonical reification of operational Metamath expressions

`Metamath.Spec.Expr` retains symbol names but erases the runtime distinction
between constants and variables.  Relative to an explicit list of active
variable names, this file reconstructs the unique frame-respecting tagged
formula: an active name is tagged as a variable and every other name as a
constant.

This is a canonical section of `operationalExpr`, not a reverse source-proof
theorem.  It does not recover labels, finite substitution syntax, database
chronology, or a runtime stack prefix.
-/

namespace Mettapedia.Languages.Metamath.InferenceOperationalExprReification

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceVariableClassification
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness

/-! ## Canonical tags -/

/-- Reconstruct the frame-determined runtime tag of one erased symbol name. -/
def reifyOperationalSym (activeVariableNames : List String)
    (name : String) : RuntimeSym :=
  if name ∈ activeVariableNames then .var name else .const name

@[simp] theorem reifyOperationalSym_of_mem
    (activeVariableNames : List String) (name : String)
    (hmem : name ∈ activeVariableNames) :
    reifyOperationalSym activeVariableNames name = .var name := by
  simp [reifyOperationalSym, hmem]

@[simp] theorem reifyOperationalSym_of_not_mem
    (activeVariableNames : List String) (name : String)
    (hnotMem : name ∉ activeVariableNames) :
    reifyOperationalSym activeVariableNames name = .const name := by
  simp [reifyOperationalSym, hnotMem]

@[simp] theorem reifyOperationalSym_value
    (activeVariableNames : List String) (name : String) :
    (reifyOperationalSym activeVariableNames name).value = name := by
  by_cases hmem : name ∈ activeVariableNames <;>
    simp [reifyOperationalSym, hmem, Metamath.Verify.Sym.value]

/-- Canonical frame-relative tagged representative of an operational
expression. -/
def reifyOperationalExpr (activeVariableNames : List String)
    (expression : Metamath.Spec.Expr) : ConstantHeadedFormula :=
  { typecode := expression.typecode.c
    body := expression.syms.map
      (reifyOperationalSym activeVariableNames) }

@[simp] theorem reifyOperationalExpr_typecode
    (activeVariableNames : List String) (expression : Metamath.Spec.Expr) :
    (reifyOperationalExpr activeVariableNames expression).typecode =
      expression.typecode.c := by
  rfl

@[simp] theorem reifyOperationalExpr_body
    (activeVariableNames : List String) (expression : Metamath.Spec.Expr) :
    (reifyOperationalExpr activeVariableNames expression).body =
      expression.syms.map (reifyOperationalSym activeVariableNames) := by
  rfl

/-! ## Exact erasure and classification -/

/-- Reification is an exact section of operational tag erasure. -/
@[simp] theorem operationalExpr_reifyOperationalExpr
    (activeVariableNames : List String) (expression : Metamath.Spec.Expr) :
    operationalExpr (reifyOperationalExpr activeVariableNames expression) =
      expression := by
  have htypecode :
      (operationalExpr
        (reifyOperationalExpr activeVariableNames expression)).typecode =
        expression.typecode := by
    rcases expression with ⟨⟨typecode⟩, symbols⟩
    simp [reifyOperationalExpr]
  have hsymbols :
      (operationalExpr
        (reifyOperationalExpr activeVariableNames expression)).syms =
        expression.syms := by
    rw [operationalExpr_syms, reifyOperationalExpr_body, List.map_map]
    induction expression.syms with
    | nil => rfl
    | cons name names ih =>
        simp only [List.map_cons, Function.comp_apply,
          reifyOperationalSym_value, ih]
  cases hoperational : operationalExpr
      (reifyOperationalExpr activeVariableNames expression) with
  | mk operationalTypecode operationalSymbols =>
      cases expression with
      | mk expressionTypecode expressionSymbols =>
          simp only [hoperational] at htypecode hsymbols
          cases htypecode
          cases hsymbols
          rfl

/-- Every symbol reconstructed by the canonical section agrees with the
supplied active-variable classification. -/
@[simp] theorem reifyOperationalExpr_respectsFrame
    (activeVariableNames : List String) (expression : Metamath.Spec.Expr) :
    formulaSymbolsRespectFrame activeVariableNames
      (reifyOperationalExpr activeVariableNames expression) = true := by
  simp only [formulaSymbolsRespectFrame, reifyOperationalExpr_body,
    List.all_map]
  apply List.all_eq_true.mpr
  intro name _hname
  by_cases hmem : name ∈ activeVariableNames
  · simp [reifyOperationalSym, hmem, symbolRespectsFrame]
  · simp [reifyOperationalSym, hmem, symbolRespectsFrame]

private theorem bodyVariables_map_reifyOperationalSym
    (activeVariableNames names : List String) :
    BodyVariables
        (names.map (reifyOperationalSym activeVariableNames)) =
      names.filter (fun name => name ∈ activeVariableNames) := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      by_cases hmem : name ∈ activeVariableNames
      · simp [reifyOperationalSym, BodyVariables, hmem, ih]
      · simp [reifyOperationalSym, BodyVariables, hmem, ih]

/-- Explicit tags select exactly the active names, preserving order and
duplicates. -/
theorem bodyVariables_reifyOperationalExpr
    (activeVariableNames : List String) (expression : Metamath.Spec.Expr) :
    BodyVariables (reifyOperationalExpr activeVariableNames expression).body =
      expression.syms.filter (fun name => name ∈ activeVariableNames) := by
  exact bodyVariables_map_reifyOperationalSym
    activeVariableNames expression.syms

/-- The tagged variable traversal agrees exactly with the operational
specification's active-name traversal. -/
theorem varsInExpr_eq_bodyVariables_reifyOperationalExpr
    (activeVariableNames : List String) (expression : Metamath.Spec.Expr) :
    Metamath.Spec.varsInExpr
        (activeVariableNames.map Metamath.Spec.Variable.mk) expression =
      (BodyVariables
        (reifyOperationalExpr activeVariableNames expression).body).map
        Metamath.Spec.Variable.mk := by
  have hnames :
      Metamath.Kernel.varNames
          (activeVariableNames.map Metamath.Spec.Variable.mk) =
        activeVariableNames := by
    induction activeVariableNames with
    | nil => rfl
    | cons name names ih =>
        simp only [List.map_cons, Metamath.Kernel.varNames]
        exact congrArg (List.cons name) ih
  have hclassification :=
    varsInExpr_eq_bodyVariables_of_respectsFrame
      (activeVariableNames.map Metamath.Spec.Variable.mk)
      activeVariableNames
      (reifyOperationalExpr activeVariableNames expression)
      hnames
      (reifyOperationalExpr_respectsFrame activeVariableNames expression)
  change
    Metamath.Spec.varsInExpr
        (activeVariableNames.map Metamath.Spec.Variable.mk)
        (operationalExpr
          (reifyOperationalExpr activeVariableNames expression)) =
      (BodyVariables
        (reifyOperationalExpr activeVariableNames expression).body).map
        Metamath.Spec.Variable.mk at hclassification
  simpa using hclassification

/-! ## Uniqueness on frame-respecting tagged formulas -/

private theorem reifyOperationalSym_value_of_respectsFrame
    (activeVariableNames : List String) (symbol : RuntimeSym)
    (hrespect :
      symbolRespectsFrame activeVariableNames symbol = true) :
    reifyOperationalSym activeVariableNames symbol.value = symbol := by
  cases symbol with
  | const constantName =>
      have hcontains :
          activeVariableNames.contains constantName = false :=
        (Bool.not_eq_true' _).mp hrespect
      have hnotMem : constantName ∉ activeVariableNames := by
        intro hmem
        have htrue : activeVariableNames.contains constantName = true :=
          List.contains_iff_mem.mpr hmem
        rw [hcontains] at htrue
        contradiction
      simp [reifyOperationalSym, hnotMem,
        Metamath.Verify.Sym.value]
  | var variableName =>
      have hmem : variableName ∈ activeVariableNames :=
        List.contains_iff_mem.mp hrespect
      simp [reifyOperationalSym, hmem,
        Metamath.Verify.Sym.value]

private theorem map_reifyOperationalSym_value_of_all_respectsFrame
    (activeVariableNames : List String) (body : List RuntimeSym)
    (hrespect :
      body.all (symbolRespectsFrame activeVariableNames) = true) :
    body.map (fun symbol =>
        reifyOperationalSym activeVariableNames symbol.value) = body := by
  induction body with
  | nil => rfl
  | cons symbol body ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hrespect
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨reifyOperationalSym_value_of_respectsFrame
          activeVariableNames symbol hrespect.1,
        ih hrespect.2⟩

/-- Operational erasure followed by canonical reification returns every
already frame-respecting tagged formula exactly. -/
theorem reifyOperationalExpr_operationalExpr_of_respectsFrame
    (activeVariableNames : List String) (formula : ConstantHeadedFormula)
    (hrespect :
      formulaSymbolsRespectFrame activeVariableNames formula = true) :
    reifyOperationalExpr activeVariableNames (operationalExpr formula) =
      formula := by
  rcases formula with ⟨typecode, body⟩
  simp only [formulaSymbolsRespectFrame] at hrespect
  have hbody := map_reifyOperationalSym_value_of_all_respectsFrame
    activeVariableNames body hrespect
  change
    body.map (reifyOperationalSym activeVariableNames ∘
      Metamath.Verify.Sym.value) = body at hbody
  simp only [reifyOperationalExpr, operationalExpr_typecode,
    operationalExpr_syms, List.map_map]
  rw [hbody]

/-- A frame-respecting tagged representative with a given erasure is the
canonical representative. -/
theorem eq_reifyOperationalExpr_of_respectsFrame
    (activeVariableNames : List String) (formula : ConstantHeadedFormula)
    (expression : Metamath.Spec.Expr)
    (hrespect :
      formulaSymbolsRespectFrame activeVariableNames formula = true)
    (herasure : operationalExpr formula = expression) :
    formula = reifyOperationalExpr activeVariableNames expression := by
  rw [← herasure]
  exact (reifyOperationalExpr_operationalExpr_of_respectsFrame
    activeVariableNames formula hrespect).symm

/-! ## Executable boundaries -/

section Examples

private def erasedExample : Metamath.Spec.Expr :=
  ⟨⟨"wff"⟩, ["x", "c", "x"]⟩

/-- Membership determines the reconstructed tag, while order and duplicate
occurrences are retained. -/
example :
    (reifyOperationalExpr ["x"] erasedExample).body =
      [.var "x", .const "c", .var "x"] ∧
    (reifyOperationalExpr [] erasedExample).body =
      [.const "x", .const "c", .const "x"] := by
  decide

private def malformedActiveConstant : ConstantHeadedFormula :=
  ⟨"wff", [.const "x"]⟩

private def canonicalActiveVariable : ConstantHeadedFormula :=
  ⟨"wff", [.var "x"]⟩

/-- Negative boundary: operational erasure cannot distinguish a malformed
constant tag from the canonical active-variable tag.  Only the latter respects
the supplied frame. -/
example :
    malformedActiveConstant ≠ canonicalActiveVariable ∧
    operationalExpr malformedActiveConstant =
      operationalExpr canonicalActiveVariable ∧
    formulaSymbolsRespectFrame ["x"] malformedActiveConstant = false ∧
    formulaSymbolsRespectFrame ["x"] canonicalActiveVariable = true := by
  decide

end Examples

end Mettapedia.Languages.Metamath.InferenceOperationalExprReification
