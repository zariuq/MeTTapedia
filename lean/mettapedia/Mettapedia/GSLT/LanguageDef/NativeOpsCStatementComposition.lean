import Mettapedia.GSLT.LanguageDef.NativeOpsCNormalization

/-! Composition of exact C statement, case and arm normalization certificates. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

theorem numeric_declare_none (representation : Representation) (environment : Environment)
    (result : NativeType) (type : CType) (name : Name) (value : CExpr) (following : List CStatement) :
    numericCheck? representation environment result (.declare type name value) following = none := by
  unfold numericCheck?
  cases nextNumericOperation? representation environment following with
  | none => rfl
  | some pair => cases pair; rfl

theorem normalize_declare (representation : Representation) (environment : Environment)
    (result : NativeType) (type : CType) (name : Name) (value : CExpr) (following : List CStatement) :
    normalizeStatement? representation result environment (.declare type name value) following =
      declare? representation environment type name value := by
  rw [normalizeStatement?]
  change (match numericCheck? representation environment result (.declare type name value) following with
    | some check => some (Normalized.mk [check] environment)
    | none => declare? representation environment type name value) = _
  rw [numeric_declare_none]

theorem normalize_discard (representation : Representation) (result : NativeType)
    (environment : Environment) (value : CExpr) (following : List CStatement)
    (discarded : pureDiscard environment value = true) :
    normalizeStatement? representation result environment (.effect value) following =
      some ⟨[], environment⟩ := by
  have numeric : numericCheck? representation environment result (.effect value) following = none := by
    unfold numericCheck?
    cases nextNumericOperation? representation environment following with
    | none => rfl
    | some pair => cases pair; rfl
  simp only [normalizeStatement?, contextCheck?, numeric, discarded, if_true]

theorem normalize_return_atom (representation : Representation) (result : NativeType)
    (environment : Environment) (value : CExpr) (following : List CStatement) (atom : NativeIR.Atom)
    (checked : typedAtom? representation environment value result = some atom) :
    normalizeStatement? representation result environment (.return (some value)) following =
      some ⟨[NativeIR.Instruction.return atom], environment⟩ := by
  have numeric : numericCheck? representation environment result (.return (some value)) following = none := by
    unfold numericCheck?
    cases nextNumericOperation? representation environment following with
    | none => rfl
    | some pair => cases pair; rfl
  simp only [normalizeStatement?, contextCheck?, numeric, checked, bind, Option.bind]

theorem normalize_switch_of_parts (representation : Representation) (result : NativeType)
    (environment : Environment) (selector : CExpr) (arms : List (CExpr × List CStatement))
    (otherwise following : List CStatement) (atom : NativeIR.Atom)
    (checkedArms : List (BitVec 64 × List NativeIR.Instruction)) (checkedOtherwise : Normalized)
    (selectorChecked : typedAtom? representation environment selector .word = some atom)
    (armsChecked : normalizeCases? representation result environment arms = some checkedArms)
    (otherwiseChecked : normalizeArm? representation result environment otherwise = some checkedOtherwise) :
    normalizeStatement? representation result environment (.switch selector arms otherwise) following =
      some ⟨[NativeIR.Instruction.switch atom checkedArms checkedOtherwise.code], environment⟩ := by
  have numeric : numericCheck? representation environment result (.switch selector arms otherwise) following = none := by
    unfold numericCheck?
    cases nextNumericOperation? representation environment following with
    | none => rfl
    | some pair => cases pair; rfl
  simp only [normalizeStatement?, contextCheck?, numeric, selectorChecked, armsChecked,
    otherwiseChecked, bind, Option.bind]

theorem normalize_statements_cons (representation : Representation) (result : NativeType)
    (environment : Environment) (first : CStatement) (rest : List CStatement)
    (head tail : Normalized)
    (headChecked : normalizeStatement? representation result environment first rest = some head)
    (tailChecked : normalizeStatements? representation result head.environment rest = some tail) :
    normalizeStatements? representation result environment (first :: rest) =
      some ⟨head.code ++ tail.code, tail.environment⟩ := by
  rw [normalizeStatements?, headChecked]
  change (do
    let other ← normalizeStatements? representation result head.environment rest
    some (Normalized.mk (head.code ++ other.code) other.environment)) = _
  rw [tailChecked]
  rfl

theorem normalize_arm_cons (representation : Representation) (result : NativeType)
    (environment : Environment) (first next : CStatement) (rest : List CStatement)
    (head tail : Normalized)
    (headChecked : normalizeStatement? representation result environment first (next :: rest) = some head)
    (tailChecked : normalizeArm? representation result head.environment (next :: rest) = some tail) :
    normalizeArm? representation result environment (first :: next :: rest) =
      some ⟨head.code ++ tail.code, tail.environment⟩ := by
  rw [normalizeArm?, headChecked]
  change (do
    let other ← normalizeArm? representation result head.environment (next :: rest)
    some (Normalized.mk (head.code ++ other.code) other.environment)) = _
  rw [tailChecked]
  rfl
  intro _ impossible
  cases impossible

theorem normalize_cases_cons (representation : Representation) (result : NativeType)
    (environment : Environment) (key : BitVec 64) (body : List CStatement)
    (rest : List (CExpr × List CStatement)) (head : Normalized)
    (tail : List (BitVec 64 × List NativeIR.Instruction))
    (headChecked : normalizeArm? representation result environment body = some head)
    (tailChecked : normalizeCases? representation result environment rest = some tail) :
    normalizeCases? representation result environment ((CExpr.word key, body) :: rest) =
      some ((key, head.code) :: tail) := by
  rw [normalizeCases?, headChecked]
  change (do
    let other ← normalizeCases? representation result environment rest
    some ((key, head.code) :: other)) = _
  rw [tailChecked]
  rfl

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
