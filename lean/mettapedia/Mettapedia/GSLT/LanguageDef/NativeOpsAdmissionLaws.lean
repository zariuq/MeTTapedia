import Mettapedia.GSLT.LanguageDef.NativeOpsNames

/-! Logical components of complete operational source admission. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

def declaredNames (program : Program) : List String :=
  program.interface.records.map Record.name ++ program.interface.opaques.map Opaque.name ++
    program.interface.externals.map (fun external => external.header.name) ++
    program.functions.map (fun function => function.header.name)

theorem programValid_iff (program : Program) : programValid program = true ↔
    identifier program.name = true ∧
    (!program.functions.isEmpty) = true ∧
    (declaredNames program).Nodup ∧
    (declaredNames program).all (fun name => identifier name &&
      !(["unit", "u64", "byte", "bool", "bytes"].contains name)) = true ∧
    program.interface.records.all (fun record => !record.fields.isEmpty &&
      (record.fields.map Parameter.name).Nodup &&
      record.fields.all (fun field => validType program.interface field.type true)) = true ∧
    (recordOrder? program.interface.records.length [] program.interface.records).isSome = true ∧
    (program.interface.externals.map External.cSymbol).Nodup ∧
    program.interface.externals.all (fun external => !program.functions.any
      (fun function => functionSymbol program.name function.header.name == external.cSymbol)) = true ∧
    program.interface.externals.all (fun external =>
      external.header.parameters.all (fun field => validType program.interface field.type true) &&
      validType program.interface external.header.result (external.header.result != .unit)) = true ∧
    program.interface.functions = program.functions.map Function.header ∧
    program.functions.all (checkFunction program.interface) = true := by
  simp only [programValid, declaredNames, Bool.and_eq_true, decide_eq_true_eq]
  tauto

end Mettapedia.GSLT.LanguageDef.NativeOps
