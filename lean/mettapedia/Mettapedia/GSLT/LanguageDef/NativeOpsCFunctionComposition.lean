import Mettapedia.GSLT.LanguageDef.NativeOpsCNormalization

/-! Separate symbol, prototype and body certificates for actual C functions. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- Ordinary function admission separates the checked prototype and binding
scope from the scalar body's normalization certificate. -/
theorem primitive_function_of_parts (representation : Representation)
    (header : Header) (macros : PrimitiveBindings) (fuel : Nat) (function : CFunction)
    (result : NativeType) (code : List NativeIR.Instruction) (supply : NativeIR.Supply)
    (resultType : nativeType? representation function.result = some result)
    (prototype : (function.name != header.name.toList || result != header.result ||
      !primitiveParametersMatch representation header.parameters function.parameters) = false)
    (scope : ((header.parameters.map Parameter.name).eraseDups.length != header.parameters.length ||
      macros.any (fun macroBinding =>
        header.parameters.any (fun parameter => parameter.name.toList == macroBinding.1))) = false)
    (normalized : primitiveStatements?
      (primitiveParameterBindings header.parameters ++ macros) result fuel function.body
      ⟨header.parameters.length⟩ representation.interface.externals = some (code, supply)) :
    primitiveFunction? representation header macros fuel function =
      some ⟨header, primitiveParameterCapture header.parameters ++ code, supply.next⟩ := by
  unfold primitiveFunction?
  rw [resultType]
  dsimp only [bind, Option.bind]
  rw [prototype]
  rw [scope]
  rw [normalized]
  rfl

/-- A checked prototype cannot repair a body rejected by its typed reader. -/
theorem primitive_function_body_refused (representation : Representation)
    (header : Header) (macros : PrimitiveBindings) (fuel : Nat) (function : CFunction)
    (result : NativeType)
    (resultType : nativeType? representation function.result = some result)
    (prototype : (function.name != header.name.toList || result != header.result ||
      !primitiveParametersMatch representation header.parameters function.parameters) = false)
    (scope : ((header.parameters.map Parameter.name).eraseDups.length != header.parameters.length ||
      macros.any (fun macroBinding =>
        header.parameters.any (fun parameter => parameter.name.toList == macroBinding.1))) = false)
    (refused : primitiveStatements?
      (primitiveParameterBindings header.parameters ++ macros) result fuel function.body
      ⟨header.parameters.length⟩ representation.interface.externals = none) :
    primitiveFunction? representation header macros fuel function = none := by
  unfold primitiveFunction?
  rw [resultType]
  dsimp only [bind, Option.bind]
  rw [prototype]
  rw [scope]
  rw [refused]
  rfl

/-- The lexer and complete parser certificates are reusable independently of
the ordinary function's prototype and immutable-parameter admission. -/
theorem primitive_function_text_of_parts (representation : Representation)
    (names : TypeNames) (header : Header) (macros : PrimitiveBindings)
    (characters : List Char) (tokens : List Token) (function : CFunction)
    (lexed : lex characters = .ok tokens)
    (parsed : function? (2 * tokens.length + 4) names (ordinaryFunctionTokens tokens) =
      some (function, [])) :
    primitiveFunctionText? representation names header macros characters =
      primitiveFunction? representation header macros (characters.length + 1) function := by
  unfold primitiveFunctionText?
  rw [lexed]
  dsimp only [Except.toOption, bind, Option.bind]
  rw [parsed]
  rfl

theorem normalize_function_of_parts (representation : Representation)
    (function : CFunction) (header : Header) (body : Normalized)
    (found : representation.interface.functions.find?
      (fun candidate => (functionSymbol representation.moduleName candidate.name).toList ==
        function.name) = some header)
    (prototype : sourcePrototype? representation header function.name true =
      some (.prototype function.result function.name function.parameters))
    (normalized : normalizeStatements? representation header.result
      ⟨header.parameters.map (fun parameter => (parameter.name, parameter.type)), [], []⟩
      function.body = some body) :
    normalizeFunction? representation function =
      some ⟨header, body.code, maximumIdentity body.code⟩ := by
  unfold normalizeFunction?
  rw [found]
  change (do
    let declaration ← sourcePrototype? representation header function.name true
    if declaration != HeaderItem.prototype function.result function.name function.parameters then none
    else do
      let checked ← normalizeStatements? representation header.result
        ⟨header.parameters.map (fun (parameter : Parameter) => (parameter.name, parameter.type)), [], []⟩
        function.body
      some (NativeIR.Function.mk header checked.code (maximumIdentity checked.code))) = _
  rw [prototype]
  simp only [bind, Option.bind, bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [normalized]

theorem normalize_function_missing_header (representation : Representation)
    (function : CFunction)
    (missing : representation.interface.functions.find?
      (fun candidate => (functionSymbol representation.moduleName candidate.name).toList ==
        function.name) = none) : normalizeFunction? representation function = none := by
  rw [normalizeFunction?, missing]
  rfl

theorem normalize_function_prototype_mismatch (representation : Representation)
    (function : CFunction) (header : Header) (declaration : HeaderItem)
    (found : representation.interface.functions.find?
      (fun candidate => (functionSymbol representation.moduleName candidate.name).toList ==
        function.name) = some header)
    (prototype : sourcePrototype? representation header function.name true = some declaration)
    (mismatch : (declaration != HeaderItem.prototype function.result function.name function.parameters) = true) :
    normalizeFunction? representation function = none := by
  unfold normalizeFunction?
  rw [found]
  dsimp only [bind, Option.bind]
  rw [prototype]
  dsimp only [bind, Option.bind]
  rw [mismatch]
  rfl

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
