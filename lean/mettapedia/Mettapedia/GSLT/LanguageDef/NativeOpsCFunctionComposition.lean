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
      ⟨header.parameters.length⟩ representation.interface.externals representation = some (code, supply)) :
    primitiveFunction? representation header macros fuel function =
      some ⟨header, primitiveParameterCapture header.parameters ++ code, supply.next⟩ := by
  unfold primitiveFunction?
  rw [resultType]
  dsimp only [bind, Option.bind]
  rw [prototype]
  rw [scope]
  rw [normalized]
  rfl

/-- A statement and its remaining body are checked at their actual successive
temporary supplies before their instruction lists are joined. -/
theorem primitive_statements_cons_of_parts (bindings : PrimitiveBindings) (result : NativeType)
    (fuel : Nat) (first : CStatement) (rest : List CStatement) (supply middle final : NativeIR.Supply)
    (catalogue : List External) (representation : Representation)
    (firstCode restCode : List NativeIR.Instruction)
    (firstChecked : primitiveStatement? bindings result fuel first supply catalogue representation =
      some (firstCode, middle))
    (restChecked : primitiveStatements? bindings result fuel rest middle catalogue representation =
      some (restCode, final)) :
    primitiveStatements? bindings result (fuel + 1) (first :: rest) supply catalogue representation =
      some (firstCode ++ restCode, final) := by
  rw [primitiveStatements?, firstChecked]
  dsimp only [bind, Option.bind]
  rw [restChecked]

/-- The complete field assignment keeps the declared destination address,
the source load and the write in their authored order. Record positions and
binding lookup are checked independently of the statement's normalization. -/
theorem primitive_field_copy_statement_of_parts (representation : Representation)
    (bindings : PrimitiveBindings) (catalogue : List External) (result type : NativeType)
    (sourceName destinationName sourceMember destinationMember : Name)
    (sourceRecord destinationRecord : String) (source destination : NativeIR.Atom)
    (sourceIndex destinationIndex next fuel : Nat)
    (sourceBinding : (bindings.find? (fun binding => binding.1 == sourceName)).map Prod.snd =
      some source)
    (destinationBinding : (bindings.find? (fun binding => binding.1 == destinationName)).map Prod.snd =
      some destination)
    (sourceType : source.type = .ref (.named sourceRecord))
    (destinationType : destination.type = .ref (.named destinationRecord))
    (sourceField : authoredField? representation sourceRecord sourceMember = some (sourceIndex, type))
    (destinationField : authoredField? representation destinationRecord destinationMember =
      some (destinationIndex, type)) :
    primitiveStatement? bindings result (fuel + 3)
      (.assign (.field (.identifier destinationName) destinationMember true)
        (.field (.identifier sourceName) sourceMember true)) ⟨next⟩ catalogue representation =
      some ([.temporary (next + 1) (.ref type)
          (.fieldAddress destination destinationRecord destinationIndex),
        .temporary (next + 2) (.ref type) (.fieldAddress source sourceRecord sourceIndex),
        .temporary (next + 3) type (.indirectRead (.temporary (next + 2) (.ref type))),
        .write (.temporary (next + 1) (.ref type)) (.temporary (next + 3) type)], ⟨next + 3⟩) := by
  simp only [primitiveStatement?, primitiveExpression?, destinationBinding, sourceBinding,
    bind, Option.bind, primitiveFieldAddress?, primitiveFieldRead?, destinationType, sourceType,
    destinationField, sourceField]
  simp only [NativeLowering.prependCode, NativeLowering.pureTemporary,
    NativeIR.fresh, NativeIR.Atom.type, List.nil_append, List.append_assoc,
    Nat.add_assoc, ↓reduceIte]
  rfl

theorem primitive_field_copy_cons_of_parts (representation : Representation)
    (bindings : PrimitiveBindings) (catalogue : List External) (result type : NativeType)
    (sourceName destinationName sourceMember destinationMember : Name)
    (sourceRecord destinationRecord : String) (source destination : NativeIR.Atom)
    (sourceIndex destinationIndex next fuel : Nat) (rest : List CStatement)
    (restCode : List NativeIR.Instruction) (final : NativeIR.Supply)
    (sourceBinding : (bindings.find? (fun binding => binding.1 == sourceName)).map Prod.snd =
      some source)
    (destinationBinding : (bindings.find? (fun binding => binding.1 == destinationName)).map Prod.snd =
      some destination)
    (sourceType : source.type = .ref (.named sourceRecord))
    (destinationType : destination.type = .ref (.named destinationRecord))
    (sourceField : authoredField? representation sourceRecord sourceMember = some (sourceIndex, type))
    (destinationField : authoredField? representation destinationRecord destinationMember =
      some (destinationIndex, type))
    (restChecked : primitiveStatements? bindings result (fuel + 3) rest ⟨next + 3⟩
      catalogue representation = some (restCode, final)) :
    primitiveStatements? bindings result (fuel + 4)
      (.assign (.field (.identifier destinationName) destinationMember true)
        (.field (.identifier sourceName) sourceMember true) :: rest) ⟨next⟩ catalogue representation =
      some ([.temporary (next + 1) (.ref type)
          (.fieldAddress destination destinationRecord destinationIndex),
        .temporary (next + 2) (.ref type) (.fieldAddress source sourceRecord sourceIndex),
        .temporary (next + 3) type (.indirectRead (.temporary (next + 2) (.ref type))),
        .write (.temporary (next + 1) (.ref type)) (.temporary (next + 3) type)] ++ restCode, final) :=
  primitive_statements_cons_of_parts bindings result (fuel + 3) _ _ ⟨next⟩ _ final
    catalogue representation _ restCode
    (primitive_field_copy_statement_of_parts representation bindings catalogue result type
      sourceName destinationName sourceMember destinationMember sourceRecord destinationRecord
      source destination sourceIndex destinationIndex next fuel sourceBinding destinationBinding
      sourceType destinationType sourceField destinationField) restChecked

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
      ⟨header.parameters.length⟩ representation.interface.externals representation = none) :
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
  have recognized : ordinaryFunctionText? names characters = some function :=
    function_text_using_of_parts (parameter? names) names characters tokens function lexed parsed
  unfold primitiveFunctionText?
  rw [recognized]
  rfl

/-- Qualification remains in the parsed function until its separate profile
check; the ordinary lexer and complete function-body parser are shared. -/
theorem qualified_readonly_text_of_parts (representation : Representation)
    (names : TypeNames) (header : Header) (aliases : RecordAliases)
    (qualifications : List Bool) (macros : PrimitiveBindings)
    (characters : List Char) (tokens : List Token) (function : CQualifiedFunction)
    (lexed : lex characters = .ok tokens)
    (parsed : qualifiedFunction? (2 * tokens.length + 4) names
      (ordinaryFunctionTokens tokens) = some (function, [])) :
    qualifiedReadOnlyFunctionText? representation names header aliases qualifications macros characters =
      qualifiedReadOnlyFunction? representation header aliases qualifications macros
        (characters.length + 1) function := by
  have recognized : qualifiedFunctionText? names characters = some function :=
    function_text_using_of_parts (qualifiedParameter? names) names characters tokens function lexed parsed
  unfold qualifiedReadOnlyFunctionText?
  rw [recognized]
  rfl

theorem qualified_readonly_missing_qualification (representation : Representation)
    (header : Header) (aliases : RecordAliases) (qualifications : List Bool)
    (macros : PrimitiveBindings) (fuel : Nat) (function : CQualifiedFunction)
    (different : (function.parameters.map CQualifiedParameter.pointeeConst != qualifications) = true) :
    qualifiedReadOnlyFunction? representation header aliases qualifications macros fuel function = none := by
  simp [qualifiedReadOnlyFunction?, different]

theorem qualified_parameter_store_text_of_parts (representation : Representation)
    (names : TypeNames) (header : Header) (aliases : RecordAliases)
    (qualifications : List Bool) (macros : PrimitiveBindings)
    (characters : List Char) (tokens : List Token) (function : CQualifiedFunction)
    (lexed : lex characters = .ok tokens)
    (parsed : qualifiedFunction? (2 * tokens.length + 4) names
      (ordinaryFunctionTokens tokens) = some (function, [])) :
    qualifiedParameterStoreFunctionText? representation names header aliases qualifications macros characters =
      qualifiedParameterStoreFunction? representation header aliases qualifications macros
        (characters.length + 1) function := by
  have recognized : qualifiedFunctionText? names characters = some function :=
    function_text_using_of_parts (qualifiedParameter? names) names characters tokens function lexed parsed
  unfold qualifiedParameterStoreFunctionText?
  rw [recognized]
  rfl

theorem qualified_parameter_store_missing_qualification (representation : Representation)
    (header : Header) (aliases : RecordAliases) (qualifications : List Bool)
    (macros : PrimitiveBindings) (fuel : Nat) (function : CQualifiedFunction)
    (different : (function.parameters.map CQualifiedParameter.pointeeConst != qualifications) = true) :
    qualifiedParameterStoreFunction? representation header aliases qualifications macros fuel function = none := by
  simp [qualifiedParameterStoreFunction?, different]

/-- Direct field transport needs the explicit destination qualification.
The syntactic profile introduces no memory-validity or payload-ownership law. -/
theorem parameter_store_field_copy_of_permission (parameters : List CQualifiedParameter)
    (catalogue : List External) (sourceName destinationName sourceMember destinationMember : Name)
    (fuel : Nat)
    (permitted : parameterStoreAllowed parameters
      (.field (.identifier destinationName) destinationMember true) = true) :
    parameterStoreStatement parameters catalogue (fuel + 3)
      (.assign (.field (.identifier destinationName) destinationMember true)
        (.field (.identifier sourceName) sourceMember true)) = true := by
  change parameterStoreAllowed parameters
    (.field (.identifier destinationName) destinationMember true) && true = true
  rw [permitted]
  rfl

/-- Separate prototype and whole-body certificates for a parameter-store
function; the void epilogue is attached after the admitted body. -/
theorem qualified_parameter_store_function_of_parts (representation : Representation)
    (header : Header) (aliases : RecordAliases) (qualifications : List Bool)
    (macros : PrimitiveBindings) (fuel : Nat) (function : CQualifiedFunction)
    (result : CType) (parameters : List CParameter) (lowered : NativeIR.Function)
    (admitted : (!recordAliasesValid representation aliases ||
      function.parameters.map CQualifiedParameter.pointeeConst != qualifications ||
      !function.body.all (parameterStoreStatement function.parameters
        representation.interface.externals fuel)) = false)
    (resultType : canonicalPrototypeType? representation aliases function.result = some result)
    (parameterTypes : function.unqualified.parameters.mapM (fun parameter => do
      let type ← canonicalPrototypeType? representation aliases parameter.type
      some { parameter with type := type }) = some parameters)
    (body : primitiveFunction? representation header macros fuel
      ⟨result, function.name, parameters, function.body⟩ = some lowered) :
    qualifiedParameterStoreFunction? representation header aliases qualifications macros fuel function =
      some { lowered with body := lowered.body ++
        (if header.result = .unit then [.return .unit] else []) } := by
  unfold qualifiedParameterStoreFunction?
  rw [admitted]
  dsimp only [CQualifiedFunction.unqualified, bind, Option.bind] at parameterTypes ⊢
  rw [resultType, parameterTypes]
  dsimp only [bind, Option.bind]
  rw [body]
  rfl

/-- Neither a const parameter nor an undeclared alias gains store authority. -/
theorem const_parameter_field_store_refused (member : Name) :
    parameterStoreAllowed [⟨⟨⟨"Record".toList, 1⟩, "input".toList⟩, true⟩]
      (.field (.identifier "input".toList) member true) = false := by rfl

theorem missing_parameter_field_store_refused (member : Name) :
    parameterStoreAllowed [⟨⟨⟨"Record".toList, 1⟩, "output".toList⟩, false⟩]
      (.field (.identifier "alias".toList) member true) = false := by rfl

theorem mutable_parameter_field_store_admitted (member : Name) :
    parameterStoreAllowed [⟨⟨⟨"Record".toList, 1⟩, "output".toList⟩, false⟩]
      (.field (.identifier "output".toList) member true) = true := by rfl

/-- An explicit store is refused even when its pointer alias is otherwise
well typed. Const erasure is not a permission to write through another name. -/
theorem readonly_store_refused (catalogue : List External) (fuel : Nat)
    (location value : CExpr) : readOnlyStatement catalogue fuel (.assign location value) = false := by
  cases fuel <;> rfl

theorem readonly_increment_refused (catalogue : List External) (fuel : Nat)
    (operand : CExpr) : readOnlyExpression catalogue fuel (.unary .increment operand) = false := by
  cases fuel <;> rfl

theorem readonly_postincrement_refused (catalogue : List External) (fuel : Nat)
    (operand : CExpr) : readOnlyExpression catalogue fuel (.postIncrement operand) = false := by
  cases fuel <;> rfl

theorem readonly_effect_service_refused (fuel : Nat) (declaration : External)
    (arguments : List CExpr) (effectful : declaration.effect = .effect) :
    readOnlyExpression [declaration] fuel (.call declaration.cSymbol.toList arguments) = false := by
  cases fuel <;> simp [readOnlyExpression, effectful]

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
