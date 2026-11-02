import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRLiteralReading

/-! Source instantiation and compiled head substitution commute. Variable
readings relate the independent source environment to the retained physical
assignment. The law is structural, including nested tuples and shared names;
it is not a statement about the compiler agreeing with itself. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.TermReading

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax Match
open GeneralFirstOrderProjection

def VariablesRead (vocabulary : Vocabulary) (environment : Environment) (bindings : Bindings) : Prop :=
  ∀ index value, Mettapedia.Languages.CHR.lookup environment index = some value →
    ∃ code, value? vocabulary value = some code ∧ bindings.lookup (variableSlot index) = some code

private theorem traverse_instance {α β : Type} (compile : α → Option Pattern) (instantiate : α → Option β)
    (encode : β → Option Pattern) (transform : Pattern → Pattern)
    (inputs : List α) (codes : List Pattern) (values : List β)
    (step : ∀ input ∈ inputs, ∀ code value, compile input = some code →
      instantiate input = some value → encode value = some (transform code))
    (compiled : inputs.mapM compile = some codes) (instantiated : inputs.mapM instantiate = some values) :
    values.mapM encode = some (codes.map transform) := by
  induction inputs generalizing codes values with
  | nil =>
    have codeEmpty : codes = [] := by simpa using compiled.symm
    have valueEmpty : values = [] := by simpa using instantiated.symm
    subst codes
    subst values
    rfl
  | cons input rest ih =>
    cases first : compile input with
    | none => simp [List.mapM_cons, first] at compiled
    | some code =>
      cases tail : rest.mapM compile with
      | none => simp [List.mapM_cons, first, tail] at compiled
      | some codeTail =>
        have codeSame : code :: codeTail = codes := by simpa [List.mapM_cons, first, tail] using compiled
        subst codes
        cases valueRead : instantiate input with
        | none => simp [List.mapM_cons, valueRead] at instantiated
        | some value =>
          cases valuesRead : rest.mapM instantiate with
          | none => simp [List.mapM_cons, valueRead, valuesRead] at instantiated
          | some valueTail =>
            have valueSame : value :: valueTail = values := by simpa [List.mapM_cons, valueRead, valuesRead] using instantiated
            subst values
            have headImage := step input List.mem_cons_self code value first valueRead
            have tailImage := ih codeTail valueTail
              (fun child member => step child (List.mem_cons_of_mem input member)) tail valuesRead
            simp only [List.mapM_cons, List.map_cons, headImage, tailImage]
            rfl

theorem term_instantiation (vocabulary : Vocabulary) (environment : Environment) (bindings : Bindings)
    (pools : RequestPools.Read vocabulary bindings) (variableRead : VariablesRead vocabulary environment bindings)
    (source : Mettapedia.Languages.CHR.Term) (code : Pattern) (value : Value)
    (compiled : term? vocabulary source = some code) (instantiated : source.instantiate environment = some value) :
    value? vocabulary value = some (applyBindings bindings code) := by
  cases source with
  | value datum =>
    have same : datum = value := by simpa only [Term.instantiate, Option.some.injEq] using instantiated
    subst value
    exact LiteralReading.literal_instantiation vocabulary bindings pools datum code (by simpa only [term?] using compiled)
  | var index =>
    have same : Pattern.fvar (variableSlot index) = code := by simpa only [term?, Option.some.injEq] using compiled
    subst code
    have found : Mettapedia.Languages.CHR.lookup environment index = some value := by simpa only [Term.instantiate] using instantiated
    obtain ⟨physical, encoded, stored⟩ := variableRead index value found
    rw [apply_variable, stored]
    exact encoded
  | tuple fields =>
    rw [term?] at compiled
    change ((fields.mapM (term? vocabulary)).bind fun values =>
      some (Pattern.apply "ChrTuple" [vector values])) = some code at compiled
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨codes, fieldsCompiled, rfl⟩ := compiled
    rw [Term.instantiate] at instantiated
    change (fields.mapM (Term.instantiate environment)).map Value.tuple = some value at instantiated
    simp only [Option.map_eq_some_iff] at instantiated
    obtain ⟨values, fieldsInstantiated, same⟩ := instantiated
    subst value
    have encoded := traverse_instance (term? vocabulary) (Term.instantiate environment) (value? vocabulary)
      (applyBindings bindings) fields codes values
      (fun field _ result datum compiledField instantiatedField =>
        term_instantiation vocabulary environment bindings pools variableRead field result datum compiledField instantiatedField)
      fieldsCompiled fieldsInstantiated
    rw [value?, encoded]
    change some (.apply "ChrTuple" [vector (codes.map (applyBindings bindings))]) =
      some (applyBindings bindings (.apply "ChrTuple" [vector codes]))
    simp only [applyBindings, vector, List.map_cons, List.map_nil, List.append_nil]
termination_by sizeOf source

theorem head_instantiation (vocabulary : Vocabulary) (environment : Environment) (bindings : Bindings)
    (pools : RequestPools.Read vocabulary bindings) (variableRead : VariablesRead vocabulary environment bindings)
    (source : Head) (code : Pattern) (value : Constraint)
    (compiled : head? vocabulary source = some code) (instantiated : source.instantiate environment = some value) :
    constraint? vocabulary value = some (applyBindings bindings code) := by
  change ((vocabulary.predicates.idxOf? source.name).bind fun index =>
    (source.arguments.mapM (term? vocabulary)).bind fun fields =>
      some (Pattern.apply "ChrConstraint" [.fvar (predicateSlot index), vector fields])) = some code at compiled
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at compiled
  obtain ⟨index, predicateRead, fields, fieldsCompiled, rfl⟩ := compiled
  change ((source.arguments.mapM (Term.instantiate environment)).bind fun fields =>
    some (Constraint.mk source.name fields)) = some value at instantiated
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at instantiated
  obtain ⟨values, fieldsInstantiated, rfl⟩ := instantiated
  have encoded := traverse_instance (term? vocabulary) (Term.instantiate environment) (value? vocabulary)
    (applyBindings bindings) source.arguments fields values
    (fun field _ result datum compiledField instantiatedField =>
      term_instantiation vocabulary environment bindings pools variableRead field result datum compiledField instantiatedField)
    fieldsCompiled fieldsInstantiated
  have atIndex : vocabulary.predicates[index]? = some source.name := by
    obtain ⟨within, same, _⟩ := List.idxOf?_eq_some_iff.mp predicateRead
    simp [within, same]
  have stored := pools.predicates index source.name atIndex
  simp only [constraint?, predicateRead, encoded]
  rw [applyBindings]
  simp only [List.map_cons, List.map_nil]
  rw [apply_variable, stored]
  simp only [applyBindings, vector, List.append_nil, Option.getD_some]
  rfl

#print axioms term_instantiation
#print axioms head_instantiation

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.TermReading
