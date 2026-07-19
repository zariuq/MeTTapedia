import Mettapedia.Languages.Metamath.MMLean4Bridge
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Metamath inference carrier encoding

This file gives a structural `Pattern` encoding of the live `mm-lean4`
runtime carriers needed by a later inference presentation.  Lists use explicit
cons/nil data, formulas expose their constant typecode separately from their
body, and frames retain both array orders exactly.

The encoding is data only.  It does not define Metamath inference rules or
claim correspondence with the runtime checker.
-/

namespace Mettapedia.Languages.Metamath.InferenceEncoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Metamath.MMLean4Bridge

/-! ## Reserved constructors and generic list data -/

def stringHead : String := "$mm.string"
def nilHead : String := "$mm.nil"
def consHead : String := "$mm.cons"
def constSymHead : String := "$mm.const"
def varSymHead : String := "$mm.var"
def formulaHead : String := "$mm.formula"
def dvPairHead : String := "$mm.dv-pair"
def frameHead : String := "$mm.frame"
def bindingHead : String := "$mm.binding"
def substitutionHead : String := "$mm.substitution"

/- Public, Pattern-level constructors used both by concrete encoders and by
future rule schemas whose components are themselves metavariable patterns. -/
namespace Builder

@[simp] def rawString (value : String) : Pattern := .apply value []
@[simp] def encodedString (rawValue : Pattern) : Pattern := .apply stringHead [rawValue]
@[simp] def nil : Pattern := .apply nilHead []
@[simp] def cons (head tail : Pattern) : Pattern := .apply consHead [head, tail]
@[simp] def constSym (encodedName : Pattern) : Pattern :=
  .apply constSymHead [encodedName]
@[simp] def varSym (encodedName : Pattern) : Pattern :=
  .apply varSymHead [encodedName]
@[simp] def formula (encodedTypecode body : Pattern) : Pattern :=
  .apply formulaHead [encodedTypecode, body]
@[simp] def dvPair (encodedLeft encodedRight : Pattern) : Pattern :=
  .apply dvPairHead [encodedLeft, encodedRight]
@[simp] def frame (dv hypotheses : Pattern) : Pattern :=
  .apply frameHead [dv, hypotheses]
@[simp] def binding (encodedVariable replacement : Pattern) : Pattern :=
  .apply bindingHead [encodedVariable, replacement]
@[simp] def substitution (bindings : Pattern) : Pattern :=
  .apply substitutionHead [bindings]

end Builder

/-- An injective string representation.  The payload is a nullary application,
so arbitrary source strings cannot be confused with encoding constructors. -/
def encodeString (value : String) : Pattern :=
  Builder.encodedString (Builder.rawString value)

def decodeString : Pattern → Option String
  | .apply tag [.apply value []] =>
      if tag = stringHead then some value else none
  | _ => none

@[simp] theorem decodeString_encodeString (value : String) :
    decodeString (encodeString value) = some value := by
  simp [decodeString, encodeString, stringHead]

theorem encodeString_injective : Function.Injective encodeString := by
  intro left right h
  have := congrArg decodeString h
  simpa using this

def encodeListWith {α : Type} (encode : α → Pattern) : List α → Pattern
  | [] => Builder.nil
  | value :: values =>
      Builder.cons (encode value) (encodeListWith encode values)

def decodeListWith {α : Type} (decode : Pattern → Option α) :
    Pattern → Option (List α)
  | .apply tag [] =>
      if tag = nilHead then some [] else none
  | .apply tag [head, tail] =>
      if tag = consHead then
        match decode head, decodeListWith decode tail with
        | some value, some values => some (value :: values)
        | _, _ => none
      else
        none
  | _ => none
termination_by pattern => sizeOf pattern

@[simp] theorem decodeListWith_encodeListWith
    {α : Type} (encode : α → Pattern) (decode : Pattern → Option α)
    (leftInverse : ∀ value, decode (encode value) = some value)
    (values : List α) :
    decodeListWith decode (encodeListWith encode values) = some values := by
  induction values with
  | nil => simp [encodeListWith, decodeListWith, nilHead]
  | cons value values ih =>
      simp [encodeListWith, decodeListWith, consHead, leftInverse value, ih]

/-! ## Runtime symbols -/

def encodeSym : RuntimeSym → Pattern
  | .const name => Builder.constSym (encodeString name)
  | .var name => Builder.varSym (encodeString name)

def decodeSym : Pattern → Option RuntimeSym
  | .apply tag [payload] =>
      match decodeString payload with
      | none => none
      | some name =>
          if tag = constSymHead then
            some (.const name)
          else if tag = varSymHead then
            some (.var name)
          else
            none
  | _ => none

@[simp] theorem decodeSym_encodeSym (symbol : RuntimeSym) :
    decodeSym (encodeSym symbol) = some symbol := by
  cases symbol <;>
    simp [encodeSym, decodeSym, constSymHead, varSymHead]

theorem encodeSym_injective : Function.Injective encodeSym := by
  intro left right h
  have := congrArg decodeSym h
  simpa using this

/-! ## Constant-headed runtime formulas -/

/-- Canonical view of the supported runtime formula domain.  Its runtime image
is exactly an array whose first symbol is a constant. -/
structure ConstantHeadedFormula where
  typecode : String
  body : List RuntimeSym
deriving DecidableEq, Repr

def ConstantHeadedFormula.toRuntime
    (formula : ConstantHeadedFormula) : RuntimeFormula :=
  (Metamath.Verify.Sym.const formula.typecode :: formula.body).toArray

def ConstantHeadedFormula.ofRuntime? (formula : RuntimeFormula) :
    Option ConstantHeadedFormula :=
  match formula.toList with
  | .const typecode :: body => some ⟨typecode, body⟩
  | _ => none

@[simp] theorem ConstantHeadedFormula.ofRuntime?_toRuntime
    (formula : ConstantHeadedFormula) :
    ConstantHeadedFormula.ofRuntime? formula.toRuntime = some formula := by
  cases formula
  simp [ConstantHeadedFormula.toRuntime, ConstantHeadedFormula.ofRuntime?]

/-- Characterization of the supported live runtime domain: decoding a view
succeeds exactly when the runtime array is that view's constant-headed image. -/
theorem ConstantHeadedFormula.ofRuntime?_eq_some_iff
    (runtime : RuntimeFormula) (formula : ConstantHeadedFormula) :
    ConstantHeadedFormula.ofRuntime? runtime = some formula ↔
      runtime = formula.toRuntime := by
  constructor
  · intro h
    unfold ConstantHeadedFormula.ofRuntime? at h
    cases hList : runtime.toList with
    | nil => simp [hList] at h
    | cons head body =>
        cases head with
        | const typecode =>
            simp [hList] at h
            cases h
            apply Array.ext'
            simp [ConstantHeadedFormula.toRuntime, hList]
        | var name => simp [hList] at h
  · intro h
    subst runtime
    simp

theorem ConstantHeadedFormula.toRuntime_injective :
    Function.Injective ConstantHeadedFormula.toRuntime := by
  intro left right h
  have := congrArg ConstantHeadedFormula.ofRuntime? h
  simpa using this

def encodeFormula (formula : ConstantHeadedFormula) : Pattern :=
  Builder.formula
    (encodeString formula.typecode) (encodeListWith encodeSym formula.body)

def decodeFormulaView : Pattern → Option ConstantHeadedFormula
  | .apply tag [typecodePattern, bodyPattern] =>
      if tag = formulaHead then
        match decodeString typecodePattern, decodeListWith decodeSym bodyPattern with
        | some typecode, some body => some ⟨typecode, body⟩
        | _, _ => none
      else
        none
  | _ => none

/-- Decode directly to the live runtime formula carrier. -/
def decodeFormula (pattern : Pattern) : Option RuntimeFormula :=
  ConstantHeadedFormula.toRuntime <$> decodeFormulaView pattern

/-- Partial encoder on the live runtime carrier.  Variable-headed and empty
arrays lie outside the supported domain and are rejected. -/
def encodeRuntimeFormula? (formula : RuntimeFormula) : Option Pattern :=
  encodeFormula <$> ConstantHeadedFormula.ofRuntime? formula

@[simp] theorem decodeFormulaView_encodeFormula
    (formula : ConstantHeadedFormula) :
    decodeFormulaView (encodeFormula formula) = some formula := by
  cases formula
  simp [decodeFormulaView, encodeFormula, formulaHead]

@[simp] theorem decodeFormula_encodeFormula
    (formula : ConstantHeadedFormula) :
    decodeFormula (encodeFormula formula) = some formula.toRuntime := by
  simp [decodeFormula]

@[simp] theorem encodeRuntimeFormula?_toRuntime
    (formula : ConstantHeadedFormula) :
    encodeRuntimeFormula? formula.toRuntime = some (encodeFormula formula) := by
  simp [encodeRuntimeFormula?]

theorem encodeFormula_injective : Function.Injective encodeFormula := by
  intro left right h
  have := congrArg decodeFormulaView h
  simpa using this

/-- Injectivity stated on the exact supported subdomain of the live runtime
formula carrier. -/
theorem encodeRuntimeFormula?_injective_on_constantHeaded
    (left right : ConstantHeadedFormula)
    (h : encodeRuntimeFormula? left.toRuntime =
      encodeRuntimeFormula? right.toRuntime) :
    left.toRuntime = right.toRuntime := by
  have hEncoded : encodeFormula left = encodeFormula right := by
    simpa using h
  exact congrArg ConstantHeadedFormula.toRuntime
    (encodeFormula_injective hEncoded)

/-! ## Exact runtime frames -/

def encodeDVPair (pair : String × String) : Pattern :=
  Builder.dvPair (encodeString pair.1) (encodeString pair.2)

def decodeDVPair : Pattern → Option (String × String)
  | .apply tag [leftPattern, rightPattern] =>
      if tag = dvPairHead then
        match decodeString leftPattern, decodeString rightPattern with
        | some left, some right => some (left, right)
        | _, _ => none
      else
        none
  | _ => none

@[simp] theorem decodeDVPair_encodeDVPair (pair : String × String) :
    decodeDVPair (encodeDVPair pair) = some pair := by
  cases pair
  simp [encodeDVPair, decodeDVPair, dvPairHead]

theorem encodeDVPair_injective : Function.Injective encodeDVPair := by
  intro left right h
  have := congrArg decodeDVPair h
  simpa using this

/-- The first list is `Frame.dj` order and the second is `Frame.hyps` order,
matching the live runtime carrier field order. -/
def encodeFrame (frame : RuntimeFrame) : Pattern :=
  Builder.frame
    (encodeListWith encodeDVPair frame.dj.toList)
    (encodeListWith encodeString frame.hyps.toList)

def decodeFrame : Pattern → Option RuntimeFrame
  | .apply tag [dvPattern, hypothesesPattern] =>
      if tag = frameHead then
        match decodeListWith decodeDVPair dvPattern,
            decodeListWith decodeString hypothesesPattern with
        | some dj, some hyps => some ⟨dj.toArray, hyps.toArray⟩
        | _, _ => none
      else
        none
  | _ => none

@[simp] theorem decodeFrame_encodeFrame (frame : RuntimeFrame) :
    decodeFrame (encodeFrame frame) = some frame := by
  cases frame
  simp [encodeFrame, decodeFrame, frameHead]

theorem encodeFrame_injective : Function.Injective encodeFrame := by
  intro left right h
  have := congrArg decodeFrame h
  simpa using this

/-! ## Finite substitution data -/

/-- One finite runtime substitution binding.  Replacements use the same exact
constant-headed domain as formulas consumed by the inference layer. -/
structure FormulaBinding where
  variableName : String
  replacement : ConstantHeadedFormula
deriving DecidableEq, Repr

/-- Ordered finite substitution syntax.  Duplicate keys remain visible data;
their rejection belongs to a later validity judgment, not this carrier codec. -/
abbrev FiniteSubstitution := List FormulaBinding

def encodeBinding (binding : FormulaBinding) : Pattern :=
  Builder.binding
    (encodeString binding.variableName) (encodeFormula binding.replacement)

def decodeBinding : Pattern → Option FormulaBinding
  | .apply tag [variablePattern, replacementPattern] =>
      if tag = bindingHead then
        match decodeString variablePattern, decodeFormulaView replacementPattern with
        | some variableName, some replacement => some ⟨variableName, replacement⟩
        | _, _ => none
      else
        none
  | _ => none

@[simp] theorem decodeBinding_encodeBinding (binding : FormulaBinding) :
    decodeBinding (encodeBinding binding) = some binding := by
  cases binding
  simp [encodeBinding, decodeBinding, bindingHead]

def encodeSubstitution (substitution : FiniteSubstitution) : Pattern :=
  Builder.substitution (encodeListWith encodeBinding substitution)

def decodeSubstitution : Pattern → Option FiniteSubstitution
  | .apply tag [bindingsPattern] =>
      if tag = substitutionHead then
        decodeListWith decodeBinding bindingsPattern
      else
        none
  | _ => none

@[simp] theorem decodeSubstitution_encodeSubstitution
    (substitution : FiniteSubstitution) :
    decodeSubstitution (encodeSubstitution substitution) = some substitution := by
  simp [encodeSubstitution, decodeSubstitution, substitutionHead]

theorem encodeSubstitution_injective : Function.Injective encodeSubstitution := by
  intro left right h
  have := congrArg decodeSubstitution h
  simpa using this

/-! ## Executable examples -/

def exampleFormula : ConstantHeadedFormula :=
  ⟨"|-", [.const "(", .var "ph", .const ")"]⟩

def exampleFrame : RuntimeFrame :=
  ⟨#[("x", "y"), ("u", "v")], #["wph", "ax-mp.1"]⟩

def exampleFrameHypothesesReordered : RuntimeFrame :=
  ⟨#[("x", "y"), ("u", "v")], #["ax-mp.1", "wph"]⟩

def exampleFrameDVReordered : RuntimeFrame :=
  ⟨#[("u", "v"), ("x", "y")], #["wph", "ax-mp.1"]⟩

def exampleSubstitution : FiniteSubstitution :=
  [⟨"ph", exampleFormula⟩]

theorem exampleFormula_roundtrip :
    decodeFormula (encodeFormula exampleFormula) =
      some exampleFormula.toRuntime := by
  simp

theorem exampleFrame_roundtrip :
    decodeFrame (encodeFrame exampleFrame) = some exampleFrame := by
  simp

theorem exampleFrame_hypothesis_order_is_significant :
    encodeFrame exampleFrame ≠ encodeFrame exampleFrameHypothesesReordered := by
  decide

theorem exampleFrame_dv_order_is_significant :
    encodeFrame exampleFrame ≠ encodeFrame exampleFrameDVReordered := by
  decide

theorem exampleSubstitution_roundtrip :
    decodeSubstitution (encodeSubstitution exampleSubstitution) =
      some exampleSubstitution := by
  simp

theorem variableHeaded_runtime_formula_rejected :
    encodeRuntimeFormula? #[.var "ph", .const "ignored"] = none := by
  simp [encodeRuntimeFormula?, ConstantHeadedFormula.ofRuntime?]

theorem malformed_string_rejected :
    decodeString (.apply stringHead []) = none := by
  rfl

theorem malformed_improper_symbol_list_rejected :
    decodeFormulaView
        (.apply formulaHead
          [encodeString "|-",
            .apply consHead [encodeSym (.var "ph"), .apply "$mm.not-nil" []]]) =
      none := by
  simp [decodeFormulaView, decodeListWith, decodeSym, decodeString, formulaHead,
    encodeString, encodeSym, consHead, nilHead, stringHead, constSymHead,
    varSymHead]

theorem malformed_untagged_symbol_rejected :
    decodeFormulaView
        (.apply formulaHead
          [encodeString "|-",
            encodeListWith id [.apply "ph" []]]) = none := by
  simp [decodeFormulaView, decodeListWith, decodeSym, decodeString, encodeListWith,
    formulaHead, consHead, nilHead, stringHead]

theorem malformed_frame_field_order_rejected :
    decodeFrame
        (.apply frameHead
          [encodeListWith encodeString ["wph"],
            encodeListWith encodeDVPair [("x", "y")]]) = none := by
  simp [decodeFrame, decodeListWith, decodeString, encodeListWith, decodeDVPair,
    encodeString, encodeDVPair, frameHead, consHead, nilHead, stringHead,
    dvPairHead]

/-! ## Exact decoder images -/

theorem decodeString_eq_some_iff (pattern : Pattern) (value : String) :
    decodeString pattern = some value ↔ pattern = encodeString value := by
  constructor
  · intro h
    cases pattern with
    | bvar index => simp [decodeString] at h
    | fvar name => simp [decodeString] at h
    | lambda binder body => simp [decodeString] at h
    | multiLambda arity binders body => simp [decodeString] at h
    | subst body replacement => simp [decodeString] at h
    | collection collectionType elements rest => simp [decodeString] at h
    | apply tag arguments =>
        cases arguments with
        | nil => simp [decodeString] at h
        | cons argument arguments =>
            cases arguments with
            | cons next arguments => simp [decodeString] at h
            | nil =>
                cases argument with
                | bvar index => simp [decodeString] at h
                | fvar name => simp [decodeString] at h
                | lambda binder body => simp [decodeString] at h
                | multiLambda arity binders body => simp [decodeString] at h
                | subst body replacement => simp [decodeString] at h
                | collection collectionType elements rest => simp [decodeString] at h
                | apply rawValue rawArguments =>
                    cases rawArguments with
                    | cons next rawArguments => simp [decodeString] at h
                    | nil =>
                        simp [decodeString] at h
                        rcases h with ⟨rfl, rfl⟩
                        rfl
  · rintro rfl
    simp

theorem decodeListWith_eq_some_iff
    {α : Type} (encode : α → Pattern) (decode : Pattern → Option α)
    (elementImage : ∀ pattern value,
      decode pattern = some value ↔ pattern = encode value)
    (pattern : Pattern) (values : List α) :
    decodeListWith decode pattern = some values ↔
      pattern = encodeListWith encode values := by
  constructor
  · intro h
    cases pattern with
    | bvar index => simp [decodeListWith] at h
    | fvar name => simp [decodeListWith] at h
    | lambda binder body => simp [decodeListWith] at h
    | multiLambda arity binders body => simp [decodeListWith] at h
    | subst body replacement => simp [decodeListWith] at h
    | collection collectionType elements rest => simp [decodeListWith] at h
    | apply tag arguments =>
        cases arguments with
        | nil =>
            simp [decodeListWith] at h
            rcases h with ⟨rfl, rfl⟩
            rfl
        | cons head arguments =>
            cases arguments with
            | nil => simp [decodeListWith] at h
            | cons tail arguments =>
                cases arguments with
                | cons extra arguments => simp [decodeListWith] at h
                | nil =>
                    cases hHead : decode head with
                    | none => simp [decodeListWith, hHead] at h
                    | some value =>
                        cases hTail : decodeListWith decode tail with
                        | none => simp [decodeListWith, hHead, hTail] at h
                        | some tailValues =>
                            simp [decodeListWith, hHead, hTail] at h
                            rcases h with ⟨rfl, rfl⟩
                            rw [(elementImage head value).mp hHead]
                            rw [(decodeListWith_eq_some_iff encode decode elementImage
                              tail tailValues).mp hTail]
                            rfl
  · rintro rfl
    exact decodeListWith_encodeListWith encode decode
      (fun value => (elementImage (encode value) value).mpr rfl) values

theorem decodeSym_eq_some_iff (pattern : Pattern) (symbol : RuntimeSym) :
    decodeSym pattern = some symbol ↔ pattern = encodeSym symbol := by
  constructor
  · intro h
    cases pattern with
    | bvar index => simp [decodeSym] at h
    | fvar name => simp [decodeSym] at h
    | lambda binder body => simp [decodeSym] at h
    | multiLambda arity binders body => simp [decodeSym] at h
    | subst body replacement => simp [decodeSym] at h
    | collection collectionType elements rest => simp [decodeSym] at h
    | apply tag arguments =>
        cases arguments with
        | nil => simp [decodeSym] at h
        | cons payload arguments =>
            cases arguments with
            | cons extra arguments => simp [decodeSym] at h
            | nil =>
                cases hName : decodeString payload with
                | none => simp [decodeSym, hName] at h
                | some name =>
                    by_cases hConst : tag = constSymHead
                    · subst tag
                      simp [decodeSym, hName] at h
                      subst symbol
                      rw [(decodeString_eq_some_iff payload name).mp hName]
                      rfl
                    · by_cases hVar : tag = varSymHead
                      · subst tag
                        simp [decodeSym, hName, hConst] at h
                        subst symbol
                        rw [(decodeString_eq_some_iff payload name).mp hName]
                        rfl
                      · simp [decodeSym, hName, hConst, hVar] at h
  · rintro rfl
    simp

theorem decodeFormulaView_eq_some_iff
    (pattern : Pattern) (formula : ConstantHeadedFormula) :
    decodeFormulaView pattern = some formula ↔
      pattern = encodeFormula formula := by
  constructor
  · intro h
    cases pattern with
    | bvar index => simp [decodeFormulaView] at h
    | fvar name => simp [decodeFormulaView] at h
    | lambda binder body => simp [decodeFormulaView] at h
    | multiLambda arity binders body => simp [decodeFormulaView] at h
    | subst body replacement => simp [decodeFormulaView] at h
    | collection collectionType elements rest => simp [decodeFormulaView] at h
    | apply tag arguments =>
        cases arguments with
        | nil => simp [decodeFormulaView] at h
        | cons typecodePattern arguments =>
            cases arguments with
            | nil => simp [decodeFormulaView] at h
            | cons bodyPattern arguments =>
                cases arguments with
                | cons extra arguments => simp [decodeFormulaView] at h
                | nil =>
                    cases hTypecode : decodeString typecodePattern with
                    | none => simp [decodeFormulaView, hTypecode] at h
                    | some typecode =>
                        cases hBody : decodeListWith decodeSym bodyPattern with
                        | none => simp [decodeFormulaView, hTypecode, hBody] at h
                        | some body =>
                            simp [decodeFormulaView, hTypecode, hBody] at h
                            rcases h with ⟨rfl, rfl⟩
                            rw [(decodeString_eq_some_iff typecodePattern typecode).mp
                              hTypecode]
                            rw [(decodeListWith_eq_some_iff encodeSym decodeSym
                              decodeSym_eq_some_iff bodyPattern body).mp hBody]
                            rfl
  · rintro rfl
    simp

@[simp] theorem ConstantHeadedFormula.hasConstHead_toRuntime
    (formula : ConstantHeadedFormula) :
    formula.toRuntime.hasConstHead = true := by
  cases formula
  simp [ConstantHeadedFormula.toRuntime, Metamath.Verify.Formula.hasConstHead]

/-- The supported-view test is exactly the live runtime's Boolean
constant-head test, not an independent approximation. -/
theorem ConstantHeadedFormula.ofRuntime?_isSome_eq_hasConstHead
    (runtime : RuntimeFormula) :
    (ConstantHeadedFormula.ofRuntime? runtime).isSome = runtime.hasConstHead := by
  cases hList : runtime.toList with
  | nil =>
      have hRuntime : runtime = (#[] : RuntimeFormula) := by
        apply Array.ext'
        simp [hList]
      subst runtime
      rfl
  | cons head body =>
      have hRuntime : runtime = (head :: body).toArray := by
        apply Array.ext'
        simp [hList]
      subst runtime
      cases head <;>
        simp [ConstantHeadedFormula.ofRuntime?, Metamath.Verify.Formula.hasConstHead]

theorem ConstantHeadedFormula.ofRuntime?_success_iff_hasConstHead
    (runtime : RuntimeFormula) :
    (∃ formula, ConstantHeadedFormula.ofRuntime? runtime = some formula) ↔
      runtime.hasConstHead = true := by
  rw [← ConstantHeadedFormula.ofRuntime?_isSome_eq_hasConstHead]
  cases h : ConstantHeadedFormula.ofRuntime? runtime <;> simp

theorem decodeFormula_eq_some_iff
    (pattern : Pattern) (runtime : RuntimeFormula) :
    decodeFormula pattern = some runtime ↔
      ∃ formula : ConstantHeadedFormula,
        runtime = formula.toRuntime ∧ pattern = encodeFormula formula := by
  constructor
  · intro h
    cases hView : decodeFormulaView pattern with
    | none => simp [decodeFormula, hView] at h
    | some formula =>
        simp [decodeFormula, hView] at h
        subst runtime
        exact ⟨formula, rfl,
          (decodeFormulaView_eq_some_iff pattern formula).mp hView⟩
  · rintro ⟨formula, rfl, rfl⟩
    simp

theorem encodeRuntimeFormula_eq_some_iff
    (runtime : RuntimeFormula) (pattern : Pattern) :
    encodeRuntimeFormula? runtime = some pattern ↔
      ∃ formula : ConstantHeadedFormula,
        runtime = formula.toRuntime ∧ pattern = encodeFormula formula := by
  constructor
  · intro h
    cases hView : ConstantHeadedFormula.ofRuntime? runtime with
    | none => simp [encodeRuntimeFormula?, hView] at h
    | some formula =>
        simp [encodeRuntimeFormula?, hView] at h
        subst pattern
        exact ⟨formula,
          (ConstantHeadedFormula.ofRuntime?_eq_some_iff runtime formula).mp hView,
          rfl⟩
  · rintro ⟨formula, rfl, rfl⟩
    simp

/-- Successful runtime encoding and successful Pattern decoding are the same
graph on the supported constant-headed domain. -/
theorem encodeRuntimeFormula_eq_some_iff_decodeFormula
    (runtime : RuntimeFormula) (pattern : Pattern) :
    encodeRuntimeFormula? runtime = some pattern ↔
      decodeFormula pattern = some runtime := by
  rw [encodeRuntimeFormula_eq_some_iff, decodeFormula_eq_some_iff]

theorem decodeDVPair_eq_some_iff
    (pattern : Pattern) (pair : String × String) :
    decodeDVPair pattern = some pair ↔ pattern = encodeDVPair pair := by
  constructor
  · intro h
    cases pattern with
    | bvar index => simp [decodeDVPair] at h
    | fvar name => simp [decodeDVPair] at h
    | lambda binder body => simp [decodeDVPair] at h
    | multiLambda arity binders body => simp [decodeDVPair] at h
    | subst body replacement => simp [decodeDVPair] at h
    | collection collectionType elements rest => simp [decodeDVPair] at h
    | apply tag arguments =>
        cases arguments with
        | nil => simp [decodeDVPair] at h
        | cons leftPattern arguments =>
            cases arguments with
            | nil => simp [decodeDVPair] at h
            | cons rightPattern arguments =>
                cases arguments with
                | cons extra arguments => simp [decodeDVPair] at h
                | nil =>
                    cases hLeft : decodeString leftPattern with
                    | none => simp [decodeDVPair, hLeft] at h
                    | some left =>
                        cases hRight : decodeString rightPattern with
                        | none => simp [decodeDVPair, hLeft, hRight] at h
                        | some right =>
                            simp [decodeDVPair, hLeft, hRight] at h
                            rcases h with ⟨rfl, rfl⟩
                            rw [(decodeString_eq_some_iff leftPattern left).mp hLeft]
                            rw [(decodeString_eq_some_iff rightPattern right).mp hRight]
                            rfl
  · rintro rfl
    simp

theorem decodeFrame_eq_some_iff
    (pattern : Pattern) (frame : RuntimeFrame) :
    decodeFrame pattern = some frame ↔ pattern = encodeFrame frame := by
  constructor
  · intro h
    cases pattern with
    | bvar index => simp [decodeFrame] at h
    | fvar name => simp [decodeFrame] at h
    | lambda binder body => simp [decodeFrame] at h
    | multiLambda arity binders body => simp [decodeFrame] at h
    | subst body replacement => simp [decodeFrame] at h
    | collection collectionType elements rest => simp [decodeFrame] at h
    | apply tag arguments =>
        cases arguments with
        | nil => simp [decodeFrame] at h
        | cons dvPattern arguments =>
            cases arguments with
            | nil => simp [decodeFrame] at h
            | cons hypothesesPattern arguments =>
                cases arguments with
                | cons extra arguments => simp [decodeFrame] at h
                | nil =>
                    cases hDV : decodeListWith decodeDVPair dvPattern with
                    | none => simp [decodeFrame, hDV] at h
                    | some dj =>
                        cases hHyps : decodeListWith decodeString hypothesesPattern with
                        | none => simp [decodeFrame, hDV, hHyps] at h
                        | some hypotheses =>
                            simp [decodeFrame, hDV, hHyps] at h
                            rcases h with ⟨rfl, rfl⟩
                            rw [(decodeListWith_eq_some_iff encodeDVPair decodeDVPair
                              decodeDVPair_eq_some_iff dvPattern dj).mp hDV]
                            rw [(decodeListWith_eq_some_iff encodeString decodeString
                              decodeString_eq_some_iff hypothesesPattern hypotheses).mp
                              hHyps]
                            simp [encodeFrame]
  · rintro rfl
    simp

theorem decodeBinding_eq_some_iff
    (pattern : Pattern) (binding : FormulaBinding) :
    decodeBinding pattern = some binding ↔ pattern = encodeBinding binding := by
  constructor
  · intro h
    cases pattern with
    | bvar index => simp [decodeBinding] at h
    | fvar name => simp [decodeBinding] at h
    | lambda binder body => simp [decodeBinding] at h
    | multiLambda arity binders body => simp [decodeBinding] at h
    | subst body replacement => simp [decodeBinding] at h
    | collection collectionType elements rest => simp [decodeBinding] at h
    | apply tag arguments =>
        cases arguments with
        | nil => simp [decodeBinding] at h
        | cons variablePattern arguments =>
            cases arguments with
            | nil => simp [decodeBinding] at h
            | cons replacementPattern arguments =>
                cases arguments with
                | cons extra arguments => simp [decodeBinding] at h
                | nil =>
                    cases hVariable : decodeString variablePattern with
                    | none => simp [decodeBinding, hVariable] at h
                    | some variableName =>
                        cases hReplacement : decodeFormulaView replacementPattern with
                        | none => simp [decodeBinding, hVariable, hReplacement] at h
                        | some replacement =>
                            simp [decodeBinding, hVariable, hReplacement] at h
                            rcases h with ⟨rfl, rfl⟩
                            rw [(decodeString_eq_some_iff variablePattern variableName).mp
                              hVariable]
                            rw [(decodeFormulaView_eq_some_iff replacementPattern
                              replacement).mp hReplacement]
                            rfl
  · rintro rfl
    simp

theorem decodeSubstitution_eq_some_iff
    (pattern : Pattern) (substitution : FiniteSubstitution) :
    decodeSubstitution pattern = some substitution ↔
      pattern = encodeSubstitution substitution := by
  constructor
  · intro h
    cases pattern with
    | bvar index => simp [decodeSubstitution] at h
    | fvar name => simp [decodeSubstitution] at h
    | lambda binder body => simp [decodeSubstitution] at h
    | multiLambda arity binders body => simp [decodeSubstitution] at h
    | subst body replacement => simp [decodeSubstitution] at h
    | collection collectionType elements rest => simp [decodeSubstitution] at h
    | apply tag arguments =>
        cases arguments with
        | nil => simp [decodeSubstitution] at h
        | cons bindingsPattern arguments =>
            cases arguments with
            | cons extra arguments => simp [decodeSubstitution] at h
            | nil =>
                cases hBindings : decodeListWith decodeBinding bindingsPattern with
                | none => simp [decodeSubstitution, hBindings] at h
                | some bindings =>
                    simp [decodeSubstitution, hBindings] at h
                    rcases h with ⟨rfl, rfl⟩
                    rw [(decodeListWith_eq_some_iff encodeBinding decodeBinding
                      decodeBinding_eq_some_iff bindingsPattern bindings).mp hBindings]
                    rfl
  · rintro rfl
    simp

theorem exampleFormula_supported_image_gate :
    ConstantHeadedFormula.ofRuntime? exampleFormula.toRuntime =
        some exampleFormula ∧
      exampleFormula.toRuntime.hasConstHead = true ∧
      encodeRuntimeFormula? exampleFormula.toRuntime =
        some (encodeFormula exampleFormula) ∧
      decodeFormula (encodeFormula exampleFormula) =
        some exampleFormula.toRuntime := by
  simp

theorem variableHeaded_formula_unsupported_image_gate :
    ConstantHeadedFormula.ofRuntime? #[.var "ph", .const "ignored"] = none ∧
      Metamath.Verify.Formula.hasConstHead
        (#[.var "ph", .const "ignored"] : RuntimeFormula) = false ∧
      encodeRuntimeFormula? #[.var "ph", .const "ignored"] = none := by
  simp [ConstantHeadedFormula.ofRuntime?, Metamath.Verify.Formula.hasConstHead,
    encodeRuntimeFormula?]

/-!
The theorems above establish an exact in-memory `Pattern` image.  Serialized
projection still owes a generated-vocabulary allocation theorem and a proof
that arbitrary source strings are escaped into parser-accepted constructor
heads.  The current nullary payload preserves arbitrary strings exactly but
does not itself discharge that external character-validity obligation.
-/

end Mettapedia.Languages.Metamath.InferenceEncoding
