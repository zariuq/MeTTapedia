import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeMatchedTransportDenotation

/-!
# A total constructor algebra for native wire Data

The actual declaration gives both `application` and `cons` the type
`Data -> Data -> Data`. Their semantic operations therefore accept arbitrary
Data arguments, including nonsymbol application heads and improper tails.
The free algebra below preserves all constructor tags and payloads. Canonical
wire values embed injectively, but neither the algebra nor its operations are
defined by the native syntactic decoder.

The algebra is total. The accompanying `Denotes` relation is a constructor
fragment of the actual native syntax, not a total interpreter of arbitrary
native functions, J expressions, or universe heads. Its substitution theorem
uses independently typed native context morphisms and compatible Data
observations; it does not infer meanings for other fields of a mixed context.
Canonical equality is reflected, and Data encodings do not become identity
proofs. No quotient, full native model, or identity principle is selected.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeWireDataDenotation

open Presentation Presentation.Declaration
open Presentation.FormationSensitive (Typing Judgment)

universe u v

variable {n m : Nat} {State Source : Type u}

/-- The carrier of the free algebra for the six actual constructor families.
There is no symbolic-head or proper-tail side condition on either operation. -/
inductive Value where
  | symbol (payload : String)
  | string (payload : String)
  | natural (payload : Nat)
  | nil
  | application (head arguments : Value)
  | cons (head tail : Value)
  deriving DecidableEq, Repr

/-- Interpretations of the declared Data operations in an arbitrary carrier.
The binary fields are total functions, not partial decoding procedures. -/
structure Algebra (Carrier : Type v) where
  symbol : String → Carrier
  string : String → Carrier
  natural : Nat → Carrier
  nil : Carrier
  application : Carrier → Carrier → Carrier
  cons : Carrier → Carrier → Carrier

def algebra : Algebra Value :=
  ⟨Value.symbol, Value.string, Value.natural, Value.nil, Value.application, Value.cons⟩

def fold {Carrier : Type v} (target : Algebra Carrier) : Value → Carrier
  | .symbol payload => target.symbol payload
  | .string payload => target.string payload
  | .natural payload => target.natural payload
  | .nil => target.nil
  | .application head arguments => target.application (fold target head) (fold target arguments)
  | .cons head tail => target.cons (fold target head) (fold target tail)

/-- The initial-algebra law: the operations determine the interpretation of
every value, not just the values arising from canonical wire encodings. -/
theorem fold_unique {Carrier : Type v} (target : Algebra Carrier)
    (interpretation : Value → Carrier)
    (symbol : ∀ payload, interpretation (.symbol payload) = target.symbol payload)
    (string : ∀ payload, interpretation (.string payload) = target.string payload)
    (natural : ∀ payload, interpretation (.natural payload) = target.natural payload)
    (nil : interpretation .nil = target.nil)
    (application : ∀ head arguments, interpretation (.application head arguments) =
      target.application (interpretation head) (interpretation arguments))
    (cons : ∀ head tail, interpretation (.cons head tail) =
      target.cons (interpretation head) (interpretation tail)) :
    interpretation = fold target := by
  funext value
  induction value with
  | symbol payload => exact symbol payload
  | string payload => exact string payload
  | natural payload => exact natural payload
  | nil => exact nil
  | application head arguments ihHead ihArguments =>
      simpa only [fold, ihHead, ihArguments] using application head arguments
  | cons head tail ihHead ihTail =>
      simpa only [fold, ihHead, ihTail] using cons head tail

@[simp] theorem fold_algebra (value : Value) : fold algebra value = value := by
  induction value <;> simp_all [fold, algebra]

mutual

def ofWire : NativeWireData.Wire → Value
  | .symbol payload => .symbol payload
  | .string payload => .string payload
  | .natural payload => .natural payload
  | .application head arguments => .application (.symbol head) (ofWires arguments)
termination_by wire => sizeOf wire

def ofWires : List NativeWireData.Wire → Value
  | [] => .nil
  | head :: tail => .cons (ofWire head) (ofWires tail)
termination_by wires => sizeOf wires

end

/-- Reification into actual closed constructor syntax, at any ambient scope.
This is a representation of semantic values, not their definition by decoding. -/
def quote {n : Nat} : Value → Tower.Tm n
  | .symbol payload => .const (.str NativeWireData.symbolPrefix payload)
  | .string payload => .const (.str NativeWireData.stringPrefix payload)
  | .natural payload => .const (.num NativeWireData.naturalPrefix payload)
  | .nil => .const NativeWireData.nilName
  | .application head arguments =>
      .app (.app (.const NativeWireData.applicationName) (quote head)) (quote arguments)
  | .cons head tail => .app (.app (.const NativeWireData.consName) (quote head)) (quote tail)

@[simp] theorem subst_quote (substitution : Sub Tower.Head n m) (value : Value) :
    subst substitution (quote value) = quote value := by
  induction value <;> simp_all [quote, subst]

@[simp] theorem rename_quote (rho : Ren n m) (value : Value) :
    rename rho (quote value) = quote value := by
  rw [← subst_renSub, subst_quote]

mutual

@[simp] theorem quote_ofWire (wire : NativeWireData.Wire) :
    quote (n := n) (ofWire wire) = NativeWireData.encode wire := by
  cases wire with
  | symbol _ | string _ | natural _ => simp only [ofWire, quote, NativeWireData.encode]
  | application head arguments =>
      simp only [ofWire, quote, NativeWireData.encode, quote_ofWires arguments]
termination_by sizeOf wire

@[simp] theorem quote_ofWires (wires : List NativeWireData.Wire) :
    quote (n := n) (ofWires wires) = NativeWireData.encodeList wires := by
  cases wires with
  | nil => simp only [ofWires, quote, NativeWireData.encodeList]
  | cons head tail =>
      simp only [ofWires, quote, NativeWireData.encodeList, quote_ofWire head, quote_ofWires tail]
termination_by sizeOf wires

end

theorem ofWire_injective : Function.Injective ofWire := by
  intro left right equal
  apply NativeWireData.encode_injective (n := 0)
  simpa only [quote_ofWire] using congrArg (quote (n := 0)) equal

theorem ofWires_injective : Function.Injective ofWires := by
  intro left right equal
  apply NativeWireData.encodeList_injective (n := 0)
  simpa only [quote_ofWires] using congrArg (quote (n := 0)) equal

@[simp] theorem ofWire_eq_iff (left right : NativeWireData.Wire) :
    ofWire left = ofWire right ↔ left = right := ofWire_injective.eq_iff

@[simp] theorem ofWires_eq_iff (left right : List NativeWireData.Wire) :
    ofWires left = ofWires right ↔ left = right := ofWires_injective.eq_iff

/-- Native denotation for constructor terms. Only typed Data variables
consult the environment. Application and cons accept any two such meanings. -/
inductive Denotes (context : Tower.Ctx n) (environment : Fin n → State → Value) :
    Tower.Tm n → (State → Value) → Prop where
  | variable (index : Fin n)
      (typed : Typing HOLNativeRelatorCompatibility.rules context
        (.var index) NativeWireData.dataType) :
      Denotes context environment (.var index) (environment index)
  | symbol (payload : String) :
      Denotes context environment (.const (.str NativeWireData.symbolPrefix payload))
        (fun _ => .symbol payload)
  | string (payload : String) :
      Denotes context environment (.const (.str NativeWireData.stringPrefix payload))
        (fun _ => .string payload)
  | natural (payload : Nat) :
      Denotes context environment (.const (.num NativeWireData.naturalPrefix payload))
        (fun _ => .natural payload)
  | nil : Denotes context environment (.const NativeWireData.nilName) (fun _ => .nil)
  | application {head arguments : Tower.Tm n} {headValue argumentsValue : State → Value}
      (headMeaning : Denotes context environment head headValue)
      (argumentsMeaning : Denotes context environment arguments argumentsValue) :
      Denotes context environment
        (.app (.app (.const NativeWireData.applicationName) head) arguments)
        (fun state => .application (headValue state) (argumentsValue state))
  | cons {head tail : Tower.Tm n} {headValue tailValue : State → Value}
      (headMeaning : Denotes context environment head headValue)
      (tailMeaning : Denotes context environment tail tailValue) :
      Denotes context environment (.app (.app (.const NativeWireData.consName) head) tail)
        (fun state => .cons (headValue state) (tailValue state))

private theorem binary_typed {context : Tower.Ctx n} {name : Lean.Name}
    (declared : NativeWireData.rules.constantType name = some NativeWireData.binaryType)
    {left right : Tower.Tm n}
    (leftTyped : Typing HOLNativeRelatorCompatibility.rules context left NativeWireData.dataType)
    (rightTyped : Typing HOLNativeRelatorCompatibility.rules context right NativeWireData.dataType) :
    Typing HOLNativeRelatorCompatibility.rules context
      (.app (.app (.const name) left) right) NativeWireData.dataType := by
  have formed : Typing NativeWireData.rules .nil NativeWireData.binaryType
      (sortTm (.max Tower.zero (.max Tower.zero Tower.zero))) :=
    .piForm (NativeWireData.dataType_formed _) (.sort _)
      (.piForm (NativeWireData.dataType_formed _) (.sort _)
        (NativeWireData.dataType_formed _) (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _)
  have headTyped : Typing HOLNativeRelatorCompatibility.rules context
      (.const name) NativeWireData.binaryType :=
    HOLNativeRelatorCompatibility.wire_typing (.const declared formed (.sort _))
  have first : Typing HOLNativeRelatorCompatibility.rules context (.app (.const name) left)
      (.pi NativeWireData.dataType NativeWireData.dataType) := by
    simpa only [NativeWireData.binaryType, NativeWireData.dataType, inst0, subst] using
      Typing.appElim headTyped leftTyped
  simpa only [NativeWireData.dataType, inst0, subst] using Typing.appElim first rightTyped

theorem Denotes.typed {context : Tower.Ctx n} {environment : Fin n → State → Value}
    {term : Tower.Tm n} {value : State → Value} (meaning : Denotes context environment term value) :
    Typing HOLNativeRelatorCompatibility.rules context term NativeWireData.dataType := by
  induction meaning with
  | «variable» _ typed => exact typed
  | symbol payload =>
      simpa only [NativeWireData.encode] using HOLNativeRelatorCompatibility.wire_typing
        (NativeWireData.encode_typing context (.symbol payload))
  | string payload =>
      simpa only [NativeWireData.encode] using HOLNativeRelatorCompatibility.wire_typing
        (NativeWireData.encode_typing context (.string payload))
  | natural payload =>
      simpa only [NativeWireData.encode] using HOLNativeRelatorCompatibility.wire_typing
        (NativeWireData.encode_typing context (.natural payload))
  | nil => exact HOLNativeRelatorCompatibility.wire_typing (NativeWireData.nil_typing context)
  | application _ _ ihHead ihArguments =>
      exact binary_typed (by decide : NativeWireData.rules.constantType
        NativeWireData.applicationName = some NativeWireData.binaryType) ihHead ihArguments
  | cons _ _ ihHead ihTail =>
      exact binary_typed (by decide : NativeWireData.rules.constantType
        NativeWireData.consName = some NativeWireData.binaryType) ihHead ihTail

theorem quote_denotes (context : Tower.Ctx n) (environment : Fin n → State → Value) (value : Value) :
    Denotes context environment (quote value) (fun _ => value) := by
  induction value with
  | symbol payload => exact .symbol payload
  | string payload => exact .string payload
  | natural payload => exact .natural payload
  | nil => exact .nil
  | application _ _ ihHead ihArguments => exact .application ihHead ihArguments
  | cons _ _ ihHead ihTail => exact .cons ihHead ihTail

/-- Every element of the total semantic carrier has a formed native Data
representative. This includes all nonsymbol heads and improper tails. -/
theorem quote_judgment {context : Tower.Ctx n}
    (formed : FormationSensitive.ContextFormation HOLNativeRelatorCompatibility.rules context)
    (value : Value) :
    Judgment HOLNativeRelatorCompatibility.rules context (quote value) NativeWireData.dataType :=
  ⟨formed, (quote_denotes (State := Unit) context (fun _ _ => .nil) value).typed⟩

theorem encode_denotes (context : Tower.Ctx n) (environment : Fin n → State → Value)
    (wire : NativeWireData.Wire) :
    Denotes context environment (NativeWireData.encode wire) (fun _ => ofWire wire) := by
  simpa only [quote_ofWire] using quote_denotes context environment (ofWire wire)

theorem encodeList_denotes (context : Tower.Ctx n) (environment : Fin n → State → Value)
    (wires : List NativeWireData.Wire) :
    Denotes context environment (NativeWireData.encodeList wires) (fun _ => ofWires wires) := by
  simpa only [quote_ofWires] using quote_denotes context environment (ofWires wires)

private theorem denotes_functional_of_term_eq {context : Tower.Ctx n}
    {environment : Fin n → State → Value} {term otherTerm : Tower.Tm n}
    {left right : State → Value} (first : Denotes context environment term left)
    (second : Denotes context environment otherTerm right) (same : term = otherTerm) : left = right := by
  induction first generalizing otherTerm right <;>
    cases second <;>
    simp_all [Tm.var.injEq, Tm.const.injEq, Tm.app.injEq,
      NativeWireData.symbolPrefix, NativeWireData.stringPrefix, NativeWireData.naturalPrefix,
      NativeWireData.nilName, NativeWireData.applicationName, NativeWireData.consName]
  all_goals
    funext state
    congr 1 <;> exact congrFun (by solve_by_elim) state

theorem Denotes.functional {context : Tower.Ctx n} {environment : Fin n → State → Value}
    {term : Tower.Tm n} {left right : State → Value}
    (first : Denotes context environment term left)
    (second : Denotes context environment term right) : left = right :=
  denotes_functional_of_term_eq first second rfl

/-! ## Agreement with the previous wire-valued constructor meanings -/

mutual

theorem partialData_denotes {context : Tower.Ctx n}
    {environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire}
    {term : Tower.Tm n} {value : State → ULift.{u, 0} NativeWireData.Wire}
    (meaning : NativeMatchedTransportDenotation.DataDenotes context environment term value) :
    Denotes context (fun index state => ofWire (environment index state).down) term
      (fun state => ofWire (value state).down) := by
  cases meaning with
  | «variable» index typed => exact .variable index typed
  | symbol payload => simpa only [ofWire] using Denotes.symbol payload
  | string payload => simpa only [ofWire] using Denotes.string payload
  | natural payload => simpa only [ofWire] using Denotes.natural payload
  | application head arguments =>
      simpa only [ofWire] using
        Denotes.application (.symbol head) (partialList_denotes arguments)

theorem partialList_denotes {context : Tower.Ctx n}
    {environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire}
    {term : Tower.Tm n} {values : State → List (ULift.{u, 0} NativeWireData.Wire)}
    (meaning : NativeMatchedTransportDenotation.DataListDenotes context environment term values) :
    Denotes context (fun index state => ofWire (environment index state).down) term
      (fun state => ofWires ((values state).map ULift.down)) := by
  cases meaning with
  | nil => simpa only [List.map_nil, ofWires] using Denotes.nil
  | cons head tail =>
      simpa only [List.map_cons, ofWires] using
        Denotes.cons (partialData_denotes head) (partialList_denotes tail)

end

/-! ## Actual native substitution and semantic reindexing -/

theorem Denotes.reindex {context : Tower.Ctx n} {environment : Fin n → State → Value}
    {term : Tower.Tm n} {value : State → Value}
    (meaning : Denotes context environment term value) (reindex : Source → State) :
    Denotes context (fun index => environment index ∘ reindex) term (value ∘ reindex) := by
  induction meaning with
  | «variable» index typed => exact .variable index typed
  | symbol payload => exact .symbol payload
  | string payload => exact .string payload
  | natural payload => exact .natural payload
  | nil => exact .nil
  | application _ _ ihHead ihArguments => exact .application ihHead ihArguments
  | cons _ _ ihHead ihTail => exact .cons ihHead ihTail

theorem Denotes.substitute {context : Tower.Ctx n} {target : Tower.Ctx m}
    {environment : Fin n → State → Value} {targetEnvironment : Fin m → Source → Value}
    {term : Tower.Tm n} {value : State → Value}
    (meaning : Denotes context environment term value)
    (substitution : Sub Tower.Head n m) (reindex : Source → State)
    (components : ∀ index, Typing HOLNativeRelatorCompatibility.rules context
      (.var index) NativeWireData.dataType →
      Denotes target targetEnvironment (substitution index)
        (fun state => environment index (reindex state))) :
    Denotes target targetEnvironment (subst substitution term) (value ∘ reindex) := by
  induction meaning with
  | «variable» index typed => exact components index typed
  | symbol payload => exact .symbol payload
  | string payload => exact .string payload
  | natural payload => exact .natural payload
  | nil => exact .nil
  | application _ _ ihHead ihArguments => exact .application ihHead ihArguments
  | cons _ _ ihHead ihTail => exact .cons ihHead ihTail

/-- Full refined context admission is an independent premise. The same
capture-safe substitution preserves the native judgment and commutes with
the semantic observations of its Data-typed components. -/
theorem Denotes.substitute_judgment {context : Tower.Ctx n} {target : Tower.Ctx m}
    {environment : Fin n → State → Value} {targetEnvironment : Fin m → Source → Value}
    {term : Tower.Tm n} {value : State → Value}
    (meaning : Denotes context environment term value)
    (contextFormed : FormationSensitive.ContextFormation HOLNativeRelatorCompatibility.rules context)
    (targetFormed : FormationSensitive.ContextFormation HOLNativeRelatorCompatibility.rules target)
    (substitution : Sub Tower.Head n m)
    (typed : FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules context target substitution)
    (reindex : Source → State)
    (components : ∀ index, Typing HOLNativeRelatorCompatibility.rules context
      (.var index) NativeWireData.dataType →
      Denotes target targetEnvironment (substitution index)
        (fun state => environment index (reindex state))) :
    Judgment HOLNativeRelatorCompatibility.rules target (subst substitution term) NativeWireData.dataType ∧
      Denotes target targetEnvironment (subst substitution term) (value ∘ reindex) := by
  refine ⟨?_, meaning.substitute substitution reindex components⟩
  have admitted : Judgment HOLNativeRelatorCompatibility.rules context term NativeWireData.dataType :=
    ⟨contextFormed, meaning.typed⟩
  simpa only [NativeWireData.dataType, subst] using admitted.substitute targetFormed typed

/-! ## Constructor and evidence boundaries -/

theorem application_injective {head arguments otherHead otherArguments : Value} :
    Value.application head arguments = .application otherHead otherArguments ↔
      head = otherHead ∧ arguments = otherArguments := by simp only [Value.application.injEq]

theorem cons_injective {head tail otherHead otherTail : Value} :
    Value.cons head tail = .cons otherHead otherTail ↔ head = otherHead ∧ tail = otherTail :=
  by simp only [Value.cons.injEq]

theorem application_ne_cons (head arguments otherHead otherTail : Value) :
    Value.application head arguments ≠ .cons otherHead otherTail := by
  intro equal
  cases equal

theorem symbol_ne_string (payload otherPayload : String) :
    Value.symbol payload ≠ .string otherPayload := by
  intro equal
  cases equal

/-- Canonical endpoint identity is transported and reflected, with its full
existing equality witness. This is not a new native identity rule. -/
def wireIdentityEquiv (left right : NativeWireData.Wire) :
    ULift.{u} (PLift (left = right)) ≃ ULift.{u} (PLift (ofWire left = ofWire right)) where
  toFun witness := ⟨⟨congrArg ofWire witness.down.down⟩⟩
  invFun witness := ⟨⟨ofWire_injective witness.down.down⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem changed_wire_has_empty_identity {left right : NativeWireData.Wire} (different : left ≠ right) :
    IsEmpty (ULift.{u} (PLift (ofWire left = ofWire right))) :=
  ⟨fun witness => different (ofWire_injective witness.down.down)⟩

/-- A reified Data value, including an encoded receipt, is not the native
reflexivity constructor. Its Data meaning supplies no proof interpretation. -/
theorem quote_ne_reflexivity (value : Value) (point : Tower.Tm n) : quote value ≠ .refl point := by
  intro equal
  cases value <;> cases equal

namespace Examples

/-- These values use precisely the arguments excluded by the old wire-only
meaning, although the native declarations have always admitted them. -/
def nonsymbolHead : Value := .application (.natural 0) .nil

def improperTail : Value := .cons (.symbol "opaque-payload") (.natural 1)

theorem noncanonical_formed_and_denoted (environment : Fin 3 → State → Value) :
    Judgment HOLNativeRelatorCompatibility.rules OpaqueRelatorScopedComputation.Common.context
        (quote nonsymbolHead) NativeWireData.dataType ∧
      Denotes OpaqueRelatorScopedComputation.Common.context environment
        (quote nonsymbolHead) (fun _ => nonsymbolHead) ∧
      Judgment HOLNativeRelatorCompatibility.rules OpaqueRelatorScopedComputation.Common.context
        (quote improperTail) NativeWireData.dataType ∧
      Denotes OpaqueRelatorScopedComputation.Common.context environment
        (quote improperTail) (fun _ => improperTail) :=
  ⟨quote_judgment OpaqueRelatorScopedComputation.Common.context_formed _, quote_denotes _ environment _,
    quote_judgment OpaqueRelatorScopedComputation.Common.context_formed _, quote_denotes _ environment _⟩

theorem nonsymbolHead_not_wire (wire : NativeWireData.Wire) : nonsymbolHead ≠ ofWire wire := by
  cases wire <;> simp [nonsymbolHead, ofWire]

theorem improperTail_not_wire (wire : NativeWireData.Wire) : improperTail ≠ ofWire wire := by
  cases wire <;> simp [improperTail, ofWire]

theorem improperTail_not_list (wires : List NativeWireData.Wire) : improperTail ≠ ofWires wires := by
  cases wires with
  | nil => simp [improperTail, ofWires]
  | cons head tail =>
      cases tail <;> simp [improperTail, ofWires]

theorem syntactic_decoding_is_not_denotation :
    NativeWireData.decode (quote (n := 3) nonsymbolHead) = none ∧
      NativeWireData.decodeList (quote (n := 3) improperTail) = none := by
  simp [nonsymbolHead, improperTail, quote, NativeWireData.decode, NativeWireData.decodeList,
    NativeWireData.applicationName, NativeWireData.consName, NativeWireData.symbolPrefix,
    NativeWireData.naturalPrefix, NativeWireData.nilName]

theorem retained_order :
    ofWires [.symbol "opaque-payload", .natural 1] ≠
      ofWires [.natural 1, .symbol "opaque-payload"] := by
  intro equal
  have ordered := ofWires_injective equal
  cases ordered

end Examples

/-! ## An arbitrary Data argument in the actual mixed native context -/

/-- A fresh Data coordinate over the existing HOL/wire/List/J context.
Only its observation is added; no meaning for the old context's types is inferred. -/
def parameterEnvironment (environment : Fin 3 → State → Value) : Fin 4 → State × Value → Value :=
  Fin.cases Prod.snd (fun index state => environment index state.1)

def parameterReindex (value : Value) (state : State) : State × Value := (state, value)

def fillParameter (value : Value) : Sub Tower.Head 4 3 := consSub (quote value) ids

theorem fillParameter_typed (value : Value) :
    FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules
      NativeMatchedTransportDenotation.parameterContext
      OpaqueRelatorScopedComputation.Common.context (fillParameter value) := by
  have identity : FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules
      OpaqueRelatorScopedComputation.Common.context OpaqueRelatorScopedComputation.Common.context ids :=
    fun index => by simpa only [ids, subst_ids] using Typing.var index
  exact identity.extend (by
    simpa only [subst_ids] using
      (quote_judgment OpaqueRelatorScopedComputation.Common.context_formed value).typing)

/-- The parameter occurs in both a head slot and an improper-tail slot. -/
def parameterTerm : Tower.Tm 4 :=
  .app (.app (.const NativeWireData.applicationName) (.var 0))
    (.app (.app (.const NativeWireData.consName) (quote (.symbol "opaque-payload"))) (.var 0))

def parameterValue (value : Value) : Value :=
  .application value (.cons (.symbol "opaque-payload") value)

theorem parameterTerm_denotes (environment : Fin 3 → State → Value) :
    Denotes NativeMatchedTransportDenotation.parameterContext (parameterEnvironment environment)
      parameterTerm (fun state => parameterValue state.2) :=
  .application (.variable 0 NativeMatchedTransportDenotation.parameter_typed)
    (.cons (.symbol "opaque-payload") (.variable 0 NativeMatchedTransportDenotation.parameter_typed))

theorem fillParameter_components (environment : Fin 3 → State → Value) (value : Value)
    (index : Fin 4)
    (typed : Typing HOLNativeRelatorCompatibility.rules NativeMatchedTransportDenotation.parameterContext
      (.var index) NativeWireData.dataType) :
    Denotes OpaqueRelatorScopedComputation.Common.context environment (fillParameter value index)
      (fun state => parameterEnvironment environment index (parameterReindex value state)) := by
  refine Fin.cases ?_ ?_ index typed
  · intro _
    exact quote_denotes _ environment value
  · intro prior priorTyped
    have specialized := priorTyped.substitute (fillParameter_typed value)
    have variableTyped : Typing HOLNativeRelatorCompatibility.rules
        OpaqueRelatorScopedComputation.Common.context (.var prior) NativeWireData.dataType := by
      simpa only [subst, fillParameter, consSub_succ, ids, NativeWireData.dataType] using specialized
    exact .variable prior variableTyped

theorem fillParameter_term (value : Value) :
    subst (fillParameter value) parameterTerm = quote (parameterValue value) := by
  simp only [parameterTerm, subst, fillParameter, consSub_zero, parameterValue, quote]

/-- A nonconstant, actually typed-context substitution square, for every
Data value rather than only wire-encoded values. Both native admission and
the semantic result use the same substituted source and parameter. -/
theorem parameter_substitution (environment : Fin 3 → State → Value) (value : Value) :
    Judgment HOLNativeRelatorCompatibility.rules OpaqueRelatorScopedComputation.Common.context
        (subst (fillParameter value) parameterTerm) NativeWireData.dataType ∧
      Denotes OpaqueRelatorScopedComputation.Common.context environment
        (subst (fillParameter value) parameterTerm) (fun _ => parameterValue value) := by
  exact (parameterTerm_denotes environment).substitute_judgment
    NativeMatchedTransportDenotation.parameterContext_formed
    OpaqueRelatorScopedComputation.Common.context_formed (fillParameter value)
    (fillParameter_typed value) (parameterReindex value) (fillParameter_components environment value)

theorem parameterValue_injective : Function.Injective parameterValue := by
  intro left right equal
  exact (Value.application.inj equal).1

/-- A changed observation cannot be assigned to the same filled source.
An actual state is required because functions from an empty state space do
not distinguish observations. -/
theorem changed_parameter_meaning_rejected (environment : Fin 3 → State → Value) (state : State)
    {left right : Value} (different : left ≠ right) :
    ¬ Denotes OpaqueRelatorScopedComputation.Common.context environment
      (subst (fillParameter left) parameterTerm) (fun _ => parameterValue right) := by
  intro changed
  have same := (parameter_substitution environment left).2.functional changed
  exact different (parameterValue_injective (congrFun same state))

namespace Examples

theorem noncanonical_parameter_square (environment : Fin 3 → State → Value) :
    FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules
        NativeMatchedTransportDenotation.parameterContext
        OpaqueRelatorScopedComputation.Common.context (fillParameter improperTail) ∧
      Judgment HOLNativeRelatorCompatibility.rules OpaqueRelatorScopedComputation.Common.context
        (subst (fillParameter improperTail) parameterTerm) NativeWireData.dataType ∧
      Denotes OpaqueRelatorScopedComputation.Common.context environment
        (subst (fillParameter improperTail) parameterTerm) (fun _ => parameterValue improperTail) ∧
      NativeWireData.decode (quote (n := 3) improperTail) = none := by
  refine ⟨fillParameter_typed _, (parameter_substitution environment _).1,
    (parameter_substitution environment _).2, ?_⟩
  simp [improperTail, quote, NativeWireData.decode, NativeWireData.consName,
    NativeWireData.applicationName, NativeWireData.symbolPrefix]

theorem changed_noncanonical_parameter_rejected (environment : Fin 3 → State → Value) (state : State) :
    ¬ Denotes OpaqueRelatorScopedComputation.Common.context environment
      (subst (fillParameter improperTail) parameterTerm) (fun _ => parameterValue nonsymbolHead) :=
  changed_parameter_meaning_rejected environment state (by decide)

end Examples

end NativeWireDataDenotation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
