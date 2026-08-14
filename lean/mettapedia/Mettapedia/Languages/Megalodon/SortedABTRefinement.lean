import Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT
import Mettapedia.Languages.Megalodon.MathdataKernel

/-!
# Megalodon two-sorted ABT refinement

Megalodon terms have independent term-variable and type-variable de Bruijn
axes.  This module lowers both axes to the generic sorted ABT carrier.  Term
and type binders are retained as different field-signature entries, so the
physical operations cannot shift or substitute the wrong variable family.

The lowering has a partial inverse, exact signature conformance, and
commuting theorems for lift, substitution, unused-binder removal, and scope
checking on both axes.
-/

namespace Mettapedia.Languages.Megalodon.SortedABTRefinement

set_option autoImplicit false

open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT

/-- The two independent locally bound variable families in Mathdata. -/
inductive VarSort where
  | type
  | term
deriving Repr, DecidableEq

/-- Structural heads in the sorted physical carrier. -/
inductive Head where
  | dataName (name : String)
  | dataNat (value : Nat)
  | typeProp
  | typeBase
  | typeArr
  | typeAll
  | termNamed
  | termPrim
  | termApp
  | termLam
  | termImp
  | termAll
  | termTypeApp
  | termTypeLam
  | termTypeAll
deriving Repr, DecidableEq

abbrev ABT := Term VarSort Head
abbrev ABTFields := Fields VarSort Head

/-- Exact per-field binder-sort signature. -/
def signature : Head → List (List VarSort)
  | .dataName _ | .dataNat _ | .typeProp => []
  | .typeBase | .termNamed | .termPrim => [[]]
  | .typeArr | .termApp | .termImp | .termTypeApp => [[], []]
  | .typeAll => [[.type]]
  | .termLam | .termAll => [[], [.term]]
  | .termTypeLam | .termTypeAll => [[.type]]

private def leaf (head : Head) : ABT := .node head .nil

private def one (head : Head) (binders : List VarSort) (field : ABT) : ABT :=
  .node head (.cons binders field .nil)

private def two (head : Head)
    (leftBinders : List VarSort) (left : ABT)
    (rightBinders : List VarSort) (right : ABT) : ABT :=
  .node head
    (.cons leftBinders left (.cons rightBinders right .nil))

@[simp] private theorem lift_leaf (target : VarSort) (cutoff amount : Nat)
    (head : Head) :
    Term.lift target cutoff amount (leaf head) = leaf head := by
  simp [leaf, Term.lift, Term.Fields.lift]

@[simp] private theorem instantiateAt_leaf (target : VarSort) (depth : Nat)
    (replacement : ABT) (head : Head) :
    Term.instantiateAt target depth replacement (leaf head) = leaf head := by
  simp [leaf, Term.instantiateAt, Term.Fields.instantiateAt]

@[simp] private theorem dropAt_leaf (target : VarSort) (cutoff : Nat)
    (head : Head) :
    Term.dropAt? target cutoff (leaf head) = some (leaf head) := by
  simp [leaf, Term.dropAt?, Term.Fields.dropAt?]

@[simp] private theorem supportedAt_leaf (depth : VarSort → Nat)
    (head : Head) :
    Term.supportedAt depth (leaf head) = true := by
  simp [leaf, Term.supportedAt, Term.Fields.supportedAt]

/-! ## Exact lowering and decoding -/

def encodeType : Tp → ABT
  | .var index => .idx .type index
  | .prop => leaf .typeProp
  | .base index => one .typeBase [] (leaf (.dataNat index))
  | .arr domain codomain =>
      two .typeArr [] (encodeType domain) [] (encodeType codomain)
  | .all body => one .typeAll [.type] (encodeType body)

def encode : Tm → ABT
  | .db index => .idx .term index
  | .named name => one .termNamed [] (leaf (.dataName name))
  | .prim index => one .termPrim [] (leaf (.dataNat index))
  | .app function argument =>
      two .termApp [] (encode function) [] (encode argument)
  | .lam type body =>
      two .termLam [] (encodeType type) [.term] (encode body)
  | .imp domain codomain =>
      two .termImp [] (encode domain) [] (encode codomain)
  | .all type body =>
      two .termAll [] (encodeType type) [.term] (encode body)
  | .typeApp function type =>
      two .termTypeApp [] (encode function) [] (encodeType type)
  | .typeLam body => one .termTypeLam [.type] (encode body)
  | .typeAll body => one .termTypeAll [.type] (encode body)

def decodeType? : ABT → Option Tp
  | .idx .type index => some (.var index)
  | .node .typeProp .nil => some .prop
  | .node .typeBase (.cons [] (.node (.dataNat index) .nil) .nil) =>
      some (.base index)
  | .node .typeArr (.cons [] domain (.cons [] codomain .nil)) => do
      return .arr (← decodeType? domain) (← decodeType? codomain)
  | .node .typeAll (.cons [.type] body .nil) =>
      return .all (← decodeType? body)
  | _ => none

def decode? : ABT → Option Tm
  | .idx .term index => some (.db index)
  | .node .termNamed
      (.cons [] (.node (.dataName name) .nil) .nil) =>
      some (.named name)
  | .node .termPrim
      (.cons [] (.node (.dataNat index) .nil) .nil) =>
      some (.prim index)
  | .node .termApp (.cons [] function (.cons [] argument .nil)) => do
      return .app (← decode? function) (← decode? argument)
  | .node .termLam
      (.cons [] type (.cons [.term] body .nil)) => do
      return .lam (← decodeType? type) (← decode? body)
  | .node .termImp (.cons [] domain (.cons [] codomain .nil)) => do
      return .imp (← decode? domain) (← decode? codomain)
  | .node .termAll
      (.cons [] type (.cons [.term] body .nil)) => do
      return .all (← decodeType? type) (← decode? body)
  | .node .termTypeApp
      (.cons [] function (.cons [] type .nil)) => do
      return .typeApp (← decode? function) (← decodeType? type)
  | .node .termTypeLam (.cons [.type] body .nil) =>
      return .typeLam (← decode? body)
  | .node .termTypeAll (.cons [.type] body .nil) =>
      return .typeAll (← decode? body)
  | _ => none

@[simp] theorem decodeType_encodeType (type : Tp) :
    decodeType? (encodeType type) = some type := by
  induction type with
  | var index => rfl
  | prop => rfl
  | base index => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeType, two, decodeType?, domainHypothesis,
        codomainHypothesis]
  | all body inductionHypothesis =>
      simp [encodeType, one, decodeType?, inductionHypothesis]

@[simp] theorem decode_encode (term : Tm) :
    decode? (encode term) = some term := by
  induction term with
  | db index => rfl
  | named name => rfl
  | prim index => rfl
  | app function argument functionHypothesis argumentHypothesis =>
      simp [encode, two, decode?, functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [encode, two, decode?, bodyHypothesis]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [encode, two, decode?, domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [encode, two, decode?, bodyHypothesis]
  | typeApp function type functionHypothesis =>
      simp [encode, two, decode?, functionHypothesis]
  | typeLam body bodyHypothesis =>
      simp [encode, one, decode?, bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [encode, one, decode?, bodyHypothesis]

theorem encodeType_injective : Function.Injective encodeType := by
  intro left right equality
  have decoded := congrArg decodeType? equality
  simpa using decoded

theorem encode_injective : Function.Injective encode := by
  intro left right equality
  have decoded := congrArg decode? equality
  simpa using decoded

/-! ## Exact signature conformance -/

@[simp] theorem encodeType_conforms (type : Tp) :
    Term.conforms signature (encodeType type) = true := by
  induction type with
  | var index => rfl
  | prop => rfl
  | base index => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeType, two, signature, Term.conforms,
        Term.Fields.conforms, domainHypothesis, codomainHypothesis]
  | all body inductionHypothesis =>
      simp [encodeType, one, signature, Term.conforms,
        Term.Fields.conforms, inductionHypothesis]

@[simp] theorem encode_conforms (term : Tm) :
    Term.conforms signature (encode term) = true := by
  induction term with
  | db index => rfl
  | named name => rfl
  | prim index => rfl
  | app function argument functionHypothesis argumentHypothesis =>
      simp [encode, two, signature, Term.conforms, Term.Fields.conforms,
        functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [encode, two, signature, Term.conforms, Term.Fields.conforms,
        bodyHypothesis]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [encode, two, signature, Term.conforms, Term.Fields.conforms,
        domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [encode, two, signature, Term.conforms, Term.Fields.conforms,
        bodyHypothesis]
  | typeApp function type functionHypothesis =>
      simp [encode, two, signature, Term.conforms, Term.Fields.conforms,
        functionHypothesis]
  | typeLam body bodyHypothesis =>
      simp [encode, one, signature, Term.conforms, Term.Fields.conforms,
        bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [encode, one, signature, Term.conforms, Term.Fields.conforms,
        bodyHypothesis]

/-! ## Both lift axes -/

@[simp] theorem termLift_encodeType (cutoff amount : Nat) (type : Tp) :
    Term.lift .term cutoff amount (encodeType type) = encodeType type := by
  induction type with
  | var index => rfl
  | prop => rfl
  | base index => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeType, two, Term.lift, Term.Fields.lift,
        domainHypothesis, codomainHypothesis]
  | all body inductionHypothesis =>
      simp [encodeType, one, Term.lift, Term.Fields.lift,
        Term.binderCount, inductionHypothesis]

theorem encodeType_shift (cutoff amount : Nat) (type : Tp) :
    encodeType (Tp.shift cutoff amount type) =
      Term.lift .type cutoff amount (encodeType type) := by
  induction type generalizing cutoff with
  | var index =>
      by_cases below : index < cutoff <;>
        simp [Tp.shift, encodeType, Term.lift, below]
  | prop => simp [Tp.shift, encodeType]
  | base index =>
      simp [Tp.shift, encodeType, one, Term.lift, Term.Fields.lift]
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [Tp.shift, encodeType, two, Term.lift, Term.Fields.lift,
        domainHypothesis, codomainHypothesis]
  | all body bodyHypothesis =>
      simp [Tp.shift, encodeType, one, Term.lift, Term.Fields.lift,
        Term.binderCount, bodyHypothesis]

theorem encode_shift (cutoff amount : Nat) (term : Tm) :
    encode (Tm.shift cutoff amount term) =
      Term.lift .term cutoff amount (encode term) := by
  induction term generalizing cutoff with
  | db index =>
      by_cases below : index < cutoff <;>
        simp [Tm.shift, encode, Term.lift, below]
  | named name => simp [Tm.shift, encode, one, Term.lift, Term.Fields.lift]
  | prim index => simp [Tm.shift, encode, one, Term.lift, Term.Fields.lift]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [Tm.shift, encode, two, Term.lift, Term.Fields.lift,
        functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [Tm.shift, encode, two, Term.lift, Term.Fields.lift,
        Term.binderCount, bodyHypothesis, termLift_encodeType]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [Tm.shift, encode, two, Term.lift, Term.Fields.lift,
        domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [Tm.shift, encode, two, Term.lift, Term.Fields.lift,
        Term.binderCount, bodyHypothesis, termLift_encodeType]
  | typeApp function type functionHypothesis =>
      simp [Tm.shift, encode, two, Term.lift, Term.Fields.lift,
        functionHypothesis, termLift_encodeType]
  | typeLam body bodyHypothesis =>
      simp [Tm.shift, encode, one, Term.lift, Term.Fields.lift,
        Term.binderCount, bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [Tm.shift, encode, one, Term.lift, Term.Fields.lift,
        Term.binderCount, bodyHypothesis]

theorem encode_typeShift (cutoff amount : Nat) (term : Tm) :
    encode (Tm.typeShift cutoff amount term) =
      Term.lift .type cutoff amount (encode term) := by
  induction term generalizing cutoff with
  | db index => simp [Tm.typeShift, encode, Term.lift]
  | named name =>
      simp [Tm.typeShift, encode, one, Term.lift, Term.Fields.lift]
  | prim index =>
      simp [Tm.typeShift, encode, one, Term.lift, Term.Fields.lift]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [Tm.typeShift, encode, two, Term.lift, Term.Fields.lift,
        functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [Tm.typeShift, encode, two, Term.lift, Term.Fields.lift,
        bodyHypothesis, encodeType_shift]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [Tm.typeShift, encode, two, Term.lift, Term.Fields.lift,
        domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [Tm.typeShift, encode, two, Term.lift, Term.Fields.lift,
        bodyHypothesis, encodeType_shift]
  | typeApp function type functionHypothesis =>
      simp [Tm.typeShift, encode, two, Term.lift, Term.Fields.lift,
        functionHypothesis, encodeType_shift]
  | typeLam body bodyHypothesis =>
      simp [Tm.typeShift, encode, one, Term.lift, Term.Fields.lift,
        Term.binderCount, bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [Tm.typeShift, encode, one, Term.lift, Term.Fields.lift,
        Term.binderCount, bodyHypothesis]

/-! ## Both substitution axes -/

@[simp] theorem termInstantiateAt_encodeType (depth : Nat)
    (replacement : ABT) (type : Tp) :
    Term.instantiateAt .term depth replacement (encodeType type) =
      encodeType type := by
  induction type with
  | var index => rfl
  | prop => rfl
  | base index => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeType, two, Term.instantiateAt,
        Term.Fields.instantiateAt, domainHypothesis, codomainHypothesis]
  | all body bodyHypothesis =>
      simp [encodeType, one, Term.instantiateAt,
        Term.Fields.instantiateAt, Term.binderCount, bodyHypothesis]

theorem encodeType_instantiateAt (depth : Nat) (replacement body : Tp) :
    encodeType (Tp.instantiateAt depth replacement body) =
      Term.instantiateAt .type depth (encodeType replacement)
        (encodeType body) := by
  induction body generalizing depth with
  | var index =>
      by_cases below : index < depth
      · simp [Tp.instantiateAt, encodeType, Term.instantiateAt, below]
      · by_cases equal : index = depth <;>
          simp [Tp.instantiateAt, encodeType, Term.instantiateAt, below,
            equal, ← encodeType_shift]
  | prop => simp [Tp.instantiateAt, encodeType]
  | base index =>
      simp [Tp.instantiateAt, encodeType, one, Term.instantiateAt,
        Term.Fields.instantiateAt]
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [Tp.instantiateAt, encodeType, two, Term.instantiateAt,
        Term.Fields.instantiateAt, domainHypothesis, codomainHypothesis]
  | all body bodyHypothesis =>
      simp [Tp.instantiateAt, encodeType, one, Term.instantiateAt,
        Term.Fields.instantiateAt, Term.binderCount, bodyHypothesis]

theorem encode_instantiateAt (depth : Nat) (replacement body : Tm) :
    encode (Tm.instantiateAt depth replacement body) =
      Term.instantiateAt .term depth (encode replacement) (encode body) := by
  induction body generalizing depth with
  | db index =>
      by_cases below : index < depth
      · simp [Tm.instantiateAt, encode, Term.instantiateAt, below]
      · by_cases equal : index = depth <;>
          simp [Tm.instantiateAt, encode, Term.instantiateAt, below, equal,
            ← encode_shift]
  | named name =>
      simp [Tm.instantiateAt, encode, one, Term.instantiateAt,
        Term.Fields.instantiateAt]
  | prim index =>
      simp [Tm.instantiateAt, encode, one, Term.instantiateAt,
        Term.Fields.instantiateAt]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [Tm.instantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [Tm.instantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, Term.binderCount, bodyHypothesis,
        termInstantiateAt_encodeType]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [Tm.instantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [Tm.instantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, Term.binderCount, bodyHypothesis,
        termInstantiateAt_encodeType]
  | typeApp function type functionHypothesis =>
      simp [Tm.instantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, functionHypothesis,
        termInstantiateAt_encodeType]
  | typeLam body bodyHypothesis =>
      simp [Tm.instantiateAt, encode, one, Term.instantiateAt,
        Term.Fields.instantiateAt, Term.binderCount, bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [Tm.instantiateAt, encode, one, Term.instantiateAt,
        Term.Fields.instantiateAt, Term.binderCount, bodyHypothesis]

theorem encode_typeInstantiateAt (depth : Nat) (replacement : Tp)
    (body : Tm) :
    encode (Tm.typeInstantiateAt depth replacement body) =
      Term.instantiateAt .type depth (encodeType replacement) (encode body) := by
  induction body generalizing depth with
  | db index => simp [Tm.typeInstantiateAt, encode, Term.instantiateAt]
  | named name =>
      simp [Tm.typeInstantiateAt, encode, one, Term.instantiateAt,
        Term.Fields.instantiateAt]
  | prim index =>
      simp [Tm.typeInstantiateAt, encode, one, Term.instantiateAt,
        Term.Fields.instantiateAt]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [Tm.typeInstantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [Tm.typeInstantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, bodyHypothesis,
        encodeType_instantiateAt]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [Tm.typeInstantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [Tm.typeInstantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, bodyHypothesis,
        encodeType_instantiateAt]
  | typeApp function type functionHypothesis =>
      simp [Tm.typeInstantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, functionHypothesis,
        encodeType_instantiateAt]
  | typeLam body bodyHypothesis =>
      simp [Tm.typeInstantiateAt, encode, one, Term.instantiateAt,
        Term.Fields.instantiateAt, Term.binderCount, bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [Tm.typeInstantiateAt, encode, one, Term.instantiateAt,
        Term.Fields.instantiateAt, Term.binderCount, bodyHypothesis]

theorem encode_instantiate (replacement body : Tm) :
    encode (Tm.instantiate replacement body) =
      Term.instantiate .term (encode replacement) (encode body) :=
  encode_instantiateAt 0 replacement body

theorem encode_typeInstantiate (replacement : Tp) (body : Tm) :
    encode (Tm.typeInstantiate replacement body) =
      Term.instantiate .type (encodeType replacement) (encode body) :=
  encode_typeInstantiateAt 0 replacement body

/-! ## Both unused-binder axes -/

@[simp] theorem termDropAt_encodeType (cutoff : Nat) (type : Tp) :
    Term.dropAt? .term cutoff (encodeType type) = some (encodeType type) := by
  induction type with
  | var index => rfl
  | prop => rfl
  | base index => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeType, two, Term.dropAt?, Term.Fields.dropAt?,
        domainHypothesis, codomainHypothesis]
  | all body bodyHypothesis =>
      simp [encodeType, one, Term.dropAt?, Term.Fields.dropAt?,
        Term.binderCount, bodyHypothesis]

theorem encodeType_dropAt? (cutoff : Nat) (type : Tp) :
    (Tp.dropAt? cutoff type).map encodeType =
      Term.dropAt? .type cutoff (encodeType type) := by
  induction type generalizing cutoff with
  | var index =>
      by_cases below : index < cutoff
      · simp [Tp.dropAt?, encodeType, Term.dropAt?, below]
      · by_cases equal : index = cutoff <;>
          simp [Tp.dropAt?, encodeType, Term.dropAt?, below, equal]
  | prop => simp [Tp.dropAt?, encodeType]
  | base index =>
      simp [Tp.dropAt?, encodeType, one, Term.dropAt?,
        Term.Fields.dropAt?]
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [Tp.dropAt?, encodeType, two, Term.dropAt?,
        Term.Fields.dropAt?, ← domainHypothesis, ← codomainHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | all body bodyHypothesis =>
      simp [Tp.dropAt?, encodeType, one, Term.dropAt?,
        Term.Fields.dropAt?, Term.binderCount, ← bodyHypothesis,
        Option.map_eq_bind, Option.bind_assoc]

theorem encode_dropAt? (cutoff : Nat) (body : Tm) :
    (Tm.dropAt? cutoff body).map encode =
      Term.dropAt? .term cutoff (encode body) := by
  induction body generalizing cutoff with
  | db index =>
      by_cases below : index < cutoff
      · simp [Tm.dropAt?, encode, Term.dropAt?, below]
      · by_cases equal : index = cutoff <;>
          simp [Tm.dropAt?, encode, Term.dropAt?, below, equal]
  | named name =>
      simp [Tm.dropAt?, encode, one, Term.dropAt?, Term.Fields.dropAt?]
  | prim index =>
      simp [Tm.dropAt?, encode, one, Term.dropAt?, Term.Fields.dropAt?]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [Tm.dropAt?, encode, two, Term.dropAt?, Term.Fields.dropAt?,
        ← functionHypothesis, ← argumentHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | lam type body bodyHypothesis =>
      simp [Tm.dropAt?, encode, two, Term.dropAt?, Term.Fields.dropAt?,
        Term.binderCount, termDropAt_encodeType, ← bodyHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [Tm.dropAt?, encode, two, Term.dropAt?, Term.Fields.dropAt?,
        ← domainHypothesis, ← codomainHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | all type body bodyHypothesis =>
      simp [Tm.dropAt?, encode, two, Term.dropAt?, Term.Fields.dropAt?,
        Term.binderCount, termDropAt_encodeType, ← bodyHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | typeApp function type functionHypothesis =>
      simp [Tm.dropAt?, encode, two, Term.dropAt?, Term.Fields.dropAt?,
        ← functionHypothesis, termDropAt_encodeType,
        Option.map_eq_bind, Option.bind_assoc]
  | typeLam body bodyHypothesis =>
      simp [Tm.dropAt?, encode, one, Term.dropAt?, Term.Fields.dropAt?,
        Term.binderCount, ← bodyHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | typeAll body bodyHypothesis =>
      simp [Tm.dropAt?, encode, one, Term.dropAt?, Term.Fields.dropAt?,
        Term.binderCount, ← bodyHypothesis,
        Option.map_eq_bind, Option.bind_assoc]

/-- Successful removal of an unused term binder yields the exact shift
witness used by the proof-relevant eta rule. -/
theorem shift_of_dropAt?_eq_some (cutoff : Nat) {body result : Tm}
    (hypothesis : Tm.dropAt? cutoff body = some result) :
    Tm.shift cutoff 1 result = body := by
  apply encode_injective
  rw [encode_shift]
  apply Term.lift_of_dropAt?_eq_some
  rw [← encode_dropAt?]
  simp [hypothesis]

theorem encode_typeDropAt? (cutoff : Nat) (body : Tm) :
    (Tm.typeDropAt? cutoff body).map encode =
      Term.dropAt? .type cutoff (encode body) := by
  induction body generalizing cutoff with
  | db index => simp [Tm.typeDropAt?, encode, Term.dropAt?]
  | named name =>
      simp [Tm.typeDropAt?, encode, one, Term.dropAt?,
        Term.Fields.dropAt?]
  | prim index =>
      simp [Tm.typeDropAt?, encode, one, Term.dropAt?,
        Term.Fields.dropAt?]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [Tm.typeDropAt?, encode, two, Term.dropAt?,
        Term.Fields.dropAt?, ← functionHypothesis, ← argumentHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | lam type body bodyHypothesis =>
      simp [Tm.typeDropAt?, encode, two, Term.dropAt?,
        Term.Fields.dropAt?, ← encodeType_dropAt?, ← bodyHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [Tm.typeDropAt?, encode, two, Term.dropAt?,
        Term.Fields.dropAt?, ← domainHypothesis, ← codomainHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | all type body bodyHypothesis =>
      simp [Tm.typeDropAt?, encode, two, Term.dropAt?,
        Term.Fields.dropAt?, ← encodeType_dropAt?, ← bodyHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | typeApp function type functionHypothesis =>
      simp [Tm.typeDropAt?, encode, two, Term.dropAt?,
        Term.Fields.dropAt?, ← functionHypothesis, ← encodeType_dropAt?,
        Option.map_eq_bind, Option.bind_assoc]
  | typeLam body bodyHypothesis =>
      simp [Tm.typeDropAt?, encode, one, Term.dropAt?,
        Term.Fields.dropAt?, Term.binderCount, ← bodyHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | typeAll body bodyHypothesis =>
      simp [Tm.typeDropAt?, encode, one, Term.dropAt?,
        Term.Fields.dropAt?, Term.binderCount, ← bodyHypothesis,
        Option.map_eq_bind, Option.bind_assoc]

/-! ## Sorted support -/

def depthOf (typeDepth termDepth : Nat) : VarSort → Nat
  | .type => typeDepth
  | .term => termDepth

@[simp] theorem enter_depthOf_type (typeDepth termDepth : Nat) :
    Term.enter (depthOf typeDepth termDepth) [.type] =
      depthOf (typeDepth + 1) termDepth := by
  funext sort
  cases sort <;> simp [Term.enter, Term.binderCount, depthOf]

@[simp] theorem enter_depthOf_term (typeDepth termDepth : Nat) :
    Term.enter (depthOf typeDepth termDepth) [.term] =
      depthOf typeDepth (termDepth + 1) := by
  funext sort
  cases sort <;> simp [Term.enter, Term.binderCount, depthOf]

def typeSupportedAt (typeDepth : Nat) : Tp → Bool
  | .var index => decide (index < typeDepth)
  | .prop | .base _ => true
  | .arr domain codomain =>
      typeSupportedAt typeDepth domain && typeSupportedAt typeDepth codomain
  | .all body => typeSupportedAt (typeDepth + 1) body

def supportedAt (typeDepth termDepth : Nat) : Tm → Bool
  | .db index => decide (index < termDepth)
  | .named _ | .prim _ => true
  | .app function argument | .imp function argument =>
      supportedAt typeDepth termDepth function &&
        supportedAt typeDepth termDepth argument
  | .lam type body | .all type body =>
      typeSupportedAt typeDepth type &&
        supportedAt typeDepth (termDepth + 1) body
  | .typeApp function type =>
      supportedAt typeDepth termDepth function &&
        typeSupportedAt typeDepth type
  | .typeLam body | .typeAll body =>
      supportedAt (typeDepth + 1) termDepth body

@[simp] theorem supportedAt_encodeType (typeDepth termDepth : Nat)
    (type : Tp) :
    Term.supportedAt (depthOf typeDepth termDepth) (encodeType type) =
      typeSupportedAt typeDepth type := by
  induction type generalizing typeDepth with
  | var index => rfl
  | prop => rfl
  | base index => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeType, two, Term.supportedAt, Term.Fields.supportedAt,
        typeSupportedAt, domainHypothesis, codomainHypothesis]
  | all body bodyHypothesis =>
      simp [encodeType, one, Term.supportedAt, Term.Fields.supportedAt,
        typeSupportedAt, bodyHypothesis]

theorem supportedAt_encode (typeDepth termDepth : Nat) (term : Tm) :
    Term.supportedAt (depthOf typeDepth termDepth) (encode term) =
      supportedAt typeDepth termDepth term := by
  induction term generalizing typeDepth termDepth with
  | db index => rfl
  | named name => rfl
  | prim index => rfl
  | app function argument functionHypothesis argumentHypothesis =>
      simp [encode, two, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [encode, two, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, supportedAt_encodeType, bodyHypothesis]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [encode, two, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [encode, two, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, supportedAt_encodeType, bodyHypothesis]
  | typeApp function type functionHypothesis =>
      simp [encode, two, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, functionHypothesis, supportedAt_encodeType]
  | typeLam body bodyHypothesis =>
      simp [encode, one, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [encode, one, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, bodyHypothesis]

/-! ## Positive and negative canaries -/

def polymorphicIdentityGoal : Tm :=
  .typeAll
    (.all (.arr (.var 0) .prop)
      (.imp
        (.all (.var 0) (.app (.db 1) (.db 0)))
        (.all (.var 0) (.app (.db 1) (.db 0)))))

theorem polymorphicIdentityGoal_supported :
    Term.supportedAt (depthOf 0 0) (encode polymorphicIdentityGoal) = true := by
  rfl

def wrongTypeBinderSort : ABT :=
  one .termTypeAll [.term]
    (two .termImp [] (.idx .type 0) [] (.idx .type 0))

/-- A type abstraction decorated as a term binder is rejected by decoding. -/
theorem wrongTypeBinderSort_rejected :
    decode? wrongTypeBinderSort = none := by
  rfl

/-- The same sort error is independently rejected by conformance. -/
theorem wrongTypeBinderSort_nonconforming :
    Term.conforms signature wrongTypeBinderSort = false := by
  rfl

/-- Type substitution changes the type axis without moving a term index. -/
theorem independent_axes_canary :
    Tm.typeInstantiate .prop
        (.typeLam (.app (.db 0) (.typeApp (.db 1) (.var 0)))) =
      .typeLam (.app (.db 0) (.typeApp (.db 1) (.var 0))) := by
  rfl

end Mettapedia.Languages.Megalodon.SortedABTRefinement
