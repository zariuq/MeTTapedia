import Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
import Mettapedia.Languages.Megalodon.MathdataKernel

/-!
# Megalodon term-variable ABT refinement

Megalodon's `Tm` syntax contains two independent de Bruijn axes: term
variables and type variables.  CeTTa's current generic ABT engine operates on
one axis at a time.  This module therefore proves the exact lowering for the
term-variable axis: term variables become ABT indices, while type-variable
indices remain rigid structural data.  `TmLam` and `TmAll` bind in their body
field; type abstraction does not bind a term variable.

The resulting carrier is signature-indexed and distinct from `Tm`.  Its
decoder rejects an incorrect field-depth declaration, and its generic shift,
substitution, unused-binder removal, and scope check commute with the
Mathdata kernel operations.  A later sorted refinement must supply the
independent type-variable axis before polymorphic proof rules are lowered.
-/

namespace Mettapedia.Languages.Megalodon.TermABTRefinement

set_option autoImplicit false

open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

/-- Structural heads in the term-axis physical carrier. -/
inductive Head where
  | dataName (name : String)
  | dataNat (value : Nat)
  | typeVar
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

abbrev ABT := Term Head
abbrev ABTFields := Fields Head

/-- Per-field term-binder depths.  Type binders deliberately have depth zero
in this single-axis presentation. -/
def signature : Head → List Nat
  | .dataName _ | .dataNat _ | .typeProp => []
  | .typeVar | .typeBase | .typeAll | .termNamed | .termPrim |
      .termTypeLam | .termTypeAll => [0]
  | .typeArr | .termApp | .termImp | .termTypeApp => [0, 0]
  | .termLam | .termAll => [0, 1]

private def leaf (head : Head) : ABT := .node head .nil
private def one (head : Head) (depth : Nat) (field : ABT) : ABT :=
  .node head (.cons depth field .nil)
private def two (head : Head)
    (leftDepth : Nat) (left : ABT)
    (rightDepth : Nat) (right : ABT) : ABT :=
  .node head
    (.cons leftDepth left (.cons rightDepth right .nil))

@[simp] private theorem lift_leaf (cutoff amount : Nat) (head : Head) :
    Term.lift cutoff amount (leaf head) = leaf head := by
  simp [leaf, Term.lift, Term.Fields.lift]

@[simp] private theorem instantiateAt_leaf (depth : Nat)
    (replacement : ABT) (head : Head) :
    Term.instantiateAt depth replacement (leaf head) = leaf head := by
  simp [leaf, Term.instantiateAt, Term.Fields.instantiateAt]

@[simp] private theorem dropAt_leaf (cutoff : Nat) (head : Head) :
    Term.dropAt? cutoff (leaf head) = some (leaf head) := by
  simp [leaf, Term.dropAt?, Term.Fields.dropAt?]

@[simp] private theorem supportedAt_leaf (depth : Nat) (head : Head) :
    Term.supportedAt depth (leaf head) = true := by
  simp [leaf, Term.supportedAt, Term.Fields.supportedAt]

/-- Types are structural data for the term-variable axis. -/
def encodeType : Tp → ABT
  | .var index => one .typeVar 0 (leaf (.dataNat index))
  | .prop => leaf .typeProp
  | .base index => one .typeBase 0 (leaf (.dataNat index))
  | .arr domain codomain =>
      two .typeArr 0 (encodeType domain) 0 (encodeType codomain)
  | .all body => one .typeAll 0 (encodeType body)

/-- Lower Mathdata terms to the single-axis, field-indexed physical carrier. -/
def encode : Tm → ABT
  | .db index => .idx index
  | .named name => one .termNamed 0 (leaf (.dataName name))
  | .prim index => one .termPrim 0 (leaf (.dataNat index))
  | .app function argument =>
      two .termApp 0 (encode function) 0 (encode argument)
  | .lam type body =>
      two .termLam 0 (encodeType type) 1 (encode body)
  | .imp domain codomain =>
      two .termImp 0 (encode domain) 0 (encode codomain)
  | .all type body =>
      two .termAll 0 (encodeType type) 1 (encode body)
  | .typeApp function type =>
      two .termTypeApp 0 (encode function) 0 (encodeType type)
  | .typeLam body => one .termTypeLam 0 (encode body)
  | .typeAll body => one .termTypeAll 0 (encode body)

/-- Partial inverse for rigid type subtrees. -/
def decodeType? : ABT → Option Tp
  | .node .typeVar (.cons 0 (.node (.dataNat index) .nil) .nil) =>
      some (.var index)
  | .node .typeProp .nil => some .prop
  | .node .typeBase (.cons 0 (.node (.dataNat index) .nil) .nil) =>
      some (.base index)
  | .node .typeArr
      (.cons 0 domain (.cons 0 codomain .nil)) => do
      return .arr (← decodeType? domain) (← decodeType? codomain)
  | .node .typeAll (.cons 0 body .nil) =>
      return .all (← decodeType? body)
  | _ => none

/-- Partial inverse that rejects malformed or wrongly decorated term nodes. -/
def decode? : ABT → Option Tm
  | .idx index => some (.db index)
  | .node .termNamed
      (.cons 0 (.node (.dataName name) .nil) .nil) =>
      some (.named name)
  | .node .termPrim
      (.cons 0 (.node (.dataNat index) .nil) .nil) =>
      some (.prim index)
  | .node .termApp
      (.cons 0 function (.cons 0 argument .nil)) => do
      return .app (← decode? function) (← decode? argument)
  | .node .termLam
      (.cons 0 type (.cons 1 body .nil)) => do
      return .lam (← decodeType? type) (← decode? body)
  | .node .termImp
      (.cons 0 domain (.cons 0 codomain .nil)) => do
      return .imp (← decode? domain) (← decode? codomain)
  | .node .termAll
      (.cons 0 type (.cons 1 body .nil)) => do
      return .all (← decodeType? type) (← decode? body)
  | .node .termTypeApp
      (.cons 0 function (.cons 0 type .nil)) => do
      return .typeApp (← decode? function) (← decodeType? type)
  | .node .termTypeLam (.cons 0 body .nil) =>
      return .typeLam (← decode? body)
  | .node .termTypeAll (.cons 0 body .nil) =>
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

theorem encode_injective : Function.Injective encode := by
  intro left right equality
  have decoded := congrArg decode? equality
  simpa using decoded

/-! ## Signature conformance -/

@[simp] theorem encodeType_conforms (type : Tp) :
    Term.conforms signature (encodeType type) = true := by
  induction type with
  | var index => rfl
  | prop => rfl
  | base index => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeType, two, signature, Term.conforms, Term.Fields.conforms,
        domainHypothesis, codomainHypothesis]
  | all body inductionHypothesis =>
      simp [encodeType, one, signature, Term.conforms, Term.Fields.conforms,
        inductionHypothesis]

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

/-! ## Shift refinement -/

@[simp] theorem lift_encodeType (cutoff amount : Nat) (type : Tp) :
    Term.lift cutoff amount (encodeType type) = encodeType type := by
  induction type with
  | var index => rfl
  | prop => rfl
  | base index => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeType, two, Term.lift, Term.Fields.lift,
        domainHypothesis, codomainHypothesis]
  | all body inductionHypothesis =>
      simp [encodeType, one, Term.lift, Term.Fields.lift,
        inductionHypothesis]

/-- Generic physical shifting computes Mathdata term shifting exactly. -/
theorem encode_shift (cutoff amount : Nat) (term : Tm) :
    encode (Tm.shift cutoff amount term) =
      Term.lift cutoff amount (encode term) := by
  induction term generalizing cutoff with
  | db index =>
      by_cases below : index < cutoff <;>
        simp [Tm.shift, encode, Term.lift, below]
  | named name =>
      simp [Tm.shift, encode, one, Term.lift, Term.Fields.lift]
  | prim index =>
      simp [Tm.shift, encode, one, Term.lift, Term.Fields.lift]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [Tm.shift, encode, two, Term.lift, Term.Fields.lift,
        functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [Tm.shift, encode, two, Term.lift, Term.Fields.lift,
        bodyHypothesis, lift_encodeType]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [Tm.shift, encode, two, Term.lift, Term.Fields.lift,
        domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [Tm.shift, encode, two, Term.lift, Term.Fields.lift,
        bodyHypothesis, lift_encodeType]
  | typeApp function type functionHypothesis =>
      simp [Tm.shift, encode, two, Term.lift, Term.Fields.lift,
        functionHypothesis, lift_encodeType]
  | typeLam body bodyHypothesis =>
      simp [Tm.shift, encode, one, Term.lift, Term.Fields.lift,
        bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [Tm.shift, encode, one, Term.lift, Term.Fields.lift,
        bodyHypothesis]

/-! ## Substitution refinement -/

@[simp] theorem instantiateAt_encodeType (depth : Nat)
    (replacement : ABT) (type : Tp) :
    Term.instantiateAt depth replacement (encodeType type) =
      encodeType type := by
  induction type with
  | var index => rfl
  | prop => rfl
  | base index => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeType, two, Term.instantiateAt,
        Term.Fields.instantiateAt,
        domainHypothesis, codomainHypothesis]
  | all body inductionHypothesis =>
      simp [encodeType, one, Term.instantiateAt,
        Term.Fields.instantiateAt,
        inductionHypothesis]

/-- Generic physical substitution computes Mathdata capture-avoiding
substitution exactly. -/
theorem encode_instantiateAt (depth : Nat) (replacement body : Tm) :
    encode (Tm.instantiateAt depth replacement body) =
      Term.instantiateAt depth (encode replacement) (encode body) := by
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
        Term.Fields.instantiateAt, bodyHypothesis,
        instantiateAt_encodeType]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [Tm.instantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [Tm.instantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, bodyHypothesis,
        instantiateAt_encodeType]
  | typeApp function type functionHypothesis =>
      simp [Tm.instantiateAt, encode, two, Term.instantiateAt,
        Term.Fields.instantiateAt, functionHypothesis,
        instantiateAt_encodeType]
  | typeLam body bodyHypothesis =>
      simp [Tm.instantiateAt, encode, one, Term.instantiateAt,
        Term.Fields.instantiateAt, bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [Tm.instantiateAt, encode, one, Term.instantiateAt,
        Term.Fields.instantiateAt, bodyHypothesis]

theorem encode_instantiate (replacement body : Tm) :
    encode (Tm.instantiate replacement body) =
      Term.instantiate (encode replacement) (encode body) :=
  encode_instantiateAt 0 replacement body

/-! ## Unused-binder refinement -/

@[simp] theorem dropAt_encodeType (cutoff : Nat) (type : Tp) :
    Term.dropAt? cutoff (encodeType type) = some (encodeType type) := by
  induction type with
  | var index => rfl
  | prop => rfl
  | base index => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeType, two, Term.dropAt?, Term.Fields.dropAt?,
        domainHypothesis, codomainHypothesis]
  | all body inductionHypothesis =>
      simp [encodeType, one, Term.dropAt?, Term.Fields.dropAt?,
        inductionHypothesis]

/-- Generic unused-binder removal computes Mathdata removal exactly. -/
theorem encode_dropAt? (cutoff : Nat) (body : Tm) :
    (Tm.dropAt? cutoff body).map encode =
      Term.dropAt? cutoff (encode body) := by
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
        dropAt_encodeType, ← bodyHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [Tm.dropAt?, encode, two, Term.dropAt?, Term.Fields.dropAt?,
        ← domainHypothesis, ← codomainHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | all type body bodyHypothesis =>
      simp [Tm.dropAt?, encode, two, Term.dropAt?, Term.Fields.dropAt?,
        dropAt_encodeType, ← bodyHypothesis,
        Option.map_eq_bind, Option.bind_assoc]
  | typeApp function type functionHypothesis =>
      simp [Tm.dropAt?, encode, two, Term.dropAt?, Term.Fields.dropAt?,
        ← functionHypothesis, dropAt_encodeType,
        Option.map_eq_bind, Option.bind_assoc]
  | typeLam body bodyHypothesis =>
      simp [Tm.dropAt?, encode, one, Term.dropAt?, Term.Fields.dropAt?,
        ← bodyHypothesis, Option.map_eq_bind, Option.bind_assoc]
  | typeAll body bodyHypothesis =>
      simp [Tm.dropAt?, encode, one, Term.dropAt?, Term.Fields.dropAt?,
        ← bodyHypothesis, Option.map_eq_bind, Option.bind_assoc]

/-! ## Scope refinement -/

@[simp] theorem supportedAt_encodeType (depth : Nat) (type : Tp) :
    Term.supportedAt depth (encodeType type) = true := by
  induction type with
  | var index => simp [encodeType, one, Term.supportedAt,
      Term.Fields.supportedAt]
  | prop => simp [encodeType]
  | base index => simp [encodeType, one, Term.supportedAt,
      Term.Fields.supportedAt]
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp [encodeType, two, Term.supportedAt, Term.Fields.supportedAt,
        domainHypothesis, codomainHypothesis]
  | all body inductionHypothesis =>
      simp [encodeType, one, Term.supportedAt, Term.Fields.supportedAt,
        inductionHypothesis]

/-- Exact term-variable scope predicate for Mathdata terms. -/
def supportedAt (depth : Nat) : Tm → Bool
  | .db index => decide (index < depth)
  | .named _ | .prim _ => true
  | .app function argument | .imp function argument =>
      supportedAt depth function && supportedAt depth argument
  | .lam _ body | .all _ body => supportedAt (depth + 1) body
  | .typeApp function _ => supportedAt depth function
  | .typeLam body | .typeAll body => supportedAt depth body

/-- The physical scope checker recognizes exactly the Mathdata term support
predicate. -/
theorem supportedAt_encode (depth : Nat) (term : Tm) :
    Term.supportedAt depth (encode term) = supportedAt depth term := by
  induction term generalizing depth with
  | db index => rfl
  | named name => rfl
  | prim index => rfl
  | app function argument functionHypothesis argumentHypothesis =>
      simp [encode, two, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, functionHypothesis, argumentHypothesis]
  | lam type body bodyHypothesis =>
      simp [encode, two, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, bodyHypothesis]
  | imp domain codomain domainHypothesis codomainHypothesis =>
      simp [encode, two, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, domainHypothesis, codomainHypothesis]
  | all type body bodyHypothesis =>
      simp [encode, two, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, bodyHypothesis]
  | typeApp function type functionHypothesis =>
      simp [encode, two, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, functionHypothesis]
  | typeLam body bodyHypothesis =>
      simp [encode, one, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, bodyHypothesis]
  | typeAll body bodyHypothesis =>
      simp [encode, one, Term.supportedAt, Term.Fields.supportedAt,
        supportedAt, bodyHypothesis]

/-! ## Positive and negative canaries -/

def closedUniversal : Tm := .all .prop (.db 0)

theorem closedUniversal_supported :
    Term.supportedAt 0 (encode closedUniversal) = true := by
  rfl

def wrongUniversalDepth : ABT :=
  two .termAll 0 (encodeType .prop) 0 (.idx 0)

/-- A body field that forgets the universal binder is rejected by decoding. -/
theorem wrongUniversalDepth_rejected :
    decode? wrongUniversalDepth = none := by
  rfl

/-- The same defect is independently rejected by signature conformance. -/
theorem wrongUniversalDepth_nonconforming :
    Term.conforms signature wrongUniversalDepth = false := by
  rfl

/-- Substitution beneath a universal binder is capture-avoiding. -/
theorem universal_substitution_canary :
    Tm.instantiate (.named "witness")
        (.all .prop (.db 1)) =
      .all .prop (.named "witness") := by
  rfl

end Mettapedia.Languages.Megalodon.TermABTRefinement
