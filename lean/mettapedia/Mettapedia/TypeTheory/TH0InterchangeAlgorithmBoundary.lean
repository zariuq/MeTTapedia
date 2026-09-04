import Mathlib.Data.Finset.Basic
import Mettapedia.Logic.HOL.Syntax.Closed
import Mettapedia.TypeTheory.Authority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTWireFormat

/-!
# TH0 interchange and algorithm boundary

This module isolates the first higher-order semantic view needed by a TPTP
interchange library.  Parsing and preserving an official THF record does not
make that record a typed HOL object.  The boundary here begins after syntax
classification:

* an explicit, serializable TH0 packet retains types and de Bruijn indices;
* a fail-closed decoder produces the existing intrinsically typed HOL syntax;
* checked, rejected, residual, incomplete, and operational-fault outcomes stay
  distinct;
* beta is exposed as one independently replayable typed operation;
* the requirements of a substitution kernel are proved to be a strict subset
  of the declared requirements of lambda-superposition.

The packet is deliberately not live MeTTa syntax.  HE-, PeTTa-, Prime-, and
CeTTa-facing adapters may carry and inspect it, but an adapter earns semantic
authority only by agreeing with the intrinsic decoder.  Higher-order search is
a replaceable consumer of the checked packet, not part of parsing.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary

open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.AuthorityTheory
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-! ## A portable, explicitly typed TH0 packet -/

/-- Serializable simple types.  The wrapper is intentionally transparent to
the intrinsic type algebra: the symbolic wire below, rather than a second
parallel inductive, supplies the physical representation.  `String` is symbol
identity at this boundary; source occurrences and namespace provenance belong
to the enclosing artifact. -/
structure TypePacket where
  decode : Ty String
deriving Repr, DecidableEq

namespace TypePacket

/-- Packet constructors mirror the TH0 simple-type signature. -/
def prop : TypePacket := ⟨.prop⟩
def base (name : String) : TypePacket := ⟨.base name⟩
def arrow (domain codomain : TypePacket) : TypePacket :=
  ⟨.arr domain.decode codomain.decode⟩

/-- Canonical packet for an intrinsic TH0 type. -/
def encode (type : Ty String) : TypePacket := ⟨type⟩

@[simp] theorem decode_encode (type : Ty String) :
    (encode type).decode = type :=
  rfl

@[simp] theorem encode_decode (packet : TypePacket) :
    encode packet.decode = packet := by
  cases packet
  rfl

theorem encode_injective : Function.Injective encode := by
  intro first second equal
  have := congrArg decode equal
  simpa using this

end TypePacket

/-- Typed constant identities used by the intrinsic decoder. -/
structure Constant (type : Ty String) where
  name : String
deriving Repr, DecidableEq

/-- An extrinsic TH0 term packet.  Application and abstraction retain both
domain and codomain annotations so a C implementation can check locally and
fail closed without reconstructing hidden metavariables. -/
inductive TermPacket where
  | bound (index : Nat) (type : TypePacket)
  | constant (name : String) (type : TypePacket)
  | app (domain codomain : TypePacket) (function argument : TermPacket)
  | lam (domain codomain : TypePacket) (body : TermPacket)
  | top
  | bottom
  | and (left right : TermPacket)
  | or (left right : TermPacket)
  | imp (antecedent consequent : TermPacket)
  | not (body : TermPacket)
  | equal (type : TypePacket) (left right : TermPacket)
  | forallE (domain : TypePacket) (body : TermPacket)
  | existsE (domain : TypePacket) (body : TermPacket)
deriving Repr, DecidableEq

/-! ## Fail-closed decoding into intrinsically typed HOL -/

/-- Look up a de Bruijn index at an expected intrinsic type.  The result type
itself certifies both scope and type agreement. -/
def decodeVar? : (context : Ctx String) → (index : Nat) →
    (type : Ty String) → Option (Var context type)
  | [], _, _ => none
  | head :: tail, 0, type =>
      if equal : head = type then
        some (cast (congrArg (fun result => Var (head :: tail) result) equal)
          (Var.vz : Var (head :: tail) head))
      else
        none
  | _head :: tail, index + 1, type =>
      (decodeVar? tail index type).map Var.vs

/-- The numerical de Bruijn index of an intrinsic variable. -/
def encodeVar {context : Ctx String} {type : Ty String} :
    Var context type → Nat
  | .vz => 0
  | .vs var => encodeVar var + 1

@[simp] theorem decodeVar?_encodeVar {context : Ctx String}
    {type : Ty String} (var : Var context type) :
    decodeVar? context (encodeVar var) type = some var := by
  induction var with
  | vz => simp [encodeVar, decodeVar?]
  | vs var inductionHypothesis =>
      simp [encodeVar, decodeVar?, inductionHypothesis]

/-- Decode one term against an explicitly expected type.  A successful result
is intrinsically scoped and typed by construction. -/
def decodeTerm? (context : Ctx String) :
    (packet : TermPacket) → (type : Ty String) →
      Option (Term Constant context type)
  | .bound index annotated, type =>
      if annotated.decode = type then
        (decodeVar? context index type).map Term.var
      else
        none
  | .constant name annotated, type =>
      if annotated.decode = type then
        some (.const ⟨name⟩)
      else
        none
  | .app domain codomain function argument, type =>
      if equal : codomain.decode = type then
        match decodeTerm? context function (.arr domain.decode codomain.decode),
            decodeTerm? context argument domain.decode with
        | some decodedFunction, some decodedArgument =>
            some (cast
              (congrArg (fun result => Term Constant context result) equal)
              (.app decodedFunction decodedArgument))
        | _, _ => none
      else
        none
  | .lam domain codomain body, type =>
      if equal : Ty.arr domain.decode codomain.decode = type then
        match decodeTerm? (domain.decode :: context) body codomain.decode with
        | some decodedBody =>
            some (cast
              (congrArg (fun result => Term Constant context result) equal)
              (.lam decodedBody))
        | none => none
      else
        none
  | .top, .prop => some .top
  | .top, _ => none
  | .bottom, .prop => some .bot
  | .bottom, _ => none
  | .and left right, .prop => do
      let decodedLeft ← decodeTerm? context left .prop
      let decodedRight ← decodeTerm? context right .prop
      some (.and decodedLeft decodedRight)
  | .and _ _, _ => none
  | .or left right, .prop => do
      let decodedLeft ← decodeTerm? context left .prop
      let decodedRight ← decodeTerm? context right .prop
      some (.or decodedLeft decodedRight)
  | .or _ _, _ => none
  | .imp antecedent consequent, .prop => do
      let decodedAntecedent ← decodeTerm? context antecedent .prop
      let decodedConsequent ← decodeTerm? context consequent .prop
      some (.imp decodedAntecedent decodedConsequent)
  | .imp _ _, _ => none
  | .not body, .prop => do
      let decodedBody ← decodeTerm? context body .prop
      some (.not decodedBody)
  | .not _, _ => none
  | .equal comparedType left right, .prop => do
      let decodedLeft ← decodeTerm? context left comparedType.decode
      let decodedRight ← decodeTerm? context right comparedType.decode
      some (.eq decodedLeft decodedRight)
  | .equal _ _ _, _ => none
  | .forallE domain body, .prop => do
      let decodedBody ←
        decodeTerm? (domain.decode :: context) body .prop
      some (.all decodedBody)
  | .forallE _ _, _ => none
  | .existsE domain body, .prop => do
      let decodedBody ←
        decodeTerm? (domain.decode :: context) body .prop
      some (.ex decodedBody)
  | .existsE _ _, _ => none
termination_by packet _type => sizeOf packet

/-- Canonical extrinsic packet for an intrinsic term. -/
def encodeTerm {context : Ctx String} {type : Ty String} :
    Term Constant context type → TermPacket
  | .var var => .bound (encodeVar var) (TypePacket.encode type)
  | .const constant =>
      .constant constant.name (TypePacket.encode type)
  | @Term.app _ _ _ domain codomain function argument =>
      .app (TypePacket.encode domain) (TypePacket.encode codomain)
        (encodeTerm function) (encodeTerm argument)
  | @Term.lam _ _ domain _ codomain body =>
      .lam (TypePacket.encode domain) (TypePacket.encode codomain)
        (encodeTerm body)
  | .top => .top
  | .bot => .bottom
  | .and left right => .and (encodeTerm left) (encodeTerm right)
  | .or left right => .or (encodeTerm left) (encodeTerm right)
  | .imp antecedent consequent =>
      .imp (encodeTerm antecedent) (encodeTerm consequent)
  | .not body => .not (encodeTerm body)
  | @Term.eq _ _ _ comparedType left right =>
      .equal (TypePacket.encode comparedType)
        (encodeTerm left) (encodeTerm right)
  | @Term.all _ _ domain _ body =>
      .forallE (TypePacket.encode domain) (encodeTerm body)
  | @Term.ex _ _ domain _ body =>
      .existsE (TypePacket.encode domain) (encodeTerm body)

@[simp] theorem decodeTerm?_encodeTerm
    {context : Ctx String} {type : Ty String}
    (term : Term Constant context type) :
    decodeTerm? context (encodeTerm term) type = some term := by
  induction term with
  | var var =>
      simp [encodeTerm, decodeTerm?, decodeVar?_encodeVar]
  | const constant => simp [encodeTerm, decodeTerm?]
  | app function argument functionIH argumentIH =>
      simp [encodeTerm, decodeTerm?, functionIH, argumentIH]
  | lam body bodyIH =>
      simp [encodeTerm, decodeTerm?, bodyIH]
  | top => simp [encodeTerm, decodeTerm?]
  | bot => simp [encodeTerm, decodeTerm?]
  | and left right leftIH rightIH =>
      simp [encodeTerm, decodeTerm?, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [encodeTerm, decodeTerm?, leftIH, rightIH]
  | imp antecedent consequent antecedentIH consequentIH =>
      simp [encodeTerm, decodeTerm?, antecedentIH, consequentIH]
  | not body bodyIH => simp [encodeTerm, decodeTerm?, bodyIH]
  | eq left right leftIH rightIH =>
      simp [encodeTerm, decodeTerm?, leftIH, rightIH]
  | all body bodyIH =>
      simp [encodeTerm, decodeTerm?, bodyIH]
  | ex body bodyIH =>
      simp [encodeTerm, decodeTerm?, bodyIH]

theorem encodeTerm_injective {context : Ctx String} {type : Ty String} :
    Function.Injective (encodeTerm : Term Constant context type → TermPacket) := by
  intro first second equal
  have decoded := congrArg (fun packet => decodeTerm? context packet type) equal
  simpa using decoded

/-- The TH0 substitution algebra is inherited from the intrinsic HOL core,
not redefined by the interchange representation. -/
theorem th0_substitution_identity {context : Ctx String}
    {type : Ty String} (term : Term Constant context type) :
    subst (Subst.id (Base := String) (Const := Constant)
      (Γ := context)) term = term :=
  subst_id (Base := String) (Const := Constant) term

theorem th0_substitution_composition
    {source middle target : Ctx String} {type : Ty String}
    (first : Subst Constant source middle)
    (second : Subst Constant middle target)
    (term : Term Constant source type) :
    subst second (subst first term) =
      subst (Subst.comp second first) term :=
  subst_comp (Base := String) (Const := Constant) second first term

/-- Intrinsic beta cannot invent a selected constant absent from both the
argument and body. -/
theorem th0_beta_no_invention
    {constantType argumentType resultType : Ty String}
    (constant : Constant constantType)
    (argument : Term Constant [] argumentType)
    (body : Term Constant [argumentType] resultType)
    (argumentFresh : NoConstOccurrence constant argument)
    (bodyFresh : NoConstOccurrence constant body) :
    NoConstOccurrence constant
      (instantiate (Base := String) argument body) :=
  noConstOccurrence_instantiate argumentFresh bodyFresh

/-! ## Canonical symbolic wire -/

def encodeTyWire : Ty String → WireTerm
  | .prop => .symbol "TH0Prop"
  | .base name => .list [.symbol "TH0Base", .symbol name]
  | .arr domain codomain =>
      .list [.symbol "TH0Arrow", encodeTyWire domain, encodeTyWire codomain]

def encodeTypeWire (packet : TypePacket) : WireTerm :=
  encodeTyWire packet.decode

def decodeTyWire : WireTerm → Option (Ty String)
  | .symbol "TH0Prop" => some .prop
  | .list [.symbol "TH0Base", .symbol name] => some (.base name)
  | .list [.symbol "TH0Arrow", domain, codomain] => do
      let decodedDomain ← decodeTyWire domain
      let decodedCodomain ← decodeTyWire codomain
      some (.arr decodedDomain decodedCodomain)
  | _ => none

def decodeTypeWire (wire : WireTerm) : Option TypePacket :=
  (decodeTyWire wire).map TypePacket.encode

@[simp] theorem decodeTyWire_encodeTyWire (type : Ty String) :
    decodeTyWire (encodeTyWire type) = some type := by
  induction type with
  | prop => rfl
  | base name => rfl
  | arr domain codomain domainIH codomainIH =>
      simp [encodeTyWire, decodeTyWire, domainIH, codomainIH]

@[simp] theorem decodeTypeWire_encodeTypeWire (packet : TypePacket) :
    decodeTypeWire (encodeTypeWire packet) = some packet := by
  simp [encodeTypeWire, decodeTypeWire]

def encodeTermWire : TermPacket → WireTerm
  | .bound index type =>
      .list [.symbol "TH0Bound", .natural index, encodeTypeWire type]
  | .constant name type =>
      .list [.symbol "TH0Const", .symbol name, encodeTypeWire type]
  | .app domain codomain function argument =>
      .list [.symbol "TH0App", encodeTypeWire domain,
        encodeTypeWire codomain, encodeTermWire function,
        encodeTermWire argument]
  | .lam domain codomain body =>
      .list [.symbol "TH0Lam", encodeTypeWire domain,
        encodeTypeWire codomain, encodeTermWire body]
  | .top => .symbol "TH0Top"
  | .bottom => .symbol "TH0Bottom"
  | .and left right =>
      .list [.symbol "TH0And", encodeTermWire left, encodeTermWire right]
  | .or left right =>
      .list [.symbol "TH0Or", encodeTermWire left, encodeTermWire right]
  | .imp antecedent consequent =>
      .list [.symbol "TH0Imp", encodeTermWire antecedent,
        encodeTermWire consequent]
  | .not body => .list [.symbol "TH0Not", encodeTermWire body]
  | .equal type left right =>
      .list [.symbol "TH0Equal", encodeTypeWire type,
        encodeTermWire left, encodeTermWire right]
  | .forallE domain body =>
      .list [.symbol "TH0Forall", encodeTypeWire domain,
        encodeTermWire body]
  | .existsE domain body =>
      .list [.symbol "TH0Exists", encodeTypeWire domain,
        encodeTermWire body]

def decodeTermWire : WireTerm → Option TermPacket
  | .list [.symbol "TH0Bound", .natural index, type] => do
      let decodedType ← decodeTypeWire type
      some (.bound index decodedType)
  | .list [.symbol "TH0Const", .symbol name, type] => do
      let decodedType ← decodeTypeWire type
      some (.constant name decodedType)
  | .list [.symbol "TH0App", domain, codomain, function, argument] => do
      let decodedDomain ← decodeTypeWire domain
      let decodedCodomain ← decodeTypeWire codomain
      let decodedFunction ← decodeTermWire function
      let decodedArgument ← decodeTermWire argument
      some (.app decodedDomain decodedCodomain decodedFunction decodedArgument)
  | .list [.symbol "TH0Lam", domain, codomain, body] => do
      let decodedDomain ← decodeTypeWire domain
      let decodedCodomain ← decodeTypeWire codomain
      let decodedBody ← decodeTermWire body
      some (.lam decodedDomain decodedCodomain decodedBody)
  | .symbol "TH0Top" => some .top
  | .symbol "TH0Bottom" => some .bottom
  | .list [.symbol "TH0And", left, right] => do
      let decodedLeft ← decodeTermWire left
      let decodedRight ← decodeTermWire right
      some (.and decodedLeft decodedRight)
  | .list [.symbol "TH0Or", left, right] => do
      let decodedLeft ← decodeTermWire left
      let decodedRight ← decodeTermWire right
      some (.or decodedLeft decodedRight)
  | .list [.symbol "TH0Imp", antecedent, consequent] => do
      let decodedAntecedent ← decodeTermWire antecedent
      let decodedConsequent ← decodeTermWire consequent
      some (.imp decodedAntecedent decodedConsequent)
  | .list [.symbol "TH0Not", body] => do
      let decodedBody ← decodeTermWire body
      some (.not decodedBody)
  | .list [.symbol "TH0Equal", type, left, right] => do
      let decodedType ← decodeTypeWire type
      let decodedLeft ← decodeTermWire left
      let decodedRight ← decodeTermWire right
      some (.equal decodedType decodedLeft decodedRight)
  | .list [.symbol "TH0Forall", domain, body] => do
      let decodedDomain ← decodeTypeWire domain
      let decodedBody ← decodeTermWire body
      some (.forallE decodedDomain decodedBody)
  | .list [.symbol "TH0Exists", domain, body] => do
      let decodedDomain ← decodeTypeWire domain
      let decodedBody ← decodeTermWire body
      some (.existsE decodedDomain decodedBody)
  | _ => none

@[simp] theorem decodeTermWire_encodeTermWire (packet : TermPacket) :
    decodeTermWire (encodeTermWire packet) = some packet := by
  induction packet with
  | bound index type => simp [encodeTermWire, decodeTermWire]
  | constant name type => simp [encodeTermWire, decodeTermWire]
  | app domain codomain function argument functionIH argumentIH =>
      simp [encodeTermWire, decodeTermWire, functionIH, argumentIH]
  | lam domain codomain body bodyIH =>
      simp [encodeTermWire, decodeTermWire, bodyIH]
  | top => rfl
  | bottom => rfl
  | and left right leftIH rightIH =>
      simp [encodeTermWire, decodeTermWire, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [encodeTermWire, decodeTermWire, leftIH, rightIH]
  | imp antecedent consequent antecedentIH consequentIH =>
      simp [encodeTermWire, decodeTermWire, antecedentIH, consequentIH]
  | not body bodyIH => simp [encodeTermWire, decodeTermWire, bodyIH]
  | equal type left right leftIH rightIH =>
      simp [encodeTermWire, decodeTermWire, leftIH, rightIH]
  | forallE domain body bodyIH =>
      simp [encodeTermWire, decodeTermWire, bodyIH]
  | existsE domain body bodyIH =>
      simp [encodeTermWire, decodeTermWire, bodyIH]

theorem encodeTermWire_injective : Function.Injective encodeTermWire := by
  intro first second equal
  have decoded := congrArg decodeTermWire equal
  simpa using decoded

def th0WireVersion : Nat := 1

def encodeVersionedTerm (packet : TermPacket) : WireTerm :=
  .list [.symbol "TH0Term", .natural th0WireVersion, encodeTermWire packet]

def decodeVersionedTerm : WireTerm → Option TermPacket
  | .list [.symbol "TH0Term", .natural version, payload] =>
      if version = th0WireVersion then decodeTermWire payload else none
  | _ => none

@[simp] theorem decodeVersionedTerm_encodeVersionedTerm (packet : TermPacket) :
    decodeVersionedTerm (encodeVersionedTerm packet) = some packet := by
  simp [decodeVersionedTerm, encodeVersionedTerm, th0WireVersion]

theorem encodeVersionedTerm_injective :
    Function.Injective encodeVersionedTerm := by
  intro first second equal
  have decoded := congrArg decodeVersionedTerm equal
  simpa using decoded

theorem decodeVersionedTerm_rejects_future_version (packet : TermPacket) :
    decodeVersionedTerm
      (.list [.symbol "TH0Term", .natural (th0WireVersion + 1),
        encodeTermWire packet]) = none := by
  simp [decodeVersionedTerm, th0WireVersion]

/-! ## Logic-indexed elaboration outcomes -/

/-- Profiles admitted by the syntax layer but intentionally outside TH0. -/
inductive HigherProfile where
  | th1
  | dependentHigherOrder
  | nonclassicalHigherOrder
  | implementationDefined (name : String)
deriving Repr, DecidableEq

/-- One monomorphic constant declaration in a TH0 document. -/
structure ConstantDeclaration where
  name : String
  type : TypePacket
deriving Repr, DecidableEq

abbrev SignaturePacket := List ConstantDeclaration

/-- The occurrence-bearing declaration list reads out to a monomorphic
signature exactly when equal names carry equal types.  Exact duplicate
occurrences are retained and accepted; conflicting type assignments are not. -/
def signatureFunctional (signature : SignaturePacket) : Bool :=
  signature.all fun first =>
    signature.all fun second =>
      if first.name == second.name then first.type == second.type else true

/-- Every constant occurrence in a term must be present with its exact type.
This is separate from scope/type decoding so each failure boundary can later
receive its own source-located diagnostic. -/
def constantsDeclared (signature : SignaturePacket) : TermPacket → Bool
  | .bound _ _ => true
  | .constant name type => signature.contains ⟨name, type⟩
  | .app _ _ function argument =>
      constantsDeclared signature function &&
        constantsDeclared signature argument
  | .lam _ _ body => constantsDeclared signature body
  | .top => true
  | .bottom => true
  | .and left right =>
      constantsDeclared signature left && constantsDeclared signature right
  | .or left right =>
      constantsDeclared signature left && constantsDeclared signature right
  | .imp antecedent consequent =>
      constantsDeclared signature antecedent &&
        constantsDeclared signature consequent
  | .not body => constantsDeclared signature body
  | .equal _ left right =>
      constantsDeclared signature left && constantsDeclared signature right
  | .forallE _ body => constantsDeclared signature body
  | .existsE _ body => constantsDeclared signature body

/-- The portable unit consumed by a TH0-aware algorithm. -/
structure FormulaPacket where
  signature : SignaturePacket
  term : TermPacket
deriving Repr, DecidableEq

def encodeConstantDeclaration (declaration : ConstantDeclaration) : WireTerm :=
  .list [.symbol "TH0Declaration", .symbol declaration.name,
    encodeTypeWire declaration.type]

def decodeConstantDeclaration : WireTerm → Option ConstantDeclaration
  | .list [.symbol "TH0Declaration", .symbol name, type] => do
      let decodedType ← decodeTypeWire type
      some ⟨name, decodedType⟩
  | _ => none

def decodeDeclarationList : List WireTerm → Option SignaturePacket
  | [] => some []
  | declaration :: declarations => do
      let decodedDeclaration ← decodeConstantDeclaration declaration
      let decodedDeclarations ← decodeDeclarationList declarations
      some (decodedDeclaration :: decodedDeclarations)

@[simp] theorem decodeConstantDeclaration_encodeConstantDeclaration
    (declaration : ConstantDeclaration) :
    decodeConstantDeclaration (encodeConstantDeclaration declaration) =
      some declaration := by
  cases declaration
  simp [encodeConstantDeclaration, decodeConstantDeclaration]

@[simp] theorem decodeDeclarationList_map_encode
    (signature : SignaturePacket) :
    decodeDeclarationList (signature.map encodeConstantDeclaration) =
      some signature := by
  induction signature with
  | nil => rfl
  | cons declaration signature inductionHypothesis =>
      simp [decodeDeclarationList, inductionHypothesis]

/-- Versioned document-level packet: signature occurrences and term share one
canonical artifact. -/
def encodeFormulaPacket (packet : FormulaPacket) : WireTerm :=
  .list [.symbol "TH0Formula", .natural th0WireVersion,
    .list (packet.signature.map encodeConstantDeclaration),
    encodeTermWire packet.term]

def decodeFormulaPacket : WireTerm → Option FormulaPacket
  | .list [.symbol "TH0Formula", .natural version,
      .list declarations, term] => do
      if version != th0WireVersion then none
      let decodedDeclarations ← decodeDeclarationList declarations
      let decodedTerm ← decodeTermWire term
      some ⟨decodedDeclarations, decodedTerm⟩
  | _ => none

@[simp] theorem decodeFormulaPacket_encodeFormulaPacket
    (packet : FormulaPacket) :
    decodeFormulaPacket (encodeFormulaPacket packet) = some packet := by
  cases packet
  simp [encodeFormulaPacket, decodeFormulaPacket, th0WireVersion]

theorem encodeFormulaPacket_injective :
    Function.Injective encodeFormulaPacket := by
  intro first second equal
  have decoded := congrArg decodeFormulaPacket equal
  simpa using decoded

/-- Declaration-aware closed-formula decoding. -/
def decodeFormula? (packet : FormulaPacket) :
    Option (ClosedFormula Constant) :=
  if signatureFunctional packet.signature &&
      constantsDeclared packet.signature packet.term then
    decodeTerm? [] packet.term .prop
  else
    none

/-- A syntax-classified formula at the semantic boundary.  The higher-profile
case retains the original symbolic payload rather than coercing it into TH0. -/
inductive ClassifiedFormula where
  | th0 (packet : FormulaPacket)
  | higher (profile : HigherProfile) (preserved : WireTerm)
deriving Repr

/-- Positive evidence is possible only for a packet that decodes to a closed
proposition in the intrinsic HOL core. -/
inductive ElaborationEvidence : ClassifiedFormula → Type where
  | checked (packet : FormulaPacket) (formula : ClosedFormula Constant)
      (replay : decodeFormula? packet = some formula) :
      ElaborationEvidence (.th0 packet)

/-- Rejection is a checked TH0 scope/type failure.  Unsupported profiles have
no rejection constructor: they are residuals, not false formulas. -/
inductive ElaborationRejection : ClassifiedFormula → Type where
  | malformed (packet : FormulaPacket)
      (replay : decodeFormula? packet = none) :
      ElaborationRejection (.th0 packet)

def elaborationAuthority : Authority ClassifiedFormula where
  Holds formula := Nonempty (ElaborationEvidence formula)
  Evidence := ElaborationEvidence
  Obstruction := ElaborationRejection
  evidenceSound := by
    intro formula evidence
    exact ⟨evidence⟩
  obstructionSound := by
    intro formula obstruction evidence
    rcases evidence with ⟨evidence⟩
    cases obstruction with
    | malformed packet failed =>
        cases evidence with
        | checked _ formula checked =>
            rw [failed] at checked
            cases checked

/-- A preserved unsupported item, including its logic profile and payload. -/
structure Residual where
  profile : HigherProfile
  preserved : WireTerm
deriving Repr

structure IncompleteReceipt where
  stage : String
  inspectedUnits : Nat
deriving Repr, DecidableEq

structure FrontendFault where
  boundary : String
  detail : String
deriving Repr, DecidableEq

abbrev ElaborationOutcome (formula : ClassifiedFormula) :=
  Outcome (ElaborationEvidence formula) (ElaborationRejection formula)
    Residual IncompleteReceipt

/-- The TH0 branch isolated from the profile classifier. -/
def elaborateTH0 (packet : FormulaPacket) :
    ElaborationOutcome (.th0 packet) :=
  match replay : decodeFormula? packet with
  | some formula => .established (.checked packet formula replay)
  | none => .refuted (.malformed packet replay)

/-- Pure elaboration: checked TH0, checked rejection, or preserved residual.
Resource interruption and operational faults wrap this function separately. -/
def elaborate : (formula : ClassifiedFormula) → ElaborationOutcome formula
  | .th0 packet => elaborateTH0 packet
  | .higher profile preserved =>
      .outsideFragment ⟨profile, preserved⟩

theorem elaborate_checked_asBool {packet : FormulaPacket}
    {formula : ClosedFormula Constant}
    (replay : decodeFormula? packet = some formula) :
    (elaborate (.th0 packet)).asBool = some true := by
  change (elaborateTH0 packet).asBool = some true
  unfold elaborateTH0
  split
  · rfl
  · simp_all

theorem elaborate_rejected_asBool {packet : FormulaPacket}
    (replay : decodeFormula? packet = none) :
    (elaborate (.th0 packet)).asBool = some false := by
  change (elaborateTH0 packet).asBool = some false
  unfold elaborateTH0
  split
  · simp_all
  · rfl

def elaborateRun (formula : ClassifiedFormula) :
    RunResult FrontendFault (ElaborationOutcome formula) :=
  .ok (elaborate formula)

def interruptedRun (formula : ClassifiedFormula) (receipt : IncompleteReceipt) :
    RunResult FrontendFault (ElaborationOutcome formula) :=
  .ok (.incomplete receipt)

def faultedRun (formula : ClassifiedFormula) (fault : FrontendFault) :
    RunResult FrontendFault (ElaborationOutcome formula) :=
  .fault fault

theorem higher_profile_is_residual (profile : HigherProfile)
    (preserved : WireTerm) :
    elaborate (.higher profile preserved) =
      .outsideFragment (⟨profile, preserved⟩ : Residual) :=
  rfl

theorem higher_profile_has_no_th0_evidence (profile : HigherProfile)
    (preserved : WireTerm) :
    ¬ Nonempty (ElaborationEvidence (.higher profile preserved)) := by
  intro evidence
  rcases evidence with ⟨evidence⟩
  cases evidence

theorem incomplete_is_not_fault (formula : ClassifiedFormula)
    (receipt : IncompleteReceipt) (fault : FrontendFault) :
    interruptedRun formula receipt ≠ faultedRun formula fault := by
  intro equal
  cases equal

/-! ## One independently replayable TH0-aware operation: beta -/

/-- Compute the exact intrinsic beta result, then re-encode it canonically. -/
def betaResult? (context : Ctx String) (domain codomain : Ty String)
    (argument body : TermPacket) : Option TermPacket := do
  let decodedArgument ← decodeTerm? context argument domain
  let decodedBody ← decodeTerm? (domain :: context) body codomain
  some (encodeTerm (instantiate (Base := String) decodedArgument decodedBody))

theorem betaResult?_sound
    {context : Ctx String} {domain codomain : Ty String}
    {argument body result : TermPacket}
    (checked : betaResult? context domain codomain argument body = some result) :
    ∃ (decodedArgument : Term Constant context domain)
        (decodedBody : Term Constant (domain :: context) codomain),
      decodeTerm? context argument domain = some decodedArgument ∧
      decodeTerm? (domain :: context) body codomain = some decodedBody ∧
      result = encodeTerm
        (instantiate (Base := String) decodedArgument decodedBody) := by
  cases argumentEquation : decodeTerm? context argument domain with
  | none =>
      simp [betaResult?, argumentEquation] at checked
  | some decodedArgument =>
      cases bodyEquation :
          decodeTerm? (domain :: context) body codomain with
      | none =>
          simp [betaResult?, argumentEquation, bodyEquation] at checked
      | some decodedBody =>
          simp [betaResult?, argumentEquation, bodyEquation] at checked
          cases checked
          exact ⟨decodedArgument, decodedBody, rfl, rfl, rfl⟩

/-- Every emitted beta packet re-enters the same typed decoder as the exact
intrinsic instantiation. -/
theorem betaResult?_readmits
    {context : Ctx String} {domain codomain : Ty String}
    {argument body result : TermPacket}
    (checked : betaResult? context domain codomain argument body = some result) :
    ∃ (decodedArgument : Term Constant context domain)
        (decodedBody : Term Constant (domain :: context) codomain),
      decodeTerm? context argument domain = some decodedArgument ∧
      decodeTerm? (domain :: context) body codomain = some decodedBody ∧
      decodeTerm? context result codomain =
        some (instantiate (Base := String) decodedArgument decodedBody) := by
  obtain ⟨decodedArgument, decodedBody, argumentReplay, bodyReplay,
      resultReplay⟩ := betaResult?_sound checked
  refine ⟨decodedArgument, decodedBody, argumentReplay, bodyReplay, ?_⟩
  rw [resultReplay]
  exact decodeTerm?_encodeTerm _

/-- Portable beta claim checked independently of candidate generation. -/
structure BetaClaim where
  context : Ctx String
  domain : TypePacket
  codomain : TypePacket
  argument : TermPacket
  body : TermPacket
  result : TermPacket
deriving Repr

structure BetaEvidence (claim : BetaClaim) where
  replay : betaResult? claim.context claim.domain.decode claim.codomain.decode
    claim.argument claim.body = some claim.result

structure BetaObstruction (claim : BetaClaim) where
  replay : betaResult? claim.context claim.domain.decode claim.codomain.decode
    claim.argument claim.body ≠ some claim.result

def betaAuthority : Authority BetaClaim where
  Holds claim :=
    betaResult? claim.context claim.domain.decode claim.codomain.decode
      claim.argument claim.body = some claim.result
  Evidence := BetaEvidence
  Obstruction := BetaObstruction
  evidenceSound := by
    intro claim evidence
    exact evidence.replay
  obstructionSound := by
    intro claim obstruction evidence
    exact obstruction.replay evidence

def checkBeta (claim : BetaClaim) :
    Outcome (BetaEvidence claim) (BetaObstruction claim) Unit Unit :=
  if checked : betaResult? claim.context claim.domain.decode
      claim.codomain.decode claim.argument claim.body = some claim.result then
    .established ⟨checked⟩
  else
    .refuted ⟨checked⟩

/-! ## Requirement refinement: substitution is not superposition -/

/-- Named obligations in a higher-order algorithm profile.  This is a
dependency ledger, not a claim that possessing the names proves completeness. -/
inductive HORequirement where
  | scopedTyping
  | captureAvoidingSubstitution
  | betaReduction
  | betaEtaEquivalence
  | higherOrderUnification
  | extensionality
  | higherOrderClausification
  | orderingAndEligibility
  | proofProducingReplay
  | fairResourceAwareSearch
deriving Repr, DecidableEq

def substitutionKernelRequirements : Finset HORequirement :=
  { .scopedTyping, .captureAvoidingSubstitution, .betaReduction }

def lambdaSuperpositionRequirements : Finset HORequirement :=
  { .scopedTyping, .captureAvoidingSubstitution, .betaReduction,
    .betaEtaEquivalence, .higherOrderUnification, .extensionality,
    .higherOrderClausification, .orderingAndEligibility,
    .proofProducingReplay, .fairResourceAwareSearch }

theorem substitution_requirements_strictly_below_superposition :
    substitutionKernelRequirements ⊂ lambdaSuperpositionRequirements := by
  decide

theorem substitution_does_not_discharge_unification :
    .higherOrderUnification ∉ substitutionKernelRequirements := by
  decide

theorem superposition_requires_unification :
    .higherOrderUnification ∈ lambdaSuperpositionRequirements := by
  decide

/-! ## Dialect adapters are meaning-preserving bindings -/

inductive MeTTaDialect where
  | he
  | petta
  | prime
deriving Repr, DecidableEq

/-- A dialect adapter may choose any representation internally, but its public
TH0 formula result must agree exactly with the intrinsic decoder. -/
structure FormulaAdapter where
  decode : FormulaPacket → Option (ClosedFormula Constant)
  agrees : ∀ packet, decode packet = decodeFormula? packet

namespace FormulaAdapter

theorem extensionalAgreement (first second : FormulaAdapter)
    (packet : FormulaPacket) : first.decode packet = second.decode packet := by
  rw [first.agrees, second.agrees]

end FormulaAdapter

/-- The mathematical reference adapter; native dialect adapters must refine
this behavior rather than define a new TH0 meaning. -/
def referenceAdapter : FormulaAdapter where
  decode packet := decodeFormula? packet
  agrees _ := rfl

def uniformDialectAdapters : MeTTaDialect → FormulaAdapter :=
  fun _ => referenceAdapter

theorem uniform_dialects_share_th0_meaning
    (first second : MeTTaDialect) (packet : FormulaPacket) :
    (uniformDialectAdapters first).decode packet =
      (uniformDialectAdapters second).decode packet :=
  rfl

/-! ## Concrete positive and negative canaries -/

namespace Canary

def individualType : Ty String := .base "individual"
def individualPacket : TypePacket := .base "individual"

def predicateConstant : Constant (.arr individualType .prop) := ⟨"P"⟩

def predicateAtBound : Term Constant [individualType] .prop :=
  .app (.const predicateConstant) (.var .vz)

/-- Intrinsic meaning of `forall x. P x -> P x`. -/
def identityFormula : ClosedFormula Constant :=
  .all (.imp predicateAtBound predicateAtBound)

def identityPacket : TermPacket :=
  .forallE individualPacket
    (.imp
      (.app individualPacket .prop
        (.constant "P" (.arrow individualPacket .prop))
        (.bound 0 individualPacket))
      (.app individualPacket .prop
        (.constant "P" (.arrow individualPacket .prop))
        (.bound 0 individualPacket)))

def predicateDeclaration : ConstantDeclaration :=
  ⟨"P", .arrow individualPacket .prop⟩

def identityDocument : FormulaPacket :=
  ⟨[predicateDeclaration], identityPacket⟩

theorem identity_packet_decodes :
    decodeTerm? [] identityPacket .prop = some identityFormula := by
  rw [show identityPacket = encodeTerm identityFormula by rfl]
  exact decodeTerm?_encodeTerm identityFormula

theorem identity_document_decodes :
    decodeFormula? identityDocument = some identityFormula := by
  have functional : signatureFunctional [predicateDeclaration] = true := by
    simp [signatureFunctional, predicateDeclaration]
  have declared :
      constantsDeclared [predicateDeclaration] identityPacket = true := by
    simp [constantsDeclared, identityPacket, predicateDeclaration,
      individualPacket, TypePacket.base, TypePacket.prop, TypePacket.arrow]
  simp [decodeFormula?, identityDocument, functional, declared,
    identity_packet_decodes]

theorem identity_packet_elaborates :
    (elaborate (.th0 identityDocument)).asBool = some true := by
  exact elaborate_checked_asBool identity_document_decodes

/-- A closed term cannot refer to bound index zero. -/
def outOfScopePacket : TermPacket := .bound 0 .prop

def outOfScopeDocument : FormulaPacket := ⟨[], outOfScopePacket⟩

theorem out_of_scope_rejects :
    decodeTerm? [] outOfScopePacket .prop = none := by
  simp [outOfScopePacket, decodeTerm?, decodeVar?]

theorem out_of_scope_document_rejects :
    decodeFormula? outOfScopeDocument = none := by
  simp [decodeFormula?, outOfScopeDocument, signatureFunctional,
    out_of_scope_rejects]

theorem out_of_scope_elaboration_refutes :
    (elaborate (.th0 outOfScopeDocument)).asBool = some false := by
  exact elaborate_rejected_asBool out_of_scope_document_rejects

/-- `P` expects an individual, not a proposition. -/
def wrongArgumentTypePacket : TermPacket :=
  .app individualPacket .prop
    (.constant "P" (.arrow individualPacket .prop)) .top

theorem wrong_argument_type_rejects :
    decodeTerm? [] wrongArgumentTypePacket .prop = none := by
  simp [wrongArgumentTypePacket, individualPacket, decodeTerm?,
    TypePacket.base, TypePacket.prop, TypePacket.arrow]

/-- A typed occurrence is rejected if its declaration is absent. -/
def undeclaredIdentityDocument : FormulaPacket :=
  ⟨[], identityPacket⟩

theorem undeclared_constant_rejects :
    decodeFormula? undeclaredIdentityDocument = none := by
  simp [decodeFormula?, undeclaredIdentityDocument, signatureFunctional,
    constantsDeclared, identityPacket]

/-- Exact duplicate declarations remain distinct source occurrences but do not
change the extensional signature meaning. -/
def duplicateDeclarationDocument : FormulaPacket :=
  ⟨[predicateDeclaration, predicateDeclaration], identityPacket⟩

theorem duplicate_declaration_preserves_meaning :
    decodeFormula? duplicateDeclarationDocument = some identityFormula := by
  have functional :
      signatureFunctional [predicateDeclaration, predicateDeclaration] =
        true := by
    simp [signatureFunctional, predicateDeclaration]
  have declared :
      constantsDeclared [predicateDeclaration, predicateDeclaration]
        identityPacket = true := by
    simp [constantsDeclared, identityPacket, predicateDeclaration,
      individualPacket, TypePacket.base, TypePacket.prop, TypePacket.arrow]
  simp [decodeFormula?, duplicateDeclarationDocument, functional, declared,
    identity_packet_decodes]

/-- The same name at two distinct monomorphic types is not a TH0 signature. -/
def conflictingDeclarationDocument : FormulaPacket :=
  ⟨[predicateDeclaration, ⟨"P", .prop⟩], identityPacket⟩

theorem conflicting_declaration_rejects :
    decodeFormula? conflictingDeclarationDocument = none := by
  simp [decodeFormula?, conflictingDeclarationDocument,
    predicateDeclaration, signatureFunctional, individualPacket,
    TypePacket.base, TypePacket.prop, TypePacket.arrow]

def retainedTH1Payload : WireTerm :=
  .list [.symbol "thf", .symbol "rank_one_polymorphic_payload"]

theorem th1_is_preserved_residual :
    elaborate (.higher .th1 retainedTH1Payload) =
      .outsideFragment
        (⟨.th1, retainedTH1Payload⟩ : Residual) :=
  rfl

theorem th1_is_not_semantically_refuted :
    (elaborate (.higher .th1 retainedTH1Payload)).asBool = none :=
  rfl

/-! Capture-avoidance canary: in `(fun x => fun y => x) z`, substituting `z`
under the inner binder must produce `fun y => z`, not `fun y => y`. -/

def freeArgument : Term Constant [individualType] individualType :=
  .var .vz

def betaBody : Term Constant
    (individualType :: [individualType])
    (.arr individualType individualType) :=
  .lam (.var (.vs .vz))

def captureAvoidingResult : Term Constant [individualType]
    (.arr individualType individualType) :=
  .lam (.var (.vs .vz))

def capturedWrongResult : Term Constant [individualType]
    (.arr individualType individualType) :=
  .lam (.var .vz)

theorem intrinsic_beta_avoids_capture :
    instantiate (Base := String) freeArgument betaBody =
      captureAvoidingResult := by
  rfl

theorem captured_result_is_distinct :
    encodeTerm captureAvoidingResult ≠ encodeTerm capturedWrongResult := by
  decide

def honestBetaClaim : BetaClaim where
  context := [individualType]
  domain := individualPacket
  codomain := .arrow individualPacket individualPacket
  argument := encodeTerm freeArgument
  body := encodeTerm betaBody
  result := encodeTerm captureAvoidingResult

def capturedBetaClaim : BetaClaim where
  context := [individualType]
  domain := individualPacket
  codomain := .arrow individualPacket individualPacket
  argument := encodeTerm freeArgument
  body := encodeTerm betaBody
  result := encodeTerm capturedWrongResult

theorem honest_beta_claim_established :
    (checkBeta honestBetaClaim).asBool = some true := by
  have replay :
      betaResult? [individualType] individualPacket.decode
          (TypePacket.arrow individualPacket individualPacket).decode
          (encodeTerm freeArgument) (encodeTerm betaBody) =
        some (encodeTerm captureAvoidingResult) := by
    change betaResult? [individualType] individualType
        (.arr individualType individualType)
        (encodeTerm freeArgument) (encodeTerm betaBody) =
      some (encodeTerm captureAvoidingResult)
    simp [betaResult?, intrinsic_beta_avoids_capture]
  simp [checkBeta, honestBetaClaim, replay, Outcome.asBool]

theorem captured_beta_claim_refuted :
    (checkBeta capturedBetaClaim).asBool = some false := by
  have replay :
      betaResult? [individualType] individualPacket.decode
          (TypePacket.arrow individualPacket individualPacket).decode
          (encodeTerm freeArgument) (encodeTerm betaBody) =
        some (encodeTerm captureAvoidingResult) := by
    change betaResult? [individualType] individualType
        (.arr individualType individualType)
        (encodeTerm freeArgument) (encodeTerm betaBody) =
      some (encodeTerm captureAvoidingResult)
    simp [betaResult?, intrinsic_beta_avoids_capture]
  have rejected :
      betaResult? [individualType] individualPacket.decode
          (TypePacket.arrow individualPacket individualPacket).decode
          (encodeTerm freeArgument) (encodeTerm betaBody) ≠
        some (encodeTerm capturedWrongResult) := by
    rw [replay]
    exact fun equal => captured_result_is_distinct (Option.some.inj equal)
  simp [checkBeta, capturedBetaClaim, rejected, Outcome.asBool]

theorem substitution_and_superposition_boundary :
    decodeTerm? [] identityPacket .prop = some identityFormula ∧
    decodeTerm? [] outOfScopePacket .prop = none ∧
    decodeFormula? undeclaredIdentityDocument = none ∧
    decodeFormula? duplicateDeclarationDocument = some identityFormula ∧
    decodeFormula? conflictingDeclarationDocument = none ∧
    (checkBeta honestBetaClaim).asBool = some true ∧
    (checkBeta capturedBetaClaim).asBool = some false ∧
    substitutionKernelRequirements ⊂ lambdaSuperpositionRequirements := by
  exact ⟨identity_packet_decodes, out_of_scope_rejects,
    undeclared_constant_rejects, duplicate_declaration_preserves_meaning,
    conflicting_declaration_rejects,
    honest_beta_claim_established, captured_beta_claim_refuted,
    substitution_requirements_strictly_below_superposition⟩

end Canary

/-! ## Audit crowns -/

#print axioms TypePacket.decode_encode
#print axioms decodeTerm?_encodeTerm
#print axioms th0_substitution_identity
#print axioms th0_substitution_composition
#print axioms th0_beta_no_invention
#print axioms decodeTermWire_encodeTermWire
#print axioms decodeFormulaPacket_encodeFormulaPacket
#print axioms betaResult?_sound
#print axioms betaResult?_readmits
#print axioms higher_profile_has_no_th0_evidence
#print axioms substitution_requirements_strictly_below_superposition
#print axioms Canary.substitution_and_superposition_boundary

end Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary
