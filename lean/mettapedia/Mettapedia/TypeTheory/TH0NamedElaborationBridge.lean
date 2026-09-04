import Mettapedia.Logic.HOL.Syntax.NamedElaboration
import Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary

/-!
# Named higher-order elaboration into the TH0 interchange boundary

The generic HOL elaborator resolves named binders and constants into intrinsic,
typed de Bruijn syntax.  The TH0 interchange boundary carries that syntax in a
serializable, declaration-bearing packet.  This module proves that the two
layers compose without turning either TPTP syntax or a MeTTa dialect into the
meaning of higher-order logic.

The source signature remains an occurrence-bearing list.  Exact duplicate
declarations survive compilation.  Conflicting declarations are rejected
before the list is read as a functional semantic signature.  Successful
compilation is then replayed by the independent TH0 decoder, and alpha-related
named formulas compile to the same packet while capture-shaped renamings do
not.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.TH0NamedElaborationBridge

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary

/-! ## From an occurrence list to a semantic lookup -/

/-- Select the first declaration with a given name.  This operation acquires
semantic force only after `signatureFunctional` has accepted the whole
occurrence list. -/
def lookupDeclaration? : SignaturePacket -> String ->
    Option (SomeConst Constant)
  | [], _ => none
  | declaration :: declarations, name =>
      if declaration.name = name then
        some ⟨declaration.type.decode, ⟨declaration.name⟩⟩
      else
        lookupDeclaration? declarations name

/-- Functional view consumed by generic named elaboration. -/
def namedSignature (signature : SignaturePacket) :
    Signature String Constant :=
  lookupDeclaration? signature

@[simp] theorem lookupDeclaration?_head
    (declaration : ConstantDeclaration) (declarations : SignaturePacket) :
    lookupDeclaration? (declaration :: declarations) declaration.name =
      some ⟨declaration.type.decode, ⟨declaration.name⟩⟩ := by
  simp [lookupDeclaration?]

@[simp] theorem lookupDeclaration?_miss
    (declaration : ConstantDeclaration) (declarations : SignaturePacket)
    (name : String) (different : declaration.name ≠ name) :
    lookupDeclaration? (declaration :: declarations) name =
      lookupDeclaration? declarations name := by
  simp [lookupDeclaration?, different]

/-! ## Exact compilation outcome -/

abbrev NamedTH0Term := NamedTerm String String String

/-- Failure boundaries are deliberately distinct.  In particular, rejecting a
malformed TH0 source is not a semantic refutation of its proposition. -/
inductive CompilationError where
  | conflictingSignature
  | source (error : Error String String String)
  | declarationReplayFailed
deriving Repr, DecidableEq

/-- Compile a named formula to the portable TH0 packet.  The generated packet
retains the authored declaration occurrences exactly. -/
def compileFormula (signature : SignaturePacket) (source : NamedTH0Term) :
    Except CompilationError FormulaPacket :=
  if _functional : signatureFunctional signature = true then
    match check (namedSignature signature)
        (BinderNames.nil : BinderNames String String []) source .prop with
    | .error error => .error (.source error)
    | .ok formula =>
        let packet : FormulaPacket := ⟨signature, encodeTerm formula⟩
        if _declared : constantsDeclared signature packet.term = true then
          .ok packet
        else
          .error .declarationReplayFailed
  else
    .error .conflictingSignature

/-- A successful named compilation has one intrinsic closed formula, preserves
the source declaration list exactly, and is admitted by the independent TH0
decoder as that same formula. -/
theorem compileFormula_sound
    {signature : SignaturePacket} {source : NamedTH0Term}
    {packet : FormulaPacket}
    (compiled : compileFormula signature source = .ok packet) :
    ∃ formula : ClosedFormula Constant,
      check (namedSignature signature)
          (BinderNames.nil : BinderNames String String []) source .prop =
        .ok formula ∧
      packet = ⟨signature, encodeTerm formula⟩ ∧
      decodeFormula? packet = some formula := by
  unfold compileFormula at compiled
  split at compiled
  next functional =>
    split at compiled
    next error errorReplay =>
      simp at compiled
    next formula checked =>
      dsimp only at compiled
      split at compiled
      next declared =>
        cases compiled
        refine ⟨formula, checked, rfl, ?_⟩
        simp [decodeFormula?, functional, declared]
      next notDeclared =>
        simp at compiled
  next notFunctional =>
    simp at compiled

/-- Alpha-related named formulas have identical compilation behavior, including
identical typed failures. -/
theorem compileFormula_eq_of_alpha
    {signature : SignaturePacket} {left right : NamedTH0Term}
    (related : Alpha
      (BinderNames.nil : BinderNames String String [])
      (BinderNames.nil : BinderNames String String []) left right) :
    compileFormula signature left = compileFormula signature right := by
  unfold compileFormula
  split
  · rw [check_eq_of_alpha (namedSignature signature) related .prop]
  · rfl

/-- Successful compilation cannot alter, deduplicate, or reorder declaration
occurrences. -/
theorem compileFormula_preserves_signature
    {signature : SignaturePacket} {source : NamedTH0Term}
    {packet : FormulaPacket}
    (compiled : compileFormula signature source = .ok packet) :
    packet.signature = signature := by
  obtain ⟨formula, _checked, packetReplay, _admitted⟩ :=
    compileFormula_sound compiled
  rw [packetReplay]

/-- Any representation-specific adapter that has discharged the existing TH0
agreement contract reads a successfully compiled packet as the same intrinsic
formula.  Thus HE, PeTTa, Prime, and a generated-C implementation may use
different storage and execution strategies without acquiring distinct HOL
meanings. -/
theorem compileFormula_adapter_readmits
    (adapter : FormulaAdapter)
    {signature : SignaturePacket} {source : NamedTH0Term}
    {packet : FormulaPacket}
    (compiled : compileFormula signature source = .ok packet) :
    ∃ formula : ClosedFormula Constant,
      adapter.decode packet = some formula := by
  obtain ⟨formula, _checked, _packetReplay, admitted⟩ :=
    compileFormula_sound compiled
  exact ⟨formula, adapter.agrees packet |>.trans admitted⟩

/-- Two independently implemented conforming adapters cannot disagree on the
meaning of a successfully compiled packet. -/
theorem compileFormula_adapter_agreement
    (first second : FormulaAdapter)
    {signature : SignaturePacket} {source : NamedTH0Term}
    {packet : FormulaPacket}
    (compiled : compileFormula signature source = .ok packet) :
    ∃ formula : ClosedFormula Constant,
      first.decode packet = some formula ∧
      second.decode packet = some formula := by
  obtain ⟨formula, admitted⟩ :=
    compileFormula_adapter_readmits first compiled
  refine ⟨formula, admitted, ?_⟩
  have reference : decodeFormula? packet = some formula := by
    rw [← first.agrees]
    exact admitted
  rw [second.agrees]
  exact reference

/-! ## Positive and negative controls -/

namespace Canary

def individual : Ty String := .base "individual"
def individualPacket : TypePacket := .base "individual"

def predicateDeclaration : ConstantDeclaration :=
  ⟨"P", .arrow individualPacket .prop⟩

def predicateSignature : SignaturePacket := [predicateDeclaration]

def namedIdentityX : NamedTH0Term :=
  .forallE "x" individual
    (.imp
      (.app (.constant "P") (.variable "x"))
      (.app (.constant "P") (.variable "x")))

def namedIdentityY : NamedTH0Term :=
  .forallE "y" individual
    (.imp
      (.app (.constant "P") (.variable "y"))
      (.app (.constant "P") (.variable "y")))

def namedIdentityAlpha : Alpha
    (BinderNames.nil : BinderNames String String [])
    (BinderNames.nil : BinderNames String String [])
    namedIdentityX namedIdentityY := by
  apply Alpha.forallE
  apply Alpha.imp
  · apply Alpha.app
    · exact Alpha.constant "P"
    · apply Alpha.var (type := individual) (intrinsicVar := Var.vz)
      · rfl
      · rfl
  · apply Alpha.app
    · exact Alpha.constant "P"
    · apply Alpha.var (type := individual) (intrinsicVar := Var.vz)
      · rfl
      · rfl

def intrinsicPredicate : Constant (.arr individual .prop) := ⟨"P"⟩

def intrinsicPredicateAtBound : Term Constant [individual] .prop :=
  .app (.const intrinsicPredicate) (.var .vz)

def intrinsicIdentity : ClosedFormula Constant :=
  .all (.imp intrinsicPredicateAtBound intrinsicPredicateAtBound)

def identityPacket : FormulaPacket :=
  ⟨predicateSignature, encodeTerm intrinsicIdentity⟩

theorem predicate_signature_is_functional :
    signatureFunctional predicateSignature = true := by
  rfl

theorem named_identity_checks :
    check (namedSignature predicateSignature)
        (BinderNames.nil : BinderNames String String []) namedIdentityX .prop =
      .ok intrinsicIdentity := by
  simp [predicateSignature, predicateDeclaration, namedIdentityX,
    namedSignature, lookupDeclaration?, intrinsicIdentity,
    intrinsicPredicateAtBound, intrinsicPredicate, individual,
    individualPacket, TypePacket.arrow, TypePacket.base, TypePacket.prop,
    check, infer, expectType]

theorem intrinsic_identity_is_declared :
    constantsDeclared predicateSignature (encodeTerm intrinsicIdentity) =
      true := by
  rfl

theorem named_identity_compiles :
    compileFormula predicateSignature namedIdentityX = .ok identityPacket := by
  simp [compileFormula, predicate_signature_is_functional,
    named_identity_checks, identityPacket, intrinsic_identity_is_declared]

theorem alpha_renaming_compiles_identically :
    compileFormula predicateSignature namedIdentityX =
      compileFormula predicateSignature namedIdentityY :=
  compileFormula_eq_of_alpha namedIdentityAlpha

theorem named_identity_replays :
    decodeFormula? identityPacket = some intrinsicIdentity := by
  have compiled := compileFormula_sound named_identity_compiles
  rcases compiled with ⟨formula, checked, packetReplay, admitted⟩
  have formulaIdentity : formula = intrinsicIdentity := by
    rw [named_identity_checks] at checked
    cases checked
    rfl
  simpa [packetReplay, formulaIdentity] using admitted

def duplicateSignature : SignaturePacket :=
  [predicateDeclaration, predicateDeclaration]

def duplicateIdentityPacket : FormulaPacket :=
  ⟨duplicateSignature, encodeTerm intrinsicIdentity⟩

theorem duplicate_signature_is_functional :
    signatureFunctional duplicateSignature = true := by
  rfl

theorem duplicate_named_identity_checks :
    check (namedSignature duplicateSignature)
        (BinderNames.nil : BinderNames String String []) namedIdentityX .prop =
      .ok intrinsicIdentity := by
  simp [duplicateSignature, predicateDeclaration, namedIdentityX,
    namedSignature, lookupDeclaration?, intrinsicIdentity,
    intrinsicPredicateAtBound, intrinsicPredicate, individual,
    individualPacket, TypePacket.arrow, TypePacket.base, TypePacket.prop,
    check, infer, expectType]

theorem duplicate_intrinsic_identity_is_declared :
    constantsDeclared duplicateSignature (encodeTerm intrinsicIdentity) =
      true := by
  rfl

theorem duplicate_named_identity_compiles :
    compileFormula duplicateSignature namedIdentityX =
      .ok duplicateIdentityPacket := by
  simp [compileFormula, duplicate_signature_is_functional,
    duplicate_named_identity_checks, duplicateIdentityPacket,
    duplicate_intrinsic_identity_is_declared]

theorem duplicate_identity_replays :
    decodeFormula? duplicateIdentityPacket = some intrinsicIdentity := by
  have compiled := compileFormula_sound duplicate_named_identity_compiles
  rcases compiled with ⟨formula, checked, packetReplay, admitted⟩
  rw [duplicate_named_identity_checks] at checked
  cases checked
  simpa [packetReplay] using admitted

theorem exact_duplicate_occurrences_survive :
    compileFormula duplicateSignature namedIdentityX =
      .ok duplicateIdentityPacket ∧
    duplicateIdentityPacket.signature.length = 2 ∧
    decodeFormula? duplicateIdentityPacket = some intrinsicIdentity := by
  exact ⟨duplicate_named_identity_compiles, rfl,
    duplicate_identity_replays⟩

def conflictingSignature : SignaturePacket :=
  [predicateDeclaration, ⟨"P", .prop⟩]

theorem conflicting_signature_is_not_functional :
    signatureFunctional conflictingSignature = false := by
  rfl

theorem conflicting_signature_rejects_before_elaboration :
    compileFormula conflictingSignature namedIdentityX =
      .error .conflictingSignature := by
  simp [compileFormula, conflicting_signature_is_not_functional]

def freeVariable : NamedTH0Term := .variable "free"

theorem free_variable_rejects_at_scope_boundary :
    compileFormula [] freeVariable =
      .error (.source (.unboundVariable "free")) := by
  simp [compileFormula, freeVariable, signatureFunctional, namedSignature,
    lookupDeclaration?, check, infer]

def wrongArgument : NamedTH0Term :=
  .app (.constant "P") .top

theorem wrong_argument_check_fails :
    check (namedSignature predicateSignature)
        (BinderNames.nil : BinderNames String String []) wrongArgument .prop =
      .error (.typeMismatch individual .prop) := by
  simp [predicateSignature, predicateDeclaration, wrongArgument,
    namedSignature, lookupDeclaration?, check, infer, expectType, individual,
    individualPacket, TypePacket.arrow, TypePacket.base, TypePacket.prop]

theorem wrong_argument_rejects_at_type_boundary :
    compileFormula predicateSignature wrongArgument =
      .error (.source (.typeMismatch individual .prop)) := by
  simp [compileFormula, predicate_signature_is_functional,
    wrong_argument_check_fails]

theorem named_th0_bridge_boundary :
    compileFormula predicateSignature namedIdentityX = .ok identityPacket ∧
    compileFormula predicateSignature namedIdentityY = .ok identityPacket ∧
    decodeFormula? identityPacket = some intrinsicIdentity ∧
    compileFormula conflictingSignature namedIdentityX =
      .error .conflictingSignature ∧
    compileFormula [] freeVariable =
      .error (.source (.unboundVariable "free")) ∧
    compileFormula predicateSignature wrongArgument =
      .error (.source (.typeMismatch individual .prop)) := by
  refine ⟨named_identity_compiles, ?_, named_identity_replays,
    conflicting_signature_rejects_before_elaboration,
    free_variable_rejects_at_scope_boundary,
    wrong_argument_rejects_at_type_boundary⟩
  rw [← alpha_renaming_compiles_identically]
  exact named_identity_compiles

end Canary

#print axioms compileFormula_sound
#print axioms compileFormula_eq_of_alpha
#print axioms compileFormula_preserves_signature
#print axioms compileFormula_adapter_readmits
#print axioms compileFormula_adapter_agreement
#print axioms Canary.alpha_renaming_compiles_identically
#print axioms Canary.exact_duplicate_occurrences_survive
#print axioms Canary.named_th0_bridge_boundary

end Mettapedia.TypeTheory.TH0NamedElaborationBridge
