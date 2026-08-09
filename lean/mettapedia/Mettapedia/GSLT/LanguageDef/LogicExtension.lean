import Mettapedia.GSLT.LanguageDef.Extension
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Typed logic programs as a coGSLT-authored extension

A five-field language may contain relation-query premises, but the relations
and clauses interpreting those premises are an independently authored layer.
This module represents that layer without opaque backend text.  Relation
signatures and typed Datalog clauses have structural syntax, a validating
elaborator, and exact quotation.

Admission checks both sides of the seam: declarations must be well typed and
safe, and every relation called by either the logic program or the base
language must have one unambiguous declaration at the requested arity.
-/

namespace Mettapedia.GSLT.LanguageDef.LogicExtension

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The typed payload and its authored syntax -/

/-- Backend-independent logical declarations.  Opaque source snippets are not
logic declarations: an importer may parse them into this structure, but they
never become a second semantic authority. -/
inductive LogicDeclaration where
  | relation (signature : LogicRelationDecl)
  | clause (clause : DatalogClause)
deriving Repr, DecidableEq

abbrev LogicProgram := List LogicDeclaration

/-- Structural syntax of the logic extension. -/
inductive LogicSyntax where
  | relation (name : String) (argTypes : List TypeExpr)
  | clause (name : String) (head : DatalogAtom) (body : List DatalogAtom)
deriving Repr, DecidableEq

def encodeLogic : LogicDeclaration → LogicSyntax
  | .relation signature => .relation signature.name signature.argTypes
  | .clause clause => .clause clause.name clause.head clause.body

def decodeLogic : LogicSyntax → LogicDeclaration
  | .relation name argTypes => .relation { name, argTypes }
  | .clause name head body => .clause { name, head, body }

@[simp] theorem decodeLogic_encodeLogic (declaration : LogicDeclaration) :
    decodeLogic (encodeLogic declaration) = declaration := by
  cases declaration <;> cases ‹_› <;> rfl

@[simp] theorem encodeLogic_decodeLogic (source : LogicSyntax) :
    encodeLogic (decodeLogic source) = source := by
  cases source <;> rfl

def logicCodec : ExactDeclarationCodec LogicSyntax LogicDeclaration where
  encode := encodeLogic
  decode := decodeLogic
  decode_encode := decodeLogic_encodeLogic
  encode_decode := encodeLogic_decodeLogic

namespace LogicProgram

def relationDeclarations (program : LogicProgram) : List LogicRelationDecl :=
  program.filterMap fun
    | .relation signature => some signature
    | .clause _ => none

def clauses (program : LogicProgram) : List DatalogClause :=
  program.filterMap fun
    | .relation _ => none
    | .clause clause => some clause

def relationKeys (program : LogicProgram) : List (String × Nat) :=
  program.relationDeclarations.map fun signature =>
    (signature.name, signature.argTypes.length)

def relationDeclared (program : LogicProgram) (relation : String)
    (arity : Nat) : Bool :=
  program.relationDeclarations.countP (fun signature =>
    signature.name == relation && signature.argTypes.length == arity) == 1

private def typeDeclaredBy (language : LanguageDef) (type : TypeExpr) : Bool :=
  type.baseNames.all fun name => name ∈ language.typeNames

private def signatureAdmissible (language : LanguageDef)
    (signature : LogicRelationDecl) : Bool :=
  !signature.name.isEmpty &&
    signature.argTypes.all (typeDeclaredBy language)

private def atomAdmissible (program : LogicProgram)
    (atom : DatalogAtom) : Bool :=
  program.relationDeclared atom.rel atom.args.length

private def clauseAdmissible (program : LogicProgram)
    (clause : DatalogClause) : Bool :=
  clause.isSafe && program.atomAdmissible clause.head &&
    clause.body.all (program.atomAdmissible)

private def premiseRelationsAdmitted (program : LogicProgram)
    (premises : List Premise) : Bool :=
  premises.all fun premise =>
    premise.relationCalls.all fun call =>
      program.relationDeclared call.1 call.2

/-- Exact admission gate for a logic program over one base language. -/
def AdmissibleFor (program : LogicProgram) (language : LanguageDef) : Bool :=
  decide program.relationKeys.Nodup &&
    program.relationDeclarations.all (signatureAdmissible language) &&
    program.clauses.all (program.clauseAdmissible) &&
    (language.equations.all fun equation =>
      program.premiseRelationsAdmitted equation.premises) &&
    (language.rewrites.all fun rewrite =>
      program.premiseRelationsAdmitted rewrite.premises)

end LogicProgram

abbrev AdmittedProgram (language : LanguageDef) :=
  { program : LogicProgram //
    LogicProgram.AdmissibleFor program language = true }

/-- The law-bearing authored GSLT for logic declaration sequences. -/
def logicAuthoringGSLT : DeclarationAuthoringGSLT LogicDeclaration :=
  logicCodec.compositionalElaboration

def logicDocumentGSLT : GSLT :=
  logicAuthoringGSLT.authoring.theory

private def elaborateProgram? (language : LanguageDef)
    (source : DeclarationDocument LogicSyntax) :
    Option (AdmittedProgram language) :=
  let program := logicCodec.elaborate source
  if admitted : LogicProgram.AdmissibleFor program language = true then
    some ⟨program, admitted⟩
  else
    none

private def quoteProgram (language : LanguageDef)
    (program : AdmittedProgram language) : DeclarationDocument LogicSyntax :=
  logicCodec.quote program.1

/-- Typed logic programs form a coGSLT-authored dependent layer over the
five-field term language. -/
def layer : CoGSLTLayer LanguageDef where
  Fiber := AdmittedProgram
  sourceGSLT := fun _ => logicDocumentGSLT
  elaborate := elaborateProgram?
  quote := quoteProgram
  elaborate_quote := by
    intro language program
    simp [quoteProgram, elaborateProgram?,
      ExactDeclarationCodec.elaborate_quote, program.2]
  elaborate_equation := by
    intro language source target equal
    unfold elaborateProgram?
    rw [logicCodec.elaborate_equation equal]
  elaborate_rewrite := by
    intro language source target impossible
    exact False.elim impossible

@[simp] theorem erase_attach (language : LanguageDef)
    (program : AdmittedProgram language) :
    layer.erase (layer.attach language program) = language :=
  rfl

/-! ## Positive and negative canaries -/

private def exampleLanguage : LanguageDef :=
  { LanguageDef.empty "logic-example" with
    types := [TypeDecl.plain "Obj"] }

private def edgeSignature : LogicDeclaration :=
  .relation { name := "edge", argTypes := [.base "Obj", .base "Obj"] }

private def edgeFact : LogicDeclaration :=
  .clause
    { name := "edge-a-b"
      head := { rel := "edge", args := [.const "a", .const "b"] }
      body := [] }

private def edgeProgram : AdmittedProgram exampleLanguage :=
  ⟨[edgeSignature, edgeFact], by decide⟩

/-- Positive: a typed safe program round-trips through its authored GSLT. -/
example :
    layer.elaborate exampleLanguage (layer.quote exampleLanguage edgeProgram) =
      some edgeProgram :=
  layer.elaborate_quote exampleLanguage edgeProgram

/-- Negative: unsafe variable facts fail admission. -/
example :
    LogicProgram.AdmissibleFor
      [edgeSignature,
       .clause
         { name := "unsafe"
           head := { rel := "edge", args := [.var "x", .const "b"] }
           body := [] }] exampleLanguage = false := by
  decide

/-- Negative: clauses cannot call an undeclared relation. -/
example :
    LogicProgram.AdmissibleFor
      [.clause
        { name := "unknown"
          head := { rel := "missing", args := [] }
          body := [] }] exampleLanguage = false := by
  decide

/-- Negative: duplicated relation signatures make lookup ambiguous. -/
example :
    LogicProgram.AdmissibleFor
      [edgeSignature, edgeSignature] exampleLanguage = false := by
  decide

private def noLogic : AdmittedProgram exampleLanguage := ⟨[], by decide⟩
private def noLogicAttached : layer.Total :=
  layer.attach exampleLanguage noLogic
private def edgeProgramAttached : layer.Total :=
  layer.attach exampleLanguage edgeProgram

def logicProgramNonTrivialFiber :
    NonTrivialFiber layer.erase (fun attached => attached.2.1) where
  left := noLogicAttached
  right := edgeProgramAttached
  sameShadow := rfl
  differentValue := by
    change ([] : LogicProgram) ≠ [edgeSignature, edgeFact]
    simp

theorem logic_program_not_determined_by_language :
    ¬ Factors layer.erase (fun attached => attached.2.1) :=
  logicProgramNonTrivialFiber.not_factors

end Mettapedia.GSLT.LanguageDef.LogicExtension
