import Mettapedia.GSLT.LanguageDef.Extension
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Oracle libraries as a coGSLT-authored language-definition extension

An oracle declaration is a typed interface exposed to a language.  It is not
part of the language's term grammar, and a native implementation of that
interface is not part of the mathematical language at all.  This module keeps
the three levels separate:

* `OracleSyntax` is the authored extension language;
* `AdmittedLibrary base` is a validated interface over one five-field base;
* `NativeRealization` supplies backend operations only for admitted entries.

The extension's GSLT elaborates structural declaration documents.  It rejects
empty names, duplicate declarations, and type references outside the base.
Quotation is an exact section, while native realization remains a separate
consumer of the admitted interface.
-/

namespace Mettapedia.GSLT.LanguageDef.OracleExtension

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Structural authored syntax -/

/-- Authored syntax for one typed external-library entry. -/
inductive OracleSyntax where
  | external (name : String) (argTypes : List TypeExpr)
      (resultType : TypeExpr)
deriving Repr, DecidableEq

def encodeOracle (declaration : OracleDecl) : OracleSyntax :=
  .external declaration.name declaration.argTypes declaration.resultType

def decodeOracle : OracleSyntax → OracleDecl
  | .external name argTypes resultType =>
      { name, argTypes, resultType }

@[simp] theorem decodeOracle_encodeOracle (declaration : OracleDecl) :
    decodeOracle (encodeOracle declaration) = declaration := by
  cases declaration
  rfl

@[simp] theorem encodeOracle_decodeOracle (source : OracleSyntax) :
    encodeOracle (decodeOracle source) = source := by
  cases source
  rfl

/-- The exact structural codec used by the declaration-document GSLT. -/
def oracleCodec : ExactDeclarationCodec OracleSyntax OracleDecl where
  encode := encodeOracle
  decode := decodeOracle
  decode_encode := decodeOracle_encodeOracle
  encode_decode := encodeOracle_decodeOracle

/-! ## Admission over a five-field language -/

/-- Every base type mentioned by an oracle interface must be declared by the
language over which the interface is attached. -/
def TypeDeclaredBy (language : LanguageDef) (type : TypeExpr) : Bool :=
  type.baseNames.all fun name => name ∈ language.typeNames

/-- Local admission for one oracle declaration. -/
def OracleDecl.admissibleFor (language : LanguageDef)
    (declaration : OracleDecl) : Bool :=
  !declaration.name.isEmpty &&
    declaration.argTypes.all (TypeDeclaredBy language) &&
    TypeDeclaredBy language declaration.resultType

/-- Admission for a library: names are unique and every typed interface is
grounded in the base language's declared sorts. -/
def LibraryAdmissible (language : LanguageDef)
    (declarations : List OracleDecl) : Bool :=
  decide (declarations.map (fun declaration => declaration.name)).Nodup &&
    declarations.all (OracleDecl.admissibleFor language)

/-- A library admitted over one exact five-field language. -/
abbrev AdmittedLibrary (language : LanguageDef) :=
  { declarations : List OracleDecl //
    LibraryAdmissible language declarations = true }

/-- The law-bearing authored GSLT for oracle declaration sequences. -/
def oracleAuthoringGSLT : DeclarationAuthoringGSLT OracleDecl :=
  oracleCodec.compositionalElaboration

/-- The declaration-document theory underlying oracle authoring. -/
def oracleDocumentGSLT : GSLT :=
  oracleAuthoringGSLT.authoring.theory

private def elaborateLibrary? (language : LanguageDef)
    (source : DeclarationDocument OracleSyntax) :
    Option (AdmittedLibrary language) :=
  let declarations := oracleCodec.elaborate source
  if admitted : LibraryAdmissible language declarations = true then
    some ⟨declarations, admitted⟩
  else
    none

private def quoteLibrary (language : LanguageDef)
    (library : AdmittedLibrary language) :
    DeclarationDocument OracleSyntax :=
  oracleCodec.quote library.1

/-- Oracle interfaces form a coGSLT-authored dependent layer over the base
language.  Invalid declarations fail at elaboration rather than being stored
in the root language record. -/
def layer : CoGSLTLayer LanguageDef where
  Fiber := AdmittedLibrary
  sourceGSLT := fun _ => oracleDocumentGSLT
  elaborate := elaborateLibrary?
  quote := quoteLibrary
  elaborate_quote := by
    intro language library
    simp [quoteLibrary, elaborateLibrary?,
      ExactDeclarationCodec.elaborate_quote, library.2]
  elaborate_equation := by
    intro language source target equal
    unfold elaborateLibrary?
    rw [oracleCodec.elaborate_equation equal]
  elaborate_rewrite := by
    intro language source target impossible
    exact False.elim impossible

@[simp] theorem erase_attach (language : LanguageDef)
    (library : AdmittedLibrary language) :
    layer.erase (layer.attach language library) = language :=
  rfl

/-! ## Native realization is a separate level -/

/-- A backend operation implementing exactly one admitted oracle declaration.
The operation type is backend-owned; the mathematical interface never stores
host code, symbol addresses, or compiler directives. -/
structure NativeRealization (language : LanguageDef)
    (library : AdmittedLibrary language) (BackendOperation : Type*) where
  implementation :
    { declaration : OracleDecl // declaration ∈ library.1 } → BackendOperation

/-! ## Positive and negative canaries -/

private def exampleLanguage : LanguageDef :=
  { LanguageDef.empty "oracle-example" with
    types := [TypeDecl.plain "Term", TypeDecl.plain "Truth"] }

private def truthOracle : OracleDecl :=
  { name := "truth"
    argTypes := [.base "Term"]
    resultType := .base "Truth" }

private def truthLibrary : AdmittedLibrary exampleLanguage :=
  ⟨[truthOracle], by decide⟩

/-- Positive: an admitted declaration quotes and elaborates back to the same
typed library. -/
example :
    layer.elaborate exampleLanguage (layer.quote exampleLanguage truthLibrary) =
      some truthLibrary :=
  layer.elaborate_quote exampleLanguage truthLibrary

/-- Negative: a declaration cannot mention a sort absent from the base. -/
example :
    LibraryAdmissible exampleLanguage
      [{ name := "bad", argTypes := [.base "Missing"],
         resultType := .base "Truth" }] = false := by
  decide

/-- Negative: duplicate host-interface names are rejected even when their
types agree. -/
example :
    LibraryAdmissible exampleLanguage [truthOracle, truthOracle] = false := by
  decide

private def noOracleLibrary : AdmittedLibrary exampleLanguage :=
  ⟨[], by decide⟩

private def noOracleAttached : layer.Total :=
  layer.attach exampleLanguage noOracleLibrary

private def truthOracleAttached : layer.Total :=
  layer.attach exampleLanguage truthLibrary

/-- The oracle library is genuine extension data: erasing it leaves the same
language, but the two interfaces remain distinguishable. -/
def oracleLibraryNonTrivialFiber :
    NonTrivialFiber layer.erase (fun attached => attached.2.1) where
  left := noOracleAttached
  right := truthOracleAttached
  sameShadow := rfl
  differentValue := by
    change ([] : List OracleDecl) ≠ [truthOracle]
    simp

theorem oracle_library_not_determined_by_language :
    ¬ Factors layer.erase (fun attached => attached.2.1) :=
  oracleLibraryNonTrivialFiber.not_factors

end Mettapedia.GSLT.LanguageDef.OracleExtension
