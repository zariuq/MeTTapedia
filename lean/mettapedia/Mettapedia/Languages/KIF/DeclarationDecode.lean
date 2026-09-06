import Mettapedia.Languages.KIF.Parser

/-!
# Source-located SUO-KIF declaration decoding

This stage recognizes the small family of top-level declarations used to
build a SUMO symbol table. Every other well-formed top-level S-expression is
retained as a formula. Recognition is syntactic and source-located; it neither
asserts consistency nor proves the formulas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.KIF

structure LocatedSymbol where
  text : String
  span : SourceSpan
  deriving DecidableEq, Repr

structure LocatedString where
  text : String
  span : SourceSpan
  deriving DecidableEq, Repr

inductive SuoDeclaration : Type
  | subclass (child : LocatedSymbol) (parent : Term)
  | instance (individual className : LocatedSymbol)
  | domain (relation : LocatedSymbol) (position : Nat) (className : LocatedSymbol)
  | domainSubclass
      (relation : LocatedSymbol) (position : Nat) (className : LocatedSymbol)
  | range (relation className : LocatedSymbol)
  | rangeSubclass (relation className : LocatedSymbol)
  | documentation
      (subject language : LocatedSymbol) (text : LocatedString)
  deriving Repr

inductive DeclarationErrorKind : Type
  | wrongArity (head : String) (expected actual : Nat)
  | expectedSymbol
  | expectedNatural
  | expectedString
  deriving DecidableEq, Repr

structure DeclarationError where
  kind : DeclarationErrorKind
  span : SourceSpan
  deriving DecidableEq, Repr

def Term.asSymbol? : Term → Option LocatedSymbol
  | Term.atom value =>
      if value.kind = .symbol then some ⟨value.text, value.span⟩ else none
  | Term.list _ _ => none

def Term.asString? : Term → Option LocatedString
  | Term.atom value =>
      if value.kind = .stringLiteral then some ⟨value.text, value.span⟩ else none
  | Term.list _ _ => none

private def requireSymbol (term : Term) : Except DeclarationError LocatedSymbol :=
  match term.asSymbol? with
  | some symbol => .ok symbol
  | none => .error ⟨.expectedSymbol, term.span⟩

private def requireString (term : Term) : Except DeclarationError LocatedString :=
  match term.asString? with
  | some text => .ok text
  | none => .error ⟨.expectedString, term.span⟩

private def decimalDigit? : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | _ => none

private def naturalFromChars : List Char → Nat → Option Nat
  | [], value => some value
  | character :: rest, value =>
      match decimalDigit? character with
      | none => none
      | some digit => naturalFromChars rest (10 * value + digit)

private def parseNatural (text : String) : Option Nat :=
  match text.toList with
  | [] => none
  | characters => naturalFromChars characters 0

private def requireNatural (term : Term) : Except DeclarationError Nat :=
  match term.asSymbol? with
  | some symbol =>
      match parseNatural symbol.text with
      | some value => .ok value
      | none => .error ⟨.expectedNatural, symbol.span⟩
  | none => .error ⟨.expectedNatural, term.span⟩

private def wrongArity (head : LocatedSymbol) (expected actual : Nat) :
    Except DeclarationError (Option SuoDeclaration) :=
  .error ⟨.wrongArity head.text expected actual, head.span⟩

/-- Decode one recognized source declaration. `none` means that the form is a
formula rather than one of the symbol-table declarations handled here. -/
def decodeDeclaration (term : Term) :
    Except DeclarationError (Option SuoDeclaration) :=
  match term with
  | .atom _ => .ok none
  | .list _ [] => .ok none
  | .list _ (headTerm :: arguments) =>
      match headTerm.asSymbol? with
      | none => .ok none
      | some head =>
          match head.text with
          | "subclass" =>
              match arguments with
              | [childTerm, parentTerm] => do
                  let child ← requireSymbol childTerm
                  pure (some (.subclass child parentTerm))
              | _ => wrongArity head 2 arguments.length
          | "instance" =>
              match arguments with
              | [individualTerm, classTerm] => do
                  let individual ← requireSymbol individualTerm
                  let className ← requireSymbol classTerm
                  pure (some (.instance individual className))
              | _ => wrongArity head 2 arguments.length
          | "domain" =>
              match arguments with
              | [relationTerm, positionTerm, classTerm] => do
                  let relation ← requireSymbol relationTerm
                  let position ← requireNatural positionTerm
                  let className ← requireSymbol classTerm
                  pure (some (.domain relation position className))
              | _ => wrongArity head 3 arguments.length
          | "domainSubclass" =>
              match arguments with
              | [relationTerm, positionTerm, classTerm] => do
                  let relation ← requireSymbol relationTerm
                  let position ← requireNatural positionTerm
                  let className ← requireSymbol classTerm
                  pure (some (.domainSubclass relation position className))
              | _ => wrongArity head 3 arguments.length
          | "range" =>
              match arguments with
              | [relationTerm, classTerm] => do
                  let relation ← requireSymbol relationTerm
                  let className ← requireSymbol classTerm
                  pure (some (.range relation className))
              | _ => wrongArity head 2 arguments.length
          | "rangeSubclass" =>
              match arguments with
              | [relationTerm, classTerm] => do
                  let relation ← requireSymbol relationTerm
                  let className ← requireSymbol classTerm
                  pure (some (.rangeSubclass relation className))
              | _ => wrongArity head 2 arguments.length
          | "documentation" =>
              match arguments with
              | [subjectTerm, languageTerm, textTerm] => do
                  let subject ← requireSymbol subjectTerm
                  let language ← requireSymbol languageTerm
                  let text ← requireString textTerm
                  pure (some (.documentation subject language text))
              | _ => wrongArity head 3 arguments.length
          | _ => .ok none

structure DeclarationInventory where
  declarations : List SuoDeclaration
  formulas : List Term
  errors : List DeclarationError
  deriving Repr

private structure InventoryState where
  reversedDeclarations : List SuoDeclaration
  reversedFormulas : List Term
  reversedErrors : List DeclarationError

private def inventoryForms : List Term → InventoryState → InventoryState
  | [], state => state
  | term :: rest, state =>
      match decodeDeclaration term with
      | .ok (some declaration) =>
          inventoryForms rest
            { state with
              reversedDeclarations := declaration :: state.reversedDeclarations }
      | .ok none =>
          inventoryForms rest
            { state with reversedFormulas := term :: state.reversedFormulas }
      | .error failure =>
          inventoryForms rest
            { state with reversedErrors := failure :: state.reversedErrors }

/-- Decode all top-level forms while preserving unrecognized formulas and
accumulating every malformed recognized declaration. -/
def declarationInventory (parsed : Parsed) : DeclarationInventory :=
  let state := inventoryForms parsed.forms ⟨[], [], []⟩
  ⟨state.reversedDeclarations.reverse, state.reversedFormulas.reverse,
    state.reversedErrors.reverse⟩

structure DeclarationCounts where
  subclasses : Nat := 0
  instances : Nat := 0
  domains : Nat := 0
  domainSubclasses : Nat := 0
  ranges : Nat := 0
  rangeSubclasses : Nat := 0
  documentation : Nat := 0
  deriving DecidableEq, Repr

def DeclarationCounts.add : DeclarationCounts → SuoDeclaration → DeclarationCounts
  | counts, .subclass _ _ => { counts with subclasses := counts.subclasses + 1 }
  | counts, .instance _ _ => { counts with instances := counts.instances + 1 }
  | counts, .domain _ _ _ => { counts with domains := counts.domains + 1 }
  | counts, .domainSubclass _ _ _ =>
      { counts with domainSubclasses := counts.domainSubclasses + 1 }
  | counts, .range _ _ => { counts with ranges := counts.ranges + 1 }
  | counts, .rangeSubclass _ _ =>
      { counts with rangeSubclasses := counts.rangeSubclasses + 1 }
  | counts, .documentation _ _ _ =>
      { counts with documentation := counts.documentation + 1 }

def declarationCounts (inventory : DeclarationInventory) : DeclarationCounts :=
  inventory.declarations.foldl DeclarationCounts.add {}

/-! ## Declaration-decoding canaries -/

private def decodeSingle (source : String) :
    Except String (Option SuoDeclaration) := do
  let lexed ← (lex source).mapError fun _ => "lexical failure"
  let parsed := parse lexed
  match parsed.forms with
  | [term] => (decodeDeclaration term).mapError fun _ => "declaration failure"
  | _ => .error "expected exactly one form"

example :
    (decodeSingle "(subclass TargetCenteredVirtueEthicsTheory GeneralVirtueEthicsTheory)").map
        (fun declaration => declaration.map fun
          | .subclass child parent =>
              (child.text, (parent.asSymbol?.map (·.text)).getD "")
          | _ => ("", "")) =
      .ok (some ("TargetCenteredVirtueEthicsTheory", "GeneralVirtueEthicsTheory")) := by
  rfl

example :
    (decodeSingle "(domain virtueTarget 2 Formula)").map
        (fun declaration => declaration.map fun
          | .domain relation position className =>
              (relation.text, position, className.text)
          | _ => ("", 0, "")) =
      .ok (some ("virtueTarget", 2, "Formula")) := by
  rfl

example :
    decodeSingle "(domain virtueTarget two Formula)" =
      .error "declaration failure" := by
  rfl

example :
    decodeSingle "(domain virtueTarget 2)" =
      .error "declaration failure" := by
  rfl

end Mettapedia.Languages.KIF
