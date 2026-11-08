import Mettapedia.Languages.Lean.ParserDescriptorLowering
import Mettapedia.GSLT.Parsing.ScopedGrammarTranslation

/-!
# Compiling scoped declarations to precedence-indexed presentation tables

The source stores complete descriptors. The target stores callable patches
of compiled presentation rows, indexed by category and requested precedence.
Installing a patch prepends its parser rows to the target table; it does not rebuild
the source state. Unsupported descriptors remain explicit error rows.

Only demanded table keys need materializing for a finite ParserPack. The
mathematical table is total, so installing a previously unseen precedence
does not require inventing a bound on the set of possible precedences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.ParserRegistrationCompiler

open ParserDescription ParserDescriptorLowering
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing

structure Key where
  category : Name
  precedence : Nat
  deriving DecidableEq, Repr

structure Registration where
  category : Name
  declaration : Name
  priority : Nat
  descriptor : Description
  deriving DecidableEq, Repr

structure Header where
  kind : Name
  precedence : Nat
  leftPrecedence : Option Nat
  body : Description
  deriving DecidableEq, Repr

def header : Description → Option Header
  | .node kind precedence body => some ⟨kind, precedence, none, body⟩
  | .trailingNode kind precedence leftPrecedence body => some ⟨kind, precedence, some leftPrecedence, body⟩
  | _ => none

inductive Refusal where
  | descriptorHeader (declaration : Name)
  | descriptorBody (declaration : Name) (body : Description)
  deriving DecidableEq, Repr

structure Row where
  declaration : Name
  kind : Name
  priority : Nat
  precedence : Nat
  leftPrecedence : Option Nat
  body : Expr
  deriving DecidableEq, Repr

abbrev Table := Key → List (Except Refusal Row)

structure Code where
  table : Table
  tokens : List String

abbrev Patch := Code

def tokenText (text : String) : String := String.ofList ((scalars text).map Char.ofNat)

/-- Token occurrences are retained until the lexical table applies its own
selection policy. Unsupported aliases remain an admission boundary. -/
def tokens : Description → List String
  | .symbol text | .nonReservedSymbol text _ => [tokenText text]
  | .unary _ body | .node _ _ body | .trailingNode _ _ _ body | .nodeWithAntiquot _ _ body => tokens body
  | .binary _ first second | .sepBy first _ second _ | .sepBy1 first _ second _ => tokens first ++ tokens second
  | .unicodeSymbol first second _ => [tokenText first, tokenText second]
  | _ => []

/-- One declaration contributes independently compiled rows at every eligible
category/precedence key. Error rows cannot silently disappear into no-parse. -/
def compileRows (bindings : Bindings) (registration : Registration) : Table := fun key =>
  if key.category ≠ registration.category then [] else
  match header registration.descriptor with
  | none => [.error (.descriptorHeader registration.declaration)]
  | some info =>
      if info.precedence < key.precedence then [] else
      match lower bindings info.body with
      | none => [.error (.descriptorBody registration.declaration info.body)]
      | some body => [.ok {
          declaration := registration.declaration
          kind := info.kind
          priority := registration.priority
          precedence := info.precedence
          leftPrecedence := info.leftPrecedence
          body := match info.leftPrecedence with
            | none => body
            | some left => .seq (.ref (bindings.categoryRef key.category left)) body }]

def compileEntry (bindings : Bindings) (registration : Registration) : Patch :=
  ⟨compileRows bindings registration, tokens registration.descriptor⟩

def sourceAdd (entries : List Registration) (registration : Registration) : List Registration :=
  entries ++ [registration]

def targetAdd (code : Code) (patch : Patch) : Code :=
  ⟨fun key => patch.table key ++ code.table key, code.tokens ++ patch.tokens⟩

def compileTable (bindings : Bindings) (entries : List Registration) : Code :=
  ⟨fun key => entries.reverse.flatMap fun registration => compileRows bindings registration key,
    entries.flatMap fun registration => tokens registration.descriptor⟩

theorem compile_entry_update (bindings : Bindings) (entries : List Registration) (registration : Registration) :
    compileTable bindings (sourceAdd entries registration) =
      targetAdd (compileTable bindings entries) (compileEntry bindings registration) := by
  simp [compileTable, compileEntry, sourceAdd, targetAdd, List.flatMap_append]

abbrev SourceState := ScopedGrammarState.State Name Registration (List Registration)
abbrev TargetState := ScopedGrammarState.State Name Patch Code

def compileState (bindings : Bindings) (source : SourceState) : TargetState :=
  ScopedGrammarTranslation.state (compileTable bindings) (compileEntry bindings) source

theorem compile_local (bindings : Bindings) (source : SourceState) (registration : Registration) :
    compileState bindings (ScopedGrammarState.localEntry sourceAdd registration source) =
      ScopedGrammarState.localEntry targetAdd (compileEntry bindings registration) (compileState bindings source) :=
  ScopedGrammarTranslation.localEntry (compileTable bindings) (compileEntry bindings) sourceAdd targetAdd
    (compile_entry_update bindings) source registration

theorem compile_registration (bindings : Bindings) (source : SourceState)
    (registration : ScopedGrammarState.Entry Name Registration) :
    compileState bindings (ScopedGrammarState.register sourceAdd registration source) =
      ScopedGrammarState.register targetAdd (ScopedGrammarTranslation.entry (compileEntry bindings) registration)
        (compileState bindings source) :=
  ScopedGrammarTranslation.register (compileTable bindings) (compileEntry bindings) sourceAdd targetAdd
    (compile_entry_update bindings) source registration

theorem compile_activation (bindings : Bindings) (source : SourceState) (scopeName : Name) (reset : Bool) :
    compileState bindings (ScopedGrammarState.activate reset sourceAdd scopeName source) =
      ScopedGrammarState.activate reset targetAdd scopeName (compileState bindings source) :=
  ScopedGrammarTranslation.activate (compileTable bindings) (compileEntry bindings) sourceAdd targetAdd
    (compile_entry_update bindings) reset scopeName source

theorem compile_push (bindings : Bindings) (source : SourceState) :
    compileState bindings (ScopedGrammarState.push source) = ScopedGrammarState.push (compileState bindings source) :=
  ScopedGrammarTranslation.push (compileTable bindings) (compileEntry bindings) source

theorem compile_pop (bindings : Bindings) (source : SourceState) :
    compileState bindings (ScopedGrammarState.pop source) = ScopedGrammarState.pop (compileState bindings source) :=
  ScopedGrammarTranslation.pop (compileTable bindings) (compileEntry bindings) source

theorem compile_delimit (bindings : Bindings) (source : SourceState) (count : Nat) :
    compileState bindings (ScopedGrammarState.delimit count source) =
      ScopedGrammarState.delimit count (compileState bindings source) :=
  ScopedGrammarTranslation.delimit (compileTable bindings) (compileEntry bindings) count source

theorem compile_imports (bindings : Bindings) (base : List Registration)
    (entries : List (ScopedGrammarState.Entry Name Registration)) :
    compileState bindings (ScopedGrammarState.imports id sourceAdd base entries) =
      ScopedGrammarState.imports id targetAdd (compileTable bindings base)
        (entries.map (ScopedGrammarTranslation.entry (compileEntry bindings))) :=
  ScopedGrammarTranslation.imports (compileTable bindings) (compileEntry bindings) sourceAdd targetAdd
    (compile_entry_update bindings) base entries

inductive Effect where
  | push
  | pop
  | delimit (count : Nat)
  | localRule (registration : Registration)
  | registration (entry : ScopedGrammarState.Entry Name Registration)
  | activate (resetBoundary : Bool) (scopeName : Name)
  deriving DecidableEq, Repr

def sourceEffect (effect : Effect) (source : SourceState) : SourceState :=
  match effect with
  | .push => ScopedGrammarState.push source
  | .pop => ScopedGrammarState.pop source
  | .delimit count => ScopedGrammarState.delimit count source
  | .localRule rule => ScopedGrammarState.localEntry sourceAdd rule source
  | .registration update => ScopedGrammarState.register sourceAdd update source
  | .activate reset scopeName => ScopedGrammarState.activate reset sourceAdd scopeName source

def targetEffect (bindings : Bindings) (effect : Effect) (target : TargetState) : TargetState :=
  match effect with
  | .push => ScopedGrammarState.push target
  | .pop => ScopedGrammarState.pop target
  | .delimit count => ScopedGrammarState.delimit count target
  | .localRule rule => ScopedGrammarState.localEntry targetAdd (compileEntry bindings rule) target
  | .registration update =>
      ScopedGrammarState.register targetAdd (ScopedGrammarTranslation.entry (compileEntry bindings) update) target
  | .activate reset scopeName => ScopedGrammarState.activate reset targetAdd scopeName target

/-- The concrete compiler/effect square. Target effects install compiled rows
and token patches, independently of the source descriptor-list operations. -/
theorem effect_commutes (bindings : Bindings) (source : SourceState) (effect : Effect) :
    compileState bindings (sourceEffect effect source) =
      targetEffect bindings effect (compileState bindings source) := by
  cases effect with
  | push => exact compile_push bindings source
  | pop => exact compile_pop bindings source
  | delimit count => exact compile_delimit bindings source count
  | localRule rule => exact compile_local bindings source rule
  | registration update => exact compile_registration bindings source update
  | activate reset scopeName => exact compile_activation bindings source scopeName reset

theorem effects_commute (bindings : Bindings) (source : SourceState) (effects : List Effect) :
    compileState bindings (effects.foldl (fun current effect => sourceEffect effect current) source) =
      effects.foldl (fun current effect => targetEffect bindings effect current) (compileState bindings source) := by
  induction effects generalizing source with
  | nil => rfl
  | cons effect rest ih => simp [List.foldl, ih, effect_commutes]

theorem wrong_category_has_no_rows (bindings : Bindings) (registration : Registration) (key : Key)
    (different : key.category ≠ registration.category) : (compileEntry bindings registration).table key = [] := by
  simp [compileEntry, compileRows, different]

theorem low_precedence_has_no_rows (bindings : Bindings) (registration : Registration) (key : Key) (info : Header)
    (found : header registration.descriptor = some info) (tooLow : info.precedence < key.precedence) :
    (compileEntry bindings registration).table key = [] := by
  simp [compileEntry, compileRows, found, tooLow]

/-- Keywords are registered even at a query whose precedence excludes the
parser row. A parser-only cache key would miss this lexical effect. -/
theorem tokens_independent_of_requested_precedence (bindings : Bindings) (registration : Registration) :
    (compileEntry bindings registration).tokens = tokens registration.descriptor := rfl

end Mettapedia.Languages.Lean.ParserRegistrationCompiler
