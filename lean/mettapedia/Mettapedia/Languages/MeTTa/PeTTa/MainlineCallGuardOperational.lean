import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.CertificateGSLTStepAdequacyGeneral
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission

/-!
# Operational LanguageDef for the PeTTa mainline call-guard compiler

This module gives the cold declaration compiler an ordinary five-field
`LanguageDef`.  The presentation traverses declarations and argument types in
authored order.  It constructs each `GuardPlan` one mode at a time and either
retains the complete ordered family or declines the whole family.

The relation environment is deliberately narrow.  It supplies structural
inequality, arity comparison, and the closed/open classification of one type
term.  It never returns a plan, a declaration family, a winning occurrence, or
a successor control state.  The state transition remains visible in the
authored rewrite rules.

The typed micro-machine is independent of the serialized presentation.  The
bridge below relates executions of the `LanguageDef` on encoded states to that
micro-machine, whose denotation is the existing ordered PeTTa compiler.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl

set_option autoImplicit false

@[reducible] private def ctor (label category : String)
    (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := policy
}

@[reducible] private def typed (entries : List (String × String)) :
    List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

@[reducible] def v (name : String) : Pattern := .fvar name
@[reducible] def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

@[reducible] def query
    (relation : String) (arguments : List Pattern) : Premise :=
  .relationQuery relation arguments

/-! ## Structural data encoding -/

def natZero : Pattern := a "petta-call-guard:nat-zero"
def natBitZero (value : Pattern) : Pattern :=
  a "petta-call-guard:nat-bit-zero" [value]
def natBitOne (value : Pattern) : Pattern :=
  a "petta-call-guard:nat-bit-one" [value]

/-- Canonical little-endian binary naturals.  Identifiers and revisions occupy
logarithmic rather than unary depth in the source presentation. -/
def encodeNat : Nat → Pattern :=
  Nat.binaryRec' natZero fun bit _ _ encoded =>
    if bit then natBitOne encoded else natBitZero encoded

def charPattern (value : Pattern) : Pattern :=
  a "petta-call-guard:char" [value]
def charsNil : Pattern := a "petta-call-guard:chars-nil"
def charsCons (head tail : Pattern) : Pattern :=
  a "petta-call-guard:chars-cons" [head, tail]

def encodeChars : List Char → Pattern
  | [] => charsNil
  | head :: tail =>
      charsCons (charPattern (encodeNat head.toNat)) (encodeChars tail)

def namePattern (characters : Pattern) : Pattern :=
  a "petta-call-guard:name" [characters]

def encodeName (name : String) : Pattern :=
  namePattern (encodeChars name.toList)

def termVariable (name : Pattern) : Pattern :=
  a "petta-call-guard:term-variable" [name]
def termNumber (lexeme : Pattern) : Pattern :=
  a "petta-call-guard:term-number" [lexeme]
def termString (value : Pattern) : Pattern :=
  a "petta-call-guard:term-string" [value]
def termAtom (name : Pattern) : Pattern :=
  a "petta-call-guard:term-atom" [name]
def termList (elements : Pattern) : Pattern :=
  a "petta-call-guard:term-list" [elements]
def termsNil : Pattern := a "petta-call-guard:terms-nil"
def termsCons (head tail : Pattern) : Pattern :=
  a "petta-call-guard:terms-cons" [head, tail]

mutual
  def encodeTerm : Term → Pattern
    | .variable name => termVariable (encodeName name)
    | .number lexeme => termNumber (encodeName lexeme)
    | .string value => termString (encodeName value)
    | .atom name => termAtom (encodeName name)
    | .list elements => termList (encodeTerms elements)

  def encodeTerms : List Term → Pattern
    | [] => termsNil
    | head :: tail => termsCons (encodeTerm head) (encodeTerms tail)
end

theorem encodeNat_closedSkeleton (value : Nat) :
    patternClosedSkeleton (encodeNat value) = true := by
  induction value using Nat.binaryRec' with
  | zero =>
      simp [encodeNat, natZero, a, patternClosedSkeleton,
        patternsClosedSkeleton]
  | bit bit value canonical inductionHypothesis =>
      rw [encodeNat, Nat.binaryRec'_eq _ _ canonical]
      cases bit
      · change patternClosedSkeleton (natBitZero (encodeNat value)) = true
        simpa [natBitZero, a, patternClosedSkeleton,
          patternsClosedSkeleton] using inductionHypothesis
      · change patternClosedSkeleton (natBitOne (encodeNat value)) = true
        simpa [natBitOne, a, patternClosedSkeleton,
          patternsClosedSkeleton] using inductionHypothesis

theorem encodeChars_closedSkeleton (characters : List Char) :
    patternClosedSkeleton (encodeChars characters) = true := by
  induction characters with
  | nil =>
      simp [encodeChars, charsNil, a, patternClosedSkeleton,
        patternsClosedSkeleton]
  | cons head tail inductionHypothesis =>
      simp [encodeChars, charsCons, charPattern, a, patternClosedSkeleton,
        patternsClosedSkeleton, encodeNat_closedSkeleton,
        inductionHypothesis]

theorem encodeName_closedSkeleton (name : String) :
    patternClosedSkeleton (encodeName name) = true := by
  simp [encodeName, namePattern, a, patternClosedSkeleton,
    patternsClosedSkeleton, encodeChars_closedSkeleton]

mutual
  theorem encodeTerm_closedSkeleton (term : Term) :
      patternClosedSkeleton (encodeTerm term) = true := by
    cases term <;>
      simp [encodeTerm, termVariable, termNumber, termString, termAtom,
        termList, a, patternClosedSkeleton, patternsClosedSkeleton,
        encodeName_closedSkeleton, encodeTerms_closedSkeleton]

  theorem encodeTerms_closedSkeleton (terms : List Term) :
      patternClosedSkeleton (encodeTerms terms) = true := by
    cases terms with
    | nil =>
        simp [encodeTerms, termsNil, a, patternClosedSkeleton,
          patternsClosedSkeleton]
    | cons head tail =>
        simp [encodeTerms, termsCons, a, patternClosedSkeleton,
          patternsClosedSkeleton, encodeTerm_closedSkeleton,
          encodeTerms_closedSkeleton]
end

@[simp] theorem encodeTerm_holeSkeleton (term : Term) :
    patternHoleSkeleton (encodeTerm term) = true :=
  patternHoleSkeleton_of_closed (encodeTerm_closedSkeleton term)

@[simp] theorem encodeTerm_occurrenceNames (term : Term) :
    patternOccurrenceNames (encodeTerm term) = [] :=
  patternOccurrenceNames_closed (encodeTerm_closedSkeleton term)

@[simp] theorem applyBindings_encodeTerm (bindings : Bindings) (term : Term) :
    applyBindings bindings (encodeTerm term) = encodeTerm term :=
  applyBindings_closedSkeleton (encodeTerm_closedSkeleton term) bindings

def declarationPattern (occurrence function inputs output : Pattern) : Pattern :=
  a "petta-call-guard:declaration" [occurrence, function, inputs, output]
def declarationsNil : Pattern := a "petta-call-guard:declarations-nil"
def declarationsCons (head tail : Pattern) : Pattern :=
  a "petta-call-guard:declarations-cons" [head, tail]

def encodeDeclaration (declaration : ArrowDeclaration) : Pattern :=
  declarationPattern (encodeNat declaration.occurrence)
    (encodeName declaration.function) (encodeTerms declaration.inputTypes)
    (encodeTerm declaration.outputType)

def encodeDeclarations : List ArrowDeclaration → Pattern
  | [] => declarationsNil
  | head :: tail =>
      declarationsCons (encodeDeclaration head) (encodeDeclarations tail)

def ownerPattern (token : Pattern) : Pattern :=
  a "petta-call-guard:owner" [token]
def encodeOwner (owner : SpaceOwner) : Pattern := ownerPattern (encodeNat owner.token)

def rawArgMode : Pattern := a "petta-call-guard:arg-raw"
def uncheckedArgMode : Pattern := a "petta-call-guard:arg-unchecked"
def checkedArgMode (expected : Pattern) : Pattern :=
  a "petta-call-guard:arg-checked" [expected]
def argModesNil : Pattern := a "petta-call-guard:arg-modes-nil"
def argModesSnoc (modes mode : Pattern) : Pattern :=
  a "petta-call-guard:arg-modes-snoc" [modes, mode]

def encodeArgMode : ArgMode → Pattern
  | .rawAtom => rawArgMode
  | .evalUnchecked => uncheckedArgMode
  | .evalSoftcutType expected => checkedArgMode (encodeTerm expected)

@[simp] theorem encodeArgMode_closedSkeleton (mode : ArgMode) :
    patternClosedSkeleton (encodeArgMode mode) = true := by
  cases mode <;>
    simp [encodeArgMode, rawArgMode, uncheckedArgMode, checkedArgMode,
      a, patternClosedSkeleton, patternsClosedSkeleton,
      encodeTerm_closedSkeleton]

@[simp] theorem encodeArgMode_holeSkeleton (mode : ArgMode) :
    patternHoleSkeleton (encodeArgMode mode) = true :=
  patternHoleSkeleton_of_closed (encodeArgMode_closedSkeleton mode)

@[simp] theorem encodeArgMode_occurrenceNames (mode : ArgMode) :
    patternOccurrenceNames (encodeArgMode mode) = [] :=
  patternOccurrenceNames_closed (encodeArgMode_closedSkeleton mode)

@[simp] theorem applyBindings_encodeArgMode
    (bindings : Bindings) (mode : ArgMode) :
    applyBindings bindings (encodeArgMode mode) = encodeArgMode mode :=
  applyBindings_closedSkeleton (encodeArgMode_closedSkeleton mode) bindings

def encodeArgModes (modes : List ArgMode) : Pattern :=
  modes.foldl (fun encoded mode => argModesSnoc encoded (encodeArgMode mode))
    argModesNil

@[simp] theorem encodeArgModes_append_singleton
    (modes : List ArgMode) (mode : ArgMode) :
    encodeArgModes (modes ++ [mode]) =
      argModesSnoc (encodeArgModes modes) (encodeArgMode mode) := by
  simp [encodeArgModes, List.foldl_append]

def uncheckedResultMode : Pattern :=
  a "petta-call-guard:result-unchecked"
def checkedResultMode (expected : Pattern) : Pattern :=
  a "petta-call-guard:result-checked" [expected]

def encodeResultMode : ResultMode → Pattern
  | .resultUnchecked => uncheckedResultMode
  | .resultSoftcutType expected => checkedResultMode (encodeTerm expected)

@[simp] theorem encodeResultMode_closedSkeleton (mode : ResultMode) :
    patternClosedSkeleton (encodeResultMode mode) = true := by
  cases mode <;>
    simp [encodeResultMode, uncheckedResultMode, checkedResultMode,
      a, patternClosedSkeleton, patternsClosedSkeleton,
      encodeTerm_closedSkeleton]

@[simp] theorem encodeResultMode_holeSkeleton (mode : ResultMode) :
    patternHoleSkeleton (encodeResultMode mode) = true :=
  patternHoleSkeleton_of_closed (encodeResultMode_closedSkeleton mode)

@[simp] theorem encodeResultMode_occurrenceNames (mode : ResultMode) :
    patternOccurrenceNames (encodeResultMode mode) = [] :=
  patternOccurrenceNames_closed (encodeResultMode_closedSkeleton mode)

@[simp] theorem applyBindings_encodeResultMode
    (bindings : Bindings) (mode : ResultMode) :
    applyBindings bindings (encodeResultMode mode) = encodeResultMode mode :=
  applyBindings_closedSkeleton (encodeResultMode_closedSkeleton mode) bindings

def planPattern (occurrence modes result declaration : Pattern) : Pattern :=
  a "petta-call-guard:plan" [occurrence, modes, result, declaration]
def plansNil : Pattern := a "petta-call-guard:plans-nil"
def plansSnoc (plans plan : Pattern) : Pattern :=
  a "petta-call-guard:plans-snoc" [plans, plan]

def encodePlan (plan : GuardPlan) : Pattern :=
  planPattern (encodeNat plan.declarationOccurrence)
    (encodeArgModes plan.argumentModes) (encodeResultMode plan.resultMode)
    (encodeDeclaration plan.declaration)

def encodePlans (plans : List GuardPlan) : Pattern :=
  plans.foldl (fun encoded plan => plansSnoc encoded (encodePlan plan)) plansNil

@[simp] theorem encodePlans_append_singleton
    (plans : List GuardPlan) (plan : GuardPlan) :
    encodePlans (plans ++ [plan]) =
      plansSnoc (encodePlans plans) (encodePlan plan) := by
  simp [encodePlans, List.foldl_append]

def familyPattern (owner revision head arity plans : Pattern) : Pattern :=
  a "petta-call-guard:family" [owner, revision, head, arity, plans]
def compiledPattern (family : Pattern) : Pattern :=
  a "petta-call-guard:compiled" [family]
def outsideFragmentPattern : Pattern :=
  a "petta-call-guard:outside-fragment"

def encodeFamily (family : CompiledGuardFamily) : Pattern :=
  familyPattern (encodeOwner family.owner) (encodeNat family.revision)
    (encodeName family.head) (encodeNat family.arity) (encodePlans family.plans)

def encodeCompilationResult : CompilationResult → Pattern
  | .compiled family => compiledPattern (encodeFamily family)
  | .outsideFragment => outsideFragmentPattern

/-! ## Typed micro-machine -/

/-- The compiler state exposed by the ordinary presentation.  `arguments` and
`result` are genuine administrative states: they make construction of one
plan visible without changing the completed compiler denotation. -/
inductive CompileLanguageControl where
  | running
      (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
      (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
  | arguments
      (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
      (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
      (inputCursor : List Term) (modes : List ArgMode)
      (accepted : List GuardPlan)
  | result
      (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
      (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
      (modes : List ArgMode) (accepted : List GuardPlan)
  | halted (result : CompilationResult)
deriving DecidableEq, Repr

def compileLanguageStart (owned : OwnedSnapshot) (head : String) (arity : Nat) :
    CompileLanguageControl :=
  .running owned.owner owned.snapshot.revision head arity
    owned.snapshot.declarations []

/-- One small compiler transition.  No branch receives a completed plan from
an environment: modes are compiled and accumulated locally. -/
def compileLanguageStep? : CompileLanguageControl → Option CompileLanguageControl
  | .halted _ => none
  | .running owner revision head arity [] accepted =>
      some (.halted (.compiled ⟨owner, revision, head, arity, accepted⟩))
  | .running owner revision head arity (declaration :: remaining) accepted =>
      if Relevant declaration head arity then
        some (.arguments owner revision head arity declaration remaining
          declaration.inputTypes [] accepted)
      else
        some (.running owner revision head arity remaining accepted)
  | .arguments owner revision head arity declaration remaining [] modes accepted =>
      some (.result owner revision head arity declaration remaining modes accepted)
  | .arguments owner revision head arity declaration remaining
      (expected :: inputs) modes accepted =>
      match compileArgMode expected with
      | none => some (.halted .outsideFragment)
      | some mode =>
          some (.arguments owner revision head arity declaration remaining
            inputs (modes ++ [mode]) accepted)
  | .result owner revision head arity declaration remaining modes accepted =>
      match compileResultMode declaration.outputType with
      | none => some (.halted .outsideFragment)
      | some resultMode =>
          let plan : GuardPlan := {
            declarationOccurrence := declaration.occurrence
            argumentModes := modes
            resultMode := resultMode
            declaration := declaration }
          some (.running owner revision head arity remaining
            (accepted ++ [plan]))

def compileLanguageGSLT : Mettapedia.GSLT.GSLT where
  Term := CompileLanguageControl
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => compileLanguageStep? source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def compileRunning (owner revision head arity remaining accepted : Pattern) :
    Pattern :=
  a "petta-call-guard:compile-running"
    [owner, revision, head, arity, remaining, accepted]

def compileArguments (owner revision head arity declaration remaining
    inputCursor modes accepted : Pattern) : Pattern :=
  a "petta-call-guard:compile-arguments"
    [owner, revision, head, arity, declaration, remaining, inputCursor, modes,
      accepted]

def compileResult (owner revision head arity declaration remaining modes
    accepted : Pattern) : Pattern :=
  a "petta-call-guard:compile-result"
    [owner, revision, head, arity, declaration, remaining, modes, accepted]

def compileHalted (result : Pattern) : Pattern :=
  a "petta-call-guard:compile-halted" [result]

def encodeCompileLanguageControl : CompileLanguageControl → Pattern
  | .running owner revision head arity remaining accepted =>
      compileRunning (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeDeclarations remaining) (encodePlans accepted)
  | .arguments owner revision head arity declaration remaining inputCursor
      modes accepted =>
      compileArguments (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeDeclaration declaration)
        (encodeDeclarations remaining) (encodeTerms inputCursor)
        (encodeArgModes modes) (encodePlans accepted)
  | .result owner revision head arity declaration remaining modes accepted =>
      compileResult (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeDeclaration declaration)
        (encodeDeclarations remaining) (encodeArgModes modes)
        (encodePlans accepted)
  | .halted result => compileHalted (encodeCompilationResult result)

/-! ## Coherent narrow relation environment -/

def decodeNat? : Pattern → Option Nat
  | .apply "petta-call-guard:nat-zero" [] => some 0
  | .apply "petta-call-guard:nat-bit-zero" [value] =>
      (decodeNat? value).map (Nat.bit false)
  | .apply "petta-call-guard:nat-bit-one" [value] =>
      (decodeNat? value).map (Nat.bit true)
  | _ => none

def decodeChar? : Pattern → Option Char
  | .apply "petta-call-guard:char" [value] =>
      (decodeNat? value).map Char.ofNat
  | _ => none

def decodeChars? : Pattern → Option (List Char)
  | .apply "petta-call-guard:chars-nil" [] => some []
  | .apply "petta-call-guard:chars-cons" [head, tail] => do
      let decodedHead ← decodeChar? head
      let decodedTail ← decodeChars? tail
      pure (decodedHead :: decodedTail)
  | _ => none

def decodeName? : Pattern → Option String
  | .apply "petta-call-guard:name" [characters] =>
      (decodeChars? characters).map String.ofList
  | _ => none

mutual
  def decodeTerm? : Pattern → Option Term
    | .apply "petta-call-guard:term-variable" [name] =>
        (decodeName? name).map Term.variable
    | .apply "petta-call-guard:term-number" [lexeme] =>
        (decodeName? lexeme).map Term.number
    | .apply "petta-call-guard:term-string" [value] =>
        (decodeName? value).map Term.string
    | .apply "petta-call-guard:term-atom" [name] =>
        (decodeName? name).map Term.atom
    | .apply "petta-call-guard:term-list" [elements] =>
        (decodeTerms? elements).map Term.list
    | _ => none

  def decodeTerms? : Pattern → Option (List Term)
    | .apply "petta-call-guard:terms-nil" [] => some []
    | .apply "petta-call-guard:terms-cons" [head, tail] => do
        let decodedHead ← decodeTerm? head
        let decodedTail ← decodeTerms? tail
        pure (decodedHead :: decodedTail)
    | _ => none
end

@[simp] theorem decodeNat_encodeNat (value : Nat) :
    decodeNat? (encodeNat value) = some value := by
  induction value using Nat.binaryRec' with
  | zero => rfl
  | bit bit value canonical inductionHypothesis =>
      rw [encodeNat, Nat.binaryRec'_eq _ _ canonical]
      cases bit <;>
        simp only [Bool.false_eq_true, ↓reduceIte, natBitZero, natBitOne, a,
          decodeNat?, Nat.bit_false, Nat.bit_true]
      · simpa only [encodeNat, natBitZero, natBitOne, a, Option.map_some] using
          congrArg (Option.map fun n => 2 * n) inductionHypothesis
      · simpa only [encodeNat, natBitZero, natBitOne, a, Option.map_some] using
          congrArg (Option.map fun n => 2 * n + 1) inductionHypothesis

@[simp] theorem decodeChars_encodeChars (characters : List Char) :
    decodeChars? (encodeChars characters) = some characters := by
  induction characters with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [encodeChars, charsCons, charPattern, a, decodeChars?, decodeChar?,
        decodeNat_encodeNat, Char.ofNat_toNat, inductionHypothesis]

@[simp] theorem decodeName_encodeName (name : String) :
    decodeName? (encodeName name) = some name := by
  simp [encodeName, namePattern, a, decodeName?, String.ofList_toList]

mutual
  @[simp] theorem decodeTerm_encodeTerm (term : Term) :
      decodeTerm? (encodeTerm term) = some term := by
    cases term <;>
      simp [encodeTerm, termVariable, termNumber, termString, termAtom,
        termList, a, decodeTerm?, decodeTerms_encodeTerms]

  @[simp] theorem decodeTerms_encodeTerms (terms : List Term) :
      decodeTerms? (encodeTerms terms) = some terms := by
    cases terms with
    | nil => rfl
    | cons head tail =>
        simp [encodeTerms, termsCons, a, decodeTerms?, decodeTerm_encodeTerm,
          decodeTerms_encodeTerms]
end

theorem encodeName_injective : Function.Injective encodeName := by
  intro left right equal
  have decoded := congrArg decodeName? equal
  simpa using decoded

def notEqualRelation : String := "PeTTaCallGuardNotEqual"
def arityMatchesRelation : String := "PeTTaCallGuardArityMatches"
def arityDiffersRelation : String := "PeTTaCallGuardArityDiffers"
def checkedInputRelation : String := "PeTTaCallGuardCheckedInput"
def openInputRelation : String := "PeTTaCallGuardOpenInput"
def checkedResultRelation : String := "PeTTaCallGuardCheckedResult"
def openResultRelation : String := "PeTTaCallGuardOpenResult"

def argumentModeClass : Pattern → Option (Option ArgMode)
  | pattern => (decodeTerm? pattern).map compileArgMode

def resultModeClass : Pattern → Option (Option ResultMode)
  | pattern => (decodeTerm? pattern).map compileResultMode

def isCheckedArgumentClass : Option (Option ArgMode) → Bool
  | some (some (.evalSoftcutType _)) => true
  | _ => false

def isCheckedResultClass : Option (Option ResultMode) → Bool
  | some (some (.resultSoftcutType _)) => true
  | _ => false

def rowWhen (condition : Bool) (arguments : List Pattern) :
    List (List Pattern) :=
  if condition then [arguments] else []

/-- Canonical local predicates.  Each relation is a deterministic view of its
arguments; supported and unsupported classifications cannot both be returned. -/
def relationEnv : RelationEnv where
  tuples relation arguments :=
    match relation, arguments with
    | relation, [left, right] =>
        if relation = notEqualRelation then
          rowWhen (decide (left ≠ right)) arguments
        else if relation = arityMatchesRelation then
          rowWhen (decide ((decodeTerms? left).map List.length = decodeNat? right))
            arguments
        else if relation = arityDiffersRelation then
          rowWhen (decide ((decodeTerms? left).map List.length ≠ decodeNat? right))
            arguments
        else
          []
    | relation, [expected] =>
        if relation = checkedInputRelation then
          rowWhen (isCheckedArgumentClass (argumentModeClass expected)) arguments
        else if relation = openInputRelation then
          rowWhen (decide (argumentModeClass expected = some none)) arguments
        else if relation = checkedResultRelation then
          rowWhen (isCheckedResultClass (resultModeClass expected)) arguments
        else if relation = openResultRelation then
          rowWhen (decide (resultModeClass expected = some none)) arguments
        else
          []
    | _, _ => []

/-! ## Authored cold-compiler rewrite rules -/

private def runningContext : List (String × TypeExpr) := typed [
  ("owner", "CGOwner"), ("revision", "CGNat"), ("head", "CGName"),
  ("arity", "CGNat"), ("remaining", "CGDeclarations"),
  ("accepted", "CGPlans")]

private def declarationContext : List (String × TypeExpr) :=
  runningContext ++ typed [
    ("occurrence", "CGNat"), ("declarationHead", "CGName"),
    ("inputs", "CGTerms"), ("output", "CGTerm")]

private def argumentContext : List (String × TypeExpr) :=
  declarationContext ++ typed [
    ("inputCursor", "CGTerms"), ("modes", "CGArgModes"),
    ("expected", "CGTerm")]

def finishTransition : RewriteRule := {
  name := "petta-call-guard-compile-finish"
  typeContext := runningContext
  premises := []
  left := compileRunning (v "owner") (v "revision") (v "head") (v "arity")
    declarationsNil (v "accepted")
  right := compileHalted (compiledPattern
    (familyPattern (v "owner") (v "revision") (v "head") (v "arity")
      (v "accepted")))
}

def skipHeadTransition : RewriteRule := {
  name := "petta-call-guard-compile-skip-head"
  typeContext := declarationContext
  premises := [query notEqualRelation [v "declarationHead", v "head"]]
  left := compileRunning (v "owner") (v "revision") (v "head") (v "arity")
    (declarationsCons
      (declarationPattern (v "occurrence") (v "declarationHead")
        (v "inputs") (v "output")) (v "remaining"))
    (v "accepted")
  right := compileRunning (v "owner") (v "revision") (v "head") (v "arity")
    (v "remaining") (v "accepted")
}

/-- The exact authored metavariable context of the `skip-head` transition.
Downstream source-indexed calculi may inspect this equation without exposing
the private context-building abbreviations used by the operational module. -/
@[simp] theorem skipHeadTransition_typeContext :
    skipHeadTransition.typeContext =
      [ ("owner", .base "CGOwner")
      , ("revision", .base "CGNat")
      , ("head", .base "CGName")
      , ("arity", .base "CGNat")
      , ("remaining", .base "CGDeclarations")
      , ("accepted", .base "CGPlans")
      , ("occurrence", .base "CGNat")
      , ("declarationHead", .base "CGName")
      , ("inputs", .base "CGTerms")
      , ("output", .base "CGTerm") ] := by
  rfl

def skipArityTransition : RewriteRule := {
  name := "petta-call-guard-compile-skip-arity"
  typeContext := declarationContext
  premises := [query arityDiffersRelation [v "inputs", v "arity"]]
  left := compileRunning (v "owner") (v "revision")
    (v "declarationHead") (v "arity")
    (declarationsCons
      (declarationPattern (v "occurrence") (v "declarationHead")
        (v "inputs") (v "output")) (v "remaining"))
    (v "accepted")
  right := compileRunning (v "owner") (v "revision")
    (v "declarationHead") (v "arity") (v "remaining") (v "accepted")
}

def beginDeclarationTransition : RewriteRule := {
  name := "petta-call-guard-compile-begin-declaration"
  typeContext := declarationContext
  premises := [query arityMatchesRelation [v "inputs", v "arity"]]
  left := compileRunning (v "owner") (v "revision")
    (v "declarationHead") (v "arity")
    (declarationsCons
      (declarationPattern (v "occurrence") (v "declarationHead")
        (v "inputs") (v "output")) (v "remaining"))
    (v "accepted")
  right := compileArguments (v "owner") (v "revision")
    (v "declarationHead") (v "arity")
    (declarationPattern (v "occurrence") (v "declarationHead")
      (v "inputs") (v "output"))
    (v "remaining") (v "inputs") argModesNil (v "accepted")
}

def argumentsFinishedTransition : RewriteRule := {
  name := "petta-call-guard-compile-arguments-finished"
  typeContext := argumentContext
  premises := []
  left := compileArguments (v "owner") (v "revision") (v "head")
    (v "arity")
    (declarationPattern (v "occurrence") (v "declarationHead")
      (v "inputs") (v "output"))
    (v "remaining") termsNil (v "modes") (v "accepted")
  right := compileResult (v "owner") (v "revision") (v "head")
    (v "arity")
    (declarationPattern (v "occurrence") (v "declarationHead")
      (v "inputs") (v "output"))
    (v "remaining") (v "modes") (v "accepted")
}

def inputStepTransition (name : String) (expected mode : Pattern)
    (premises : List Premise := []) : RewriteRule := {
  name := name
  typeContext := argumentContext
  premises := premises
  left := compileArguments (v "owner") (v "revision") (v "head")
    (v "arity")
    (declarationPattern (v "occurrence") (v "declarationHead")
      (v "inputs") (v "output"))
    (v "remaining") (termsCons expected (v "inputCursor"))
    (v "modes") (v "accepted")
  right := compileArguments (v "owner") (v "revision") (v "head")
    (v "arity")
    (declarationPattern (v "occurrence") (v "declarationHead")
      (v "inputs") (v "output"))
    (v "remaining") (v "inputCursor")
    (argModesSnoc (v "modes") mode) (v "accepted")
}

def rawInputTransition : RewriteRule :=
  inputStepTransition "petta-call-guard-compile-input-raw"
    (encodeTerm atomType) rawArgMode

def undefinedInputTransition : RewriteRule :=
  inputStepTransition "petta-call-guard-compile-input-undefined"
    (encodeTerm undefinedType) uncheckedArgMode

def holeInputTransition : RewriteRule :=
  inputStepTransition "petta-call-guard-compile-input-hole"
    (encodeTerm holeType) uncheckedArgMode

def checkedInputTransition : RewriteRule :=
  inputStepTransition "petta-call-guard-compile-input-checked"
    (v "expected") (checkedArgMode (v "expected"))
    [query checkedInputRelation [v "expected"]]

def openInputTransition : RewriteRule := {
  name := "petta-call-guard-compile-input-open"
  typeContext := argumentContext
  premises := [query openInputRelation [v "expected"]]
  left := compileArguments (v "owner") (v "revision") (v "head")
    (v "arity")
    (declarationPattern (v "occurrence") (v "declarationHead")
      (v "inputs") (v "output"))
    (v "remaining") (termsCons (v "expected") (v "inputCursor"))
    (v "modes") (v "accepted")
  right := compileHalted outsideFragmentPattern
}

def resultStepTransition (name : String) (output resultMode : Pattern)
    (premises : List Premise := []) : RewriteRule := {
  name := name
  typeContext := argumentContext
  premises := premises
  left := compileResult (v "owner") (v "revision") (v "head")
    (v "arity")
    (declarationPattern (v "occurrence") (v "declarationHead")
      (v "inputs") output)
    (v "remaining") (v "modes") (v "accepted")
  right := compileRunning (v "owner") (v "revision") (v "head")
    (v "arity") (v "remaining")
    (plansSnoc (v "accepted")
      (planPattern (v "occurrence") (v "modes") resultMode
        (declarationPattern (v "occurrence") (v "declarationHead")
          (v "inputs") output)))
}

def undefinedResultTransition : RewriteRule :=
  resultStepTransition "petta-call-guard-compile-result-undefined"
    (encodeTerm undefinedType) uncheckedResultMode

def holeResultTransition : RewriteRule :=
  resultStepTransition "petta-call-guard-compile-result-hole"
    (encodeTerm holeType) uncheckedResultMode

def atomResultTransition : RewriteRule :=
  resultStepTransition "petta-call-guard-compile-result-atom"
    (encodeTerm atomType) uncheckedResultMode

def checkedResultTransition : RewriteRule :=
  resultStepTransition "petta-call-guard-compile-result-checked"
    (v "output") (checkedResultMode (v "output"))
    [query checkedResultRelation [v "output"]]

def openResultTransition : RewriteRule := {
  name := "petta-call-guard-compile-result-open"
  typeContext := argumentContext
  premises := [query openResultRelation [v "output"]]
  left := compileResult (v "owner") (v "revision") (v "head")
    (v "arity")
    (declarationPattern (v "occurrence") (v "declarationHead")
      (v "inputs") (v "output"))
    (v "remaining") (v "modes") (v "accepted")
  right := compileHalted outsideFragmentPattern
}

def transitions : List RewriteRule := [
  finishTransition,
  skipHeadTransition,
  skipArityTransition,
  beginDeclarationTransition,
  argumentsFinishedTransition,
  rawInputTransition,
  undefinedInputTransition,
  holeInputTransition,
  checkedInputTransition,
  openInputTransition,
  undefinedResultTransition,
  holeResultTransition,
  atomResultTransition,
  checkedResultTransition,
  openResultTransition]

def terms : List GrammarRule := [
  ctor "petta-call-guard:nat-zero" "CGNat" [],
  ctor "petta-call-guard:nat-bit-zero" "CGNat" [("value", "CGNat")],
  ctor "petta-call-guard:nat-bit-one" "CGNat" [("value", "CGNat")],
  ctor "petta-call-guard:char" "CGChar" [("value", "CGNat")],
  ctor "petta-call-guard:chars-nil" "CGChars" [],
  ctor "petta-call-guard:chars-cons" "CGChars"
    [("head", "CGChar"), ("tail", "CGChars")],
  ctor "petta-call-guard:name" "CGName" [("characters", "CGChars")],
  ctor "petta-call-guard:term-variable" "CGTerm" [("name", "CGName")],
  ctor "petta-call-guard:term-number" "CGTerm" [("lexeme", "CGName")],
  ctor "petta-call-guard:term-string" "CGTerm" [("value", "CGName")],
  ctor "petta-call-guard:term-atom" "CGTerm" [("name", "CGName")],
  ctor "petta-call-guard:term-list" "CGTerm" [("elements", "CGTerms")],
  ctor "petta-call-guard:terms-nil" "CGTerms" [],
  ctor "petta-call-guard:terms-cons" "CGTerms"
    [("head", "CGTerm"), ("tail", "CGTerms")],
  ctor "petta-call-guard:declaration" "CGDeclaration"
    [("occurrence", "CGNat"), ("function", "CGName"),
      ("inputs", "CGTerms"), ("output", "CGTerm")],
  ctor "petta-call-guard:declarations-nil" "CGDeclarations" [],
  ctor "petta-call-guard:declarations-cons" "CGDeclarations"
    [("head", "CGDeclaration"), ("tail", "CGDeclarations")],
  ctor "petta-call-guard:owner" "CGOwner" [("token", "CGNat")],
  ctor "petta-call-guard:arg-raw" "CGArgMode" [],
  ctor "petta-call-guard:arg-unchecked" "CGArgMode" [],
  ctor "petta-call-guard:arg-checked" "CGArgMode" [("expected", "CGTerm")],
  ctor "petta-call-guard:arg-modes-nil" "CGArgModes" [],
  ctor "petta-call-guard:arg-modes-snoc" "CGArgModes"
    [("modes", "CGArgModes"), ("mode", "CGArgMode")],
  ctor "petta-call-guard:result-unchecked" "CGResultMode" [],
  ctor "petta-call-guard:result-checked" "CGResultMode"
    [("expected", "CGTerm")],
  ctor "petta-call-guard:plan" "CGPlan"
    [("occurrence", "CGNat"), ("modes", "CGArgModes"),
      ("result", "CGResultMode"), ("declaration", "CGDeclaration")],
  ctor "petta-call-guard:plans-nil" "CGPlans" [],
  ctor "petta-call-guard:plans-snoc" "CGPlans"
    [("plans", "CGPlans"), ("plan", "CGPlan")],
  ctor "petta-call-guard:family" "CGFamily"
    [("owner", "CGOwner"), ("revision", "CGNat"), ("head", "CGName"),
      ("arity", "CGNat"), ("plans", "CGPlans")],
  ctor "petta-call-guard:compiled" "CGCompilationResult"
    [("family", "CGFamily")],
  ctor "petta-call-guard:outside-fragment" "CGCompilationResult" [],
  ctor "petta-call-guard:compile-running" "CGCompileControl"
    [("owner", "CGOwner"), ("revision", "CGNat"), ("head", "CGName"),
      ("arity", "CGNat"), ("remaining", "CGDeclarations"),
      ("accepted", "CGPlans")] (some .rewrite),
  ctor "petta-call-guard:compile-arguments" "CGCompileControl"
    [("owner", "CGOwner"), ("revision", "CGNat"), ("head", "CGName"),
      ("arity", "CGNat"), ("declaration", "CGDeclaration"),
      ("remaining", "CGDeclarations"), ("inputCursor", "CGTerms"),
      ("modes", "CGArgModes"), ("accepted", "CGPlans")] (some .rewrite),
  ctor "petta-call-guard:compile-result" "CGCompileControl"
    [("owner", "CGOwner"), ("revision", "CGNat"), ("head", "CGName"),
      ("arity", "CGNat"), ("declaration", "CGDeclaration"),
      ("remaining", "CGDeclarations"), ("modes", "CGArgModes"),
      ("accepted", "CGPlans")] (some .rewrite),
  ctor "petta-call-guard:compile-halted" "CGCompileControl"
    [("result", "CGCompilationResult")]
]

/-- The ordinary source presentation consumed by shared LanguageDef/OSLF
transformations. -/
def language : LanguageDef := {
  name := "PeTTaMainlineCallGuardOperational"
  types := [
    "CGNat", "CGChar", "CGChars", "CGName", "CGTerm", "CGTerms",
    "CGDeclaration", "CGDeclarations", "CGOwner", "CGArgMode",
    "CGArgModes", "CGResultMode", "CGPlan", "CGPlans", "CGFamily",
    "CGCompilationResult", "CGCompileControl"]
  terms := terms
  equations := []
  rewrites := transitions
}

theorem language_inventory :
    language.types.length = 17 ∧ language.terms.length = 35 ∧
      language.rewrites.length = 15 := by
  decide

private def declaredTypeNames : List String := [
  "CGNat", "CGChar", "CGChars", "CGName", "CGTerm", "CGTerms",
  "CGDeclaration", "CGDeclarations", "CGOwner", "CGArgMode",
  "CGArgModes", "CGResultMode", "CGPlan", "CGPlans", "CGFamily",
  "CGCompilationResult", "CGCompileControl"]

private theorem language_typeNames_eq :
    language.typeNames = declaredTypeNames := by
  rfl

private def constructorSignatures : List (String × Nat) :=
  terms.map fun declaration => (declaration.label, declaration.params.length)

private theorem terms_constructorSignatures_eq :
    terms.map (fun declaration =>
      (declaration.label, declaration.params.length)) =
      constructorSignatures := by
  rfl

private def constructorLabels : List String :=
  constructorSignatures.map Prod.fst

private theorem terms_constructorLabels_eq :
    terms.map (fun declaration => declaration.label) = constructorLabels := by
  simp [constructorLabels, constructorSignatures, List.map_map]

private theorem terms_labels_nodup :
    (terms.map fun declaration => declaration.label).Nodup := by
  decide +kernel

private theorem validatePatternConstructors_eq_nil_of_signatures
    (context : String) (pattern : Pattern)
    (declared : ∀ reference ∈ pattern.constructorRefs,
      reference ∈ constructorSignatures) :
    LanguageDef.validatePatternConstructors context terms pattern = [] := by
  unfold LanguageDef.validatePatternConstructors
  apply List.flatMap_eq_nil_iff.mpr
  intro reference referenceMembership
  have signatureMembership :
      reference ∈ terms.map (fun declaration =>
        (declaration.label, declaration.params.length)) := by
    rw [terms_constructorSignatures_eq]
    exact declared reference referenceMembership
  obtain ⟨declaration, declarationMembership, declarationSignature⟩ :=
    List.mem_map.mp signatureMembership
  rcases reference with ⟨label, arity⟩
  have labelEquality : declaration.label = label :=
    congrArg Prod.fst declarationSignature
  have arityEquality : declaration.params.length = arity :=
    congrArg Prod.snd declarationSignature
  subst label
  dsimp only
  rw [LanguageDef.filter_terms_by_label_eq_singleton terms declaration
    terms_labels_nodup declarationMembership]
  simp [arityEquality]

private structure RewriteCertificate (rewrite : RewriteRule) : Prop where
  contextTypes : ∀ entry ∈ rewrite.typeContext,
    ∀ name ∈ entry.2.baseNames, name ∈ language.typeNames
  leftDeclared : ∀ reference ∈ rewrite.left.constructorRefs,
    reference ∈ constructorSignatures
  rightDeclared : ∀ reference ∈ rewrite.right.constructorRefs,
    reference ∈ constructorSignatures
  premisesDeclared : ∀ pattern ∈
      rewrite.premises.flatMap LanguageDef.premisePatterns,
    ∀ reference ∈ pattern.constructorRefs,
      reference ∈ constructorSignatures
  allPatternsScoped :
    ([rewrite.left, rewrite.right] ++
      rewrite.premises.flatMap LanguageDef.premisePatterns).all
        Pattern.isWellScoped = true
  fvarsAvoidConstructors : ∀ name ∈
      ((LanguageDef.patternFvarNames [] rewrite.left ++
        LanguageDef.patternFvarNames [] rewrite.right ++
        rewrite.premises.flatMap
          (LanguageDef.premiseFvarNames [])).eraseDups),
    name ∉ constructorLabels
  bindersAvoidConstructors : ∀ name ∈
      ((LanguageDef.patternBinderNames rewrite.left ++
        LanguageDef.patternBinderNames rewrite.right ++
        (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
          LanguageDef.patternBinderNames ++
        rewrite.premises.flatMap
          LanguageDef.premiseForAllParams).eraseDups),
    name ∉ constructorLabels
  contextAvoidsConstructors : ∀ entry ∈ rewrite.typeContext,
    entry.1 ∉ constructorLabels
  rightBound : ∀ name ∈
      (LanguageDef.patternFvarNames [] rewrite.right).eraseDups,
    name ∈ LanguageDef.patternFvarNames [] rewrite.left ++
      rewrite.premises.flatMap
        (LanguageDef.premiseProducedFvarNames [])

private theorem RewriteCertificate.patternsClean
    {rewrite : RewriteRule} (certificate : RewriteCertificate rewrite) :
    LanguageDef.validateRulePatterns s!"rewrite {rewrite.name}"
      constructorLabels rewrite.typeContext rewrite.premises
      rewrite.left rewrite.right = [] := by
  unfold LanguageDef.validateRulePatterns
  simp only [certificate.allPatternsScoped, if_true,
    List.append_eq_nil_iff, true_and]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    simp [certificate.fvarsAvoidConstructors name membership]
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    simp [certificate.bindersAvoidConstructors name membership]
  · apply List.filterMap_eq_nil_iff.mpr
    intro entry membership
    simp [certificate.contextAvoidsConstructors entry membership]
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    have bound := certificate.rightBound name membership
    simp only [List.mem_append] at bound
    rcases bound with leftBound | premiseBound
    · unfold LanguageDef.patternFvarNames at leftBound
      simp only [List.mem_filter] at leftBound
      simp [leftBound.1]
    · simp only [List.mem_flatMap] at premiseBound
      obtain ⟨premise, premiseMembership, nameMembership⟩ := premiseBound
      simp
      intro _ premiseAbsent
      exact (premiseAbsent premise premiseMembership nameMembership).elim

private theorem validateRewrite_eq_nil_of_certificate
    {rewrite : RewriteRule} (certificate : RewriteCertificate rewrite) :
    LanguageDef.validateRewrite language rewrite = [] := by
  unfold LanguageDef.validateRewrite
  simp only [List.append_eq_nil_iff]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · apply List.flatMap_eq_nil_iff.mpr
    intro entry entryMembership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    exact certificate.contextTypes entry entryMembership
  · exact validatePatternConstructors_eq_nil_of_signatures
      _ rewrite.left certificate.leftDeclared
  · exact validatePatternConstructors_eq_nil_of_signatures
      _ rewrite.right certificate.rightDeclared
  · apply List.flatMap_eq_nil_iff.mpr
    intro pattern patternMembership
    exact validatePatternConstructors_eq_nil_of_signatures _ pattern
      (certificate.premisesDeclared pattern patternMembership)
  · change LanguageDef.validateRulePatterns _
      (terms.map fun declaration => declaration.label) _ _ _ _ = []
    rw [terms_constructorLabels_eq]
    exact certificate.patternsClean

private def contextTypesCheck (rewrite : RewriteRule) : Bool :=
  rewrite.typeContext.all fun entry =>
    entry.2.baseNames.all fun name => decide (name ∈ declaredTypeNames)

private def patternDeclaredCheck (pattern : Pattern) : Bool :=
  pattern.constructorRefs.all fun reference =>
    decide (reference ∈ constructorSignatures)

private theorem constructorRefsList_all (patterns : List Pattern)
    (predicate : String × Nat → Bool) :
    (Pattern.constructorRefsList patterns).all predicate =
      patterns.all fun pattern => pattern.constructorRefs.all predicate := by
  induction patterns with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [Pattern.constructorRefsList, List.all_append,
        inductionHypothesis]

@[simp] private theorem patternDeclaredCheck_fvar (name : String) :
    patternDeclaredCheck (.fvar name) = true := by
  rfl

@[simp] private theorem patternDeclaredCheck_apply
    (label : String) (arguments : List Pattern)
    (notZip : label ≠ Pattern.zipHead)
    (notMap : label ≠ Pattern.mapHead)
    (notEval : label ≠ Pattern.evalHead) :
    patternDeclaredCheck (.apply label arguments) =
      (decide ((label, arguments.length) ∈ constructorSignatures) &&
        arguments.all patternDeclaredCheck) := by
  unfold patternDeclaredCheck
  simp only [Pattern.constructorRefs]
  split <;>
    simp_all [Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
      constructorRefsList_all]

/-! The ground data encoder is used inside several rewrite rules.  Proving its
structural facts once keeps rule validation proportional to the rule skeleton,
rather than repeatedly normalizing every bit of a literal name. -/

@[simp] private theorem patternDeclaredCheck_natZero :
    patternDeclaredCheck natZero = true := by
  simp [patternDeclaredCheck, natZero, a, Pattern.constructorRefs,
    Pattern.constructorRefsList, constructorSignatures, terms, ctor]

@[simp] private theorem patternDeclaredCheck_natBitZero (pattern : Pattern) :
    patternDeclaredCheck (natBitZero pattern) =
      patternDeclaredCheck pattern := by
  simp [patternDeclaredCheck, natBitZero, a, Pattern.constructorRefs,
    Pattern.constructorRefsList, constructorSignatures, terms, ctor]

@[simp] private theorem patternDeclaredCheck_natBitOne (pattern : Pattern) :
    patternDeclaredCheck (natBitOne pattern) =
      patternDeclaredCheck pattern := by
  simp [patternDeclaredCheck, natBitOne, a, Pattern.constructorRefs,
    Pattern.constructorRefsList, constructorSignatures, terms, ctor]

@[simp] private theorem patternDeclaredCheck_charPattern (pattern : Pattern) :
    patternDeclaredCheck (charPattern pattern) =
      patternDeclaredCheck pattern := by
  simp [patternDeclaredCheck, charPattern, a, Pattern.constructorRefs,
    Pattern.constructorRefsList, constructorSignatures, terms, ctor]

@[simp] private theorem patternDeclaredCheck_charsNil :
    patternDeclaredCheck charsNil = true := by
  simp [patternDeclaredCheck, charsNil, a, Pattern.constructorRefs,
    Pattern.constructorRefsList, constructorSignatures, terms, ctor]

@[simp] private theorem patternDeclaredCheck_charsCons
    (head tail : Pattern) :
    patternDeclaredCheck (charsCons head tail) =
      (patternDeclaredCheck head && patternDeclaredCheck tail) := by
  simp [patternDeclaredCheck, charsCons, a, Pattern.constructorRefs,
    Pattern.constructorRefsList, constructorSignatures, terms, ctor,
    List.all_append]

@[simp] private theorem patternDeclaredCheck_namePattern (pattern : Pattern) :
    patternDeclaredCheck (namePattern pattern) =
      patternDeclaredCheck pattern := by
  simp [patternDeclaredCheck, namePattern, a, Pattern.constructorRefs,
    Pattern.constructorRefsList, constructorSignatures, terms, ctor]

@[simp] private theorem patternDeclaredCheck_termAtom (pattern : Pattern) :
    patternDeclaredCheck (termAtom pattern) =
      patternDeclaredCheck pattern := by
  simp [patternDeclaredCheck, termAtom, a, Pattern.constructorRefs,
    Pattern.constructorRefsList, constructorSignatures, terms, ctor]

@[simp] private theorem patternDeclaredCheck_encodeNat (value : Nat) :
    patternDeclaredCheck (encodeNat value) = true := by
  induction value using Nat.binaryRec' with
  | zero => simp [encodeNat]
  | bit bit value canonical inductionHypothesis =>
      rw [encodeNat, Nat.binaryRec'_eq _ _ canonical]
      cases bit <;> simpa only [Bool.false_eq_true, ↓reduceIte,
        patternDeclaredCheck_natBitZero, patternDeclaredCheck_natBitOne,
        encodeNat] using inductionHypothesis

@[simp] private theorem patternDeclaredCheck_encodeChars
    (characters : List Char) :
    patternDeclaredCheck (encodeChars characters) = true := by
  induction characters with
  | nil => simp [encodeChars]
  | cons head tail inductionHypothesis =>
      simp [encodeChars, inductionHypothesis]

@[simp] private theorem patternDeclaredCheck_encodeName (name : String) :
    patternDeclaredCheck (encodeName name) = true := by
  simp [encodeName]

@[simp] private theorem patternDeclaredCheck_encodeAtom (name : String) :
    patternDeclaredCheck (encodeTerm (.atom name)) = true := by
  simp [encodeTerm]

@[simp] private theorem freeFvarNames_natBitZero (pattern : Pattern) :
    (natBitZero pattern).freeFvarNames = pattern.freeFvarNames := by
  simp [natBitZero, a, Pattern.freeFvarNames]

@[simp] private theorem freeFvarNames_natBitOne (pattern : Pattern) :
    (natBitOne pattern).freeFvarNames = pattern.freeFvarNames := by
  simp [natBitOne, a, Pattern.freeFvarNames]

@[simp] private theorem binderNames_natBitZero (pattern : Pattern) :
    LanguageDef.patternBinderNames (natBitZero pattern) =
      LanguageDef.patternBinderNames pattern := by
  simp [natBitZero, a, LanguageDef.patternBinderNames]

@[simp] private theorem binderNames_natBitOne (pattern : Pattern) :
    LanguageDef.patternBinderNames (natBitOne pattern) =
      LanguageDef.patternBinderNames pattern := by
  simp [natBitOne, a, LanguageDef.patternBinderNames]

@[simp] private theorem wellScoped_natBitZero (depth : Nat)
    (pattern : Pattern) :
    Pattern.isWellScopedAt depth (natBitZero pattern) =
      Pattern.isWellScopedAt depth pattern := by
  simp [natBitZero, a, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

@[simp] private theorem wellScoped_natBitOne (depth : Nat)
    (pattern : Pattern) :
    Pattern.isWellScopedAt depth (natBitOne pattern) =
      Pattern.isWellScopedAt depth pattern := by
  simp [natBitOne, a, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

@[simp] private theorem freeFvarNames_encodeNat (value : Nat) :
    (encodeNat value).freeFvarNames = [] := by
  induction value using Nat.binaryRec' with
  | zero => simp [encodeNat, natZero, a, Pattern.freeFvarNames]
  | bit bit value canonical inductionHypothesis =>
      rw [encodeNat, Nat.binaryRec'_eq _ _ canonical]
      have child :
          (Nat.binaryRec' (motive := fun _ => Pattern) natZero
            (fun bit _ _ encoded =>
              if bit then natBitOne encoded else natBitZero encoded)
            value).freeFvarNames = [] := by
        simpa only [encodeNat, natBitZero, natBitOne, a] using
          inductionHypothesis
      cases bit <;>
        simpa only [Bool.false_eq_true, ↓reduceIte,
          freeFvarNames_natBitZero, freeFvarNames_natBitOne] using child

@[simp] private theorem freeFvarNames_encodeChars (characters : List Char) :
    (encodeChars characters).freeFvarNames = [] := by
  induction characters with
  | nil => simp [encodeChars, charsNil, a, Pattern.freeFvarNames]
  | cons head tail inductionHypothesis =>
      simp [encodeChars, charsCons, charPattern, a, Pattern.freeFvarNames,
        inductionHypothesis]

@[simp] private theorem freeFvarNames_encodeName (name : String) :
    (encodeName name).freeFvarNames = [] := by
  simp [encodeName, namePattern, a, Pattern.freeFvarNames]

@[simp] private theorem freeFvarNames_encodeAtom (name : String) :
    (encodeTerm (.atom name)).freeFvarNames = [] := by
  simp [encodeTerm, termAtom, a, Pattern.freeFvarNames]

@[simp] private theorem binderNames_encodeNat (value : Nat) :
    LanguageDef.patternBinderNames (encodeNat value) = [] := by
  induction value using Nat.binaryRec' with
  | zero => simp [encodeNat, natZero, a, LanguageDef.patternBinderNames]
  | bit bit value canonical inductionHypothesis =>
      rw [encodeNat, Nat.binaryRec'_eq _ _ canonical]
      have child :
          LanguageDef.patternBinderNames
            (Nat.binaryRec' (motive := fun _ => Pattern) natZero
              (fun bit _ _ encoded =>
                if bit then natBitOne encoded else natBitZero encoded)
              value) = [] := by
        simpa only [encodeNat, natBitZero, natBitOne, a] using
          inductionHypothesis
      cases bit <;>
        simpa only [Bool.false_eq_true, ↓reduceIte,
          binderNames_natBitZero, binderNames_natBitOne] using child

@[simp] private theorem binderNames_encodeChars (characters : List Char) :
    LanguageDef.patternBinderNames (encodeChars characters) = [] := by
  induction characters with
  | nil => simp [encodeChars, charsNil, a, LanguageDef.patternBinderNames]
  | cons head tail inductionHypothesis =>
      simp [encodeChars, charsCons, charPattern, a,
        LanguageDef.patternBinderNames, inductionHypothesis]

@[simp] private theorem binderNames_encodeName (name : String) :
    LanguageDef.patternBinderNames (encodeName name) = [] := by
  simp [encodeName, namePattern, a, LanguageDef.patternBinderNames]

@[simp] private theorem binderNames_encodeAtom (name : String) :
    LanguageDef.patternBinderNames (encodeTerm (.atom name)) = [] := by
  simp [encodeTerm, termAtom, a, LanguageDef.patternBinderNames]

@[simp] private theorem wellScoped_encodeNat (depth value : Nat) :
    Pattern.isWellScopedAt depth (encodeNat value) = true := by
  induction value using Nat.binaryRec' with
  | zero =>
      simp [encodeNat, natZero, a, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt]
  | bit bit value canonical inductionHypothesis =>
      rw [encodeNat, Nat.binaryRec'_eq _ _ canonical]
      have child :
          Pattern.isWellScopedAt depth
            (Nat.binaryRec' (motive := fun _ => Pattern) natZero
              (fun bit _ _ encoded =>
                if bit then natBitOne encoded else natBitZero encoded)
              value) = true := by
        simpa only [encodeNat, natBitZero, natBitOne, a] using
          inductionHypothesis
      cases bit <;>
        simpa only [Bool.false_eq_true, ↓reduceIte,
          wellScoped_natBitZero, wellScoped_natBitOne] using child

@[simp] private theorem wellScoped_encodeChars (depth : Nat)
    (characters : List Char) :
    Pattern.isWellScopedAt depth (encodeChars characters) = true := by
  induction characters with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [encodeChars, charsCons, charPattern, a, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt, inductionHypothesis]

@[simp] private theorem wellScoped_encodeName (depth : Nat) (name : String) :
    Pattern.isWellScopedAt depth (encodeName name) = true := by
  simp [encodeName, namePattern, a, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

@[simp] private theorem wellScoped_encodeAtom (depth : Nat) (name : String) :
    Pattern.isWellScopedAt depth (encodeTerm (.atom name)) = true := by
  simp [encodeTerm, termAtom, a, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

private def premisesDeclaredCheck (rewrite : RewriteRule) : Bool :=
  (rewrite.premises.flatMap LanguageDef.premisePatterns).all
    patternDeclaredCheck

private def allPatternsScopedCheck (rewrite : RewriteRule) : Bool :=
  ([rewrite.left, rewrite.right] ++
    rewrite.premises.flatMap LanguageDef.premisePatterns).all
      Pattern.isWellScoped

private def fvarsAvoidConstructorsCheck (rewrite : RewriteRule) : Bool :=
  ((LanguageDef.patternFvarNames [] rewrite.left ++
    LanguageDef.patternFvarNames [] rewrite.right ++
    rewrite.premises.flatMap
      (LanguageDef.premiseFvarNames [])).eraseDups).all fun name =>
    decide (name ∉ constructorLabels)

private def bindersAvoidConstructorsCheck (rewrite : RewriteRule) : Bool :=
  ((LanguageDef.patternBinderNames rewrite.left ++
    LanguageDef.patternBinderNames rewrite.right ++
    (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
      LanguageDef.patternBinderNames ++
    rewrite.premises.flatMap
      LanguageDef.premiseForAllParams).eraseDups).all fun name =>
    decide (name ∉ constructorLabels)

private def contextAvoidsConstructorsCheck (rewrite : RewriteRule) : Bool :=
  rewrite.typeContext.all fun entry => decide (entry.1 ∉ constructorLabels)

private def rightBoundCheck (rewrite : RewriteRule) : Bool :=
  let supplied := LanguageDef.patternFvarNames [] rewrite.left ++
    rewrite.premises.flatMap (LanguageDef.premiseProducedFvarNames [])
  (LanguageDef.patternFvarNames [] rewrite.right).eraseDups.all fun name =>
    decide (name ∈ supplied)

private def rewriteCertificateCheck (rewrite : RewriteRule) : Bool :=
  contextTypesCheck rewrite &&
    (patternDeclaredCheck rewrite.left &&
      (patternDeclaredCheck rewrite.right &&
        (premisesDeclaredCheck rewrite &&
          (allPatternsScopedCheck rewrite &&
            (fvarsAvoidConstructorsCheck rewrite &&
              (bindersAvoidConstructorsCheck rewrite &&
                (contextAvoidsConstructorsCheck rewrite &&
                  rightBoundCheck rewrite)))))))

private theorem rewriteCertificate_of_check
    {rewrite : RewriteRule} (check : rewriteCertificateCheck rewrite = true) :
    RewriteCertificate rewrite := by
  simp only [rewriteCertificateCheck, Bool.and_eq_true] at check
  rcases check with
    ⟨contextCheck, leftCheck, rightCheck, premisesCheck, scopedCheck,
      fvarsCheck, bindersCheck, contextNamesCheck, rightBoundedCheck⟩
  refine {
    contextTypes := ?_
    leftDeclared := ?_
    rightDeclared := ?_
    premisesDeclared := ?_
    allPatternsScoped := scopedCheck
    fvarsAvoidConstructors := ?_
    bindersAvoidConstructors := ?_
    contextAvoidsConstructors := ?_
    rightBound := ?_ }
  · intro entry entryMembership name nameMembership
    rw [language_typeNames_eq]
    exact decide_eq_true_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp contextCheck entry entryMembership)
      name nameMembership)
  · intro reference referenceMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp leftCheck reference referenceMembership)
  · intro reference referenceMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp rightCheck reference referenceMembership)
  · intro pattern patternMembership reference referenceMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp
        (List.all_eq_true.mp premisesCheck pattern patternMembership)
        reference referenceMembership)
  · intro name nameMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp fvarsCheck name nameMembership)
  · intro name nameMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp bindersCheck name nameMembership)
  · intro entry entryMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp contextNamesCheck entry entryMembership)
  · intro name nameMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp rightBoundedCheck name nameMembership)

local macro "certify_transition" rule:Lean.Parser.Tactic.simpLemma : tactic =>
  `(tactic| simp [rewriteCertificateCheck, contextTypesCheck,
    premisesDeclaredCheck, allPatternsScopedCheck,
    fvarsAvoidConstructorsCheck, bindersAvoidConstructorsCheck,
    contextAvoidsConstructorsCheck, rightBoundCheck, declaredTypeNames,
    constructorSignatures, constructorLabels, terms, runningContext,
    declarationContext, argumentContext, typed, ctor, query, $rule,
    inputStepTransition, resultStepTransition, compileRunning,
    compileArguments, compileResult, compileHalted, declarationsNil,
    declarationsCons, declarationPattern, termsNil, termsCons, argModesNil,
    argModesSnoc, rawArgMode, uncheckedArgMode, checkedArgMode,
    uncheckedResultMode, checkedResultMode, plansSnoc, planPattern,
    compiledPattern, familyPattern, outsideFragmentPattern,
    atomType, undefinedType, holeType,
    a, v,
    LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
    LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
    TypeExpr.baseNames, Pattern.freeFvarNames,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt])

private theorem finishTransition_certified :
    rewriteCertificateCheck finishTransition = true := by
  certify_transition finishTransition

private theorem skipHeadTransition_certified :
    rewriteCertificateCheck skipHeadTransition = true := by
  certify_transition skipHeadTransition

private theorem skipArityTransition_certified :
    rewriteCertificateCheck skipArityTransition = true := by
  certify_transition skipArityTransition

private theorem beginDeclarationTransition_certified :
    rewriteCertificateCheck beginDeclarationTransition = true := by
  certify_transition beginDeclarationTransition

private theorem argumentsFinishedTransition_certified :
    rewriteCertificateCheck argumentsFinishedTransition = true := by
  certify_transition argumentsFinishedTransition

private theorem rawInputTransition_certified :
    rewriteCertificateCheck rawInputTransition = true := by
  certify_transition rawInputTransition

private theorem undefinedInputTransition_certified :
    rewriteCertificateCheck undefinedInputTransition = true := by
  certify_transition undefinedInputTransition

private theorem holeInputTransition_certified :
    rewriteCertificateCheck holeInputTransition = true := by
  certify_transition holeInputTransition

private theorem checkedInputTransition_certified :
    rewriteCertificateCheck checkedInputTransition = true := by
  certify_transition checkedInputTransition

private theorem openInputTransition_certified :
    rewriteCertificateCheck openInputTransition = true := by
  certify_transition openInputTransition

private theorem undefinedResultTransition_certified :
    rewriteCertificateCheck undefinedResultTransition = true := by
  certify_transition undefinedResultTransition

private theorem holeResultTransition_certified :
    rewriteCertificateCheck holeResultTransition = true := by
  certify_transition holeResultTransition

private theorem atomResultTransition_certified :
    rewriteCertificateCheck atomResultTransition = true := by
  certify_transition atomResultTransition

private theorem checkedResultTransition_certified :
    rewriteCertificateCheck checkedResultTransition = true := by
  certify_transition checkedResultTransition

private theorem openResultTransition_certified :
    rewriteCertificateCheck openResultTransition = true := by
  certify_transition openResultTransition

private theorem transitions_certified :
    transitions.all rewriteCertificateCheck = true := by
  simp [transitions, finishTransition_certified, skipHeadTransition_certified,
    skipArityTransition_certified, beginDeclarationTransition_certified,
    argumentsFinishedTransition_certified, rawInputTransition_certified,
    undefinedInputTransition_certified, holeInputTransition_certified,
    checkedInputTransition_certified, openInputTransition_certified,
    undefinedResultTransition_certified, holeResultTransition_certified,
    atomResultTransition_certified, checkedResultTransition_certified,
    openResultTransition_certified]

private def schemaNamesPrivateErrors (rewrite : RewriteRule) : List String :=
  (Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames
    rewrite).filter fun name => decide (name.toList.head? = some '$')

local macro "certify_private_schema" rule:Lean.Parser.Tactic.simpLemma : tactic =>
  `(tactic| simp [schemaNamesPrivateErrors,
    Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames,
    $rule, inputStepTransition, resultStepTransition, compileRunning,
    compileArguments, compileResult, compileHalted, declarationsNil,
    declarationsCons, declarationPattern, termsNil, termsCons, argModesNil,
    argModesSnoc, rawArgMode, uncheckedArgMode, checkedArgMode,
    uncheckedResultMode, checkedResultMode, plansSnoc, planPattern,
    compiledPattern, familyPattern, outsideFragmentPattern,
    atomType, undefinedType, holeType, runningContext, declarationContext,
    argumentContext, typed, query, a, v,
    LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
    LanguageDef.premiseForAllParams, Pattern.freeFvarNames]
    <;> aesop)

private theorem finishTransition_privateSchema :
    schemaNamesPrivateErrors finishTransition = [] := by
  certify_private_schema finishTransition

private theorem skipHeadTransition_privateSchema :
    schemaNamesPrivateErrors skipHeadTransition = [] := by
  certify_private_schema skipHeadTransition

private theorem skipArityTransition_privateSchema :
    schemaNamesPrivateErrors skipArityTransition = [] := by
  certify_private_schema skipArityTransition

private theorem beginDeclarationTransition_privateSchema :
    schemaNamesPrivateErrors beginDeclarationTransition = [] := by
  certify_private_schema beginDeclarationTransition

private theorem argumentsFinishedTransition_privateSchema :
    schemaNamesPrivateErrors argumentsFinishedTransition = [] := by
  certify_private_schema argumentsFinishedTransition

private theorem rawInputTransition_privateSchema :
    schemaNamesPrivateErrors rawInputTransition = [] := by
  certify_private_schema rawInputTransition

private theorem undefinedInputTransition_privateSchema :
    schemaNamesPrivateErrors undefinedInputTransition = [] := by
  certify_private_schema undefinedInputTransition

private theorem holeInputTransition_privateSchema :
    schemaNamesPrivateErrors holeInputTransition = [] := by
  certify_private_schema holeInputTransition

private theorem checkedInputTransition_privateSchema :
    schemaNamesPrivateErrors checkedInputTransition = [] := by
  certify_private_schema checkedInputTransition

private theorem openInputTransition_privateSchema :
    schemaNamesPrivateErrors openInputTransition = [] := by
  certify_private_schema openInputTransition

private theorem undefinedResultTransition_privateSchema :
    schemaNamesPrivateErrors undefinedResultTransition = [] := by
  certify_private_schema undefinedResultTransition

private theorem holeResultTransition_privateSchema :
    schemaNamesPrivateErrors holeResultTransition = [] := by
  certify_private_schema holeResultTransition

private theorem atomResultTransition_privateSchema :
    schemaNamesPrivateErrors atomResultTransition = [] := by
  certify_private_schema atomResultTransition

private theorem checkedResultTransition_privateSchema :
    schemaNamesPrivateErrors checkedResultTransition = [] := by
  certify_private_schema checkedResultTransition

private theorem openResultTransition_privateSchema :
    schemaNamesPrivateErrors openResultTransition = [] := by
  certify_private_schema openResultTransition

private theorem not_generatedPrefix_of_privateErrors
    (rewrite : RewriteRule) (errors : schemaNamesPrivateErrors rewrite = []) :
    ∀ name ∈
      Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames
        rewrite,
      name.toList.head? ≠ some '$' := by
  intro name nameMembership equality
  have absent := (List.filter_eq_nil_iff.mp errors) name nameMembership
  exact absent (decide_eq_true_eq.mpr equality)

/-- Authored schema names stay outside the private generated-calculus
namespace.  This makes later signature extension capture-freedom a structural
fact rather than a repeated whole-validator computation. -/
theorem transition_schemaNames_not_generatedPrefix (rewrite : RewriteRule)
    (membership : rewrite ∈ language.rewrites) :
    ∀ name ∈
      Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames
        rewrite,
      name.toList.head? ≠ some '$' := by
  change rewrite ∈ transitions at membership
  simp only [transitions, List.mem_cons, List.mem_nil_iff, or_false]
    at membership
  rcases membership with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  · exact not_generatedPrefix_of_privateErrors _
      finishTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _
      skipHeadTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _
      skipArityTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _
      beginDeclarationTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _
      argumentsFinishedTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _ rawInputTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _
      undefinedInputTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _ holeInputTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _
      checkedInputTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _ openInputTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _
      undefinedResultTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _ holeResultTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _ atomResultTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _
      checkedResultTransition_privateSchema
  · exact not_generatedPrefix_of_privateErrors _ openResultTransition_privateSchema

/-- Every authored cold-compiler transition carries the shared structural
rewrite certificate.  This is the reusable validation boundary for later
capture-free signature extensions; clients need not unfold the source
presentation's binary literal encodings again. -/
theorem transition_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ language.rewrites) :
    Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate.Certificate
      language rewrite := by
  change rewrite ∈ transitions at membership
  have checked := List.all_eq_true.mp transitions_certified rewrite membership
  have certificate := rewriteCertificate_of_check checked
  exact {
    contextTypes := certificate.contextTypes
    leftDeclared := by
      intro reference referenceMembership
      simpa only [
        Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate.constructorSignatures,
        constructorSignatures, language] using
        certificate.leftDeclared reference referenceMembership
    rightDeclared := by
      intro reference referenceMembership
      simpa only [
        Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate.constructorSignatures,
        constructorSignatures, language] using
        certificate.rightDeclared reference referenceMembership
    premisesDeclared := by
      intro pattern patternMembership reference referenceMembership
      simpa only [
        Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate.constructorSignatures,
        constructorSignatures, language] using
        certificate.premisesDeclared pattern patternMembership reference
          referenceMembership
    allPatternsScoped := certificate.allPatternsScoped
    fvarsAvoidConstructors := by
      intro name nameMembership
      change name ∉ terms.map (fun declaration => declaration.label)
      rw [terms_constructorLabels_eq]
      exact certificate.fvarsAvoidConstructors name nameMembership
    bindersAvoidConstructors := by
      intro name nameMembership
      change name ∉ terms.map (fun declaration => declaration.label)
      rw [terms_constructorLabels_eq]
      exact certificate.bindersAvoidConstructors name nameMembership
    contextAvoidsConstructors := by
      intro entry entryMembership
      change entry.1 ∉ terms.map (fun declaration => declaration.label)
      rw [terms_constructorLabels_eq]
      exact certificate.contextAvoidsConstructors entry entryMembership
    rightBound := certificate.rightBound }

private theorem rewrites_validate :
    ∀ rewrite ∈ language.rewrites,
      LanguageDef.validateRewrite language rewrite = [] := by
  intro rewrite membership
  change rewrite ∈ transitions at membership
  have checked := List.all_eq_true.mp transitions_certified rewrite membership
  exact validateRewrite_eq_nil_of_certificate
    (rewriteCertificate_of_check checked)

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  exact rewrites_validate

#print axioms language_validate

/-- Every cold-compiler rule has only root-local premises, so contextual
closure adds no transition beyond the authored root executor. -/
theorem language_rules_noncontextual :
    ∀ rule, rule ∈ language.rewrites →
      Mettapedia.OSLF.MeTTaIL.ContextualStep.NoncontextualPremises
        rule.premises := by
  intro rule ruleMember
  change rule ∈ transitions at ruleMember
  simp only [transitions, List.mem_cons, List.mem_nil_iff, or_false]
    at ruleMember
  rcases ruleMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  all_goals first | exact .nil | exact .relationQuery .nil

private theorem rootStep_iff_mem_executor (source target : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.RootStep relationEnv language
        source target ↔
      target ∈ rewriteStepWithPremisesUsing relationEnv language source := by
  simp [Mettapedia.OSLF.MeTTaIL.ContextualStep.RootStep,
    rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing]

/-- The least one-step relation is exactly the root executor because every
authored guard-compiler premise is a local relation query. -/
theorem language_step_iff_mem_executor (source target : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        source target ↔
      target ∈ rewriteStepWithPremisesUsing relationEnv language source := by
  unfold Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
  rw [Mettapedia.OSLF.MeTTaIL.ContextualStep.step_iff_rootStep_of_noncontextualRules
    language_rules_noncontextual]
  exact rootStep_iff_mem_executor source target

/-- The least compiler-language step is exactly one authored root-rule
application.  This proof-facing form supports rule-local inversion without
normalizing the complete executable rule list. -/
theorem language_step_iff_rootStep (source target : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        source target ↔
      Mettapedia.OSLF.MeTTaIL.ContextualStep.RootStep relationEnv language
        source target := by
  unfold Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
  exact Mettapedia.OSLF.MeTTaIL.ContextualStep.step_iff_rootStep_of_noncontextualRules
    language_rules_noncontextual

theorem language_finish_step_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    rewriteStepWithPremisesUsing relationEnv language
        (encodeCompileLanguageControl
          (.running owner revision head arity [] accepted)) =
      [encodeCompileLanguageControl
        (.halted (.compiled ⟨owner, revision, head, arity, accepted⟩))] := by
  simp [rewriteStepWithPremisesUsing, language, transitions,
    applyRuleWithPremisesUsing, applyPremisesWithEnv,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic,
    finishTransition, skipHeadTransition, skipArityTransition,
    beginDeclarationTransition, argumentsFinishedTransition,
    rawInputTransition, undefinedInputTransition, holeInputTransition,
    checkedInputTransition, openInputTransition,
    undefinedResultTransition, holeResultTransition, atomResultTransition,
    checkedResultTransition, openResultTransition,
    inputStepTransition, resultStepTransition,
    encodeCompileLanguageControl, compileRunning, compileArguments,
    compileResult, compileHalted, encodeCompilationResult, encodeFamily,
    familyPattern, compiledPattern, encodeDeclarations, declarationsNil,
    declarationsCons, a, v, applyBindings,
    matchPattern, matchArgs, mergeBindings]

#print axioms language_finish_step_exact

theorem language_finish_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.running owner revision head arity [] accepted))
        (encodeCompileLanguageControl
          (.halted (.compiled ⟨owner, revision, head, arity, accepted⟩))) := by
  rw [Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing_iff_execUsing]
  refine ⟨1, ?_⟩
  rw [Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt_one_eq_rewriteStepWithPremisesUsing]
  rw [language_finish_step_exact]
  simp

#print axioms language_finish_step

@[simp] theorem relationEnv_notEqual_encodeName (left right : String) :
    relationEnv.tuples notEqualRelation [encodeName left, encodeName right] =
      if left = right then []
      else [[encodeName left, encodeName right]] := by
  by_cases equal : left = right
  · subst right
    simp [relationEnv, notEqualRelation, rowWhen]
  · have encodedDifferent : encodeName left ≠ encodeName right := by
      intro encodedEqual
      exact equal (encodeName_injective encodedEqual)
    simp [relationEnv, notEqualRelation, rowWhen, equal, encodedDifferent]

@[simp] theorem relationEnv_arityMatches_encoded
    (inputs : List Term) (arity : Nat) :
    relationEnv.tuples arityMatchesRelation
        [encodeTerms inputs, encodeNat arity] =
      if inputs.length = arity then
        [[encodeTerms inputs, encodeNat arity]]
      else [] := by
  by_cases sameArity : inputs.length = arity <;>
    simp [relationEnv, arityMatchesRelation, notEqualRelation, rowWhen,
      sameArity]

@[simp] theorem relationEnv_arityDiffers_encoded
    (inputs : List Term) (arity : Nat) :
    relationEnv.tuples arityDiffersRelation
        [encodeTerms inputs, encodeNat arity] =
      if inputs.length ≠ arity then
        [[encodeTerms inputs, encodeNat arity]]
      else [] := by
  by_cases differs : inputs.length ≠ arity <;>
    simp [relationEnv, arityDiffersRelation, arityMatchesRelation,
      notEqualRelation, rowWhen, differs]

theorem relationEnv_checkedInput_encoded
    (expected : Term)
    (compiled : compileArgMode expected = some (.evalSoftcutType expected)) :
    [encodeTerm expected] ∈
      relationEnv.tuples checkedInputRelation [encodeTerm expected] := by
  simp [relationEnv, checkedInputRelation, openInputRelation,
    checkedResultRelation, openResultRelation, notEqualRelation,
    arityMatchesRelation, arityDiffersRelation, argumentModeClass,
    isCheckedArgumentClass, rowWhen, compiled]

theorem relationEnv_openInput_encoded
    (expected : Term) (compiled : compileArgMode expected = none) :
    [encodeTerm expected] ∈
      relationEnv.tuples openInputRelation [encodeTerm expected] := by
  simp [relationEnv, checkedInputRelation, openInputRelation,
    checkedResultRelation, openResultRelation, notEqualRelation,
    arityMatchesRelation, arityDiffersRelation, argumentModeClass,
    rowWhen, compiled]

theorem relationEnv_checkedResult_encoded
    (expected : Term)
    (compiled :
      compileResultMode expected = some (.resultSoftcutType expected)) :
    [encodeTerm expected] ∈
      relationEnv.tuples checkedResultRelation [encodeTerm expected] := by
  simp [relationEnv, checkedInputRelation, openInputRelation,
    checkedResultRelation, openResultRelation, notEqualRelation,
    arityMatchesRelation, arityDiffersRelation, resultModeClass,
    isCheckedResultClass, rowWhen, compiled]

theorem relationEnv_openResult_encoded
    (expected : Term) (compiled : compileResultMode expected = none) :
    [encodeTerm expected] ∈
      relationEnv.tuples openResultRelation [encodeTerm expected] := by
  simp [relationEnv, checkedInputRelation, openInputRelation,
    checkedResultRelation, openResultRelation, notEqualRelation,
    arityMatchesRelation, arityDiffersRelation, resultModeClass,
    rowWhen, compiled]

private def runningDeclarationAmbient
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted : Pattern) : Bindings := [
  ("owner", owner), ("revision", revision), ("head", head),
  ("arity", arity), ("occurrence", occurrence),
  ("declarationHead", declarationHead), ("inputs", inputs),
  ("output", output), ("remaining", remaining), ("accepted", accepted)]

private def runningDeclarationNames : List String :=
  ["owner", "revision", "head", "arity", "occurrence",
    "declarationHead", "inputs", "output", "remaining", "accepted"]

private theorem skipHead_left_holeSkeleton :
    patternHoleSkeleton skipHeadTransition.left = true := by
  simp [skipHeadTransition, compileRunning, declarationsCons,
    declarationPattern, a, v, patternHoleSkeleton, patternsHoleSkeleton]

private theorem skipHead_left_occurrenceNames :
    patternOccurrenceNames skipHeadTransition.left =
      runningDeclarationNames := by
  simp [skipHeadTransition, compileRunning, declarationsCons,
    declarationPattern, a, v, patternOccurrenceNames,
    runningDeclarationNames,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]

private theorem apply_runningDeclarationAmbient_skipHead_left
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted : Pattern) :
    applyBindings
        (runningDeclarationAmbient owner revision head arity occurrence
          declarationHead inputs output remaining accepted)
        skipHeadTransition.left =
      compileRunning owner revision head arity
        (declarationsCons
          (declarationPattern occurrence declarationHead inputs output)
          remaining)
        accepted := by
  simp [runningDeclarationAmbient, skipHeadTransition, compileRunning,
    declarationsCons, declarationPattern, a, v, applyBindings]

private theorem runningDeclarationAmbient_covers_names
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted : Pattern) :
    ∀ name ∈ runningDeclarationNames,
      (Bindings.lookup
        (runningDeclarationAmbient owner revision head arity occurrence
          declarationHead inputs output remaining accepted) name).isSome := by
  intro name nameMember
  unfold runningDeclarationNames at nameMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at nameMember
  rcases nameMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [runningDeclarationAmbient, Bindings.lookup]

private theorem runningDeclarationAmbient_covers_skipHead_left
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted : Pattern) :
    ∀ name ∈ patternOccurrenceNames skipHeadTransition.left,
      (Bindings.lookup
        (runningDeclarationAmbient owner revision head arity occurrence
          declarationHead inputs output remaining accepted) name).isSome := by
  rw [skipHead_left_occurrenceNames]
  exact runningDeclarationAmbient_covers_names owner revision head arity
    occurrence declarationHead inputs output remaining accepted

private theorem match_skipHead_left_own_instance
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted : Pattern) :
    ∃ bindings ∈
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
          language skipHeadTransition
          (compileRunning owner revision head arity
            (declarationsCons
              (declarationPattern occurrence declarationHead inputs output)
              remaining)
            accepted),
      bindingsAgreeWith
          (runningDeclarationAmbient owner revision head arity occurrence
            declarationHead inputs output remaining accepted)
          bindings ∧
        ∀ name ∈ patternOccurrenceNames skipHeadTransition.left,
          (Bindings.lookup bindings name).isSome := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
  rw [← apply_runningDeclarationAmbient_skipHead_left]
  exact matchPattern_own_instance skipHead_left_holeSkeleton
    (runningDeclarationAmbient_covers_skipHead_left owner revision head arity
      occurrence declarationHead inputs output remaining accepted)

private theorem lookup_eq_of_agree
    {ambient bindings : Bindings}
    (agree : bindingsAgreeWith ambient bindings)
    {name : String} {value : Pattern}
    (covered : (Bindings.lookup bindings name).isSome)
    (ambientLookup : Bindings.lookup ambient name = some value) :
    Bindings.lookup bindings name = some value := by
  obtain ⟨found, foundEq⟩ := Option.isSome_iff_exists.mp covered
  have ambientFound := bindingsAgreeWith_lookup agree foundEq
  have valueEq : found = value :=
    Option.some.inj (ambientFound.symm.trans ambientLookup)
  simpa [valueEq] using foundEq

/-- Admit one concrete source transition from a hole-skeleton rule instance.
The matcher may choose any proof-relevant binding order; agreement and
coverage are enough to recover the authored target without normalizing that
order. -/
private theorem language_step_of_ambient
    (rule : RewriteRule)
    (ruleMember : rule ∈ language.rewrites)
    (noncontextual :
      Mettapedia.OSLF.MeTTaIL.ContextualStep.NoncontextualPremises
        rule.premises)
    {ambient : Bindings} {source target : Pattern}
    (leftHole : patternHoleSkeleton rule.left = true)
    (rightHole : patternHoleSkeleton rule.right = true)
    (ambientCover : ∀ name ∈ patternOccurrenceNames rule.left,
      (Bindings.lookup ambient name).isSome)
    (rightNamesFromLeft : ∀ name ∈ patternOccurrenceNames rule.right,
      name ∈ patternOccurrenceNames rule.left)
    (sourceEq : applyBindings ambient rule.left = source)
    (premisesSelf : ∀ bindings,
      bindingsAgreeWith ambient bindings →
      (∀ name ∈ patternOccurrenceNames rule.left,
        (Bindings.lookup bindings name).isSome) →
      bindings ∈ applyPremisesWithEnv relationEnv language
        rule.premises bindings)
    (targetEq : applyBindings ambient rule.right = target) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
      relationEnv language source target := by
  have matchedInstance :
      ∃ bindings ∈
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
            language rule source,
        bindingsAgreeWith ambient bindings ∧
          ∀ name ∈ patternOccurrenceNames rule.left,
            (Bindings.lookup bindings name).isSome := by
    rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    rw [← sourceEq]
    exact matchPattern_own_instance leftHole ambientCover
  obtain ⟨bindings, matched, agree, bindingsCover⟩ := matchedInstance
  have targetAgreement :
      applyBindings bindings rule.right = applyBindings ambient rule.right := by
    apply applyBindings_agree rightHole
    intro name nameMember
    have leftMember := rightNamesFromLeft name nameMember
    obtain ⟨value, ambientLookup⟩ := Option.isSome_iff_exists.mp
      (ambientCover name leftMember)
    have bindingsLookup := lookup_eq_of_agree agree
      (bindingsCover name leftMember) ambientLookup
    exact bindingsLookup.trans ambientLookup.symm
  have appliedTarget :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
          language rule bindings = target := by
    rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
      targetAgreement, targetEq]
  exact Mettapedia.OSLF.MeTTaIL.ContextualStep.step_of_rule ruleMember matched
    noncontextual (premisesSelf bindings agree bindingsCover) appliedTarget

private theorem binaryRelationQuery_self
    (bindings : Bindings) (relation firstName secondName : String)
    (first second : Pattern)
    (firstLookup : Bindings.lookup bindings firstName = some first)
    (secondLookup : Bindings.lookup bindings secondName = some second)
    (row : [first, second] ∈
      relationEnv.tuples relation [first, second]) :
    bindings ∈ applyPremisesWithEnv relationEnv language
      [.relationQuery relation [v firstName, v secondName]] bindings := by
  have engineRow : [first, second] ∈
      relationEnv.tuples relation
        ([v firstName, v secondName].map (applyBindings bindings)) := by
    simpa [v, applyBindings_fvar, firstLookup, secondLookup] using row
  have argumentMatch : ([] : Bindings) ∈
      matchRelationArgs bindings [v firstName, v secondName]
        [first, second] := by
    simp [matchRelationArgs, matchRelationArgument, v, firstLookup,
      secondLookup, mergeBindings]
  have queryResult : bindings ∈
      premiseStepWithEnv relationEnv language bindings
        (.relationQuery relation [v firstName, v secondName]) :=
    Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission.premiseStepWithEnv_relationQuery_of_env_tuple
      engineRow argumentMatch rfl
  simpa [applyPremisesWithEnv] using queryResult

private theorem unaryRelationQuery_self
    (bindings : Bindings) (relation name : String) (value : Pattern)
    (lookup : Bindings.lookup bindings name = some value)
    (row : [value] ∈ relationEnv.tuples relation [value]) :
    bindings ∈ applyPremisesWithEnv relationEnv language
      [.relationQuery relation [v name]] bindings := by
  have engineRow : [value] ∈ relationEnv.tuples relation
      ([v name].map (applyBindings bindings)) := by
    simpa [v, applyBindings_fvar, lookup] using row
  have argumentMatch : ([] : Bindings) ∈
      matchRelationArgs bindings [v name] [value] := by
    simp [matchRelationArgs, matchRelationArgument, v, lookup,
      mergeBindings]
  have queryResult : bindings ∈
      premiseStepWithEnv relationEnv language bindings
        (.relationQuery relation [v name]) :=
    Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission.premiseStepWithEnv_relationQuery_of_env_tuple
      engineRow argumentMatch rfl
  simpa [applyPremisesWithEnv] using queryResult

/-- A non-relevant declaration really takes the authored skip transition in
the generic `LanguageDef` semantics.  This proof constructs matcher and
premise evidence separately; it does not normalize the complete engine. -/
theorem language_skipHead_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (different : declaration.function ≠ head) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.running owner revision head arity (declaration :: remaining)
            accepted))
        (encodeCompileLanguageControl
          (.running owner revision head arity remaining accepted)) := by
  let ambient := runningDeclarationAmbient (encodeOwner owner)
    (encodeNat revision) (encodeName head) (encodeNat arity)
    (encodeNat declaration.occurrence) (encodeName declaration.function)
    (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
    (encodeDeclarations remaining) (encodePlans accepted)
  obtain ⟨bindings, matched, agree, covered⟩ :=
    match_skipHead_left_own_instance (encodeOwner owner)
      (encodeNat revision) (encodeName head) (encodeNat arity)
      (encodeNat declaration.occurrence) (encodeName declaration.function)
      (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
      (encodeDeclarations remaining) (encodePlans accepted)
  have lookupFor : ∀ name ∈ patternOccurrenceNames skipHeadTransition.left,
      ∀ value, Bindings.lookup ambient name = some value →
        Bindings.lookup bindings name = some value := by
    intro name nameMember value ambientLookup
    exact lookup_eq_of_agree agree (covered name nameMember) ambientLookup
  have ownerLookup : Bindings.lookup bindings "owner" =
      some (encodeOwner owner) := by
    apply lookupFor "owner" (by rw [skipHead_left_occurrenceNames]; simp [runningDeclarationNames])
    simp [ambient, runningDeclarationAmbient, Bindings.lookup]
  have revisionLookup : Bindings.lookup bindings "revision" =
      some (encodeNat revision) := by
    apply lookupFor "revision" (by rw [skipHead_left_occurrenceNames]; simp [runningDeclarationNames])
    simp [ambient, runningDeclarationAmbient, Bindings.lookup]
  have headLookup : Bindings.lookup bindings "head" =
      some (encodeName head) := by
    apply lookupFor "head" (by rw [skipHead_left_occurrenceNames]; simp [runningDeclarationNames])
    simp [ambient, runningDeclarationAmbient, Bindings.lookup]
  have arityLookup : Bindings.lookup bindings "arity" =
      some (encodeNat arity) := by
    apply lookupFor "arity" (by rw [skipHead_left_occurrenceNames]; simp [runningDeclarationNames])
    simp [ambient, runningDeclarationAmbient, Bindings.lookup]
  have declarationHeadLookup :
      Bindings.lookup bindings "declarationHead" =
        some (encodeName declaration.function) := by
    apply lookupFor "declarationHead"
      (by rw [skipHead_left_occurrenceNames]; simp [runningDeclarationNames])
    simp [ambient, runningDeclarationAmbient, Bindings.lookup]
  have remainingLookup : Bindings.lookup bindings "remaining" =
      some (encodeDeclarations remaining) := by
    apply lookupFor "remaining" (by rw [skipHead_left_occurrenceNames]; simp [runningDeclarationNames])
    simp [ambient, runningDeclarationAmbient, Bindings.lookup]
  have acceptedLookup : Bindings.lookup bindings "accepted" =
      some (encodePlans accepted) := by
    apply lookupFor "accepted" (by rw [skipHead_left_occurrenceNames]; simp [runningDeclarationNames])
    simp [ambient, runningDeclarationAmbient, Bindings.lookup]
  have queryArguments :
      [v "declarationHead", v "head"].map (applyBindings bindings) =
        [encodeName declaration.function, encodeName head] := by
    simp [v, applyBindings_fvar, declarationHeadLookup, headLookup]
  have row :
      [encodeName declaration.function, encodeName head] ∈
        relationEnv.tuples notEqualRelation
          ([v "declarationHead", v "head"].map
            (applyBindings bindings)) := by
    rw [queryArguments]
    simp [different]
  have argumentMatch : ([] : Bindings) ∈
      matchRelationArgs bindings [v "declarationHead", v "head"]
        [encodeName declaration.function, encodeName head] := by
    simp [matchRelationArgs, matchRelationArgument, v,
      declarationHeadLookup, headLookup, mergeBindings]
  have queryResult : bindings ∈
      premiseStepWithEnv relationEnv language bindings
        (.relationQuery notEqualRelation [v "declarationHead", v "head"]) :=
    Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission.premiseStepWithEnv_relationQuery_of_env_tuple
      row argumentMatch rfl
  have premises : bindings ∈
      applyPremisesWithEnv relationEnv language
        skipHeadTransition.premises bindings := by
    simpa [skipHeadTransition, query, applyPremisesWithEnv] using queryResult
  have targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
          language skipHeadTransition bindings =
        encodeCompileLanguageControl
          (.running owner revision head arity remaining accepted) := by
    rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic]
    unfold skipHeadTransition encodeCompileLanguageControl compileRunning a
    simp only [applyBindings, List.map_cons, List.map_nil,
      applyBindings_fvar]
    rw [ownerLookup, revisionLookup, headLookup, arityLookup,
      remainingLookup, acceptedLookup]
    rfl
  apply Mettapedia.OSLF.MeTTaIL.ContextualStep.step_of_rule
      (rule := skipHeadTransition) (initialBindings := bindings)
      (finalBindings := bindings)
  · change skipHeadTransition ∈ transitions
    simp [transitions]
  · simpa [encodeCompileLanguageControl, encodeDeclaration,
      encodeDeclarations, declarationsCons, declarationPattern] using matched
  · exact .relationQuery .nil
  · exact premises
  · exact targetEq

#print axioms language_skipHead_step

private theorem skipArity_left_holeSkeleton :
    patternHoleSkeleton skipArityTransition.left = true := by
  simp [skipArityTransition, compileRunning, declarationsCons,
    declarationPattern, a, v, patternHoleSkeleton, patternsHoleSkeleton]

private theorem skipArity_right_holeSkeleton :
    patternHoleSkeleton skipArityTransition.right = true := by
  simp [skipArityTransition, compileRunning, a, v, patternHoleSkeleton,
    patternsHoleSkeleton]

private theorem skipArity_left_names_subset :
    ∀ name ∈ patternOccurrenceNames skipArityTransition.left,
      name ∈ runningDeclarationNames := by
  intro name member
  simp [skipArityTransition, compileRunning, declarationsCons,
    declarationPattern, a, v, patternOccurrenceNames,
    runningDeclarationNames,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]
    at member ⊢
  aesop

private theorem skipArity_right_names_from_left :
    ∀ name ∈ patternOccurrenceNames skipArityTransition.right,
      name ∈ patternOccurrenceNames skipArityTransition.left := by
  intro name member
  simp [skipArityTransition, compileRunning, declarationsCons,
    declarationPattern, a, v, patternOccurrenceNames,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]
    at member ⊢
  aesop

private theorem apply_runningDeclarationAmbient_skipArity_left
    (owner revision head arity occurrence inputs output remaining accepted :
      Pattern) :
    applyBindings
        (runningDeclarationAmbient owner revision head arity occurrence head
          inputs output remaining accepted)
        skipArityTransition.left =
      compileRunning owner revision head arity
        (declarationsCons
          (declarationPattern occurrence head inputs output) remaining)
        accepted := by
  simp [runningDeclarationAmbient, skipArityTransition, compileRunning,
    declarationsCons, declarationPattern, a, v, applyBindings]

private theorem apply_runningDeclarationAmbient_skipArity_right
    (owner revision head arity occurrence inputs output remaining accepted :
      Pattern) :
    applyBindings
        (runningDeclarationAmbient owner revision head arity occurrence head
          inputs output remaining accepted)
        skipArityTransition.right =
      compileRunning owner revision head arity remaining accepted := by
  simp [runningDeclarationAmbient, skipArityTransition, compileRunning,
    a, v, applyBindings]

/-- A same-head declaration with the wrong arity takes the distinct authored
skip-arity rule. -/
theorem language_skipArity_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (sameHead : declaration.function = head)
    (differentArity : declaration.inputTypes.length ≠ arity) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.running owner revision head arity (declaration :: remaining)
            accepted))
        (encodeCompileLanguageControl
          (.running owner revision head arity remaining accepted)) := by
  subst head
  let ambient := runningDeclarationAmbient (encodeOwner owner)
    (encodeNat revision) (encodeName declaration.function) (encodeNat arity)
    (encodeNat declaration.occurrence) (encodeName declaration.function)
    (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
    (encodeDeclarations remaining) (encodePlans accepted)
  refine language_step_of_ambient skipArityTransition
    (by change skipArityTransition ∈ transitions; simp [transitions])
    (.relationQuery .nil) (ambient := ambient)
    skipArity_left_holeSkeleton skipArity_right_holeSkeleton ?_
    skipArity_right_names_from_left ?_ ?_ ?_
  · intro name member
    apply runningDeclarationAmbient_covers_names
    exact skipArity_left_names_subset name member
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration,
      encodeDeclarations, declarationsCons, declarationPattern] using
      apply_runningDeclarationAmbient_skipArity_left
        (encodeOwner owner) (encodeNat revision)
        (encodeName declaration.function) (encodeNat arity)
        (encodeNat declaration.occurrence)
        (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
        (encodeDeclarations remaining) (encodePlans accepted)
  · intro bindings agree covered
    have inputsLookup : Bindings.lookup bindings "inputs" =
        some (encodeTerms declaration.inputTypes) := by
      apply lookup_eq_of_agree agree
        (covered "inputs" (by
          simp [skipArityTransition, compileRunning, declarationsCons,
            declarationPattern, a, v, patternOccurrenceNames,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]))
      simp [ambient, runningDeclarationAmbient, Bindings.lookup]
    have arityLookup : Bindings.lookup bindings "arity" =
        some (encodeNat arity) := by
      apply lookup_eq_of_agree agree
        (covered "arity" (by
          simp [skipArityTransition, compileRunning, declarationsCons,
            declarationPattern, a, v, patternOccurrenceNames,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]))
      simp [ambient, runningDeclarationAmbient, Bindings.lookup]
    simpa [skipArityTransition, query] using
      binaryRelationQuery_self bindings arityDiffersRelation "inputs" "arity"
        (encodeTerms declaration.inputTypes) (encodeNat arity)
        inputsLookup arityLookup (by simp [differentArity])
  · simpa [ambient, encodeCompileLanguageControl] using
      apply_runningDeclarationAmbient_skipArity_right
        (encodeOwner owner) (encodeNat revision)
        (encodeName declaration.function) (encodeNat arity)
        (encodeNat declaration.occurrence)
        (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
        (encodeDeclarations remaining) (encodePlans accepted)

#print axioms language_skipArity_step

private theorem beginDeclaration_left_eq_skipArity_left :
    beginDeclarationTransition.left = skipArityTransition.left := rfl

private theorem beginDeclaration_left_holeSkeleton :
    patternHoleSkeleton beginDeclarationTransition.left = true := by
  rw [beginDeclaration_left_eq_skipArity_left]
  exact skipArity_left_holeSkeleton

private theorem beginDeclaration_right_holeSkeleton :
    patternHoleSkeleton beginDeclarationTransition.right = true := by
  simp [beginDeclarationTransition, compileArguments, declarationPattern,
    argModesNil, a, v, patternHoleSkeleton, patternsHoleSkeleton]

private theorem beginDeclaration_left_names_subset :
    ∀ name ∈ patternOccurrenceNames beginDeclarationTransition.left,
      name ∈ runningDeclarationNames := by
  rw [beginDeclaration_left_eq_skipArity_left]
  exact skipArity_left_names_subset

private theorem beginDeclaration_right_names_from_left :
    ∀ name ∈ patternOccurrenceNames beginDeclarationTransition.right,
      name ∈ patternOccurrenceNames beginDeclarationTransition.left := by
  intro name member
  simp [beginDeclarationTransition, compileRunning, compileArguments,
    declarationsCons, declarationPattern, argModesNil, a, v,
    patternOccurrenceNames,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]
    at member ⊢
  aesop

private theorem apply_runningDeclarationAmbient_beginDeclaration_left
    (owner revision head arity occurrence inputs output remaining accepted :
      Pattern) :
    applyBindings
        (runningDeclarationAmbient owner revision head arity occurrence head
          inputs output remaining accepted)
        beginDeclarationTransition.left =
      compileRunning owner revision head arity
        (declarationsCons
          (declarationPattern occurrence head inputs output) remaining)
        accepted := by
  rw [beginDeclaration_left_eq_skipArity_left]
  exact apply_runningDeclarationAmbient_skipArity_left owner revision head arity
    occurrence inputs output remaining accepted

private theorem apply_runningDeclarationAmbient_beginDeclaration_right
    (owner revision head arity occurrence inputs output remaining accepted :
      Pattern) :
    applyBindings
        (runningDeclarationAmbient owner revision head arity occurrence head
          inputs output remaining accepted)
        beginDeclarationTransition.right =
      compileArguments owner revision head arity
        (declarationPattern occurrence head inputs output)
        remaining inputs argModesNil accepted := by
  simp [runningDeclarationAmbient, beginDeclarationTransition,
    compileArguments, declarationPattern, argModesNil, a, v, applyBindings]

/-- A relevant declaration enters the explicit argument-mode compiler with
the authored declaration and input cursors intact. -/
theorem language_beginDeclaration_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (sameHead : declaration.function = head)
    (sameArity : declaration.inputTypes.length = arity) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.running owner revision head arity (declaration :: remaining)
            accepted))
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            declaration.inputTypes [] accepted)) := by
  subst head
  let ambient := runningDeclarationAmbient (encodeOwner owner)
    (encodeNat revision) (encodeName declaration.function) (encodeNat arity)
    (encodeNat declaration.occurrence) (encodeName declaration.function)
    (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
    (encodeDeclarations remaining) (encodePlans accepted)
  refine language_step_of_ambient beginDeclarationTransition
    (by change beginDeclarationTransition ∈ transitions; simp [transitions])
    (.relationQuery .nil) (ambient := ambient)
    beginDeclaration_left_holeSkeleton
    beginDeclaration_right_holeSkeleton ?_
    beginDeclaration_right_names_from_left ?_ ?_ ?_
  · intro name member
    apply runningDeclarationAmbient_covers_names
    exact beginDeclaration_left_names_subset name member
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration,
      encodeDeclarations, declarationsCons, declarationPattern] using
      apply_runningDeclarationAmbient_beginDeclaration_left
        (encodeOwner owner) (encodeNat revision)
        (encodeName declaration.function) (encodeNat arity)
        (encodeNat declaration.occurrence)
        (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
        (encodeDeclarations remaining) (encodePlans accepted)
  · intro bindings agree covered
    have inputsLookup : Bindings.lookup bindings "inputs" =
        some (encodeTerms declaration.inputTypes) := by
      apply lookup_eq_of_agree agree
        (covered "inputs" (by
          rw [beginDeclaration_left_eq_skipArity_left]
          simp [skipArityTransition, compileRunning, declarationsCons,
            declarationPattern, a, v, patternOccurrenceNames,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]))
      simp [ambient, runningDeclarationAmbient, Bindings.lookup]
    have arityLookup : Bindings.lookup bindings "arity" =
        some (encodeNat arity) := by
      apply lookup_eq_of_agree agree
        (covered "arity" (by
          rw [beginDeclaration_left_eq_skipArity_left]
          simp [skipArityTransition, compileRunning, declarationsCons,
            declarationPattern, a, v, patternOccurrenceNames,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]))
      simp [ambient, runningDeclarationAmbient, Bindings.lookup]
    simpa [beginDeclarationTransition, query] using
      binaryRelationQuery_self bindings arityMatchesRelation "inputs" "arity"
        (encodeTerms declaration.inputTypes) (encodeNat arity)
        inputsLookup arityLookup (by simp [sameArity])
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration,
      encodeArgModes] using
      apply_runningDeclarationAmbient_beginDeclaration_right
        (encodeOwner owner) (encodeNat revision)
        (encodeName declaration.function) (encodeNat arity)
        (encodeNat declaration.occurrence)
        (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
        (encodeDeclarations remaining) (encodePlans accepted)

#print axioms language_beginDeclaration_step

private def argumentAmbient
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted inputCursor modes expected : Pattern) : Bindings := [
  ("owner", owner), ("revision", revision), ("head", head),
  ("arity", arity), ("occurrence", occurrence),
  ("declarationHead", declarationHead), ("inputs", inputs),
  ("output", output), ("remaining", remaining), ("accepted", accepted),
  ("inputCursor", inputCursor), ("modes", modes), ("expected", expected)]

private def argumentNames : List String :=
  ["owner", "revision", "head", "arity", "occurrence",
    "declarationHead", "inputs", "output", "remaining", "accepted",
    "inputCursor", "modes", "expected"]

private theorem argumentAmbient_covers_names
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted inputCursor modes expected : Pattern) :
    ∀ name ∈ argumentNames,
      (Bindings.lookup
        (argumentAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted inputCursor modes expected)
        name).isSome := by
  intro name nameMember
  unfold argumentNames at nameMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at nameMember
  rcases nameMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    simp [argumentAmbient, Bindings.lookup]

private theorem argumentsFinished_left_holeSkeleton :
    patternHoleSkeleton argumentsFinishedTransition.left = true := by
  simp [argumentsFinishedTransition, compileArguments, declarationPattern,
    termsNil, a, v, patternHoleSkeleton, patternsHoleSkeleton]

private theorem argumentsFinished_right_holeSkeleton :
    patternHoleSkeleton argumentsFinishedTransition.right = true := by
  simp [argumentsFinishedTransition, compileResult, declarationPattern,
    a, v, patternHoleSkeleton, patternsHoleSkeleton]

private theorem argumentsFinished_left_names_subset :
    ∀ name ∈ patternOccurrenceNames argumentsFinishedTransition.left,
      name ∈ argumentNames := by
  intro name member
  simp [argumentsFinishedTransition, compileArguments, declarationPattern,
    termsNil, a, v, patternOccurrenceNames, argumentNames,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]
    at member ⊢
  aesop

private theorem argumentsFinished_right_names_from_left :
    ∀ name ∈ patternOccurrenceNames argumentsFinishedTransition.right,
      name ∈ patternOccurrenceNames argumentsFinishedTransition.left := by
  intro name member
  simp [argumentsFinishedTransition, compileArguments, compileResult,
    declarationPattern, termsNil, a, v, patternOccurrenceNames,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]
    at member ⊢
  aesop

private theorem apply_argumentAmbient_argumentsFinished_left
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted modes : Pattern) :
    applyBindings
        (argumentAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted termsNil modes termsNil)
        argumentsFinishedTransition.left =
      compileArguments owner revision head arity
        (declarationPattern occurrence declarationHead inputs output)
        remaining termsNil modes accepted := by
  simp [argumentAmbient, argumentsFinishedTransition, compileArguments,
    declarationPattern, termsNil, a, v, applyBindings]

private theorem apply_argumentAmbient_argumentsFinished_right
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted modes : Pattern) :
    applyBindings
        (argumentAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted termsNil modes termsNil)
        argumentsFinishedTransition.right =
      compileResult owner revision head arity
        (declarationPattern occurrence declarationHead inputs output)
        remaining modes accepted := by
  simp [argumentAmbient, argumentsFinishedTransition, compileResult,
    declarationPattern, termsNil, a, v, applyBindings]

theorem language_argumentsFinished_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining [] modes
            accepted))
        (encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted)) := by
  let ambient := argumentAmbient (encodeOwner owner) (encodeNat revision)
    (encodeName head) (encodeNat arity) (encodeNat declaration.occurrence)
    (encodeName declaration.function) (encodeTerms declaration.inputTypes)
    (encodeTerm declaration.outputType) (encodeDeclarations remaining)
    (encodePlans accepted) termsNil (encodeArgModes modes) termsNil
  refine language_step_of_ambient argumentsFinishedTransition
    (by change argumentsFinishedTransition ∈ transitions; simp [transitions])
    .nil (ambient := ambient) argumentsFinished_left_holeSkeleton
    argumentsFinished_right_holeSkeleton ?_
    argumentsFinished_right_names_from_left ?_ ?_ ?_
  · intro name member
    apply argumentAmbient_covers_names
    exact argumentsFinished_left_names_subset name member
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration,
      encodeTerms] using
      apply_argumentAmbient_argumentsFinished_left
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeArgModes modes)
  · intro bindings _ _
    simp [argumentsFinishedTransition, applyPremisesWithEnv]
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration] using
      apply_argumentAmbient_argumentsFinished_right
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeArgModes modes)

#print axioms language_argumentsFinished_step

private theorem fixedInput_left_holeSkeleton
    (name : String) (expected : Term) (mode : ArgMode) :
    patternHoleSkeleton
        (inputStepTransition name (encodeTerm expected) (encodeArgMode mode) []).left =
      true := by
  simp [inputStepTransition, compileArguments, declarationPattern, termsCons,
    a, v, patternHoleSkeleton, patternsHoleSkeleton]

private theorem fixedInput_right_holeSkeleton
    (name : String) (expected : Term) (mode : ArgMode) :
    patternHoleSkeleton
        (inputStepTransition name (encodeTerm expected) (encodeArgMode mode) []).right =
      true := by
  simp [inputStepTransition, compileArguments, declarationPattern,
    argModesSnoc, a, v, patternHoleSkeleton, patternsHoleSkeleton]

private theorem fixedInput_left_names_subset
    (name : String) (expected : Term) (mode : ArgMode) :
    ∀ variableName ∈ patternOccurrenceNames
        (inputStepTransition name (encodeTerm expected) (encodeArgMode mode) []).left,
      variableName ∈ argumentNames := by
  intro variableName member
  simp [inputStepTransition, compileArguments, declarationPattern, termsCons,
    a, v, argumentNames] at member ⊢
  aesop

private theorem fixedInput_right_names_from_left
    (name : String) (expected : Term) (mode : ArgMode) :
    ∀ variableName ∈ patternOccurrenceNames
        (inputStepTransition name (encodeTerm expected) (encodeArgMode mode) []).right,
      variableName ∈ patternOccurrenceNames
        (inputStepTransition name (encodeTerm expected) (encodeArgMode mode) []).left := by
  intro variableName member
  simp [inputStepTransition, compileArguments, declarationPattern, termsCons,
    argModesSnoc, a, v] at member ⊢
  aesop

private theorem apply_argumentAmbient_fixedInput_left
    (name : String) (expected : Term) (mode : ArgMode)
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted inputCursor modes : Pattern) :
    applyBindings
        (argumentAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted inputCursor modes
          (encodeTerm expected))
        (inputStepTransition name (encodeTerm expected) (encodeArgMode mode) []).left =
      compileArguments owner revision head arity
        (declarationPattern occurrence declarationHead inputs output)
        remaining (termsCons (encodeTerm expected) inputCursor) modes
        accepted := by
  simp [argumentAmbient, inputStepTransition, compileArguments,
    declarationPattern, termsCons, a, v, applyBindings]

private theorem apply_argumentAmbient_fixedInput_right
    (name : String) (expected : Term) (mode : ArgMode)
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted inputCursor modes : Pattern) :
    applyBindings
        (argumentAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted inputCursor modes
          (encodeTerm expected))
        (inputStepTransition name (encodeTerm expected) (encodeArgMode mode) []).right =
      compileArguments owner revision head arity
        (declarationPattern occurrence declarationHead inputs output)
        remaining inputCursor (argModesSnoc modes (encodeArgMode mode)) accepted := by
  simp [argumentAmbient, inputStepTransition, compileArguments,
    declarationPattern, argModesSnoc, a, v, applyBindings]

private theorem language_fixedInput_step
    (transitionName : String) (expected : Term) (mode : ArgMode)
    (ruleMember :
      inputStepTransition transitionName (encodeTerm expected)
          (encodeArgMode mode) [] ∈ transitions)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (expected :: inputCursor) modes accepted))
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            inputCursor (modes ++ [mode]) accepted)) := by
  let ambient := argumentAmbient (encodeOwner owner) (encodeNat revision)
    (encodeName head) (encodeNat arity) (encodeNat declaration.occurrence)
    (encodeName declaration.function) (encodeTerms declaration.inputTypes)
    (encodeTerm declaration.outputType) (encodeDeclarations remaining)
    (encodePlans accepted) (encodeTerms inputCursor) (encodeArgModes modes)
    (encodeTerm expected)
  refine language_step_of_ambient
    (inputStepTransition transitionName (encodeTerm expected)
      (encodeArgMode mode) []) ruleMember .nil (ambient := ambient)
    (fixedInput_left_holeSkeleton transitionName expected mode)
    (fixedInput_right_holeSkeleton transitionName expected mode) ?_
    (fixedInput_right_names_from_left transitionName expected mode) ?_ ?_ ?_
  · intro name member
    apply argumentAmbient_covers_names
    exact fixedInput_left_names_subset transitionName expected mode name member
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration,
      encodeTerms] using
      apply_argumentAmbient_fixedInput_left transitionName expected mode
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeTerms inputCursor) (encodeArgModes modes)
  · intro bindings _ _
    simp [inputStepTransition, applyPremisesWithEnv]
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration,
      encodeArgModes_append_singleton] using
      apply_argumentAmbient_fixedInput_right transitionName expected mode
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeTerms inputCursor) (encodeArgModes modes)

/-- The special `Atom` input is copied without evaluation. -/
theorem language_rawInput_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (atomType :: inputCursor) modes accepted))
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            inputCursor (modes ++ [.rawAtom]) accepted)) := by
  apply language_fixedInput_step
    "petta-call-guard-compile-input-raw" atomType .rawAtom
  change rawInputTransition ∈ transitions
  simp [transitions]

/-- `%Undefined%` inputs are evaluated without a type query. -/
theorem language_undefinedInput_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (undefinedType :: inputCursor) modes accepted))
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            inputCursor (modes ++ [.evalUnchecked]) accepted)) := by
  apply language_fixedInput_step
    "petta-call-guard-compile-input-undefined" undefinedType .evalUnchecked
  change undefinedInputTransition ∈ transitions
  simp [transitions]

/-- `_` inputs are evaluated without a type query. -/
theorem language_holeInput_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (holeType :: inputCursor) modes accepted))
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            inputCursor (modes ++ [.evalUnchecked]) accepted)) := by
  apply language_fixedInput_step
    "petta-call-guard-compile-input-hole" holeType .evalUnchecked
  change holeInputTransition ∈ transitions
  simp [transitions]

private theorem checkedInput_left_holeSkeleton :
    patternHoleSkeleton checkedInputTransition.left = true := by
  simp [checkedInputTransition, inputStepTransition, compileArguments,
    declarationPattern, termsCons, a, v, patternHoleSkeleton,
    patternsHoleSkeleton]

private theorem checkedInput_right_holeSkeleton :
    patternHoleSkeleton checkedInputTransition.right = true := by
  simp [checkedInputTransition, inputStepTransition, compileArguments,
    declarationPattern, argModesSnoc, checkedArgMode, a, v,
    patternHoleSkeleton, patternsHoleSkeleton]

private theorem checkedInput_left_names_subset :
    ∀ name ∈ patternOccurrenceNames checkedInputTransition.left,
      name ∈ argumentNames := by
  intro name member
  simp [checkedInputTransition, inputStepTransition, compileArguments,
    declarationPattern, termsCons, a, v, argumentNames] at member ⊢
  aesop

private theorem checkedInput_right_names_from_left :
    ∀ name ∈ patternOccurrenceNames checkedInputTransition.right,
      name ∈ patternOccurrenceNames checkedInputTransition.left := by
  intro name member
  simp [checkedInputTransition, inputStepTransition, compileArguments,
    declarationPattern, termsCons, argModesSnoc, checkedArgMode,
    a, v] at member ⊢
  aesop

private theorem apply_argumentAmbient_checkedInput_left
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted inputCursor modes expected : Pattern) :
    applyBindings
        (argumentAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted inputCursor modes expected)
        checkedInputTransition.left =
      compileArguments owner revision head arity
        (declarationPattern occurrence declarationHead inputs output)
        remaining (termsCons expected inputCursor) modes accepted := by
  simp [argumentAmbient, checkedInputTransition, inputStepTransition,
    compileArguments, declarationPattern, termsCons, a, v, applyBindings]

private theorem apply_argumentAmbient_checkedInput_right
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted inputCursor modes expected : Pattern) :
    applyBindings
        (argumentAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted inputCursor modes expected)
        checkedInputTransition.right =
      compileArguments owner revision head arity
        (declarationPattern occurrence declarationHead inputs output)
        remaining inputCursor (argModesSnoc modes (checkedArgMode expected))
        accepted := by
  simp [argumentAmbient, checkedInputTransition, inputStepTransition,
    compileArguments, declarationPattern, argModesSnoc, checkedArgMode,
    a, v, applyBindings]

/-- Every supported ordinary input is compiled to the checked soft-cut mode by
the authored relation-query rule. -/
theorem language_checkedInput_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (expected : Term) (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan)
    (compiled : compileArgMode expected = some (.evalSoftcutType expected)) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (expected :: inputCursor) modes accepted))
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            inputCursor (modes ++ [.evalSoftcutType expected]) accepted)) := by
  let ambient := argumentAmbient (encodeOwner owner) (encodeNat revision)
    (encodeName head) (encodeNat arity) (encodeNat declaration.occurrence)
    (encodeName declaration.function) (encodeTerms declaration.inputTypes)
    (encodeTerm declaration.outputType) (encodeDeclarations remaining)
    (encodePlans accepted) (encodeTerms inputCursor) (encodeArgModes modes)
    (encodeTerm expected)
  refine language_step_of_ambient checkedInputTransition
    (by change checkedInputTransition ∈ transitions; simp [transitions])
    (.relationQuery .nil) (ambient := ambient)
    checkedInput_left_holeSkeleton checkedInput_right_holeSkeleton ?_
    checkedInput_right_names_from_left ?_ ?_ ?_
  · intro name member
    apply argumentAmbient_covers_names
    exact checkedInput_left_names_subset name member
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration,
      encodeTerms] using
      apply_argumentAmbient_checkedInput_left
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeTerms inputCursor) (encodeArgModes modes)
        (encodeTerm expected)
  · intro bindings agree covered
    have expectedLookup : Bindings.lookup bindings "expected" =
        some (encodeTerm expected) := by
      apply lookup_eq_of_agree agree
        (covered "expected" (by
          simp [checkedInputTransition, inputStepTransition, compileArguments,
            declarationPattern, termsCons, a, v, patternOccurrenceNames,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]))
      simp [ambient, argumentAmbient, Bindings.lookup]
    simpa [checkedInputTransition, inputStepTransition, query] using
      unaryRelationQuery_self bindings checkedInputRelation "expected"
        (encodeTerm expected) expectedLookup
        (relationEnv_checkedInput_encoded expected compiled)
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration,
      encodeArgModes_append_singleton, encodeArgMode] using
      apply_argumentAmbient_checkedInput_right
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeTerms inputCursor) (encodeArgModes modes)
        (encodeTerm expected)

private theorem openInput_left_eq_checkedInput_left :
    openInputTransition.left = checkedInputTransition.left := rfl

private theorem openInput_left_holeSkeleton :
    patternHoleSkeleton openInputTransition.left = true := by
  rw [openInput_left_eq_checkedInput_left]
  exact checkedInput_left_holeSkeleton

private theorem openInput_right_holeSkeleton :
    patternHoleSkeleton openInputTransition.right = true := by
  simp [openInputTransition, compileHalted, outsideFragmentPattern,
    a, patternHoleSkeleton, patternsHoleSkeleton]

private theorem openInput_left_names_subset :
    ∀ name ∈ patternOccurrenceNames openInputTransition.left,
      name ∈ argumentNames := by
  rw [openInput_left_eq_checkedInput_left]
  exact checkedInput_left_names_subset

private theorem openInput_right_names_from_left :
    ∀ name ∈ patternOccurrenceNames openInputTransition.right,
      name ∈ patternOccurrenceNames openInputTransition.left := by
  intro name member
  simp [openInputTransition, compileHalted, outsideFragmentPattern,
    a, patternOccurrenceNames,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]
    at member

private theorem apply_argumentAmbient_openInput_left
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted inputCursor modes expected : Pattern) :
    applyBindings
        (argumentAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted inputCursor modes expected)
        openInputTransition.left =
      compileArguments owner revision head arity
        (declarationPattern occurrence declarationHead inputs output)
        remaining (termsCons expected inputCursor) modes accepted := by
  rw [openInput_left_eq_checkedInput_left]
  exact apply_argumentAmbient_checkedInput_left owner revision head arity
    occurrence declarationHead inputs output remaining accepted inputCursor
    modes expected

private theorem apply_argumentAmbient_openInput_right
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted inputCursor modes expected : Pattern) :
    applyBindings
        (argumentAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted inputCursor modes expected)
        openInputTransition.right =
      compileHalted outsideFragmentPattern := by
  simp [argumentAmbient, openInputTransition, compileHalted,
    outsideFragmentPattern, a, applyBindings]

/-- An unsupported open input declines the complete family; it is not silently
omitted and is not compiled as an unchecked guard. -/
theorem language_openInput_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (expected : Term) (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (compiled : compileArgMode expected = none) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (expected :: inputCursor) modes accepted))
        (encodeCompileLanguageControl (.halted .outsideFragment)) := by
  let ambient := argumentAmbient (encodeOwner owner) (encodeNat revision)
    (encodeName head) (encodeNat arity) (encodeNat declaration.occurrence)
    (encodeName declaration.function) (encodeTerms declaration.inputTypes)
    (encodeTerm declaration.outputType) (encodeDeclarations remaining)
    (encodePlans accepted) (encodeTerms inputCursor) (encodeArgModes modes)
    (encodeTerm expected)
  refine language_step_of_ambient openInputTransition
    (by change openInputTransition ∈ transitions; simp [transitions])
    (.relationQuery .nil) (ambient := ambient)
    openInput_left_holeSkeleton openInput_right_holeSkeleton ?_
    openInput_right_names_from_left ?_ ?_ ?_
  · intro name member
    apply argumentAmbient_covers_names
    exact openInput_left_names_subset name member
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration,
      encodeTerms] using
      apply_argumentAmbient_openInput_left
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeTerms inputCursor) (encodeArgModes modes)
        (encodeTerm expected)
  · intro bindings agree covered
    have expectedLookup : Bindings.lookup bindings "expected" =
        some (encodeTerm expected) := by
      apply lookup_eq_of_agree agree
        (covered "expected" (by
          rw [openInput_left_eq_checkedInput_left]
          simp [checkedInputTransition, inputStepTransition, compileArguments,
            declarationPattern, termsCons, a, v, patternOccurrenceNames,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]))
      simp [ambient, argumentAmbient, Bindings.lookup]
    simpa [openInputTransition, query] using
      unaryRelationQuery_self bindings openInputRelation "expected"
        (encodeTerm expected) expectedLookup
        (relationEnv_openInput_encoded expected compiled)
  · simpa [ambient, encodeCompileLanguageControl,
      encodeCompilationResult] using
      apply_argumentAmbient_openInput_right
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeTerms inputCursor) (encodeArgModes modes)
        (encodeTerm expected)

/-- Successful mode compilation selects exactly one of the four supported
authored input transitions. -/
theorem language_compiledInput_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (expected : Term) (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (mode : ArgMode)
    (compiled : compileArgMode expected = some mode) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (expected :: inputCursor) modes accepted))
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            inputCursor (modes ++ [mode]) accepted)) := by
  by_cases atom : expected = atomType
  · subst expected
    have modeExact : (.rawAtom : ArgMode) = mode := by
      simpa [compileArgMode] using compiled
    subst mode
    exact language_rawInput_step owner revision head arity declaration
      remaining inputCursor modes accepted
  · by_cases undefined : expected = undefinedType
    · subst expected
      have modeExact : (.evalUnchecked : ArgMode) = mode := by
        simpa [compileArgMode, atom] using compiled
      subst mode
      exact language_undefinedInput_step owner revision head arity declaration
        remaining inputCursor modes accepted
    · by_cases hole : expected = holeType
      · subst expected
        have modeExact : (.evalUnchecked : ArgMode) = mode := by
          simpa [compileArgMode, atom, undefined] using compiled
        subst mode
        exact language_holeInput_step owner revision head arity declaration
          remaining inputCursor modes accepted
      · by_cases closed : termIsClosed expected = true
        · have modeExact : (.evalSoftcutType expected : ArgMode) = mode := by
            simpa [compileArgMode, atom, undefined, hole, closed] using compiled
          subst mode
          apply language_checkedInput_step
          simp [compileArgMode, atom, undefined, hole, closed]
        · simp [compileArgMode, atom, undefined, hole, closed] at compiled

#print axioms language_rawInput_step
#print axioms language_undefinedInput_step
#print axioms language_holeInput_step
#print axioms language_checkedInput_step
#print axioms language_openInput_step
#print axioms language_compiledInput_step

private def resultAmbient
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted modes : Pattern) : Bindings := [
  ("owner", owner), ("revision", revision), ("head", head),
  ("arity", arity), ("occurrence", occurrence),
  ("declarationHead", declarationHead), ("inputs", inputs),
  ("output", output), ("remaining", remaining), ("accepted", accepted),
  ("modes", modes)]

private def resultNames : List String :=
  ["owner", "revision", "head", "arity", "occurrence",
    "declarationHead", "inputs", "output", "remaining", "accepted", "modes"]

private theorem resultAmbient_covers_names
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted modes : Pattern) :
    ∀ name ∈ resultNames,
      (Bindings.lookup
        (resultAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted modes) name).isSome := by
  intro name nameMember
  unfold resultNames at nameMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at nameMember
  rcases nameMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [resultAmbient, Bindings.lookup]

private theorem fixedResult_left_holeSkeleton
    (name : String) (expected : Term) (mode : ResultMode) :
    patternHoleSkeleton
        (resultStepTransition name (encodeTerm expected)
          (encodeResultMode mode) []).left = true := by
  simp [resultStepTransition, compileResult, declarationPattern,
    a, v, patternHoleSkeleton, patternsHoleSkeleton]

private theorem fixedResult_right_holeSkeleton
    (name : String) (expected : Term) (mode : ResultMode) :
    patternHoleSkeleton
        (resultStepTransition name (encodeTerm expected)
          (encodeResultMode mode) []).right = true := by
  simp [resultStepTransition, compileRunning, plansSnoc, planPattern,
    declarationPattern, a, v, patternHoleSkeleton, patternsHoleSkeleton]

private theorem fixedResult_left_names_subset
    (name : String) (expected : Term) (mode : ResultMode) :
    ∀ variableName ∈ patternOccurrenceNames
        (resultStepTransition name (encodeTerm expected)
          (encodeResultMode mode) []).left,
      variableName ∈ resultNames := by
  intro variableName member
  simp [resultStepTransition, compileResult, declarationPattern,
    a, v, resultNames] at member ⊢
  aesop

private theorem fixedResult_right_names_from_left
    (name : String) (expected : Term) (mode : ResultMode) :
    ∀ variableName ∈ patternOccurrenceNames
        (resultStepTransition name (encodeTerm expected)
          (encodeResultMode mode) []).right,
      variableName ∈ patternOccurrenceNames
        (resultStepTransition name (encodeTerm expected)
          (encodeResultMode mode) []).left := by
  intro variableName member
  simp [resultStepTransition, compileResult, compileRunning, plansSnoc,
    planPattern, declarationPattern, a, v] at member ⊢
  aesop

private theorem apply_resultAmbient_fixedResult_left
    (name : String) (expected : Term) (mode : ResultMode)
    (owner revision head arity occurrence declarationHead inputs remaining
      accepted modes : Pattern) :
    applyBindings
        (resultAmbient owner revision head arity occurrence declarationHead
          inputs (encodeTerm expected) remaining accepted modes)
        (resultStepTransition name (encodeTerm expected)
          (encodeResultMode mode) []).left =
      compileResult owner revision head arity
        (declarationPattern occurrence declarationHead inputs
          (encodeTerm expected)) remaining modes accepted := by
  simp [resultAmbient, resultStepTransition, compileResult,
    declarationPattern, a, v, applyBindings]

private theorem apply_resultAmbient_fixedResult_right
    (name : String) (expected : Term) (mode : ResultMode)
    (owner revision head arity occurrence declarationHead inputs remaining
      accepted modes : Pattern) :
    applyBindings
        (resultAmbient owner revision head arity occurrence declarationHead
          inputs (encodeTerm expected) remaining accepted modes)
        (resultStepTransition name (encodeTerm expected)
          (encodeResultMode mode) []).right =
      compileRunning owner revision head arity remaining
        (plansSnoc accepted
          (planPattern occurrence modes (encodeResultMode mode)
            (declarationPattern occurrence declarationHead inputs
              (encodeTerm expected)))) := by
  simp [resultAmbient, resultStepTransition, compileRunning, plansSnoc,
    planPattern, declarationPattern, a, v, applyBindings]

private theorem language_fixedResult_step
    (transitionName : String) (expected : Term) (mode : ResultMode)
    (ruleMember :
      resultStepTransition transitionName (encodeTerm expected)
          (encodeResultMode mode) [] ∈ transitions)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (outputExact : declaration.outputType = expected) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted))
        (encodeCompileLanguageControl
          (.running owner revision head arity remaining
            (accepted ++ [{
              declarationOccurrence := declaration.occurrence
              argumentModes := modes
              resultMode := mode
              declaration := declaration }]))) := by
  cases declaration with
  | mk occurrence declarationHead inputs output =>
      dsimp at outputExact ⊢
      subst output
      let ambient := resultAmbient (encodeOwner owner) (encodeNat revision)
        (encodeName head) (encodeNat arity) (encodeNat occurrence)
        (encodeName declarationHead) (encodeTerms inputs) (encodeTerm expected)
        (encodeDeclarations remaining) (encodePlans accepted)
        (encodeArgModes modes)
      refine language_step_of_ambient
        (resultStepTransition transitionName (encodeTerm expected)
          (encodeResultMode mode) []) ruleMember .nil (ambient := ambient)
        (fixedResult_left_holeSkeleton transitionName expected mode)
        (fixedResult_right_holeSkeleton transitionName expected mode) ?_
        (fixedResult_right_names_from_left transitionName expected mode)
        ?_ ?_ ?_
      · intro name member
        apply resultAmbient_covers_names
        exact fixedResult_left_names_subset transitionName expected mode
          name member
      · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration] using
          apply_resultAmbient_fixedResult_left transitionName expected mode
            (encodeOwner owner) (encodeNat revision) (encodeName head)
            (encodeNat arity) (encodeNat occurrence)
            (encodeName declarationHead) (encodeTerms inputs)
            (encodeDeclarations remaining) (encodePlans accepted)
            (encodeArgModes modes)
      · intro bindings _ _
        simp [resultStepTransition, applyPremisesWithEnv]
      · simpa [ambient, encodeCompileLanguageControl,
          encodePlans_append_singleton, encodePlan, encodeDeclaration] using
          apply_resultAmbient_fixedResult_right transitionName expected mode
            (encodeOwner owner) (encodeNat revision) (encodeName head)
            (encodeNat arity) (encodeNat occurrence)
            (encodeName declarationHead) (encodeTerms inputs)
            (encodeDeclarations remaining) (encodePlans accepted)
            (encodeArgModes modes)

theorem language_undefinedResult_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (outputExact : declaration.outputType = undefinedType) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted))
        (encodeCompileLanguageControl
          (.running owner revision head arity remaining
            (accepted ++ [{
              declarationOccurrence := declaration.occurrence
              argumentModes := modes
              resultMode := .resultUnchecked
              declaration := declaration }]))) := by
  apply language_fixedResult_step
    "petta-call-guard-compile-result-undefined" undefinedType
    .resultUnchecked
  · change undefinedResultTransition ∈ transitions
    simp [transitions]
  · exact outputExact

theorem language_holeResult_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (outputExact : declaration.outputType = holeType) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted))
        (encodeCompileLanguageControl
          (.running owner revision head arity remaining
            (accepted ++ [{
              declarationOccurrence := declaration.occurrence
              argumentModes := modes
              resultMode := .resultUnchecked
              declaration := declaration }]))) := by
  apply language_fixedResult_step
    "petta-call-guard-compile-result-hole" holeType .resultUnchecked
  · change holeResultTransition ∈ transitions
    simp [transitions]
  · exact outputExact

theorem language_atomResult_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (outputExact : declaration.outputType = atomType) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted))
        (encodeCompileLanguageControl
          (.running owner revision head arity remaining
            (accepted ++ [{
              declarationOccurrence := declaration.occurrence
              argumentModes := modes
              resultMode := .resultUnchecked
              declaration := declaration }]))) := by
  apply language_fixedResult_step
    "petta-call-guard-compile-result-atom" atomType .resultUnchecked
  · change atomResultTransition ∈ transitions
    simp [transitions]
  · exact outputExact

#print axioms language_undefinedResult_step
#print axioms language_holeResult_step
#print axioms language_atomResult_step

private theorem checkedResult_left_holeSkeleton :
    patternHoleSkeleton checkedResultTransition.left = true := by
  simp [checkedResultTransition, resultStepTransition, compileResult,
    declarationPattern, a, v, patternHoleSkeleton, patternsHoleSkeleton]

private theorem checkedResult_right_holeSkeleton :
    patternHoleSkeleton checkedResultTransition.right = true := by
  simp [checkedResultTransition, resultStepTransition, compileRunning,
    plansSnoc, planPattern, declarationPattern, checkedResultMode,
    a, v, patternHoleSkeleton, patternsHoleSkeleton]

private theorem checkedResult_left_names_subset :
    ∀ name ∈ patternOccurrenceNames checkedResultTransition.left,
      name ∈ resultNames := by
  intro name member
  simp [checkedResultTransition, resultStepTransition, compileResult,
    declarationPattern, a, v, resultNames] at member ⊢
  aesop

private theorem checkedResult_right_names_from_left :
    ∀ name ∈ patternOccurrenceNames checkedResultTransition.right,
      name ∈ patternOccurrenceNames checkedResultTransition.left := by
  intro name member
  simp [checkedResultTransition, resultStepTransition, compileResult,
    compileRunning, plansSnoc, planPattern, declarationPattern,
    checkedResultMode, a, v] at member ⊢
  aesop

private theorem apply_resultAmbient_checkedResult_left
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted modes : Pattern) :
    applyBindings
        (resultAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted modes)
        checkedResultTransition.left =
      compileResult owner revision head arity
        (declarationPattern occurrence declarationHead inputs output)
        remaining modes accepted := by
  simp [resultAmbient, checkedResultTransition, resultStepTransition,
    compileResult, declarationPattern, a, v, applyBindings]

private theorem apply_resultAmbient_checkedResult_right
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted modes : Pattern) :
    applyBindings
        (resultAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted modes)
        checkedResultTransition.right =
      compileRunning owner revision head arity remaining
        (plansSnoc accepted
          (planPattern occurrence modes (checkedResultMode output)
            (declarationPattern occurrence declarationHead inputs output))) := by
  simp [resultAmbient, checkedResultTransition, resultStepTransition,
    compileRunning, plansSnoc, planPattern, declarationPattern,
    checkedResultMode, a, v, applyBindings]

/-- Every supported ordinary result is compiled to the checked soft-cut mode
by the authored relation-query rule. -/
theorem language_checkedResult_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (compiled : compileResultMode declaration.outputType =
      some (.resultSoftcutType declaration.outputType)) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted))
        (encodeCompileLanguageControl
          (.running owner revision head arity remaining
            (accepted ++ [{
              declarationOccurrence := declaration.occurrence
              argumentModes := modes
              resultMode := .resultSoftcutType declaration.outputType
              declaration := declaration }]))) := by
  let ambient := resultAmbient (encodeOwner owner) (encodeNat revision)
    (encodeName head) (encodeNat arity) (encodeNat declaration.occurrence)
    (encodeName declaration.function) (encodeTerms declaration.inputTypes)
    (encodeTerm declaration.outputType) (encodeDeclarations remaining)
    (encodePlans accepted) (encodeArgModes modes)
  refine language_step_of_ambient checkedResultTransition
    (by change checkedResultTransition ∈ transitions; simp [transitions])
    (.relationQuery .nil) (ambient := ambient)
    checkedResult_left_holeSkeleton checkedResult_right_holeSkeleton ?_
    checkedResult_right_names_from_left ?_ ?_ ?_
  · intro name member
    apply resultAmbient_covers_names
    exact checkedResult_left_names_subset name member
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration] using
      apply_resultAmbient_checkedResult_left
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeArgModes modes)
  · intro bindings agree covered
    have outputLookup : Bindings.lookup bindings "output" =
        some (encodeTerm declaration.outputType) := by
      apply lookup_eq_of_agree agree
        (covered "output" (by
          simp [checkedResultTransition, resultStepTransition, compileResult,
            declarationPattern, a, v, patternOccurrenceNames,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]))
      simp [ambient, resultAmbient, Bindings.lookup]
    simpa [checkedResultTransition, resultStepTransition, query] using
      unaryRelationQuery_self bindings checkedResultRelation "output"
        (encodeTerm declaration.outputType) outputLookup
        (relationEnv_checkedResult_encoded declaration.outputType compiled)
  · simpa [ambient, encodeCompileLanguageControl,
      encodePlans_append_singleton, encodePlan, encodeDeclaration,
      encodeResultMode] using
      apply_resultAmbient_checkedResult_right
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeArgModes modes)

private theorem openResult_left_eq_checkedResult_left :
    openResultTransition.left = checkedResultTransition.left := rfl

private theorem openResult_left_holeSkeleton :
    patternHoleSkeleton openResultTransition.left = true := by
  rw [openResult_left_eq_checkedResult_left]
  exact checkedResult_left_holeSkeleton

private theorem openResult_right_holeSkeleton :
    patternHoleSkeleton openResultTransition.right = true := by
  simp [openResultTransition, compileHalted, outsideFragmentPattern,
    a, patternHoleSkeleton, patternsHoleSkeleton]

private theorem openResult_left_names_subset :
    ∀ name ∈ patternOccurrenceNames openResultTransition.left,
      name ∈ resultNames := by
  rw [openResult_left_eq_checkedResult_left]
  exact checkedResult_left_names_subset

private theorem openResult_right_names_from_left :
    ∀ name ∈ patternOccurrenceNames openResultTransition.right,
      name ∈ patternOccurrenceNames openResultTransition.left := by
  intro name member
  simp [openResultTransition, compileHalted, outsideFragmentPattern,
    a, patternOccurrenceNames,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
    Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]
    at member

private theorem apply_resultAmbient_openResult_left
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted modes : Pattern) :
    applyBindings
        (resultAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted modes)
        openResultTransition.left =
      compileResult owner revision head arity
        (declarationPattern occurrence declarationHead inputs output)
        remaining modes accepted := by
  rw [openResult_left_eq_checkedResult_left]
  exact apply_resultAmbient_checkedResult_left owner revision head arity
    occurrence declarationHead inputs output remaining accepted modes

private theorem apply_resultAmbient_openResult_right
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted modes : Pattern) :
    applyBindings
        (resultAmbient owner revision head arity occurrence declarationHead
          inputs output remaining accepted modes)
        openResultTransition.right = compileHalted outsideFragmentPattern := by
  simp [resultAmbient, openResultTransition, compileHalted,
    outsideFragmentPattern, a, applyBindings]

/-- An unsupported open result declines the complete family. -/
theorem language_openResult_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (compiled : compileResultMode declaration.outputType = none) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted))
        (encodeCompileLanguageControl (.halted .outsideFragment)) := by
  let ambient := resultAmbient (encodeOwner owner) (encodeNat revision)
    (encodeName head) (encodeNat arity) (encodeNat declaration.occurrence)
    (encodeName declaration.function) (encodeTerms declaration.inputTypes)
    (encodeTerm declaration.outputType) (encodeDeclarations remaining)
    (encodePlans accepted) (encodeArgModes modes)
  refine language_step_of_ambient openResultTransition
    (by change openResultTransition ∈ transitions; simp [transitions])
    (.relationQuery .nil) (ambient := ambient)
    openResult_left_holeSkeleton openResult_right_holeSkeleton ?_
    openResult_right_names_from_left ?_ ?_ ?_
  · intro name member
    apply resultAmbient_covers_names
    exact openResult_left_names_subset name member
  · simpa [ambient, encodeCompileLanguageControl, encodeDeclaration] using
      apply_resultAmbient_openResult_left
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeArgModes modes)
  · intro bindings agree covered
    have outputLookup : Bindings.lookup bindings "output" =
        some (encodeTerm declaration.outputType) := by
      apply lookup_eq_of_agree agree
        (covered "output" (by
          rw [openResult_left_eq_checkedResult_left]
          simp [checkedResultTransition, resultStepTransition, compileResult,
            declarationPattern, a, v, patternOccurrenceNames,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternMetavariableOccurrencesAt,
            Mettapedia.GSLT.LanguageDef.InferenceChecker.patternsMetavariableOccurrencesAt]))
      simp [ambient, resultAmbient, Bindings.lookup]
    simpa [openResultTransition, query] using
      unaryRelationQuery_self bindings openResultRelation "output"
        (encodeTerm declaration.outputType) outputLookup
        (relationEnv_openResult_encoded declaration.outputType compiled)
  · simpa [ambient, encodeCompileLanguageControl,
      encodeCompilationResult] using
      apply_resultAmbient_openResult_right
        (encodeOwner owner) (encodeNat revision) (encodeName head)
        (encodeNat arity) (encodeNat declaration.occurrence)
        (encodeName declaration.function) (encodeTerms declaration.inputTypes)
        (encodeTerm declaration.outputType) (encodeDeclarations remaining)
        (encodePlans accepted) (encodeArgModes modes)

/-- Successful result-mode compilation selects exactly one supported authored
result transition. -/
theorem language_compiledResult_step
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) (mode : ResultMode)
    (compiled : compileResultMode declaration.outputType = some mode) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted))
        (encodeCompileLanguageControl
          (.running owner revision head arity remaining
            (accepted ++ [{
              declarationOccurrence := declaration.occurrence
              argumentModes := modes
              resultMode := mode
              declaration := declaration }]))) := by
  by_cases undefined : declaration.outputType = undefinedType
  · have modeExact : (.resultUnchecked : ResultMode) = mode := by
      simpa [compileResultMode, undefined] using compiled
    subst mode
    exact language_undefinedResult_step owner revision head arity declaration
      remaining modes accepted undefined
  · by_cases hole : declaration.outputType = holeType
    · have modeExact : (.resultUnchecked : ResultMode) = mode := by
        simpa [compileResultMode, undefined, hole] using compiled
      subst mode
      exact language_holeResult_step owner revision head arity declaration
        remaining modes accepted hole
    · by_cases atom : declaration.outputType = atomType
      · have modeExact : (.resultUnchecked : ResultMode) = mode := by
          simpa [compileResultMode, undefined, hole, atom] using compiled
        subst mode
        exact language_atomResult_step owner revision head arity declaration
          remaining modes accepted atom
      · by_cases closed : termIsClosed declaration.outputType = true
        · have modeExact :
              (.resultSoftcutType declaration.outputType : ResultMode) = mode := by
            simpa [compileResultMode, undefined, hole, atom, closed] using
              compiled
          subst mode
          apply language_checkedResult_step
          simp [compileResultMode, undefined, hole, atom, closed]
        · simp [compileResultMode, undefined, hole, atom, closed] at compiled

#print axioms language_checkedResult_step
#print axioms language_openResult_step
#print axioms language_compiledResult_step

/-- Every transition computed by the independent cold micro-machine is an
actual step of the ordinary authored `LanguageDef` on encoded states. -/
theorem language_step_complete
    {source target : CompileLanguageControl}
    (step : compileLanguageStep? source = some target) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
      (encodeCompileLanguageControl source)
      (encodeCompileLanguageControl target) := by
  cases source with
  | halted result =>
      simp [compileLanguageStep?] at step
  | running owner revision head arity remaining accepted =>
      cases remaining with
      | nil =>
          simp [compileLanguageStep?] at step
          subst target
          exact language_finish_step owner revision head arity accepted
      | cons declaration remaining =>
          by_cases relevant : Relevant declaration head arity
          · simp [compileLanguageStep?, relevant] at step
            subst target
            exact language_beginDeclaration_step owner revision head arity
              declaration remaining accepted relevant.1 relevant.2
          · simp [compileLanguageStep?, relevant] at step
            subst target
            by_cases sameHead : declaration.function = head
            · apply language_skipArity_step owner revision head arity
                declaration remaining accepted sameHead
              intro sameArity
              exact relevant ⟨sameHead, sameArity⟩
            · exact language_skipHead_step owner revision head arity
                declaration remaining accepted sameHead
  | arguments owner revision head arity declaration remaining inputCursor
      modes accepted =>
      cases inputCursor with
      | nil =>
          simp [compileLanguageStep?] at step
          subst target
          exact language_argumentsFinished_step owner revision head arity
            declaration remaining modes accepted
      | cons expected inputCursor =>
          cases compiled : compileArgMode expected with
          | none =>
              simp [compileLanguageStep?, compiled] at step
              subst target
              exact language_openInput_step owner revision head arity
                declaration remaining expected inputCursor modes accepted
                compiled
          | some mode =>
              simp [compileLanguageStep?, compiled] at step
              subst target
              exact language_compiledInput_step owner revision head arity
                declaration remaining expected inputCursor modes accepted mode
                compiled
  | result owner revision head arity declaration remaining modes accepted =>
      cases compiled : compileResultMode declaration.outputType with
      | none =>
          simp [compileLanguageStep?, compiled] at step
          subst target
          exact language_openResult_step owner revision head arity declaration
            remaining modes accepted compiled
      | some mode =>
          simp [compileLanguageStep?, compiled] at step
          subst target
          exact language_compiledResult_step owner revision head arity
            declaration remaining modes accepted mode compiled

#print axioms language_step_complete

/-! ## Independent denotation and normalization of the typed micro-machine -/

def finishPlan (declaration : ArrowDeclaration) (modes : List ArgMode) :
    Option GuardPlan := do
  let resultMode ← compileResultMode declaration.outputType
  pure {
    declarationOccurrence := declaration.occurrence
    argumentModes := modes
    resultMode := resultMode
    declaration := declaration }

def compileArgumentTail (declaration : ArrowDeclaration) :
    List Term → List ArgMode → Option GuardPlan
  | [], modes => finishPlan declaration modes
  | expected :: remaining, modes => do
      let mode ← compileArgMode expected
      compileArgumentTail declaration remaining (modes ++ [mode])

theorem compileArgumentTail_exact (declaration : ArrowDeclaration)
    (remaining : List Term) (modes : List ArgMode) :
    compileArgumentTail declaration remaining modes =
      match compileArgumentModes remaining with
      | none => none
      | some suffix => finishPlan declaration (modes ++ suffix) := by
  induction remaining generalizing modes with
  | nil => simp [compileArgumentTail, compileArgumentModes]
  | cons expected remaining inductionHypothesis =>
      cases compiled : compileArgMode expected with
      | none =>
          simp [compileArgumentTail, compileArgumentModes, compiled]
      | some mode =>
          cases tailCompiled : compileArgumentModes remaining with
          | none =>
              simp [compileArgumentTail, compileArgumentModes, compiled,
                inductionHypothesis, tailCompiled]
          | some suffix =>
              simp [compileArgumentTail, compileArgumentModes, compiled,
                inductionHypothesis, tailCompiled, List.append_assoc]

theorem compileArgumentTail_start_exact (declaration : ArrowDeclaration) :
    compileArgumentTail declaration declaration.inputTypes [] =
      compileGuard declaration := by
  rw [compileArgumentTail_exact]
  unfold compileGuard finishPlan
  cases arguments : compileArgumentModes declaration.inputTypes with
  | none => simp
  | some modes => simp

def CompileLanguageControl.denote :
    CompileLanguageControl → CompilationResult
  | .running owner revision head arity remaining accepted =>
      compileOrdered owner revision head arity accepted remaining
  | .arguments owner revision head arity declaration remaining inputCursor
      modes accepted =>
      match compileArgumentTail declaration inputCursor modes with
      | none => .outsideFragment
      | some plan =>
          compileOrdered owner revision head arity (accepted ++ [plan])
            remaining
  | .result owner revision head arity declaration remaining modes accepted =>
      match finishPlan declaration modes with
      | none => .outsideFragment
      | some plan =>
          compileOrdered owner revision head arity (accepted ++ [plan])
            remaining
  | .halted compilation => compilation

theorem compileLanguageStep_denote_preserved
    {source target : CompileLanguageControl}
    (step : compileLanguageStep? source = some target) :
    source.denote = target.denote := by
  cases source with
  | halted compilation => simp [compileLanguageStep?] at step
  | running owner revision head arity remaining accepted =>
      cases remaining with
      | nil =>
          simp only [compileLanguageStep?] at step
          cases Option.some.inj step
          rfl
      | cons declaration remaining =>
          by_cases relevant : Relevant declaration head arity
          · simp only [compileLanguageStep?, relevant, if_pos] at step
            cases Option.some.inj step
            simp [CompileLanguageControl.denote, compileOrdered, relevant,
              compileArgumentTail_start_exact]
            rfl
          · simp only [compileLanguageStep?, relevant] at step
            cases Option.some.inj step
            simp [CompileLanguageControl.denote, compileOrdered, relevant]
  | arguments owner revision head arity declaration remaining inputCursor
      modes accepted =>
      cases inputCursor with
      | nil =>
          simp only [compileLanguageStep?] at step
          cases Option.some.inj step
          rfl
      | cons expected inputCursor =>
          cases compiled : compileArgMode expected with
          | none =>
              simp only [compileLanguageStep?, compiled] at step
              cases Option.some.inj step
              simp [CompileLanguageControl.denote, compileArgumentTail,
                compiled]
          | some mode =>
              simp only [compileLanguageStep?, compiled] at step
              cases Option.some.inj step
              simp [CompileLanguageControl.denote, compileArgumentTail,
                compiled]
  | result owner revision head arity declaration remaining modes accepted =>
      cases compiled : compileResultMode declaration.outputType with
      | none =>
          simp only [compileLanguageStep?, compiled] at step
          cases Option.some.inj step
          simp [CompileLanguageControl.denote, finishPlan, compiled]
      | some resultMode =>
          simp only [compileLanguageStep?, compiled] at step
          cases Option.some.inj step
          simp [CompileLanguageControl.denote, finishPlan, compiled]

theorem compileLanguageStart_denote_exact (owned : OwnedSnapshot)
    (head : String) (arity : Nat) :
    (compileLanguageStart owned head arity).denote =
      compileGuards owned head arity := by
  change compileOrdered owned.owner owned.snapshot.revision head arity []
      owned.snapshot.declarations = compileGuards owned head arity
  simpa [compileStart, CompileControl.denote] using
    compileStart_denote_exact owned head arity

def declarationsWork : List ArrowDeclaration → Nat
  | [] => 1
  | declaration :: remaining =>
      declaration.inputTypes.length + 3 + declarationsWork remaining

def CompileLanguageControl.stepBound : CompileLanguageControl → Nat
  | .running _ _ _ _ remaining _ => declarationsWork remaining
  | .arguments _ _ _ _ _ remaining inputCursor _ _ =>
      inputCursor.length + 2 + declarationsWork remaining
  | .result _ _ _ _ _ remaining _ _ => 1 + declarationsWork remaining
  | .halted _ => 0

theorem compileLanguageStep?_none_iff_halted
    (source : CompileLanguageControl) :
    compileLanguageStep? source = none ↔
      ∃ result, source = .halted result := by
  cases source with
  | halted compilation => simp [compileLanguageStep?]
  | running owner revision head arity remaining accepted =>
      cases remaining with
      | nil => simp [compileLanguageStep?]
      | cons declaration remaining =>
          by_cases relevant : Relevant declaration head arity <;>
            simp [compileLanguageStep?, relevant]
  | arguments owner revision head arity declaration remaining inputCursor
      modes accepted =>
      cases inputCursor with
      | nil => simp [compileLanguageStep?]
      | cons expected inputCursor =>
          cases compiled : compileArgMode expected <;>
            simp [compileLanguageStep?, compiled]
  | result owner revision head arity declaration remaining modes accepted =>
      cases compiled : compileResultMode declaration.outputType <;>
        simp [compileLanguageStep?, compiled]

theorem compileLanguageStep_stepBound_decreases
    {source target : CompileLanguageControl}
    (step : compileLanguageStep? source = some target) :
    target.stepBound < source.stepBound := by
  cases source with
  | halted compilation => simp [compileLanguageStep?] at step
  | running owner revision head arity remaining accepted =>
      cases remaining with
      | nil =>
          simp [compileLanguageStep?] at step
          subst target
          simp [CompileLanguageControl.stepBound, declarationsWork]
      | cons declaration remaining =>
          by_cases relevant : Relevant declaration head arity <;>
            simp [compileLanguageStep?, relevant] at step
          all_goals subst target
          all_goals simp [CompileLanguageControl.stepBound, declarationsWork]
  | arguments owner revision head arity declaration remaining inputCursor
      modes accepted =>
      cases inputCursor with
      | nil =>
          simp [compileLanguageStep?] at step
          subst target
          simp [CompileLanguageControl.stepBound]
      | cons expected inputCursor =>
          cases compiled : compileArgMode expected <;>
            simp [compileLanguageStep?, compiled] at step
          all_goals subst target
          all_goals simp [CompileLanguageControl.stepBound]
  | result owner revision head arity declaration remaining modes accepted =>
      cases compiled : compileResultMode declaration.outputType <;>
        simp [compileLanguageStep?, compiled] at step
      all_goals subst target
      all_goals simp [CompileLanguageControl.stepBound]

theorem compileLanguageGSLT_multiStep_denote_preserved :
    ∀ {source target : CompileLanguageControl},
      compileLanguageGSLT.MultiStep source target →
        source.denote = target.denote
  | _, _, .refl _ => rfl
  | _, _, .step one rest =>
      (compileLanguageStep_denote_preserved one).trans
        (compileLanguageGSLT_multiStep_denote_preserved rest)

theorem compileLanguageGSLT_normalizes (source : CompileLanguageControl) :
    ∃ result,
      compileLanguageGSLT.MultiStep source (.halted result) ∧
        result = source.denote := by
  induction source using
      (measure CompileLanguageControl.stepBound).wf.induction with
  | h source inductionHypothesis =>
      cases next : compileLanguageStep? source with
      | none =>
          obtain ⟨result, rfl⟩ :=
            (compileLanguageStep?_none_iff_halted source).1 next
          exact ⟨result, .refl _, rfl⟩
      | some target =>
          obtain ⟨result, steps, resultExact⟩ :=
            inductionHypothesis target
              (compileLanguageStep_stepBound_decreases next)
          exact ⟨result, .step next steps,
            resultExact.trans
              (compileLanguageStep_denote_preserved next).symm⟩

theorem compileLanguageGSLT_total_exact (owned : OwnedSnapshot)
    (head : String) (arity : Nat) :
    compileLanguageGSLT.MultiStep (compileLanguageStart owned head arity)
      (.halted (compileGuards owned head arity)) := by
  obtain ⟨result, steps, resultExact⟩ :=
    compileLanguageGSLT_normalizes (compileLanguageStart owned head arity)
  have exactResult : result = compileGuards owned head arity :=
    resultExact.trans (compileLanguageStart_denote_exact owned head arity)
  simpa [exactResult] using steps

#print axioms compileArgumentTail_start_exact
#print axioms skipHeadTransition_typeContext
#print axioms compileLanguageStep_denote_preserved
#print axioms compileLanguageStart_denote_exact
#print axioms compileLanguageGSLT_multiStep_denote_preserved
#print axioms compileLanguageGSLT_normalizes
#print axioms compileLanguageGSLT_total_exact

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
