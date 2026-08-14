import Mettapedia.GSLT.LanguageDef.LiteralHoleRunCompilation

/-!
# Literal-head separation after compact template compilation

An immutable flat template sometimes begins with a literal known when the
template itself is compiled.  A value-local recognizer may move that literal
out of the tagged literal-or-hole stream, compare or write it directly, and
leave the residual stream to the existing compact interpreter.

This is a second, optional stage after literal-run compilation.  A leading
hole or an empty template retains the preceding representation exactly.  The
recognizer inspects only the compiled source value, so different guests may
select the optimization without extending the generic runtime or its opcode
vocabulary.
-/

namespace Mettapedia.GSLT.LanguageDef.LiteralHeadSeparationCompilation

universe uToken uVar

abbrev TemplateAtom (Token : Type uToken) (Var : Type uVar) :=
  FirstOrderFrameCompilation.TemplateAtom Token Var

abbrev Template (Token : Type uToken) (Var : Type uVar) :=
  FirstOrderFrameCompilation.Template Token Var

abbrev Formula (Token : Type uToken) :=
  FirstOrderFrameCompilation.Formula Token

abbrev Substitution (Var : Type uVar) (Token : Type uToken) :=
  FirstOrderFrameCompilation.Substitution Var Token

abbrev Program (Token : Type uToken) (Var : Type uVar) :=
  LiteralHoleRunCompilation.Program Token Var

/-! ## Local recognition and residual representation -/

/-- Replayable result of finding a literal in the first source position. -/
structure Plan (Token : Type uToken) (Var : Type uVar) where
  head : Token
  tail : Template Token Var
deriving DecidableEq, Repr

/-- The recognizer is deliberately value-local.  It does not infer that every
template of a language has a fixed head. -/
def recognize : Template Token Var → Option (Plan Token Var)
  | .literal head :: tail => some { head, tail }
  | _ => none

theorem recognize_eq_some_iff
    (template : Template Token Var) (plan : Plan Token Var) :
    recognize template = some plan ↔
      template = .literal plan.head :: plan.tail := by
  cases template with
  | nil => simp [recognize]
  | cons atom tail =>
      cases atom with
      | literal head =>
          constructor
          · intro accepted
            simp [recognize] at accepted
            subst plan
            rfl
          · intro exactShape
            cases exactShape
            simp [recognize]
      | hole holeId => simp [recognize]

/-- Runtime carrier.  `unseparated` is the exact prior compact program and is
the fail-closed result when the local recognizer rejects. -/
inductive Representation (Token : Type uToken) (Var : Type uVar) where
  | unseparated (program : Program Token Var)
  | separated (head : Token) (residual : Program Token Var)
deriving DecidableEq, Repr

/-- Run the local recognizer after literal-run admission. -/
def lower (template : Template Token Var) : Representation Token Var :=
  match recognize template with
  | some plan =>
      .separated plan.head
        (LiteralHoleRunCompilation.compile plan.tail)
  | none =>
      .unseparated (LiteralHoleRunCompilation.compile template)

/-! ## Independent execution -/

def instantiateRepresentation
    (σ : Substitution Var Token) :
    Representation Token Var → Option (Formula Token)
  | .unseparated program =>
      LiteralHoleRunCompilation.instantiateRun σ program
  | .separated head residual => do
      let tail ← LiteralHoleRunCompilation.instantiateRun σ residual
      pure (head :: tail)

/-- The optional second stage preserves exact instantiation for recognized and
rejected values alike. -/
theorem instantiateRepresentation_lower
    (σ : Substitution Var Token) (template : Template Token Var) :
    instantiateRepresentation σ (lower template) =
      FirstOrderFrameCompilation.instantiate σ template := by
  cases template with
  | nil =>
      simpa [lower, recognize, instantiateRepresentation] using
        (LiteralHoleRunCompilation.instantiateRun_compile
          σ ([] : Template Token Var))
  | cons atom tail =>
      cases atom with
      | literal head =>
          simp only [lower, recognize, instantiateRepresentation]
          rw [LiteralHoleRunCompilation.instantiateRun_compile]
          rfl
      | hole holeId =>
          simpa [lower, recognize, instantiateRepresentation] using
            (LiteralHoleRunCompilation.instantiateRun_compile
              σ (.hole holeId :: tail))

def matchRepresentation [DecidableEq Token]
    (σ : Substitution Var Token) :
    Representation Token Var → Formula Token → Option Unit
  | .unseparated program, input =>
      LiteralHoleRunCompilation.compactMatch σ program input
  | .separated head residual, input =>
      match input with
      | [] => none
      | actualHead :: actualTail =>
          if head = actualHead then
            LiteralHoleRunCompilation.compactMatch
              σ residual actualTail
          else
            none

theorem matchRepresentation_eq_some_iff [DecidableEq Token]
    (σ : Substitution Var Token) (representation : Representation Token Var)
    (input : Formula Token) :
    matchRepresentation σ representation input = some () ↔
      instantiateRepresentation σ representation = some input := by
  cases representation with
  | unseparated program =>
      exact LiteralHoleRunCompilation.compactMatch_eq_some_iff
        σ program input
  | separated head residual =>
      cases input with
      | nil =>
          cases runEq :
              LiteralHoleRunCompilation.instantiateRun σ residual <;>
            simp [matchRepresentation, instantiateRepresentation, runEq]
      | cons actualHead actualTail =>
          by_cases equal : head = actualHead
          · subst actualHead
            simp only [matchRepresentation, if_pos]
            rw [LiteralHoleRunCompilation.compactMatch_eq_some_iff]
            cases runEq :
                LiteralHoleRunCompilation.instantiateRun σ residual <;>
              simp [instantiateRepresentation, runEq]
          · cases runEq :
                LiteralHoleRunCompilation.instantiateRun σ residual <;>
              simp [matchRepresentation, instantiateRepresentation,
                equal, runEq]

theorem matchRepresentation_lower_eq_some_iff [DecidableEq Token]
    (σ : Substitution Var Token) (template : Template Token Var)
    (input : Formula Token) :
    matchRepresentation σ (lower template) input = some () ↔
      FirstOrderFrameCompilation.instantiate σ template = some input := by
  rw [matchRepresentation_eq_some_iff,
    instantiateRepresentation_lower]

/-- Direct headed matching is exactly the source instantiate-and-compare
observation. -/
theorem matchRepresentation_lower_eq_materializedMatch
    [DecidableEq Token]
    (σ : Substitution Var Token) (template : Template Token Var)
    (input : Formula Token) :
    matchRepresentation σ (lower template) input =
      FirstOrderFrameCompilation.materializedMatch σ template input := by
  cases sourceEq :
      FirstOrderFrameCompilation.materializedMatch σ template input with
  | none =>
      cases compiledEq : matchRepresentation σ (lower template) input with
      | none => rfl
      | some value =>
          cases value
          have sourceAccepted :
              FirstOrderFrameCompilation.materializedMatch
                  σ template input = some () :=
            (FirstOrderFrameCompilation.materializedMatch_eq_some_iff
              σ template input).mpr
              ((matchRepresentation_lower_eq_some_iff
                σ template input).mp compiledEq)
          rw [sourceEq] at sourceAccepted
          contradiction
  | some value =>
      cases value
      have compiledAccepted :
          matchRepresentation σ (lower template) input = some () :=
        (matchRepresentation_lower_eq_some_iff
          σ template input).mpr
          ((FirstOrderFrameCompilation.materializedMatch_eq_some_iff
            σ template input).mp sourceEq)
      exact compiledAccepted

/-! ## Composable realization -/

structure Artifact (Token : Type uToken) (Var : Type uVar) where
  representation : Representation Token Var
  substitution : Substitution Var Token

def compileArtifact
    (source : LiteralHoleRunCompilation.AdmittedProgram Token Var) :
    Artifact Token Var :=
  { representation := lower source.source.template
    substitution := source.source.substitution }

/-- Head separation is a total optional refinement after the admitted
literal-run pass. -/
def literalHeadSeparationRealization :
    Mettapedia.GSLT.SimpleRealization
      (LiteralHoleRunCompilation.AdmittedProgram Token Var)
      (Artifact Token Var) (Option (Formula Token)) where
  compile := fun _ source => compileArtifact source
  observeSource := fun _ source =>
    FirstOrderFrameCompilation.instantiate
      source.source.substitution source.source.template
  observeArtifact := fun _ artifact =>
    instantiateRepresentation artifact.substitution
      artifact.representation
  adequate := by
    intro _ source
    exact instantiateRepresentation_lower
      source.source.substitution source.source.template

/-! ## Cost refinement -/

/-- Dynamic part tags inspected by the residual interpreter.  The separated
head is a direct scalar comparison rather than a tagged part. -/
def tagDispatchCost : Representation Token Var → Nat
  | .unseparated program => program.length
  | .separated _ residual => residual.length

/-- Descriptor and literal-pool words, including one scalar word for a
separated head. -/
def physicalWordCost : Representation Token Var → Nat
  | .unseparated program =>
      LiteralHoleRunCompilation.compiledWordCost program
  | .separated _ residual =>
      1 + LiteralHoleRunCompilation.compiledWordCost residual

theorem length_le_prependLiteral (head : Token)
    (program : Program Token Var) :
    program.length ≤
      (LiteralHoleRunCompilation.prependLiteral head program).length := by
  cases program with
  | nil => simp [LiteralHoleRunCompilation.prependLiteral]
  | cons part rest =>
      cases part <;> simp [LiteralHoleRunCompilation.prependLiteral]

/-- Separating a recognized head never increases dynamic tag dispatches
relative to the preceding literal-run representation. -/
theorem tagDispatchCost_lower_le_prior
    (template : Template Token Var) :
    tagDispatchCost (lower template) ≤
      LiteralHoleRunCompilation.compiledDispatchCost template := by
  cases template with
  | nil => simp [lower, recognize, tagDispatchCost,
      LiteralHoleRunCompilation.compiledDispatchCost]
  | cons atom tail =>
      cases atom with
      | hole holeId =>
          simp [lower, recognize, tagDispatchCost,
            LiteralHoleRunCompilation.compiledDispatchCost]
      | literal head =>
          simpa [lower, recognize, tagDispatchCost,
            LiteralHoleRunCompilation.compiledDispatchCost,
            LiteralHoleRunCompilation.compile] using
            length_le_prependLiteral head
              (LiteralHoleRunCompilation.compile tail)

theorem headWordCost_le_prependLiteral (head : Token)
    (program : Program Token Var) :
    1 + LiteralHoleRunCompilation.compiledWordCost program ≤
      LiteralHoleRunCompilation.compiledWordCost
        (LiteralHoleRunCompilation.prependLiteral head program) := by
  cases program with
  | nil => simp [LiteralHoleRunCompilation.prependLiteral,
      LiteralHoleRunCompilation.compiledWordCost,
      LiteralHoleRunCompilation.partWordCost]
  | cons part rest =>
      cases part with
      | hole holeId =>
          simp [LiteralHoleRunCompilation.prependLiteral,
            LiteralHoleRunCompilation.compiledWordCost,
            LiteralHoleRunCompilation.partWordCost]
      | literals literal literalTail =>
          cases literalTail with
          | nil =>
              simp [LiteralHoleRunCompilation.prependLiteral,
                LiteralHoleRunCompilation.compiledWordCost,
                LiteralHoleRunCompilation.partWordCost]
              omega
          | cons next remaining =>
              simp [LiteralHoleRunCompilation.prependLiteral,
                LiteralHoleRunCompilation.compiledWordCost,
                LiteralHoleRunCompilation.partWordCost]
              omega

/-- The scalar-head carrier never uses more words than the compact program it
refines. -/
theorem physicalWordCost_lower_le_prior
    (template : Template Token Var) :
    physicalWordCost (lower template) ≤
      LiteralHoleRunCompilation.compiledWordCost
        (LiteralHoleRunCompilation.compile template) := by
  cases template with
  | nil => simp [lower, recognize, physicalWordCost]
  | cons atom tail =>
      cases atom with
      | hole holeId => simp [lower, recognize, physicalWordCost]
      | literal head =>
          simpa [lower, recognize, physicalWordCost,
            LiteralHoleRunCompilation.compile] using
            headWordCost_le_prependLiteral head
              (LiteralHoleRunCompilation.compile tail)

/-! ## Independent witnesses and rejection cases -/

private def admittedShape : LiteralHoleRunCompilation.Shape :=
  { sequenceLayout := .flatSymbolIds
    formulaLifetime := .persistent
    holeInventoryLifetime := .persistent
    sourceRegion := .stateRun
    executionRegion := .proofCall }

private def parserSource :
    LiteralHoleRunCompilation.SourceProgram String Nat :=
  { shape := admittedShape
    template := [.literal "call", .literal "open", .hole 0,
      .literal "close"]
    substitution := fun
      | 0 => some ["payload"]
      | _ => none }

private def parserAdmitted :
    LiteralHoleRunCompilation.AdmittedProgram String Nat :=
  (LiteralHoleRunCompilation.admit? parserSource).get (by decide)

/-- A parser-like immutable template derives its own separated head. -/
example : lower parserSource.template =
    .separated "call"
      (LiteralHoleRunCompilation.compile
        [.literal "open", .hole 0, .literal "close"]) := by
  decide

example :
    literalHeadSeparationRealization.observeArtifact ()
        (literalHeadSeparationRealization.compile () parserAdmitted) =
      some ["call", "open", "payload", "close"] := by
  decide

private def rewriteSource :
    LiteralHoleRunCompilation.SourceProgram Nat Nat :=
  { shape := admittedShape
    template := [.literal 9, .hole 1, .literal 10, .literal 11]
    substitution := fun
      | 1 => some [4, 5]
      | _ => none }

private def rewriteAdmitted :
    LiteralHoleRunCompilation.AdmittedProgram Nat Nat :=
  (LiteralHoleRunCompilation.admit? rewriteSource).get (by decide)

/-- A rewrite-like template independently uses the same local pass. -/
example :
    literalHeadSeparationRealization.observeArtifact ()
        (literalHeadSeparationRealization.compile () rewriteAdmitted) =
      some [9, 4, 5, 10, 11] := by
  decide

example :
    tagDispatchCost (lower rewriteSource.template) = 2 ∧
    LiteralHoleRunCompilation.compiledDispatchCost
        rewriteSource.template = 3 ∧
    physicalWordCost (lower rewriteSource.template) = 7 ∧
    LiteralHoleRunCompilation.compiledWordCost
        (LiteralHoleRunCompilation.compile rewriteSource.template) = 8 := by
  decide

private def leadingHole : Template Nat Nat :=
  [.hole 0, .literal 7]

/-- A leading hole is not reclassified as a literal head. -/
example : recognize leadingHole = none ∧
    lower leadingHole =
      .unseparated (LiteralHoleRunCompilation.compile leadingHole) := by
  decide

/-- An empty sequence remains the exact prior empty representation. -/
example : recognize ([] : Template Nat Nat) = none ∧
    lower ([] : Template Nat Nat) = .unseparated [] := by
  decide

end Mettapedia.GSLT.LanguageDef.LiteralHeadSeparationCompilation
