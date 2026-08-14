import Mathlib.Data.List.Basic
import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation

/-!
# Literal-run and hole-program compilation

A flat symbolic template alternates between literal tokens and substitution
holes.  When the generated sequence, storage, and escape analyses establish a
flat immutable template with a call-local execution result, adjacent literals
may be grouped into one run.  The generic machine then dispatches once per run
or hole while traversing every token exactly once.

The compact interpreter below is independent of the source template
interpreter.  Exact instantiation and exact matching are proved before the
representation and dispatch-cost refinements are exposed.  The admission
procedure refers only to local layout, lifetime, and region properties; parser
patterns and rewrite patterns instantiate the same boundary.
-/

namespace Mettapedia.GSLT.LanguageDef.LiteralHoleRunCompilation

universe uToken uVar

abbrev TemplateAtom (Token : Type uToken) (Var : Type uVar) :=
  FirstOrderFrameCompilation.TemplateAtom Token Var

abbrev Template (Token : Type uToken) (Var : Type uVar) :=
  FirstOrderFrameCompilation.Template Token Var

abbrev Formula (Token : Type uToken) :=
  FirstOrderFrameCompilation.Formula Token

abbrev Substitution (Var : Type uVar) (Token : Type uToken) :=
  FirstOrderFrameCompilation.Substitution Var Token

/-! ## Compact semantic carrier -/

/-- A compact program part.  `literals head tail` is nonempty by construction;
the physical C carrier stores a singleton inline and a longer run in its
literal pool. -/
inductive Part (Token : Type uToken) (Var : Type uVar) where
  | literals (head : Token) (tail : List Token)
  | hole (holeId : Var)
deriving DecidableEq, Repr

abbrev Program (Token : Type uToken) (Var : Type uVar) :=
  List (Part Token Var)

def expandPart : Part Token Var → Template Token Var
  | .literals head tail =>
      (head :: tail).map
        FirstOrderFrameCompilation.TemplateAtom.literal
  | .hole holeId => [.hole holeId]

def expand (program : Program Token Var) : Template Token Var :=
  program.flatMap expandPart

/-- Prepending a literal extends an existing leading literal run or starts a
new singleton run.  This is the semantic counterpart of the generated C
builder's coalescing operation. -/
def prependLiteral (token : Token) :
    Program Token Var → Program Token Var
  | .literals head tail :: rest =>
      .literals token (head :: tail) :: rest
  | program => .literals token [] :: program

/-- Compile right-to-left so every maximal adjacent literal sequence becomes
one part while holes retain their exact order and identity. -/
def compile : Template Token Var → Program Token Var
  | [] => []
  | .literal token :: rest => prependLiteral token (compile rest)
  | .hole holeId :: rest => .hole holeId :: compile rest

theorem expand_prependLiteral (token : Token)
    (program : Program Token Var) :
    expand (prependLiteral token program) =
      FirstOrderFrameCompilation.TemplateAtom.literal token ::
        expand program := by
  cases program with
  | nil => rfl
  | cons part rest =>
      cases part <;> simp [prependLiteral, expand, expandPart]

/-- The compact program expands to the exact source template, including every
duplicate literal and every repeated hole occurrence. -/
theorem expand_compile (template : Template Token Var) :
    expand (compile template) = template := by
  induction template with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      cases atom with
      | literal token =>
          simp only [compile, expand_prependLiteral, inductionHypothesis]
      | hole holeId =>
          simp only [compile, expand, List.flatMap_cons, expandPart,
            List.singleton_append, List.cons.injEq, true_and]
          simpa only [expand] using inductionHypothesis

/-! ## Independent compact execution -/

/-- Instantiate the compact representation directly.  This interpreter does
not expand the program and does not call the source interpreter. -/
def instantiateRun (σ : Substitution Var Token) :
    Program Token Var → Option (Formula Token)
  | [] => some []
  | .literals head tail :: rest => do
      let suffix ← instantiateRun σ rest
      pure ((head :: tail) ++ suffix)
  | .hole holeId :: rest => do
      let image ← σ holeId
      let suffix ← instantiateRun σ rest
      pure (image ++ suffix)

theorem instantiateRun_prependLiteral
    (σ : Substitution Var Token) (token : Token)
    (program : Program Token Var) :
    instantiateRun σ (prependLiteral token program) =
      (instantiateRun σ program).map (List.cons token) := by
  cases program with
  | nil => rfl
  | cons part rest =>
      cases part with
      | literals head tail =>
          simp only [prependLiteral, instantiateRun]
          cases instantiateRun σ rest <;> simp
      | hole holeId =>
          simp only [prependLiteral, instantiateRun]
          cases imageEq : σ holeId with
          | none => simp
          | some image =>
              cases instantiateRun σ rest <;> simp

/-- Direct compact instantiation is exactly source instantiation after
compilation. -/
theorem instantiateRun_compile
    (σ : Substitution Var Token) (template : Template Token Var) :
    instantiateRun σ (compile template) =
      FirstOrderFrameCompilation.instantiate σ template := by
  induction template with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      cases atom with
      | literal token =>
          simp only [compile,
            FirstOrderFrameCompilation.instantiate]
          rw [instantiateRun_prependLiteral, inductionHypothesis]
          cases FirstOrderFrameCompilation.instantiate σ rest <;> rfl
      | hole holeId =>
          simp only [compile, instantiateRun,
            FirstOrderFrameCompilation.instantiate]
          cases σ holeId <;> simp [inductionHypothesis]

/-- Consume a compact program and an input together.  Literal runs and hole
images use the same prefix primitive, but the program itself is never
expanded or materialized. -/
def consumeRun [DecidableEq Token]
    (σ : Substitution Var Token) :
    Program Token Var → Formula Token → Option (Formula Token)
  | [], input => some input
  | .literals head tail :: rest, input =>
      match FirstOrderFrameCompilation.consumeLiteralPrefix
          (head :: tail) input with
      | none => none
      | some remaining => consumeRun σ rest remaining
  | .hole holeId :: rest, input =>
      match σ holeId with
      | none => none
      | some image =>
          match FirstOrderFrameCompilation.consumeLiteralPrefix image input with
          | none => none
          | some remaining => consumeRun σ rest remaining

/-- Soundness of direct compact consumption. -/
theorem consumeRun_sound [DecidableEq Token]
    (σ : Substitution Var Token) (program : Program Token Var)
    (input rest : Formula Token)
    (accepted : consumeRun σ program input = some rest) :
    ∃ instantiated,
      instantiateRun σ program = some instantiated ∧
      input = instantiated ++ rest := by
  induction program generalizing input rest with
  | nil =>
      simp [consumeRun, instantiateRun] at accepted ⊢
      exact accepted
  | cons part program inductionHypothesis =>
      cases part with
      | literals head tail =>
          cases prefixEq :
              FirstOrderFrameCompilation.consumeLiteralPrefix
                (head :: tail) input with
          | none => simp [consumeRun, prefixEq] at accepted
          | some remaining =>
              simp only [consumeRun, prefixEq] at accepted
              obtain ⟨suffix, suffixEq, remainingEq⟩ :=
                inductionHypothesis remaining rest accepted
              have inputEq : input = (head :: tail) ++ remaining :=
                (FirstOrderFrameCompilation.consumeLiteralPrefix_eq_some_iff
                  (head :: tail) input remaining).mp prefixEq
              refine ⟨(head :: tail) ++ suffix, ?_, ?_⟩
              · simp [instantiateRun, suffixEq]
              · rw [inputEq, remainingEq, List.append_assoc]
      | hole holeId =>
          cases imageEq : σ holeId with
          | none => simp [consumeRun, imageEq] at accepted
          | some image =>
              cases prefixEq :
                  FirstOrderFrameCompilation.consumeLiteralPrefix image input with
              | none => simp [consumeRun, imageEq, prefixEq] at accepted
              | some remaining =>
                  simp only [consumeRun, imageEq, prefixEq] at accepted
                  obtain ⟨suffix, suffixEq, remainingEq⟩ :=
                    inductionHypothesis remaining rest accepted
                  have inputEq : input = image ++ remaining :=
                    (FirstOrderFrameCompilation.consumeLiteralPrefix_eq_some_iff
                      image input remaining).mp prefixEq
                  refine ⟨image ++ suffix, ?_, ?_⟩
                  · simp [instantiateRun, imageEq, suffixEq]
                  · rw [inputEq, remainingEq, List.append_assoc]

/-- Completeness of direct compact consumption. -/
theorem consumeRun_complete [DecidableEq Token]
    (σ : Substitution Var Token) (program : Program Token Var)
    (input rest instantiated : Formula Token)
    (instantiatedEq : instantiateRun σ program = some instantiated)
    (inputEq : input = instantiated ++ rest) :
    consumeRun σ program input = some rest := by
  induction program generalizing input rest instantiated with
  | nil =>
      simp [instantiateRun] at instantiatedEq
      subst instantiated
      simpa [consumeRun] using inputEq
  | cons part program inductionHypothesis =>
      cases part with
      | literals head tail =>
          cases suffixEq : instantiateRun σ program with
          | none => simp [instantiateRun, suffixEq] at instantiatedEq
          | some suffix =>
              simp [instantiateRun, suffixEq] at instantiatedEq
              subst instantiated
              subst input
              have prefixAccepted :
                  FirstOrderFrameCompilation.consumeLiteralPrefix
                      (head :: tail)
                        (head :: (tail ++ suffix) ++ rest) =
                    some (suffix ++ rest) :=
                (FirstOrderFrameCompilation.consumeLiteralPrefix_eq_some_iff
                  (head :: tail) (head :: (tail ++ suffix) ++ rest)
                    (suffix ++ rest)).mpr (by simp [List.append_assoc])
              rw [consumeRun, prefixAccepted]
              exact inductionHypothesis
                (suffix ++ rest) rest suffix suffixEq rfl
      | hole holeId =>
          cases imageEq : σ holeId with
          | none => simp [instantiateRun, imageEq] at instantiatedEq
          | some image =>
              cases suffixEq : instantiateRun σ program with
              | none =>
                  simp [instantiateRun, imageEq, suffixEq] at instantiatedEq
              | some suffix =>
                  simp [instantiateRun, imageEq, suffixEq] at instantiatedEq
                  subst instantiated
                  subst input
                  have prefixAccepted :
                      FirstOrderFrameCompilation.consumeLiteralPrefix
                          image (image ++ suffix ++ rest) =
                        some (suffix ++ rest) :=
                    (FirstOrderFrameCompilation.consumeLiteralPrefix_eq_some_iff
                      image (image ++ suffix ++ rest) (suffix ++ rest)).mpr
                        (by simp [List.append_assoc])
                  simp only [consumeRun, imageEq, prefixAccepted]
                  exact inductionHypothesis
                    (suffix ++ rest) rest suffix suffixEq rfl

theorem consumeRun_eq_some_iff [DecidableEq Token]
    (σ : Substitution Var Token) (program : Program Token Var)
    (input rest : Formula Token) :
    consumeRun σ program input = some rest ↔
      ∃ instantiated,
        instantiateRun σ program = some instantiated ∧
        input = instantiated ++ rest := by
  constructor
  · exact consumeRun_sound σ program input rest
  · rintro ⟨instantiated, instantiatedEq, inputEq⟩
    exact consumeRun_complete
      σ program input rest instantiated instantiatedEq inputEq

def compactMatch [DecidableEq Token]
    (σ : Substitution Var Token) (program : Program Token Var)
    (input : Formula Token) : Option Unit :=
  match consumeRun σ program input with
  | some [] => some ()
  | _ => none

theorem compactMatch_eq_some_iff [DecidableEq Token]
    (σ : Substitution Var Token) (program : Program Token Var)
    (input : Formula Token) :
    compactMatch σ program input = some () ↔
      instantiateRun σ program = some input := by
  constructor
  · intro accepted
    unfold compactMatch at accepted
    cases consumedEq : consumeRun σ program input with
    | none => simp [consumedEq] at accepted
    | some remaining =>
        cases remaining with
        | nil =>
            obtain ⟨instantiated, instantiatedEq, inputEq⟩ :=
              (consumeRun_eq_some_iff σ program input []).mp consumedEq
            have equal : input = instantiated := by simpa using inputEq
            rw [equal]
            exact instantiatedEq
        | cons token tail => simp [consumedEq] at accepted
  · intro instantiatedEq
    have consumedEq : consumeRun σ program input = some [] :=
      consumeRun_complete σ program input [] input
        instantiatedEq (by simp)
    simp [compactMatch, consumedEq]

/-- Grouping literal runs preserves exact source matching. -/
theorem compactMatch_compile_eq_materializedMatch [DecidableEq Token]
    (σ : Substitution Var Token) (template : Template Token Var)
    (input : Formula Token) :
    compactMatch σ (compile template) input =
      FirstOrderFrameCompilation.materializedMatch σ template input := by
  cases sourceEq :
      FirstOrderFrameCompilation.materializedMatch σ template input with
  | none =>
      cases compactEq : compactMatch σ (compile template) input with
      | none => rfl
      | some value =>
          cases value
          have sourceAccepted :
              FirstOrderFrameCompilation.materializedMatch
                  σ template input = some () :=
            (FirstOrderFrameCompilation.materializedMatch_eq_some_iff
              σ template input).mpr
              (instantiateRun_compile σ template ▸
                (compactMatch_eq_some_iff
                  σ (compile template) input).mp compactEq)
          rw [sourceEq] at sourceAccepted
          contradiction
  | some value =>
      cases value
      have compactAccepted :
          compactMatch σ (compile template) input = some () :=
        (compactMatch_eq_some_iff σ (compile template) input).mpr
          (instantiateRun_compile σ template ▸
            (FirstOrderFrameCompilation.materializedMatch_eq_some_iff
              σ template input).mp sourceEq)
      exact compactAccepted

/-! ## Local admission and certified realization -/

inductive SequenceLayout where
  | flatSymbolIds
  | nestedTerms
deriving DecidableEq, Repr

inductive DataLifetime where
  | persistent
  | scoped
deriving DecidableEq, Repr

inductive Region where
  | stateRun
  | proofCall
  | retained
deriving DecidableEq, Repr

/-- Only the facts consumed by this optimization.  Native-type analysis
supplies the flat carrier; storage/effect analysis supplies the lifetimes and
non-escape boundary. -/
structure Shape where
  sequenceLayout : SequenceLayout
  formulaLifetime : DataLifetime
  holeInventoryLifetime : DataLifetime
  sourceRegion : Region
  executionRegion : Region
deriving DecidableEq, Repr

/-- Replayable product of successful local recognition. -/
structure Plan where
  sourceRegion : Region
  executionRegion : Region
deriving DecidableEq, Repr

def recognize (shape : Shape) : Option Plan :=
  if shape.sequenceLayout = .flatSymbolIds ∧
      shape.formulaLifetime = .persistent ∧
      shape.holeInventoryLifetime = .persistent ∧
      shape.sourceRegion = .stateRun ∧
      shape.executionRegion = .proofCall then
    some
      { sourceRegion := shape.sourceRegion
        executionRegion := shape.executionRegion }
  else
    none

structure SourceProgram (Token : Type uToken) (Var : Type uVar) where
  shape : Shape
  template : Template Token Var
  substitution : Substitution Var Token

structure AdmittedProgram (Token : Type uToken) (Var : Type uVar) where
  source : SourceProgram Token Var
  plan : Plan
  accepted : recognize source.shape = some plan

structure Artifact (Token : Type uToken) (Var : Type uVar) where
  plan : Plan
  program : Program Token Var
  substitution : Substitution Var Token

def admit? (source : SourceProgram Token Var) :
    Option (AdmittedProgram Token Var) :=
  match accepted : recognize source.shape with
  | none => none
  | some plan => some { source, plan, accepted }

def compileArtifact (admitted : AdmittedProgram Token Var) :
    Artifact Token Var :=
  { plan := admitted.plan
    program := compile admitted.source.template
    substitution := admitted.source.substitution }

/-- Literal-run grouping is a composable exact realization of instantiation,
not merely a representation equality. -/
def literalHoleRunRealization :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedProgram Token Var) (Artifact Token Var)
      (Option (Formula Token)) where
  compile := fun _ admitted => compileArtifact admitted
  observeSource := fun _ admitted =>
    FirstOrderFrameCompilation.instantiate
      admitted.source.substitution admitted.source.template
  observeArtifact := fun _ artifact =>
    instantiateRun artifact.substitution artifact.program
  adequate := by
    intro _ admitted
    exact instantiateRun_compile
      admitted.source.substitution admitted.source.template

/-! ## Dispatch and representation cost certificates -/

def sourceDispatchCost (template : Template Token Var) : Nat :=
  template.length

def compiledDispatchCost (template : Template Token Var) : Nat :=
  (compile template).length

theorem length_prependLiteral_le (token : Token)
    (program : Program Token Var) :
    (prependLiteral token program).length ≤ program.length + 1 := by
  cases program with
  | nil => simp [prependLiteral]
  | cons part rest => cases part <;> simp [prependLiteral]

/-- Coalescing cannot increase interpreter dispatches. -/
theorem compiledDispatchCost_le_sourceDispatchCost
    (template : Template Token Var) :
    compiledDispatchCost template ≤ sourceDispatchCost template := by
  induction template with
  | nil => simp [compiledDispatchCost, sourceDispatchCost, compile]
  | cons atom rest inductionHypothesis =>
      cases atom with
      | literal token =>
          change (compile rest).length ≤ rest.length at inductionHypothesis
          change (compile (.literal token :: rest)).length ≤
            (.literal token :: rest).length
          simp only [compile, List.length_cons]
          have localBound :=
            length_prependLiteral_le token (compile rest)
          omega
      | hole holeId =>
          change (compile rest).length ≤ rest.length at inductionHypothesis
          change (compile (.hole holeId :: rest)).length ≤
            (.hole holeId :: rest).length
          simp only [compile, List.length_cons]
          omega

/-- Physical words used by one compact part.  Two words hold its descriptor;
a run of length at least two additionally occupies its literal-pool cells. -/
def partWordCost : Part Token Var → Nat
  | .hole _ => 2
  | .literals _ [] => 2
  | .literals _ (_ :: tail) => 2 + (2 + tail.length)

def compiledWordCost (program : Program Token Var) : Nat :=
  (program.map partWordCost).sum

def sourceWordCost (template : Template Token Var) : Nat :=
  2 * template.length

theorem partWordCost_le_expanded (part : Part Token Var) :
    partWordCost part ≤ 2 * (expandPart part).length := by
  cases part with
  | hole holeId => simp [partWordCost, expandPart]
  | literals head tail =>
      cases tail with
      | nil => simp [partWordCost, expandPart]
      | cons _ tail =>
          simp [partWordCost, expandPart]
          omega

theorem compiledWordCost_le_expanded
    (program : Program Token Var) :
    compiledWordCost program ≤ 2 * (expand program).length := by
  induction program with
  | nil => simp [compiledWordCost, expand]
  | cons part program inductionHypothesis =>
      simp only [compiledWordCost, List.map_cons, List.sum_cons,
        expand, List.flatMap_cons, List.length_append]
      have partBound := partWordCost_le_expanded part
      have tailBound : (program.map partWordCost).sum ≤
          2 * (program.flatMap expandPart).length := by
        simpa only [compiledWordCost, expand] using inductionHypothesis
      omega

/-- The physical descriptor-plus-pool carrier never uses more words than the
former two-word-per-cell carrier. -/
theorem compiledWordCost_compile_le_sourceWordCost
    (template : Template Token Var) :
    compiledWordCost (compile template) ≤ sourceWordCost template := by
  calc
    compiledWordCost (compile template) ≤
        2 * (expand (compile template)).length :=
      compiledWordCost_le_expanded (compile template)
    _ = sourceWordCost template := by
      simp [sourceWordCost, expand_compile]

/-! ## Independent witnesses and fail-closed boundary -/

private def admittedShape : Shape :=
  { sequenceLayout := .flatSymbolIds
    formulaLifetime := .persistent
    holeInventoryLifetime := .persistent
    sourceRegion := .stateRun
    executionRegion := .proofCall }

private def parserPattern : SourceProgram String Nat :=
  { shape := admittedShape
    template := [.literal "open", .literal "name", .hole 0,
      .literal "close", .literal "eof"]
    substitution := fun
      | 0 => some ["payload"]
      | _ => none }

/-- A parser action pattern instantiates the same local layout. -/
example : (admit? parserPattern).isSome = true := by
  decide

example :
    let admitted := (admit? parserPattern).get (by decide)
    literalHoleRunRealization.observeArtifact ()
        (literalHoleRunRealization.compile () admitted) =
      some ["open", "name", "payload", "close", "eof"] := by
  decide

private def rewritePattern : SourceProgram Nat Nat :=
  { shape := admittedShape
    template := [.literal 7, .hole 1, .literal 9, .literal 10,
      .literal 11, .hole 1]
    substitution := fun
      | 1 => some [3, 4]
      | _ => none }

/-- A rewrite-machine pattern preserves repeated hole occurrences and gains
the same literal-run dispatch reduction. -/
example :
    let admitted := (admit? rewritePattern).get (by decide)
    literalHoleRunRealization.observeArtifact ()
        (literalHoleRunRealization.compile () admitted) =
      some [7, 3, 4, 9, 10, 11, 3, 4] := by
  decide

example : compiledDispatchCost rewritePattern.template = 4 ∧
    sourceDispatchCost rewritePattern.template = 6 ∧
    compiledWordCost (compile rewritePattern.template) = 11 ∧
    sourceWordCost rewritePattern.template = 12 := by
  decide

private def nestedPattern : SourceProgram String Nat :=
  { parserPattern with shape :=
      { admittedShape with sequenceLayout := .nestedTerms } }

/-- A nested carrier is not silently flattened. -/
example : (admit? nestedPattern).isSome = false := by
  decide

private def scopedFormulaPattern : SourceProgram String Nat :=
  { parserPattern with shape :=
      { admittedShape with formulaLifetime := .scoped } }

/-- A source template that is not persistent fails admission. -/
example : (admit? scopedFormulaPattern).isSome = false := by
  decide

private def escapingPattern : SourceProgram Nat Nat :=
  { rewritePattern with shape :=
      { admittedShape with executionRegion := .retained } }

/-- A compact program that may escape its call region is not admitted. -/
example : (admit? escapingPattern).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.LiteralHoleRunCompilation
