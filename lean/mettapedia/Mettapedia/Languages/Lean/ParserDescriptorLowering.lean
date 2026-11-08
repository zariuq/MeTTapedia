import Mettapedia.Languages.Lean.ParserDescription
import Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-!
# Declarative parser bodies lowered to the existing syntax presentation language

This fragment admits tokens, category calls, explicitly resolved primitives,
sequencing and grouping. Parser callbacks and other combinators are refused.
Precedence and leading/trailing registration belong to the enclosing rule.

The source judgment describes descriptor operations separately from the
compiled presentation expressions. Both use the actual presentation for
reference resolution; no parser implementation is supplied as a correctness
assumption. Lexical competition and category selection are later boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.ParserDescriptorLowering

open ParserDescription
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

structure Bindings where
  categoryRef : Name → Nat → String
  primitiveRef : Name → Option String
  whitespace : String

def sequenceName : Name := .str .anonymous "andthen"
def groupName : Name := .str .anonymous "group"
def asciiSpace (character : Char) : Bool :=
  character.toNat == 32 || (decide (9 ≤ character.toNat) && decide (character.toNat ≤ 13))

def scalars (text : String) : List Nat :=
  (((text.toList.dropWhile asciiSpace).reverse.dropWhile asciiSpace).reverse).map Char.toNat

def lower (bindings : Bindings) : Description → Option Expr
  | .symbol text =>
      if (scalars text).isEmpty then none
      else some (.left (.literal (scalars text)) (.ref bindings.whitespace))
  | .category name precedence => some (.ref (bindings.categoryRef name precedence))
  | .constant name | .parser name => (bindings.primitiveRef name).map Expr.ref
  | .binary name first second =>
      if name = sequenceName then do return .seq (← lower bindings first) (← lower bindings second)
      else none
  | .unary name body =>
      if name = groupName then (lower bindings body).map (.node "group") else none
  | _ => none

set_option autoImplicit true in
/-- Source descriptor execution with complete concrete-syntax output. -/
inductive Derives (bindings : Bindings) (classes : String → Nat → Prop)
    (presentation : Presentation) (input : List Nat) : Description → Nat → Nat → List CST → Type where
  | symbol (nonempty : (scalars text).isEmpty = false)
      (token : RecognizesAtUsing classes presentation input (.literal (scalars text)) start middle)
      (spaces : RecognizesAtUsing classes presentation input (.ref bindings.whitespace) middle stop) :
      Derives bindings classes presentation input (.symbol text) start stop token.cst
  | category
      (body : RecognizesAtUsing classes presentation input (.ref (bindings.categoryRef name precedence)) start stop) :
      Derives bindings classes presentation input (.category name precedence) start stop body.cst
  | constant (resolved : bindings.primitiveRef name = some reference)
      (body : RecognizesAtUsing classes presentation input (.ref reference) start stop) :
      Derives bindings classes presentation input (.constant name) start stop body.cst
  | parser (resolved : bindings.primitiveRef name = some reference)
      (body : RecognizesAtUsing classes presentation input (.ref reference) start stop) :
      Derives bindings classes presentation input (.parser name) start stop body.cst
  | sequence
      (first : Derives bindings classes presentation input left start middle firstOutput)
      (second : Derives bindings classes presentation input right middle stop secondOutput) :
      Derives bindings classes presentation input (.binary sequenceName left right) start stop
        (firstOutput ++ secondOutput)
  | group (body : Derives bindings classes presentation input descriptor start stop output) :
      Derives bindings classes presentation input (.unary groupName descriptor) start stop
        [.node "group" start stop output]

variable {bindings : Bindings} {classes : String → Nat → Prop} {presentation : Presentation}
  {input : List Nat} {descriptor : Description} {start stop : Nat} {output : List CST}

/-- Every source execution lowers to an execution with exactly the same CST. -/
theorem sound (source : Derives bindings classes presentation input descriptor start stop output) :
    ∃ expression, lower bindings descriptor = some expression ∧
      Nonempty (CSTRecognizesAtUsing classes presentation input expression start stop output) := by
  induction source with
  | symbol nonempty token spaces =>
      exact ⟨_, ⟨by simp [lower, nonempty], ⟨⟨.left token spaces, rfl⟩⟩⟩⟩
  | category body => exact ⟨_, ⟨rfl, ⟨⟨body, rfl⟩⟩⟩⟩
  | constant resolved body => exact ⟨_, ⟨by simp [lower, resolved], ⟨⟨body, rfl⟩⟩⟩⟩
  | parser resolved body => exact ⟨_, ⟨by simp [lower, resolved], ⟨⟨body, rfl⟩⟩⟩⟩
  | sequence first second ihFirst ihSecond =>
      obtain ⟨left, leftLower, ⟨leftRun, leftOutput⟩⟩ := ihFirst
      obtain ⟨right, rightLower, ⟨rightRun, rightOutput⟩⟩ := ihSecond
      exact ⟨_, ⟨by simp [lower, leftLower, rightLower],
        ⟨⟨.seq leftRun rightRun, by simp [RecognizesAtUsing.cst, leftOutput, rightOutput]⟩⟩⟩⟩
  | group body ih =>
      obtain ⟨expression, compiled, ⟨run, result⟩⟩ := ih
      exact ⟨.node "group" expression, ⟨by simp [lower, compiled],
        ⟨⟨.node run, by simp [RecognizesAtUsing.cst, result]⟩⟩⟩⟩

/-- Compiled descriptor bodies cannot invent a source execution or CST. -/
theorem complete {expression : Expr}
    (compiled : lower bindings descriptor = some expression)
    (target : CSTRecognizesAtUsing classes presentation input expression start stop output) :
    Nonempty (Derives bindings classes presentation input descriptor start stop output) := by
  induction descriptor generalizing expression start stop output with
  | symbol text =>
      cases empty : (scalars text).isEmpty with
      | true => simp [lower, empty] at compiled
      | false =>
          simp only [lower, empty, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at compiled
          subst expression
          rcases target with ⟨run, rfl⟩
          cases run with
          | left token spaces => exact ⟨.symbol empty token spaces⟩
  | category name precedence =>
      cases compiled
      rcases target with ⟨run, rfl⟩
      exact ⟨.category run⟩
  | constant name =>
      cases resolved : bindings.primitiveRef name with
      | none => simp [lower, resolved] at compiled
      | some reference =>
          simp only [lower, resolved, Option.map_some, Option.some.injEq] at compiled
          subst expression
          rcases target with ⟨run, rfl⟩
          exact ⟨.constant resolved run⟩
  | parser name =>
      cases resolved : bindings.primitiveRef name with
      | none => simp [lower, resolved] at compiled
      | some reference =>
          simp only [lower, resolved, Option.map_some, Option.some.injEq] at compiled
          subst expression
          rcases target with ⟨run, rfl⟩
          exact ⟨.parser resolved run⟩
  | binary name first second firstIH secondIH =>
      by_cases named : name = sequenceName
      · subst name
        cases left : lower bindings first with
        | none => simp [lower, left] at compiled
        | some firstExpression =>
            cases right : lower bindings second with
            | none => simp [lower, left, right] at compiled
            | some secondExpression =>
                simp [lower, left, right] at compiled
                subst expression
                rcases target with ⟨run, rfl⟩
                cases run with
                | seq firstRun secondRun =>
                    obtain ⟨firstSource⟩ := firstIH left ⟨firstRun, rfl⟩
                    obtain ⟨secondSource⟩ := secondIH right ⟨secondRun, rfl⟩
                    exact ⟨.sequence firstSource secondSource⟩
      · simp [lower, named] at compiled
  | unary name body ih =>
      by_cases named : name = groupName
      · subst name
        cases lowered : lower bindings body with
        | none => simp [lower, lowered] at compiled
        | some bodyExpression =>
            simp only [lower, ↓reduceIte, lowered, Option.map_some, Option.some.injEq] at compiled
            subst expression
            rcases target with ⟨run, rfl⟩
            cases run with
            | node bodyRun =>
                obtain ⟨source⟩ := ih lowered ⟨bodyRun, rfl⟩
                exact ⟨.group source⟩
      · simp [lower, named] at compiled
  | node | trailingNode | nodeWithAntiquot | nonReservedSymbol | sepBy | sepBy1 | unicodeSymbol =>
      simp [lower] at compiled

theorem correspondence {expression : Expr}
    (compiled : lower bindings descriptor = some expression) :
    Nonempty (Derives bindings classes presentation input descriptor start stop output) ↔
      Nonempty (CSTRecognizesAtUsing classes presentation input expression start stop output) := by
  constructor
  · rintro ⟨source⟩
    obtain ⟨result, equality, run⟩ := sound source
    have same : result = expression := Option.some.inj (equality.symm.trans compiled)
    simpa [same] using run
  · rintro ⟨target⟩
    exact complete compiled target

theorem unknown_primitive_refused (bindings : Bindings) (name : Name)
    (unknown : bindings.primitiveRef name = none) : lower bindings (.parser name) = none := by
  simp [lower, unknown]

theorem blank_token_refused (bindings : Bindings) : lower bindings (.symbol " ") = none := by
  have empty : (scalars " ").isEmpty = true := by decide
  simp [lower, empty]

end Mettapedia.Languages.Lean.ParserDescriptorLowering
