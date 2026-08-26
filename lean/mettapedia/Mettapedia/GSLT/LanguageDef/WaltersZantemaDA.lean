import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Digits.Lemmas
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Walters--Zantema digit-application arithmetic

This file transcribes the ten rule schemata of Walters and Zantema's DA
system for natural-number arithmetic.  A `Schema` generates a finite,
premise-free `LanguageDef` for every radix of at least two.  Digits are unary
postfix operators at the paper level; the underlying `Pattern` uses ordinary
unary applications.

The DA rules themselves contain addition and multiplication.  No native
arithmetic relation or host evaluator occurs in the generated presentation.
-/

namespace Mettapedia.GSLT.LanguageDef.WaltersZantemaDA

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Parameters of one finite DA instance. -/
structure Schema where
  radix : Nat
  radix_ge_two : 2 ≤ radix

namespace Schema

/-- Ordered digit indices of one radix. -/
def digits (schema : Schema) : List Nat :=
  List.range schema.radix

theorem mem_digits_iff (schema : Schema) (digit : Nat) :
    digit ∈ schema.digits ↔ digit < schema.radix := by
  simp [digits]

end Schema

private def ctor (label category : String)
    (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := policy
}

/-- Free-variable pattern used by the DA schemata. -/
def v (name : String) : Pattern := .fvar name

/-- Constructor application used by the DA schemata. -/
def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def empty : Pattern := a "da:empty"
def add (left right : Pattern) : Pattern := a "da:add" [left, right]
def mul (left right : Pattern) : Pattern := a "da:mul" [left, right]
def succ (body : Pattern) : Pattern := a "da:succ" [body]

def digitLabel (digit : Nat) : String := s!"da:digit:{digit}"
def starLabel (digit : Nat) : String := s!"da:star:{digit}"

/-- Postfix digit application `body digit` from the paper. -/
def digit (index : Nat) (body : Pattern) : Pattern :=
  a (digitLabel index) [body]

/-- Auxiliary multiplication operator `star_index(body)` from the paper. -/
def star (index : Nat) (body : Pattern) : Pattern :=
  a (starLabel index) [body]

private def natVariable (name : String) : String × TypeExpr :=
  (name, .base "Nat")

private def rule (name : String) (metavariables : List String)
    (left right : Pattern) : RewriteRule := {
  name := name
  typeContext := metavariables.map natVariable
  premises := []
  left := left
  right := right
}

/-! The schema is authored once as a small typed arithmetic term language.
`AuthoredRule.toRewriteRule` is the only projection into generic `Pattern`
syntax, so the semantic rules proved below are exactly the rules exported by
the generated `LanguageDef`. -/

/-- Closed vocabulary used by the DA rule schemata.  Digit and star indices
remain explicit data; finite-instance generation separately restricts them to
the selected radix. -/
inductive SemanticTerm where
  | variable : String → SemanticTerm
  | empty : SemanticTerm
  | digit : Nat → SemanticTerm → SemanticTerm
  | add : SemanticTerm → SemanticTerm → SemanticTerm
  | mul : SemanticTerm → SemanticTerm → SemanticTerm
  | succ : SemanticTerm → SemanticTerm
  | star : Nat → SemanticTerm → SemanticTerm
deriving Repr, DecidableEq

namespace SemanticTerm

/-- Erasure of an authored DA term into the generic GSLT pattern carrier. -/
def toPattern : SemanticTerm → Pattern
  | .variable name => v name
  | .empty => WaltersZantemaDA.empty
  | .digit index body => WaltersZantemaDA.digit index body.toPattern
  | .add left right => WaltersZantemaDA.add left.toPattern right.toPattern
  | .mul left right => WaltersZantemaDA.mul left.toPattern right.toPattern
  | .succ body => WaltersZantemaDA.succ body.toPattern
  | .star index body => WaltersZantemaDA.star index body.toPattern

/-- Standard-natural-number model of the complete DA vocabulary. -/
def denote (schema : Schema) (valuation : String → Nat) : SemanticTerm → Nat
  | .variable name => valuation name
  | .empty => 0
  | .digit index body => schema.radix * denote schema valuation body + index
  | .add left right => denote schema valuation left + denote schema valuation right
  | .mul left right => denote schema valuation left * denote schema valuation right
  | .succ body => denote schema valuation body + 1
  | .star index body => index * denote schema valuation body

end SemanticTerm

/-- One authored DA rule before erasure into the generic `RewriteRule` type. -/
structure AuthoredRule (schema : Schema) where
  name : String
  metavariables : List String
  left : SemanticTerm
  right : SemanticTerm
deriving Repr, DecidableEq

namespace AuthoredRule

/-- The generated generic rewrite is a direct projection of the authored
semantic rule, rather than an independently maintained table. -/
def toRewriteRule {schema : Schema} (authored : AuthoredRule schema) : RewriteRule :=
  rule authored.name authored.metavariables
    authored.left.toPattern authored.right.toPattern

/-- Denotational soundness of one authored schema instance. -/
def Sound {schema : Schema} (authored : AuthoredRule schema) : Prop :=
  ∀ valuation, authored.left.denote schema valuation =
    authored.right.denote schema valuation

end AuthoredRule

private def instanceName (family : Nat) (schema : Schema)
    (indices : List Nat := []) : String :=
  let suffix := indices.foldl (fun text index => text ++ s!",{index}") ""
  s!"wz-da:{family}[radix={schema.radix}{suffix}]"

/-- Apply the paper's carry schema to a body. -/
def carryApply (schema : Schema) (first second : Nat)
    (body : Pattern) : Pattern :=
  if schema.radix ≤ first + second then succ body else body

/-- The paper's digit-addition schema. -/
def digitSum (schema : Schema) (first second : Nat) : Nat :=
  (first + second) % schema.radix

/-- Canonical DA numeral for a product of two digits.

The product is smaller than `radix^2`, so at most two digit constructors are
needed.  Zero is the empty numeral, as in the paper. -/
def digitProductNumeral (schema : Schema) (first second : Nat) : Pattern :=
  let product := first * second
  if product = 0 then empty
  else
    let high := product / schema.radix
    let low := product % schema.radix
    if high = 0 then digit low empty
    else digit low (digit high empty)

/-- Authored-term counterpart of the paper's carry schema. -/
def semanticCarryApply (schema : Schema) (first second : Nat)
    (body : SemanticTerm) : SemanticTerm :=
  if schema.radix ≤ first + second then .succ body else body

/-- Authored-term counterpart of `digitProductNumeral`. -/
def semanticDigitProductNumeral (schema : Schema) (first second : Nat) :
    SemanticTerm :=
  let product := first * second
  if product = 0 then .empty
  else
    let high := product / schema.radix
    let low := product % schema.radix
    if high = 0 then .digit low .empty
    else .digit low (.digit high .empty)

theorem semanticDigitProductNumeral_toPattern (schema : Schema)
    (first second : Nat) :
    (semanticDigitProductNumeral schema first second).toPattern =
      digitProductNumeral schema first second := by
  by_cases productZero : first * second = 0
  · simp only [semanticDigitProductNumeral, digitProductNumeral, productZero,
      if_pos]
    rfl
  · by_cases highZero : first * second / schema.radix = 0
    · simp only [semanticDigitProductNumeral, digitProductNumeral, productZero,
        highZero, if_pos]
      rfl
    · simp only [semanticDigitProductNumeral, digitProductNumeral, productZero,
        highZero]
      rfl

/-- Paper rule 1: eliminate a leading zero. -/
def authoredRule1 (schema : Schema) : AuthoredRule schema := {
  name := instanceName 1 schema
  metavariables := []
  left := .digit 0 .empty
  right := .empty
}

def rule1 (schema : Schema) : RewriteRule :=
  (authoredRule1 schema).toRewriteRule

/-- Paper rule 2: empty numeral is a left additive unit. -/
def authoredRule2 (schema : Schema) : AuthoredRule schema := {
  name := instanceName 2 schema
  metavariables := ["x"]
  left := .add .empty (.variable "x")
  right := .variable "x"
}

def rule2 (schema : Schema) : RewriteRule :=
  (authoredRule2 schema).toRewriteRule

/-- Paper rule 3: empty numeral is a right additive unit. -/
def authoredRule3 (schema : Schema) : AuthoredRule schema := {
  name := instanceName 3 schema
  metavariables := ["x"]
  left := .add (.variable "x") .empty
  right := .variable "x"
}

def rule3 (schema : Schema) : RewriteRule :=
  (authoredRule3 schema).toRewriteRule

/-- Paper rule 4: digitwise addition with carry. -/
def authoredRule4 (schema : Schema) (first second : Nat) : AuthoredRule schema :=
  let body := SemanticTerm.add (.variable "x") (.variable "y")
  {
    name := instanceName 4 schema [first, second]
    metavariables := ["x", "y"]
    left := .add (.digit first (.variable "x"))
      (.digit second (.variable "y"))
    right := .digit (digitSum schema first second)
      (semanticCarryApply schema first second body)
  }

def rule4 (schema : Schema) (first second : Nat) : RewriteRule :=
  (authoredRule4 schema first second).toRewriteRule

/-- Paper rule 5: empty numeral annihilates multiplication on the left. -/
def authoredRule5 (schema : Schema) : AuthoredRule schema := {
  name := instanceName 5 schema
  metavariables := ["x"]
  left := .mul .empty (.variable "x")
  right := .empty
}

def rule5 (schema : Schema) : RewriteRule :=
  (authoredRule5 schema).toRewriteRule

/-- Paper rule 6: shift-and-add multiplication by the final digit. -/
def authoredRule6 (schema : Schema) (index : Nat) : AuthoredRule schema := {
  name := instanceName 6 schema [index]
  metavariables := ["x", "y"]
  left := .mul (.digit index (.variable "x")) (.variable "y")
  right := .add (.digit 0 (.mul (.variable "x") (.variable "y")))
    (.star index (.variable "y"))
}

def rule6 (schema : Schema) (index : Nat) : RewriteRule :=
  (authoredRule6 schema index).toRewriteRule

/-- Paper rule 7: successor of zero. -/
def authoredRule7 (schema : Schema) : AuthoredRule schema := {
  name := instanceName 7 schema
  metavariables := []
  left := .succ .empty
  right := .digit 1 .empty
}

def rule7 (schema : Schema) : RewriteRule :=
  (authoredRule7 schema).toRewriteRule

/-- Paper rule 8: successor with digit carry. -/
def authoredRule8 (schema : Schema) (index : Nat) : AuthoredRule schema := {
  name := instanceName 8 schema [index]
  metavariables := ["x"]
  left := .succ (.digit index (.variable "x"))
  right := .digit (digitSum schema 1 index)
    (semanticCarryApply schema 1 index (.variable "x"))
}

def rule8 (schema : Schema) (index : Nat) : RewriteRule :=
  (authoredRule8 schema index).toRewriteRule

/-- Paper rule 9: auxiliary digit multiplication at zero. -/
def authoredRule9 (schema : Schema) (index : Nat) : AuthoredRule schema := {
  name := instanceName 9 schema [index]
  metavariables := []
  left := .star index .empty
  right := .empty
}

def rule9 (schema : Schema) (index : Nat) : RewriteRule :=
  (authoredRule9 schema index).toRewriteRule

/-- Paper rule 10: auxiliary digit multiplication over a final digit. -/
def authoredRule10 (schema : Schema) (first second : Nat) : AuthoredRule schema := {
  name := instanceName 10 schema [first, second]
  metavariables := ["x"]
  left := .star first (.digit second (.variable "x"))
  right := .add (.digit 0 (.star first (.variable "x")))
    (semanticDigitProductNumeral schema first second)
}

def rule10 (schema : Schema) (first second : Nat) : RewriteRule :=
  (authoredRule10 schema first second).toRewriteRule

def authoredRule4Family (schema : Schema) : List (AuthoredRule schema) :=
  schema.digits.flatMap fun first =>
    schema.digits.map fun second => authoredRule4 schema first second

def authoredRule6Family (schema : Schema) : List (AuthoredRule schema) :=
  schema.digits.map (authoredRule6 schema)

def authoredRule8Family (schema : Schema) : List (AuthoredRule schema) :=
  schema.digits.map (authoredRule8 schema)

def authoredRule9Family (schema : Schema) : List (AuthoredRule schema) :=
  schema.digits.map (authoredRule9 schema)

def authoredRule10Family (schema : Schema) : List (AuthoredRule schema) :=
  schema.digits.flatMap fun first =>
    schema.digits.map fun second => authoredRule10 schema first second

/-- The complete finite expansion before generic-pattern erasure. -/
def authoredRules (schema : Schema) : List (AuthoredRule schema) :=
  [authoredRule1 schema, authoredRule2 schema, authoredRule3 schema] ++
    (authoredRule4Family schema ++
    ([authoredRule5 schema] ++
    (authoredRule6Family schema ++
    ([authoredRule7 schema] ++
    (authoredRule8Family schema ++
    (authoredRule9Family schema ++
      authoredRule10Family schema))))))

def rule4Family (schema : Schema) : List RewriteRule :=
  (authoredRule4Family schema).map AuthoredRule.toRewriteRule

def rule6Family (schema : Schema) : List RewriteRule :=
  (authoredRule6Family schema).map AuthoredRule.toRewriteRule

def rule8Family (schema : Schema) : List RewriteRule :=
  (authoredRule8Family schema).map AuthoredRule.toRewriteRule

def rule9Family (schema : Schema) : List RewriteRule :=
  (authoredRule9Family schema).map AuthoredRule.toRewriteRule

def rule10Family (schema : Schema) : List RewriteRule :=
  (authoredRule10Family schema).map AuthoredRule.toRewriteRule

/-- The complete finite expansion of the ten DA rule schemata. -/
def rewrites (schema : Schema) : List RewriteRule :=
  (authoredRules schema).map AuthoredRule.toRewriteRule

private def digitCtor (index : Nat) : GrammarRule :=
  ctor (digitLabel index) "Nat" [("body", "Nat")]

private def starCtor (index : Nat) : GrammarRule :=
  ctor (starLabel index) "Nat" [("body", "Nat")] (some .rewrite)

/-- Constructor signature of one generated DA instance. -/
def terms (schema : Schema) : List GrammarRule :=
  [ctor "da:empty" "Nat" []] ++
    schema.digits.map digitCtor ++
    [ctor "da:add" "Nat" [("left", "Nat"), ("right", "Nat")]
        (some .rewrite),
     ctor "da:mul" "Nat" [("left", "Nat"), ("right", "Nat")]
        (some .rewrite),
     ctor "da:succ" "Nat" [("body", "Nat")] (some .rewrite)] ++
    schema.digits.map starCtor

/-- Generated premise-free DA `LanguageDef` for one radix. -/
def language (schema : Schema) : LanguageDef := {
  name := s!"WaltersZantemaDA{schema.radix}"
  types := ["Nat"]
  terms := terms schema
  equations := []
  rewrites := rewrites schema
}

/-- The empty numeral constructor is present in every generated DA
presentation. -/
theorem empty_constructor_declared (schema : Schema) :
    ∃ rule ∈ (language schema).terms,
      rule.label = "da:empty" ∧ rule.params.length = 0 := by
  refine ⟨ctor "da:empty" "Nat" [], ?_, rfl, rfl⟩
  simp [language, terms]

/-- Every in-range digit constructor is present in the generated DA
presentation. -/
theorem digit_constructor_declared (schema : Schema) {index : Nat}
    (inRange : index < schema.radix) :
    ∃ rule ∈ (language schema).terms,
      rule.label = digitLabel index ∧ rule.params.length = 1 := by
  refine ⟨digitCtor index, ?_, rfl, rfl⟩
  change digitCtor index ∈ terms schema
  have digitMember : index ∈ schema.digits :=
    (Schema.mem_digits_iff schema index).2 inRange
  have mapped : digitCtor index ∈ schema.digits.map digitCtor :=
    List.mem_map.mpr ⟨index, digitMember, rfl⟩
  unfold terms
  exact List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ mapped))

/-- Radix two is the primary closed qualification instance. -/
def radixTwo : Schema := ⟨2, by omega⟩

/-! ## Radix representation and bounded digit arithmetic -/

/-- Least-significant-digit-first encoding used by the DA postfix view. -/
def encodeDigits (schema : Schema) (number : Nat) : List Nat :=
  Nat.digits schema.radix number

/-- Denotation of a least-significant-digit-first representation. -/
def decodeDigits (schema : Schema) (digits : List Nat) : Nat :=
  Nat.ofDigits schema.radix digits

/-- Paper normal-form invariant for the digit list: every digit is in range,
and a nonempty numeral has a nonzero most-significant digit. -/
def CanonicalDigits (schema : Schema) (digits : List Nat) : Prop :=
  (∀ digit ∈ digits, digit < schema.radix) ∧
    ∀ nonempty : digits ≠ [], digits.getLast nonempty ≠ 0

theorem decodeDigits_encodeDigits (schema : Schema) (number : Nat) :
    decodeDigits schema (encodeDigits schema number) = number := by
  exact Nat.ofDigits_digits schema.radix number

theorem encodeDigits_canonical (schema : Schema) (number : Nat) :
    CanonicalDigits schema (encodeDigits schema number) := by
  have radixGtOne : 1 < schema.radix := schema.radix_ge_two
  constructor
  · intro digit member
    exact Nat.digits_lt_base radixGtOne member
  · intro nonempty
    exact Nat.getLast_digit_ne_zero schema.radix
      (Nat.digits_ne_nil_iff_ne_zero.mp nonempty)

/-- Canonical digit representations have no denotational aliases. -/
theorem decodeDigits_injective_on_canonical (schema : Schema)
    {left right : List Nat}
    (leftCanonical : CanonicalDigits schema left)
    (rightCanonical : CanonicalDigits schema right)
    (equal : decodeDigits schema left = decodeDigits schema right) :
    left = right := by
  have radixGtOne : 1 < schema.radix := schema.radix_ge_two
  calc
    left = Nat.digits schema.radix (decodeDigits schema left) :=
      (Nat.digits_ofDigits schema.radix radixGtOne left
        leftCanonical.1 leftCanonical.2).symm
    _ = Nat.digits schema.radix (decodeDigits schema right) :=
      congrArg (Nat.digits schema.radix) equal
    _ = right :=
      Nat.digits_ofDigits schema.radix radixGtOne right
        rightCanonical.1 rightCanonical.2

/-- Embed one least-significant-digit-first sequence as paper-style postfix
digit applications. -/
def patternOfDigits (digits : List Nat) : Pattern :=
  digits.foldr digit empty

/-- Canonical authored numeral pattern for one natural number. -/
def encodePattern (schema : Schema) (number : Nat) : Pattern :=
  patternOfDigits (encodeDigits schema number)

theorem radixTwo_encode_five :
    encodePattern radixTwo 5 = digit 1 (digit 0 (digit 1 empty)) := by
  decide +kernel

/-- Quotient/remainder result used to instantiate paper carry schemata. -/
def digitAddCarry (schema : Schema) (first second : Nat) : Nat × Nat :=
  ((first + second) / schema.radix, (first + second) % schema.radix)

/-- One schema-level arithmetic fact discharges digit range and carry bounds
for rules 4 and 8 at every radix. -/
theorem digitAddCarry_spec (schema : Schema) {first second : Nat}
    (firstDigit : first < schema.radix)
    (secondDigit : second < schema.radix) :
    first + second =
        (digitAddCarry schema first second).1 * schema.radix +
          (digitAddCarry schema first second).2 ∧
      (digitAddCarry schema first second).2 < schema.radix ∧
      (digitAddCarry schema first second).1 ≤ 1 := by
  have radixPositive : 0 < schema.radix := by omega
  have decomposition := Nat.mod_add_div (first + second) schema.radix
  have sumBound : first + second < 2 * schema.radix := by omega
  have carryBound : (first + second) / schema.radix < 2 :=
    (Nat.div_lt_iff_lt_mul radixPositive).2 sumBound
  constructor
  · simpa [digitAddCarry, Nat.mul_comm, Nat.add_comm] using decomposition.symm
  · constructor
    · simpa [digitAddCarry] using Nat.mod_lt (first + second) radixPositive
    · simpa [digitAddCarry] using (Nat.lt_succ_iff.mp carryBound)

/-! ## Denotational soundness of the authored schemata -/

theorem semanticDigitProductNumeral_denote (schema : Schema)
    (valuation : String → Nat) (first second : Nat) :
    (semanticDigitProductNumeral schema first second).denote schema valuation =
      first * second := by
  have radixLowerBound := schema.radix_ge_two
  have radixPositive : 0 < schema.radix := by omega
  by_cases productZero : first * second = 0
  · simp [semanticDigitProductNumeral, productZero, SemanticTerm.denote]
  · by_cases highZero : first * second / schema.radix = 0
    · have productLt : first * second < schema.radix :=
        (Nat.div_eq_zero_iff_lt radixPositive).mp highZero
      simp [semanticDigitProductNumeral, productZero, highZero,
        SemanticTerm.denote, Nat.mod_eq_of_lt productLt]
    · have decomposition := Nat.mod_add_div (first * second) schema.radix
      simp only [semanticDigitProductNumeral, productZero, highZero, if_false,
        SemanticTerm.denote]
      simpa [Nat.add_comm, Nat.mul_comm] using decomposition

theorem authoredRule1_sound (schema : Schema) :
    (authoredRule1 schema).Sound := by
  intro valuation
  simp [authoredRule1, SemanticTerm.denote]

theorem authoredRule2_sound (schema : Schema) :
    (authoredRule2 schema).Sound := by
  intro valuation
  simp [authoredRule2, SemanticTerm.denote]

theorem authoredRule3_sound (schema : Schema) :
    (authoredRule3 schema).Sound := by
  intro valuation
  simp [authoredRule3, SemanticTerm.denote]

theorem authoredRule4_sound (schema : Schema) {first second : Nat}
    (firstDigit : first < schema.radix)
    (secondDigit : second < schema.radix) :
    (authoredRule4 schema first second).Sound := by
  intro valuation
  have radixPositive : 0 < schema.radix := by omega
  have sumBound : first + second < 2 * schema.radix := by omega
  by_cases carry : schema.radix ≤ first + second
  · have quotientPositive : 0 < (first + second) / schema.radix :=
      Nat.div_pos carry radixPositive
    have quotientBound : (first + second) / schema.radix < 2 :=
      (Nat.div_lt_iff_lt_mul radixPositive).2 sumBound
    have quotientOne : (first + second) / schema.radix = 1 := by omega
    have decomposition := Nat.mod_add_div (first + second) schema.radix
    have sumEquation :
        first + second = schema.radix + (first + second) % schema.radix := by
      calc
        first + second =
            (first + second) % schema.radix +
              schema.radix * ((first + second) / schema.radix) :=
          decomposition.symm
        _ = (first + second) % schema.radix + schema.radix * 1 := by
          rw [quotientOne]
        _ = schema.radix + (first + second) % schema.radix := by ring
    simp only [authoredRule4, SemanticTerm.denote,
      semanticCarryApply, carry, if_pos, digitSum]
    calc
      (schema.radix * valuation "x" + first) +
          (schema.radix * valuation "y" + second) =
          schema.radix * (valuation "x" + valuation "y") +
            (first + second) := by ring
      _ = schema.radix * (valuation "x" + valuation "y") +
            (schema.radix + (first + second) % schema.radix) := by
          exact congrArg
            (fun value => schema.radix * (valuation "x" + valuation "y") + value)
            sumEquation
      _ = schema.radix * (valuation "x" + valuation "y" + 1) +
            (first + second) % schema.radix := by ring
  · have sumLt : first + second < schema.radix := Nat.lt_of_not_ge carry
    have remainder : (first + second) % schema.radix = first + second :=
      Nat.mod_eq_of_lt sumLt
    simp only [authoredRule4, SemanticTerm.denote,
      semanticCarryApply, carry, if_false, digitSum]
    calc
      (schema.radix * valuation "x" + first) +
          (schema.radix * valuation "y" + second) =
          schema.radix * (valuation "x" + valuation "y") +
            (first + second) := by ring
      _ = schema.radix * (valuation "x" + valuation "y") +
            (first + second) % schema.radix := by rw [remainder]

theorem authoredRule5_sound (schema : Schema) :
    (authoredRule5 schema).Sound := by
  intro valuation
  simp [authoredRule5, SemanticTerm.denote]

theorem authoredRule6_sound (schema : Schema) (index : Nat) :
    (authoredRule6 schema index).Sound := by
  intro valuation
  simp only [authoredRule6, SemanticTerm.denote]
  ring

theorem authoredRule7_sound (schema : Schema) :
    (authoredRule7 schema).Sound := by
  intro valuation
  simp [authoredRule7, SemanticTerm.denote]

theorem authoredRule8_sound (schema : Schema) {index : Nat}
    (indexDigit : index < schema.radix) :
    (authoredRule8 schema index).Sound := by
  intro valuation
  have radixPositive : 0 < schema.radix := by omega
  have oneDigit : 1 < schema.radix := schema.radix_ge_two
  have sumBound : 1 + index < 2 * schema.radix := by omega
  by_cases carry : schema.radix ≤ 1 + index
  · have quotientPositive : 0 < (1 + index) / schema.radix :=
      Nat.div_pos carry radixPositive
    have quotientBound : (1 + index) / schema.radix < 2 :=
      (Nat.div_lt_iff_lt_mul radixPositive).2 sumBound
    have quotientOne : (1 + index) / schema.radix = 1 := by omega
    have decomposition := Nat.mod_add_div (1 + index) schema.radix
    have sumEquation :
        1 + index = schema.radix + (1 + index) % schema.radix := by
      calc
        1 + index = (1 + index) % schema.radix +
            schema.radix * ((1 + index) / schema.radix) :=
          decomposition.symm
        _ = (1 + index) % schema.radix + schema.radix * 1 := by
          rw [quotientOne]
        _ = schema.radix + (1 + index) % schema.radix := by ring
    simp only [authoredRule8, SemanticTerm.denote,
      semanticCarryApply, carry, if_pos, digitSum]
    calc
      schema.radix * valuation "x" + index + 1 =
          schema.radix * valuation "x" + (1 + index) := by ring
      _ = schema.radix * valuation "x" +
            (schema.radix + (1 + index) % schema.radix) := by
          exact congrArg
            (fun value => schema.radix * valuation "x" + value)
            sumEquation
      _ = schema.radix * (valuation "x" + 1) +
            (1 + index) % schema.radix := by ring
  · have sumLt : 1 + index < schema.radix := Nat.lt_of_not_ge carry
    have remainder : (1 + index) % schema.radix = 1 + index :=
      Nat.mod_eq_of_lt sumLt
    simp only [authoredRule8, SemanticTerm.denote,
      semanticCarryApply, carry, if_false, digitSum]
    calc
      schema.radix * valuation "x" + index + 1 =
          schema.radix * valuation "x" + (1 + index) := by ring
      _ = schema.radix * valuation "x" +
            (1 + index) % schema.radix := by rw [remainder]

theorem authoredRule9_sound (schema : Schema) (index : Nat) :
    (authoredRule9 schema index).Sound := by
  intro valuation
  simp [authoredRule9, SemanticTerm.denote]

theorem authoredRule10_sound (schema : Schema) (first second : Nat) :
    (authoredRule10 schema first second).Sound := by
  intro valuation
  simp only [authoredRule10, SemanticTerm.denote]
  rw [semanticDigitProductNumeral_denote]
  ring

theorem authoredRule4Family_sound (schema : Schema) :
    ∀ generated ∈ authoredRule4Family schema, generated.Sound := by
  simp only [authoredRule4Family, List.forall_mem_flatMap,
    List.forall_mem_map]
  intro first firstMember second secondMember
  exact authoredRule4_sound schema
    ((Schema.mem_digits_iff schema first).mp firstMember)
    ((Schema.mem_digits_iff schema second).mp secondMember)

theorem authoredRule6Family_sound (schema : Schema) :
    ∀ generated ∈ authoredRule6Family schema, generated.Sound := by
  simp only [authoredRule6Family, List.forall_mem_map]
  intro index indexMember
  exact authoredRule6_sound schema index

theorem authoredRule8Family_sound (schema : Schema) :
    ∀ generated ∈ authoredRule8Family schema, generated.Sound := by
  simp only [authoredRule8Family, List.forall_mem_map]
  intro index indexMember
  exact authoredRule8_sound schema
    ((Schema.mem_digits_iff schema index).mp indexMember)

theorem authoredRule9Family_sound (schema : Schema) :
    ∀ generated ∈ authoredRule9Family schema, generated.Sound := by
  simp only [authoredRule9Family, List.forall_mem_map]
  intro index indexMember
  exact authoredRule9_sound schema index

theorem authoredRule10Family_sound (schema : Schema) :
    ∀ generated ∈ authoredRule10Family schema, generated.Sound := by
  simp only [authoredRule10Family, List.forall_mem_flatMap,
    List.forall_mem_map]
  intro first firstMember second secondMember
  exact authoredRule10_sound schema first second

/-- Every rule projected into the generated `LanguageDef` preserves the
standard-natural-number denotation. -/
theorem authoredRules_sound (schema : Schema) :
    ∀ generated ∈ authoredRules schema, generated.Sound := by
  have firstThree :
      ∀ generated ∈ [authoredRule1 schema, authoredRule2 schema,
        authoredRule3 schema], generated.Sound := by
    simp only [List.forall_mem_cons]
    exact ⟨authoredRule1_sound schema,
      authoredRule2_sound schema,
      authoredRule3_sound schema,
      List.forall_mem_nil _⟩
  have fifth : ∀ generated ∈ [authoredRule5 schema], generated.Sound := by
    simp only [List.forall_mem_cons]
    exact ⟨authoredRule5_sound schema, List.forall_mem_nil _⟩
  have seventh : ∀ generated ∈ [authoredRule7 schema], generated.Sound := by
    simp only [List.forall_mem_cons]
    exact ⟨authoredRule7_sound schema, List.forall_mem_nil _⟩
  simp only [authoredRules, List.forall_mem_append]
  exact ⟨firstThree,
    authoredRule4Family_sound schema,
    fifth,
    authoredRule6Family_sound schema,
    seventh,
    authoredRule8Family_sound schema,
    authoredRule9Family_sound schema,
    authoredRule10Family_sound schema⟩

/-! ## Independent radix-two transcription gate -/

/-- Rule content compared independently of display identity.  Excluding the
name is intentional: paper-family identity is retained for provenance, while
rename-only changes must not alter arithmetic. -/
structure RuleShape where
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
deriving DecidableEq

def RuleShape.ofRule (generated : RewriteRule) : RuleShape := {
  typeContext := generated.typeContext
  premises := generated.premises
  left := generated.left
  right := generated.right
}

private def paperShape (metavariables : List String)
    (left right : Pattern) : RuleShape := {
  typeContext := metavariables.map natVariable
  premises := []
  left := left
  right := right
}

/-- Explicit paper transcription for radix two.  This is deliberately not
defined through `rule1`--`rule10`; equality below checks the schema generator
against a second representation of the published DA rules. -/
def radixTwoPaperShapes : List RuleShape :=
  [
    -- 1
    paperShape [] (digit 0 empty) empty,
    -- 2--3
    paperShape ["x"] (add empty (v "x")) (v "x"),
    paperShape ["x"] (add (v "x") empty) (v "x"),
    -- 4, all digit pairs
    paperShape ["x", "y"]
      (add (digit 0 (v "x")) (digit 0 (v "y")))
      (digit 0 (add (v "x") (v "y"))),
    paperShape ["x", "y"]
      (add (digit 0 (v "x")) (digit 1 (v "y")))
      (digit 1 (add (v "x") (v "y"))),
    paperShape ["x", "y"]
      (add (digit 1 (v "x")) (digit 0 (v "y")))
      (digit 1 (add (v "x") (v "y"))),
    paperShape ["x", "y"]
      (add (digit 1 (v "x")) (digit 1 (v "y")))
      (digit 0 (succ (add (v "x") (v "y")))),
    -- 5
    paperShape ["x"] (mul empty (v "x")) empty,
    -- 6, both final digits
    paperShape ["x", "y"] (mul (digit 0 (v "x")) (v "y"))
      (add (digit 0 (mul (v "x") (v "y"))) (star 0 (v "y"))),
    paperShape ["x", "y"] (mul (digit 1 (v "x")) (v "y"))
      (add (digit 0 (mul (v "x") (v "y"))) (star 1 (v "y"))),
    -- 7
    paperShape [] (succ empty) (digit 1 empty),
    -- 8, both final digits
    paperShape ["x"] (succ (digit 0 (v "x"))) (digit 1 (v "x")),
    paperShape ["x"] (succ (digit 1 (v "x")))
      (digit 0 (succ (v "x"))),
    -- 9, both auxiliary digit multipliers
    paperShape [] (star 0 empty) empty,
    paperShape [] (star 1 empty) empty,
    -- 10, all multiplier/final-digit pairs
    paperShape ["x"] (star 0 (digit 0 (v "x")))
      (add (digit 0 (star 0 (v "x"))) empty),
    paperShape ["x"] (star 0 (digit 1 (v "x")))
      (add (digit 0 (star 0 (v "x"))) empty),
    paperShape ["x"] (star 1 (digit 0 (v "x")))
      (add (digit 0 (star 1 (v "x"))) empty),
    paperShape ["x"] (star 1 (digit 1 (v "x")))
      (add (digit 0 (star 1 (v "x"))) (digit 1 empty))
  ]

/-- The generated radix-two instance exactly matches the independently
transcribed paper rules, in paper-family and digit-lexicographic order. -/
theorem radixTwo_matches_paper :
    (language radixTwo).rewrites.map RuleShape.ofRule = radixTwoPaperShapes := by
  decide +kernel

/-- Negative control: a dropped carry is rejected by the independent paper
transcription, rather than merely by a theorem about the generator itself. -/
theorem radixTwo_dropped_carry_fails_paper_gate :
    ((language radixTwo).rewrites.map RuleShape.ofRule).set 6
        (paperShape ["x", "y"]
          (add (digit 1 (v "x")) (digit 1 (v "y")))
          (digit 0 (add (v "x") (v "y")))) ≠
      radixTwoPaperShapes := by
  decide +kernel

theorem rule4Family_length (schema : Schema) :
    (rule4Family schema).length = schema.radix * schema.radix := by
  simp [rule4Family, authoredRule4Family, Schema.digits]

theorem rule6Family_length (schema : Schema) :
    (rule6Family schema).length = schema.radix := by
  simp [rule6Family, authoredRule6Family, Schema.digits]

theorem rule8Family_length (schema : Schema) :
    (rule8Family schema).length = schema.radix := by
  simp [rule8Family, authoredRule8Family, Schema.digits]

theorem rule9Family_length (schema : Schema) :
    (rule9Family schema).length = schema.radix := by
  simp [rule9Family, authoredRule9Family, Schema.digits]

theorem rule10Family_length (schema : Schema) :
    (rule10Family schema).length = schema.radix * schema.radix := by
  simp [rule10Family, authoredRule10Family, Schema.digits]

/-- Every finite DA instance has exactly `5 + 3R + 2R^2` rules. -/
theorem rewrites_length (schema : Schema) :
    (rewrites schema).length =
      5 + 3 * schema.radix + 2 * (schema.radix * schema.radix) := by
  simp [rewrites, authoredRules, authoredRule4Family,
    authoredRule6Family, authoredRule8Family, authoredRule9Family,
    authoredRule10Family, Schema.digits]
  omega

theorem radixTwo_rule_count : (language radixTwo).rewrites.length = 19 := by
  decide

theorem radixTwo_term_count : (language radixTwo).terms.length = 8 := by
  decide

/-- Small-radix expansion is closed: the paper's DA rules have no premises. -/
theorem radixTwo_premise_free :
    ∀ generated ∈ (language radixTwo).rewrites, generated.premises = [] := by
  decide

/-- The carry instance `1 + 1` is structurally present at radix two. -/
theorem radixTwo_one_plus_one_rule :
    (rule4 radixTwo 1 1).right =
      digit 0 (succ (add (v "x") (v "y"))) := by
  decide

/-- Negative control: dropping the carry cannot preserve the generated rule. -/
theorem radixTwo_dropped_carry_rejected :
    (rule4 radixTwo 1 1).right ≠
      digit 0 (add (v "x") (v "y")) := by
  decide

/-- The zero digit product is the canonical empty numeral, not a hidden
noncanonical `empty 0` requiring an unrelated cleanup step. -/
theorem radixTwo_zero_product_is_empty :
    digitProductNumeral radixTwo 0 1 = empty := by
  decide

#print axioms rewrites_length
#print axioms radixTwo_premise_free
#print axioms radixTwo_one_plus_one_rule
#print axioms radixTwo_matches_paper
#print axioms radixTwo_dropped_carry_fails_paper_gate
#print axioms decodeDigits_injective_on_canonical
#print axioms digitAddCarry_spec
#print axioms authoredRules_sound

end Mettapedia.GSLT.LanguageDef.WaltersZantemaDA
