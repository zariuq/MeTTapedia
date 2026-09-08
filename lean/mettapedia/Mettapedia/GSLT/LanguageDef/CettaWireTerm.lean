/-!
# Physical CeTTa S-expression carrier

CeTTa's authored data protocols distinguish symbols, quoted strings, natural
numbers, and applications.  This module records that shared physical carrier
once, independently of any grammar, calculus, or proof protocol.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CettaWire

universe u v

/-- The distinctions retained by CeTTa's parsed S-expression carrier. -/
inductive Term where
  | symbol (name : String)
  | string (value : String)
  | natural (value : Nat)
  | application (head : String) (arguments : List Term)
deriving Repr

mutual

/-- Render one physical carrier value using CeTTa's authored catalog syntax. -/
def Term.render : Term -> String
  | .symbol name => name
  | .string value => reprStr value
  | .natural value => toString value
  | .application head arguments =>
      "(" ++ head ++ Term.renderArguments arguments ++ ")"

def Term.renderArguments : List Term -> String
  | [] => ""
  | argument :: arguments =>
      " " ++ argument.render ++ Term.renderArguments arguments

end

/-- The exact `LNil`/`LCons` algebraic-list carrier shared by CeTTa data
protocols. -/
def encodeList {α : Type u} (encode : α -> Term) : List α -> Term
  | [] => .symbol "LNil"
  | value :: values =>
      .application "LCons" [encode value, encodeList encode values]

/-- Fail-closed decoding of the exact `LNil`/`LCons` carrier. -/
def decodeList {α : Type u} (decode : Term -> Option α) :
    Term -> Option (List α)
  | .symbol "LNil" => some []
  | .application "LCons" [value, values] => do
      let head <- decode value
      let tail <- decodeList decode values
      some (head :: tail)
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodeList_encodeList {α : Type u}
    (decode : Term -> Option α)
    (encode : α -> Term)
    (roundTrip : forall value, decode (encode value) = some value)
    (values : List α) :
    decodeList decode (encodeList encode values) = some values := by
  induction values with
  | nil => simp [encodeList, decodeList]
  | cons value values inductionHypothesis =>
      simp [encodeList, decodeList, roundTrip, inductionHypothesis]

/-- Heterogeneous list correspondence for a physical element encoder whose
decoder produces a distinct typed representation. -/
theorem decodeList_encodeList_map {α : Type u} {β : Type v}
    (decode : Term -> Option β) (encode : α -> Term) (meaning : α -> β)
    (elementExact : forall value, decode (encode value) = some (meaning value))
    (values : List α) :
    decodeList decode (encodeList encode values) = some (values.map meaning) := by
  induction values with
  | nil => simp [encodeList, decodeList]
  | cons value values inductionHypothesis =>
      simp [encodeList, decodeList, elementExact, inductionHypothesis]

end Mettapedia.GSLT.LanguageDef.CettaWire
