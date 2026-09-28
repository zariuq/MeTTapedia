import Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation

/-!
# Literal concatenation does not preserve alternative identity

The literal-only projection branch concatenates fixed terminal spellings and
omits the production label. Distinct alternatives can therefore have the same
payload. These controls use the existing authored BNF alternative carrier;
they do not propose another grammar or canonical term representation.

This is a counterexample to recovering every derivation from its literal
payload, not to relational text round trips. Retaining two equal answer
occurrences preserves multiplicity but cannot recover their rule identities.
The native branch still needs a source-preserving repair before a universal
derivation round-trip theorem can describe it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CanonicalLiteralIdentity

open PlainBnfStructuredDenotation

/-- The literal-only projection accepts every fixed terminal, in order,
and refuses a nonterminal reference. -/
def literalText? : List Element → Option String
  | [] => some ""
  | .literal text _ :: rest => (literalText? rest).map (text ++ ·)
  | .reference _ _ :: _ => none

def oneTerminal : Alternative :=
  ⟨[.literal "ab" ⟨0, 4⟩], ⟨0, 4⟩⟩

def twoTerminals : Alternative :=
  ⟨[.literal "a" ⟨7, 10⟩, .literal "b" ⟨11, 14⟩], ⟨7, 14⟩⟩

/-- These are the two alternatives of `s ::= "ab" | "a" "b"`. -/
def alternatives : List Alternative := [oneTerminal, twoTerminals]

theorem alternatives_distinct : oneTerminal ≠ twoTerminals := by decide +kernel

theorem one_payload : literalText? oneTerminal.elements = some "ab" := by decide +kernel

theorem two_payload : literalText? twoTerminals.elements = some "ab" := by decide +kernel

/-- No deterministic decoder of this payload can recover both authored
alternatives, even with this one fixed grammar and sort supplied externally. -/
theorem no_literal_left_inverse (recover : String → Option Alternative) :
    ¬ (∀ alternative ∈ alternatives, ∀ text,
      literalText? alternative.elements = some text → recover text = some alternative) := by
  intro inverse
  have first := inverse oneTerminal (by simp [alternatives]) "ab" one_payload
  have second := inverse twoTerminals (by simp [alternatives]) "ab" two_payload
  exact alternatives_distinct (Option.some.inj (first.symm.trans second))

theorem literal_projection_not_injective :
    ¬ Function.Injective (fun alternative : Alternative =>
      literalText? alternative.elements) := by
  intro injective
  exact alternatives_distinct (injective (one_payload.trans two_payload.symm))

/-- A reference is not mistaken for an empty or literal-only production. -/
example : literalText? [.reference "x" ⟨0, 3⟩] = none := rfl

example : literalText? [] = some "" := rfl

example : literalText? [.literal "a" ⟨0, 3⟩, .reference "x" ⟨4, 7⟩] = none := rfl

#print axioms no_literal_left_inverse
#print axioms literal_projection_not_injective

end Mettapedia.GSLT.Parsing.CanonicalLiteralIdentity
