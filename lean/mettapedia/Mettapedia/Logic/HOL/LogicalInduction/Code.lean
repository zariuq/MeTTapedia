import Mettapedia.Logic.HOL.Syntax.Closed

/-!
# Logical-Induction-Ready Coding of Closed HOL Syntax

This module provides the canonical "code" layer for closed HOL syntax used by
the logical-induction-ready higher-order belief infrastructure.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), we treat closed formulas as the
primary tradable/queryable objects.  In this first pass, the canonical code is
the real closed HOL syntax itself, together with explicit encode/decode views.

This keeps the code layer honest and close to the existing Church-style HOL
syntax while still giving a dedicated interface for future quoting, reflection,
and trader-style reasoning.
-/

namespace Mettapedia.Logic.HOL.LogicalInduction

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

section DecEq

noncomputable instance instDecidableEqTerm : DecidableEq (Term Const Γ τ) := by
  intro a b
  classical
  exact inferInstance

end DecEq

/-- Canonical closed-term code for logical-induction-ready HOL reasoning.

In this first pass the code is the real closed syntax itself. -/
abbrev ClosedTermCode (Const : Ty Base → Type v) (τ : Ty Base) := ClosedTerm Const τ

/-- Canonical closed-formula code for logical-induction-ready HOL reasoning. -/
abbrev ClosedFormulaCode (Const : Ty Base → Type v) := ClosedFormula Const

/-- Alias emphasizing the sentence-level use in belief/trader layers. -/
abbrev ClosedSentenceCode (Const : Ty Base → Type v) := ClosedFormulaCode Const

/-- Encode a closed HOL term into the canonical LI code layer. -/
def encodeClosedTerm (t : ClosedTerm Const τ) : ClosedTermCode Const τ := t

/-- Decode a canonical LI closed-term code back to the underlying HOL term. -/
def decodeClosedTerm (c : ClosedTermCode Const τ) : ClosedTerm Const τ := c

/-- Encode a closed HOL formula into the canonical LI code layer. -/
def encodeClosedFormula (φ : ClosedFormula Const) : ClosedFormulaCode Const := φ

/-- Decode a canonical LI closed-formula code back to the underlying HOL formula. -/
def decodeClosedFormula (c : ClosedFormulaCode Const) : ClosedFormula Const := c

@[simp] theorem decode_encodeClosedTerm (t : ClosedTerm Const τ) :
    decodeClosedTerm (encodeClosedTerm t) = t := rfl

@[simp] theorem encode_decodeClosedTerm (c : ClosedTermCode Const τ) :
    encodeClosedTerm (decodeClosedTerm c) = c := rfl

@[simp] theorem decode_encodeClosedFormula (φ : ClosedFormula Const) :
    decodeClosedFormula (encodeClosedFormula φ) = φ := rfl

@[simp] theorem encode_decodeClosedFormula (c : ClosedFormulaCode Const) :
    encodeClosedFormula (decodeClosedFormula c) = c := rfl

theorem closedFormulaCode_roundTrip (φ : ClosedFormula Const) :
    encodeClosedFormula (decodeClosedFormula (encodeClosedFormula φ)) =
      encodeClosedFormula φ := by
  rfl

end Mettapedia.Logic.HOL.LogicalInduction
