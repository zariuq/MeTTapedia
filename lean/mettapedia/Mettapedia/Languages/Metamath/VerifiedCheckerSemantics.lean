import Mettapedia.Languages.Metamath.GroundedSemantics

/-!
# Verified Metamath checker semantics

This module exposes the smallest semantic boundary needed by generated
source parsers.  It depends directly on the verified `mm-lean4` runtime and
declarative theorem, but not on fixture computations or on a syntax grammar.

The syntax grammar remains an independent source of parser certificates.
Their only semantic connection is the typed lowering proved in a separate
composition module.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.VerifiedCheckerSemantics

open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.MMLean4Bridge

/-- Acceptance by the verified proof machine at an explicit runtime
database. -/
def RuntimeAccepts (database : RuntimeDB) (label : String)
    (formula : RuntimeFormula) : Prop :=
  ∃ (proof : Array String) (finalState : RuntimeProofState)
      (result : RuntimeFormula),
    proof.foldlM (fun state step => database.stepNormal state step)
      ⟨⟨0, 0⟩, label, formula, database.frame, #[], #[],
        Metamath.Verify.ProofTokenParser.normal⟩ = .ok finalState ∧
      finalState.stack.size = 1 ∧
      finalState.stack[0]? = some result ∧
      toOperationalExpr result = toOperationalExpr formula

/-- Acceptance by the verified source parser and proof checker. -/
def ImplementationAccepts (bytes : ByteArray) (label : String)
    (formula : RuntimeFormula) : Prop :=
  RuntimeAccepts (checkBytesDB bytes) label formula

theorem implementationAccepts_iff_runtimeAccepts
    (bytes : ByteArray) (label : String) (formula : RuntimeFormula) :
    ImplementationAccepts bytes label formula ↔
      RuntimeAccepts (checkBytesDB bytes) label formula := by
  rfl

/-- Declarative acceptance in the operational specification exported by
`mm-lean4`. -/
def DeclarativeAccepts (bytes : ByteArray) (formula : RuntimeFormula) : Prop :=
  ∃ (database : OperationalDatabase) (frame : OperationalFrame),
    toOperationalDatabase (checkBytesDB bytes) = some database ∧
      toOperationalFrame (checkBytesDB bytes) (checkBytesDB bytes).frame =
        some frame ∧
      OperationalProvable database frame (toOperationalExpr formula)

/-- The verified checker accepts exactly the declaratively provable claims,
provided source parsing completed successfully. -/
theorem implementationAccepts_iff_declarativeAccepts
    (bytes : ByteArray) (label : String) (formula : RuntimeFormula)
    (readerAccepted : (checkBytesDB bytes).error? = none) :
    ImplementationAccepts bytes label formula ↔
      DeclarativeAccepts bytes formula := by
  simpa [ImplementationAccepts, RuntimeAccepts, DeclarativeAccepts,
    checkBytesDB] using
    parserAcceptance_iff_specProvable bytes label formula readerAccepted

end Mettapedia.Languages.Metamath.VerifiedCheckerSemantics
