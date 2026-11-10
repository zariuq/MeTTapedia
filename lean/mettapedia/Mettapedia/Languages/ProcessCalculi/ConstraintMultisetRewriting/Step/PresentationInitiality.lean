import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSourceRecovery
import Mettapedia.GSLT.Parsing.LanguageDefGrammarInitiality

/-! # Initial structural interpretation of the transform presentation

Initiality fixes how a declared constructor interpretation extends to trees.
It does not choose the frame, solver, admission profile or operational
observation. Payload decoding is an actual consumer of this unique fold.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation

open Mettapedia.GSLT.Parsing
open LanguageDefGrammarAlgebra

/-- All 29 constructors of the composed entry participate in the universal
property. A target must interpret their actual ordered input sorts. -/
theorem authored_interpretation_exists_unique (target : Interpretation Source.rules) :
    ∃! read : Reader target, PreservesConstructors target read :=
  interpretation_exists_unique target

/-- Any constructor-preserving implementation of the payload interpretation
agrees with the independent structural decoder on every authored route. -/
theorem payload_reader_agrees (read : Reader Payloads.interpretation)
    (laws : PreservesConstructors Payloads.interpretation read)
    {sort : String} (route : Payloads.Route sort) :
    Payloads.decode sort ((syntaxAlgebra Payloads.rules).evaluate route).tree =
      some (read sort route) := by
  rw [reader_unique Payloads.interpretation read laws route]
  exact Payloads.decode_route route

/-- In particular, a constant readout cannot masquerade as the structural
interpretation: the actual zero and successor constructors remain distinct. -/
theorem payload_reader_cannot_collapse_indices (read : Reader Payloads.interpretation)
    (laws : PreservesConstructors Payloads.interpretation read) :
    read "TcIndex" (Payloads.indexRoute 0) ≠ read "TcIndex" (Payloads.indexRoute 1) := by
  rw [reader_unique Payloads.interpretation read laws (Payloads.indexRoute 0),
    reader_unique Payloads.interpretation read laws (Payloads.indexRoute 1)]
  change (0 : Nat) ≠ 1
  decide +kernel

#print axioms authored_interpretation_exists_unique
#print axioms payload_reader_agrees
#print axioms payload_reader_cannot_collapse_indices

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation
