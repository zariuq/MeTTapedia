import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRuleSignature
import Mathlib.Data.List.OfFn

/-!
# Ordered occurrence readouts of supplied dependent typing proofs

Readouts are computed by a local rule algebra, recording each premise path
and variable index. Identical labels at different positions remain separate
uses. This reads the actual supplied proof tree and does not choose another
certificate for its proof-irrelevant typing proposition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveRuleReadout

open JudgmentDerivation FormationSensitiveRuleSignature

inductive Label where
  | headType | variable (index : Nat) | constant (name : DeclName)
  | piForm | sigmaForm | lamIntro | appElim | pairIntro | fstElim | sndElim
  | idForm | reflIntro | cumul | convert
  deriving DecidableEq, Repr

structure Use where
  position : List Nat
  label : Label
  deriving DecidableEq, Repr

variable {Head : Type} {R : Rules Head}

def label {j : Judgment Head} : Rule R j → Label
  | .headType _ => .headType
  | .var index => .variable index.val
  | @Rule.const _ _ _ _ name _ _ _ _ => .constant name
  | .piForm _ _ _ => .piForm
  | .sigmaForm _ _ _ => .sigmaForm
  | .lamIntro _ => .lamIntro
  | .appElim => .appElim
  | .pairIntro _ => .pairIntro
  | .fstElim => .fstElim
  | .sndElim => .sndElim
  | .idForm _ => .idForm
  | .reflIntro => .reflIntro
  | .cumul _ => .cumul
  | .convert _ _ => .convert

def prependPosition (position : Nat) (use : Use) : Use :=
  ⟨position :: use.position, use.label⟩

def algebra (R : Rules Head) : Algebra (signature R) where
  Carrier _ := List Use
  conclude rule premises :=
    ⟨[], label rule⟩ :: (List.ofFn (fun position : Fin (premiseCount rule) =>
      (premises position).map (prependPosition position.val))).flatten

def readout {j : Judgment Head} (tree : Tree R j) : List Use := interpret (algebra R) tree

/-- The readout includes the current rule and all ordered child uses at
their separately supplied premise positions. -/
theorem readout_node {j : Judgment Head} (rule : Rule R j)
    (premises : (p : Fin (premiseCount rule)) → Tree R (hypothesis rule p)) :
    readout (.node rule premises) =
      ⟨[], label rule⟩ :: (List.ofFn (fun p : Fin (premiseCount rule) =>
        (readout (premises p)).map (prependPosition p.val))).flatten := rfl

/-- Different positions remain different even with equal rule labels and
equal internal paths. -/
theorem different_positions {first second : Nat} (different : first ≠ second) (use : Use) :
    prependPosition first use ≠ prependPosition second use := by
  intro equal
  have paths := congrArg Use.position equal
  exact different (List.cons.inj paths).1

/-- Literal recovery after origin-retaining transport can consume this
computed readout; erasing proof choices need not preserve it. -/
theorem readout_congr {j : Judgment Head} {first second : Tree R j}
    (same : first = second) : readout first = readout second := congrArg readout same

end FormationSensitiveRuleReadout
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
