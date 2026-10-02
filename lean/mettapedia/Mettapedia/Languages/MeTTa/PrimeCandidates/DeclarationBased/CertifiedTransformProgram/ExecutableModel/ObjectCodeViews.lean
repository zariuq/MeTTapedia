import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetSquareTerms
import Mettapedia.GSLT.Core.NonFactorization

/-!
# The object package's proposition codes as data and as truth values

A closed proposition code of the object package can be viewed as data, the code
term itself, or as a truth value, its meaning.  The set tower sees a code only
through its truth value, and the code keeps more than the truth value does.
This is the instance, at the candidate's own codes, of the comparison of views
in `Mettapedia.Logic.Propositions.Verification`.

* `truthOf`: the truth value of a closed code, its meaning in a setting.
* **The set tower reads a code through its truth value**
  (`factors_truthOf_towerValue`): the tower's value of a closed code is a
  function of its meaning, by `ev_closed`.
* **A code keeps more than its truth value**: the code `(λp. p) c` and the code
  `c` have one meaning (`redex_truthOf`) and are different code terms, so
  whether a code is a redex is not a feature of its truth value
  (`isRedex_not_factors_truthOf`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Consistency (Carrier Kind Setting Q numClass sucClass
  Truth Read World Morph DataEq dataValue InterpAt Interp levelsBelow NumVal numVal_numeral)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp traceApp_graph_beta)
open ZFSetTraceProofDecoding (truthCode)
open FormationSensitiveHOLInterface (typeAt)
open Mettapedia.Logic
open Mettapedia.GSLT.Core.NonFactorization

universe u

namespace CodeModel
namespace SetSquare

section Views

variable {Head : Type} (S : Setting Head)
  (plus : Q S.numerals .num → Q S.numerals .num → Q S.numerals .num)

/-- The truth value of a closed code: its meaning. -/
def truthOf (code : CodeTerm [] .prop) : Prop :=
  code.meaning S plus MEnv.nil

/-- The code `(λp. p) c`. -/
def redexOf (code : CodeTerm [] .prop) : CodeTerm [] .prop :=
  .app (.lam (.var .zero)) code

/-- The redex has the meaning of its argument. -/
theorem redex_truthOf (code : CodeTerm [] .prop) :
    truthOf S plus (redexOf code) = truthOf S plus code :=
  rfl

/-- Whether a closed code is an application of an abstraction. -/
def isRedex : CodeTerm [] .prop → Bool
  | .app (.lam _) _ => true
  | _ => false

/-- The code of falsity, `all@prop (λp. p)`. -/
def falsity : CodeTerm [] .prop :=
  .allOf .prop (.var .zero)

/-- The witness: one truth value, two codes. -/
def isRedexFiber : NonTrivialFiber (truthOf S plus) isRedex where
  left := redexOf falsity
  right := falsity
  sameShadow := redex_truthOf S plus falsity
  differentValue := Bool.noConfusion

/-- **Whether a code is a redex is not a feature of its truth value.** -/
theorem isRedex_not_factors_truthOf : ¬ Factors (truthOf S plus) isRedex :=
  (isRedexFiber S plus).not_factors

end Views

section Tower

variable (h : CofinalInaccessibles.{u}) {Head : Type} {S : Setting Head} (laws : S.Laws)
  {plus : Q S.numerals .num → Q S.numerals .num → Q S.numerals .num}
  (plusNumerals : ∀ i j, plus (numClass S.numerals i) (numClass S.numerals j) =
    numClass S.numerals (i + j))

include laws plusNumerals in
/-- **The set tower reads a closed code through its truth value.** -/
theorem factors_truthOf_towerValue :
    Factors (truthOf S plus)
      (fun code : CodeTerm [] .prop => ev (objHeads h) (objectSetConsts h) code.toC Fin.elim0) :=
  ⟨fun truth => truthCode truth, fun code => (ev_closed h laws plusNumerals code).symm⟩

end Tower

end SetSquare
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
