import Mettapedia.CategoryTheory.RelativeClosedRawInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSoundness

/-!
# Independent complete argument-first function readouts

The authored raw application reads a supplied function on its entire value
and parameter context. The exchange required by the raw context-first
evaluation is cancelled explicitly. No realized whole model or semantic
application law is supplied as an assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.RawFunctionInterpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open GeneratedCategory Interpretation RawInterpretation

universe u v a w z
variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : Assignment C symbols D)

theorem read {context argument result : Object signature}
    {raw : RawHom context (exponentialObject argument result)} {Γ A B : D}
    {function : Γ ⟶ (A ⟶[D] B)}
    (contextRead : ObjectReads meanings context Γ)
    (argumentRead : ObjectReads meanings argument A)
    (resultRead : ObjectReads meanings result B)
    (functionRead : Reads meanings raw function) :
    Reads meanings (RawHom.read raw) (MonoidalClosed.uncurry function) := by
  have first := RawInterpretation.compose meanings
    (RawInterpretation.first meanings (left := context) (right := argument) contextRead argumentRead)
    functionRead
  have second := RawInterpretation.second meanings (left := context) (right := argument)
    contextRead argumentRead
  have applied := RawInterpretation.compose meanings (RawInterpretation.pair meanings first second)
    (RawInterpretation.evaluation meanings (argument := argument) (result := result) argumentRead resultRead)
  have supplied := RawInterpretation.compose meanings
    (RawInterpretation.exchange meanings (left := argument) (right := context) argumentRead contextRead) applied
  have complete : Interpretation.exchange A Γ ≫
      (lift (fst Γ A ≫ function) (snd Γ A) ≫ Interpretation.evaluation A B) =
      MonoidalClosed.uncurry function := by
    rw [Interpretation.application_eq, ← Category.assoc,
      Interpretation.exchange_exchange, Category.id_comp]
  exact supplied.trans (congrArg (fun arrow => some (⟨A ⊗ Γ, B, arrow⟩ : ArrowValue D)) complete)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.RawFunctionInterpretation
