import Mettapedia.CategoryTheory.RelativeClosedRawConstructions
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSoundness

/-!
# Independent structural readings of authored raw categorical arrows

These local lemmas read actual raw constructors in an independently supplied
target assignment. Exponential readings retain both argument and parameter;
presented equalizers use the actual two supplied defining arrows. No
generated-tree soundness or declaration realization is assumed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.RawInterpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open GeneratedCategory Interpretation

universe u v a w z
variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : Assignment C symbols D)

abbrev ObjectReads (raw : Object signature) (value : D) : Prop :=
  meanings.evaluateObject raw.code = some value

abbrev Reads {source target : Object signature} (raw : RawHom source target)
    {before after : D} (value : before ⟶ after) : Prop :=
  meanings.evaluateArrow raw.code = some ⟨before, after, value⟩

theorem identity {source : Object signature} {value : D}
    (sourceRead : ObjectReads meanings source value) :
    Reads meanings (RawHom.identity source) (𝟙 value) := meanings.evaluate_identity sourceRead

theorem terminal {source : Object signature} {value : D}
    (sourceRead : ObjectReads meanings source value) :
    Reads meanings (RawHom.terminal source) (toUnit value) :=
  meanings.evaluate_terminal_arrow sourceRead

theorem first {left right : Object signature} {before after : D}
    (leftRead : ObjectReads meanings left before) (rightRead : ObjectReads meanings right after) :
    Reads meanings (RawHom.first left right) (fst before after) :=
  meanings.evaluate_first leftRead rightRead

theorem second {left right : Object signature} {before after : D}
    (leftRead : ObjectReads meanings left before) (rightRead : ObjectReads meanings right after) :
    Reads meanings (RawHom.second left right) (snd before after) :=
  meanings.evaluate_second leftRead rightRead

theorem compose {source middle target : Object signature}
    {before : RawHom source middle} {after : RawHom middle target}
    {first second third : D} {f : first ⟶ second} {g : second ⟶ third}
    (beforeRead : Reads meanings before f) (afterRead : Reads meanings after g) :
    Reads meanings (before.compose after) (f ≫ g) :=
  meanings.evaluate_compose f g beforeRead afterRead

theorem pair {source left right : Object signature}
    {before : RawHom source left} {after : RawHom source right}
    {context first second : D} {f : context ⟶ first} {g : context ⟶ second}
    (beforeRead : Reads meanings before f) (afterRead : Reads meanings after g) :
    Reads meanings (RawHom.pair before after) (lift f g) :=
  meanings.evaluate_pair f g beforeRead afterRead

theorem exchange {left right : Object signature} {before after : D}
    (leftRead : ObjectReads meanings left before) (rightRead : ObjectReads meanings right after) :
    Reads meanings (RawHom.exchange left right) (Interpretation.exchange before after) :=
  pair meanings (second meanings leftRead rightRead) (first meanings leftRead rightRead)

theorem evaluation {argument result : Object signature} {before after : D}
    (argumentRead : ObjectReads meanings argument before) (resultRead : ObjectReads meanings result after) :
    Reads meanings (RawHom.evaluation argument result) (Interpretation.evaluation before after) :=
  meanings.evaluate_evaluation argumentRead resultRead

theorem abstract {context argument result : Object signature}
    {body : RawHom (product context argument) result} {Γ A B : D} {value : Γ ⊗ A ⟶ B}
    (contextRead : ObjectReads meanings context Γ) (argumentRead : ObjectReads meanings argument A)
    (resultRead : ObjectReads meanings result B) (bodyRead : Reads meanings body value) :
    Reads meanings (RawHom.abstract body) (Interpretation.abstraction value) :=
  meanings.evaluate_abstraction value contextRead argumentRead resultRead bodyRead

theorem quote {context argument result : Object signature}
    {body : RawHom (product argument context) result} {Γ A B : D} {value : A ⊗ Γ ⟶ B}
    (contextRead : ObjectReads meanings context Γ) (argumentRead : ObjectReads meanings argument A)
    (resultRead : ObjectReads meanings result B) (bodyRead : Reads meanings body value) :
    Reads meanings (RawHom.quote body) (MonoidalClosed.curry value) := by
  have supplied := abstract meanings contextRead argumentRead resultRead
    (compose meanings (exchange meanings contextRead argumentRead) bodyRead)
  have actual : Interpretation.abstraction (Interpretation.exchange Γ A ≫ value) =
      MonoidalClosed.curry value := by
    unfold Interpretation.abstraction
    rw [← Category.assoc, Interpretation.exchange_exchange, Category.id_comp]
  exact supplied.trans (congrArg (fun arrow => some (⟨Γ, A ⟶[D] B, arrow⟩ : ArrowValue D)) actual)

theorem inclusion {source target : Object signature} {before after : RawHom source target}
    {first second : D} {f g : first ⟶ second}
    (sourceRead : ObjectReads meanings source first) (targetRead : ObjectReads meanings target second)
    (beforeRead : Reads meanings before f) (afterRead : Reads meanings after g) :
    Reads meanings (RawHom.inclusion before after) (equalizer.ι f g) :=
  meanings.evaluate_equalizer_arrow f g sourceRead targetRead beforeRead afterRead

end Mettapedia.CategoryTheory.RelativeClosedSyntax.RawInterpretation
