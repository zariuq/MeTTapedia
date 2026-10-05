import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ExtractionLaws

/-! # Checked source elimination

These proof constructors select a source branch before running its body. The
other branch is not an evaluated operand. The extractor must prove the branch
runs from the actual source; these laws do not supply guest computations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction

def encodePair {α β : Type} (left : α → Term) (right : β → Term) (value : α × β) : Term :=
  named "Pair" [left value.1, right value.2]

theorem boolean_injective : Function.Injective boolean := by
  intro left right equal
  cases left <;> cases right <;> simp_all [boolean]

theorem encodeOption_injective {α : Type} {encode : α → Term}
    (injective : Function.Injective encode) : Function.Injective (encodeOption encode) := by
  intro left right equal
  cases left with
  | none => cases right <;> simp_all [encodeOption]
  | some first =>
      cases right with
      | none => cases equal
      | some second =>
          have fields : encode first = encode second := by
            simpa [encodeOption] using equal
          exact congrArg Option.some (injective fields)

theorem encodePair_injective {α β : Type} {left : α → Term} {right : β → Term}
    (leftInjective : Function.Injective left) (rightInjective : Function.Injective right) :
    Function.Injective (encodePair left right) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ equal
  have fields : left a = left c ∧ right b = right d := by
    simpa [encodePair, named] using equal
  exact Prod.ext (leftInjective fields.1) (rightInjective fields.2)

theorem applies_bool_elimination {α : Type} {P : Program} {H : Host}
    (encode : α → Term) (head : String) (captures : List Term) (condition : Bool)
    (whenFalse whenTrue : α)
    (falseCase : Applies P H head (.sym "False" :: captures) (encode whenFalse))
    (trueCase : Applies P H head (.sym "True" :: captures) (encode whenTrue)) :
    Applies P H head (boolean condition :: captures)
      (encode (if condition then whenTrue else whenFalse)) := by
  cases condition with
  | false => exact falseCase
  | true => exact trueCase

theorem applies_ite_elimination {α : Type} {P : Program} {H : Host}
    (encode : α → Term) (head : String) (captures : List Term) (condition : Prop)
    [Decidable condition] (whenTrue whenFalse : α)
    (trueCase : condition → Applies P H head (.sym "True" :: captures) (encode whenTrue))
    (falseCase : ¬ condition → Applies P H head (.sym "False" :: captures) (encode whenFalse)) :
    Applies P H head (boolean (decide condition) :: captures)
      (encode (if condition then whenTrue else whenFalse)) := by
  by_cases holds : condition
  · simpa [holds, boolean] using trueCase holds
  · simpa [holds, boolean] using falseCase holds

theorem applies_dite_elimination {α : Type} {P : Program} {H : Host}
    (encode : α → Term) (head : String) (captures : List Term) (condition : Prop)
    [Decidable condition] (whenTrue : condition → α) (whenFalse : ¬ condition → α)
    (trueCase : ∀ proof, Applies P H head (.sym "True" :: captures) (encode (whenTrue proof)))
    (falseCase : ∀ proof, Applies P H head (.sym "False" :: captures) (encode (whenFalse proof))) :
    Applies P H head (boolean (decide condition) :: captures)
      (encode (if proof : condition then whenTrue proof else whenFalse proof)) := by
  by_cases holds : condition
  · simpa [holds, boolean] using trueCase holds
  · simpa [holds, boolean] using falseCase holds

theorem applies_option_elimination {α β : Type} {P : Program} {H : Host}
    (encode : α → Term) (encodeResult : β → Term) (head : String) (captures : List Term)
    (source : Option α) (whenNone : β) (whenSome : α → β)
    (noneCase : Applies P H head (.sym "None" :: captures) (encodeResult whenNone))
    (someCase : ∀ value, Applies P H head (named "Some" [encode value] :: captures)
      (encodeResult (whenSome value))) :
    Applies P H head (encodeOption encode source :: captures)
      (encodeResult (source.elim whenNone whenSome)) := by
  cases source with
  | none => exact noneCase
  | some value => exact someCase value

theorem applies_product_elimination {α β γ : Type} {P : Program} {H : Host}
    (left : α → Term) (right : β → Term) (encodeResult : γ → Term)
    (head : String) (captures : List Term) (source : α × β) (body : α → β → γ)
    (selected : ∀ a b, Applies P H head (encodePair left right (a, b) :: captures)
      (encodeResult (body a b))) :
    Applies P H head (encodePair left right source :: captures)
      (encodeResult (body source.1 source.2)) := by
  cases source with
  | mk a b => exact selected a b

theorem applies_result_congr {P : Program} {H : Host} {head : String}
    {arguments : List Term} {first second : Term}
    (computed : Applies P H head arguments first) (equal : first = second) :
    Applies P H head arguments second := equal ▸ computed

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction
