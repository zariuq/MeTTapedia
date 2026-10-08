import Mettapedia.CategoryTheory.RelativeClosedSyntaxRelations

/-!
# Reconstructive regularity of relative closed judgments

Every admitted arrow has formed endpoints. Every generated equation has
formed endpoints and actual arrow admissions of both sides. The proof
reconstructs these judgments from the individual local rules, including
complete annotated abstraction and equalizer lifts. No interpretation or
global regularity premise is used.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Regularity

open _root_.CategoryTheory

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}

def Result (signature : Signature (C := C) (symbols := symbols)) : Judgment C symbols → Prop
  | .object code => Nonempty (Derivation signature (.object code))
  | .arrow source target _ =>
      Nonempty (Derivation signature (.object source)) ∧
      Nonempty (Derivation signature (.object target))
  | .equation source target before after =>
      Nonempty (Derivation signature (.object source)) ∧
      Nonempty (Derivation signature (.object target)) ∧
      Nonempty (Derivation signature (.arrow source target before)) ∧
      Nonempty (Derivation signature (.arrow source target after))

theorem derivation {judgment : Judgment C symbols} (tree : Derivation signature judgment) :
    Result signature judgment := by
  induction tree with
  | baseObject object => exact ⟨.baseObject object⟩
  | objectName origin => exact ⟨.objectName origin⟩
  | terminalObject => exact ⟨.terminalObject⟩
  | productObject left right _ _ => exact ⟨.productObject left right⟩
  | exponentialObject argument result _ _ => exact ⟨.exponentialObject argument result⟩
  | equalizerObject source target before after _ _ _ _ =>
      exact ⟨.equalizerObject source target before after⟩
  | baseArrow _arrow => exact ⟨⟨.baseObject _⟩, ⟨.baseObject _⟩⟩
  | arrowName _origin source target _ _ => exact ⟨⟨source⟩, ⟨target⟩⟩
  | identity formed _ => exact ⟨⟨formed⟩, ⟨formed⟩⟩
  | compose _before _after beforeIH afterIH => exact ⟨beforeIH.1, afterIH.2⟩
  | terminalArrow source _ => exact ⟨⟨source⟩, ⟨.terminalObject⟩⟩
  | first left right _ _ => exact ⟨⟨.productObject left right⟩, ⟨left⟩⟩
  | second left right _ _ => exact ⟨⟨.productObject left right⟩, ⟨right⟩⟩
  | pair _before _after beforeIH afterIH =>
      exact ⟨beforeIH.1, ⟨.productObject beforeIH.2.some afterIH.2.some⟩⟩
  | evaluation argument result _ _ =>
      exact ⟨⟨.productObject (.exponentialObject argument result) argument⟩, ⟨result⟩⟩
  | curry context argument result _body _ _ _ _ =>
      exact ⟨⟨context⟩, ⟨.exponentialObject argument result⟩⟩
  | equalizerArrow source target before after _ _ _ _ =>
      exact ⟨⟨.equalizerObject source target before after⟩, ⟨source⟩⟩
  | equalizerLift source target context before after _candidate _commutes _ _ _ _ _ _ _ =>
      exact ⟨⟨context⟩, ⟨.equalizerObject source target before after⟩⟩
  | reflexivity typed typedIH => exact ⟨typedIH.1, typedIH.2, ⟨typed⟩, ⟨typed⟩⟩
  | symmetry _same sameIH => exact ⟨sameIH.1, sameIH.2.1, sameIH.2.2.2, sameIH.2.2.1⟩
  | transitivity _before _after beforeIH afterIH =>
      exact ⟨beforeIH.1, beforeIH.2.1, beforeIH.2.2.1, afterIH.2.2.2⟩
  | compositionCongruence _beforeSame _afterSame beforeIH afterIH =>
      exact ⟨beforeIH.1, afterIH.2.1,
        ⟨.compose beforeIH.2.2.1.some afterIH.2.2.1.some⟩,
        ⟨.compose beforeIH.2.2.2.some afterIH.2.2.2.some⟩⟩
  | pairCongruence _beforeSame _afterSame beforeIH afterIH =>
      exact ⟨beforeIH.1, ⟨.productObject beforeIH.2.1.some afterIH.2.1.some⟩,
        ⟨.pair beforeIH.2.2.1.some afterIH.2.2.1.some⟩,
        ⟨.pair beforeIH.2.2.2.some afterIH.2.2.2.some⟩⟩
  | curryCongruence context argument result _same _ _ _ sameIH =>
      exact ⟨⟨context⟩, ⟨.exponentialObject argument result⟩,
        ⟨.curry context argument result sameIH.2.2.1.some⟩,
        ⟨.curry context argument result sameIH.2.2.2.some⟩⟩
  | leftIdentity source typed _ typedIH =>
      exact ⟨⟨source⟩, typedIH.2, ⟨.compose (.identity source) typed⟩, ⟨typed⟩⟩
  | rightIdentity target typed _ typedIH =>
      exact ⟨typedIH.1, ⟨target⟩, ⟨.compose typed (.identity target)⟩, ⟨typed⟩⟩
  | associativity before middle after beforeIH _ afterIH =>
      exact ⟨beforeIH.1, afterIH.2, ⟨.compose (.compose before middle) after⟩,
        ⟨.compose before (.compose middle after)⟩⟩
  | terminalUniqueness before after beforeIH _ =>
      exact ⟨beforeIH.1, ⟨.terminalObject⟩, ⟨before⟩, ⟨after⟩⟩
  | firstBeta left right before after _ _ beforeIH _ =>
      exact ⟨beforeIH.1, ⟨left⟩, ⟨.compose (.pair before after) (.first left right)⟩,
        ⟨before⟩⟩
  | secondBeta left right before after _ _ beforeIH _ =>
      exact ⟨beforeIH.1, ⟨right⟩, ⟨.compose (.pair before after) (.second left right)⟩,
        ⟨after⟩⟩
  | productEta left right typed _ _ typedIH =>
      exact ⟨typedIH.1, ⟨.productObject left right⟩,
        ⟨.pair (.compose typed (.first left right)) (.compose typed (.second left right))⟩,
        ⟨typed⟩⟩
  | exponentialBeta context argument result body _ _ _ _ =>
      exact ⟨⟨.productObject context argument⟩, ⟨result⟩,
        ⟨.compose
          (.pair (.compose (.first context argument) (.curry context argument result body))
            (.second context argument))
          (.evaluation argument result)⟩,
        ⟨body⟩⟩
  | exponentialEta context argument result typed _ _ _ _ =>
      exact ⟨⟨context⟩, ⟨.exponentialObject argument result⟩,
        ⟨.curry context argument result
          (.compose (.pair (.compose (.first context argument) typed) (.second context argument))
            (.evaluation argument result))⟩,
        ⟨typed⟩⟩
  | equalizerCondition source target before after _ _ _ _ =>
      exact ⟨⟨.equalizerObject source target before after⟩, ⟨target⟩,
        ⟨.compose (.equalizerArrow source target before after) before⟩,
        ⟨.compose (.equalizerArrow source target before after) after⟩⟩
  | equalizerBeta source target context before after candidate commutes _ _ _ _ _ _ _ =>
      exact ⟨⟨context⟩, ⟨source⟩,
        ⟨.compose (.equalizerLift source target context before after candidate commutes)
          (.equalizerArrow source target before after)⟩,
        ⟨candidate⟩⟩
  | equalizerUniqueness before after _same beforeIH _ _ =>
      exact ⟨beforeIH.1, beforeIH.2, ⟨before⟩, ⟨after⟩⟩
  | baseIdentity object =>
      exact ⟨⟨.baseObject object⟩, ⟨.baseObject object⟩, ⟨.baseArrow (𝟙 object)⟩,
        ⟨.identity (.baseObject object)⟩⟩
  | baseComposition before after =>
      exact ⟨⟨.baseObject _⟩, ⟨.baseObject _⟩, ⟨.baseArrow (before ≫ after)⟩,
        ⟨.compose (.baseArrow before) (.baseArrow after)⟩⟩
  | baseEquality _same =>
      exact ⟨⟨.baseObject _⟩, ⟨.baseObject _⟩, ⟨.baseArrow _⟩, ⟨.baseArrow _⟩⟩
  | declaredEquation _origin before after beforeIH _ =>
      exact ⟨beforeIH.1, beforeIH.2, ⟨before⟩, ⟨after⟩⟩

theorem arrow_endpoints {source target : ObjectCode C symbols} {code : ArrowCode C symbols}
    (typed : Nonempty (Derivation signature (.arrow source target code))) :
    Nonempty (Derivation signature (.object source)) ∧
      Nonempty (Derivation signature (.object target)) :=
  derivation typed.some

theorem equation_admissions {source target : ObjectCode C symbols}
    {before after : ArrowCode C symbols}
    (same : Nonempty (Derivation signature (.equation source target before after))) :
    Nonempty (Derivation signature (.arrow source target before)) ∧
      Nonempty (Derivation signature (.arrow source target after)) :=
  ⟨(derivation same.some).2.2.1, (derivation same.some).2.2.2⟩

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Regularity
