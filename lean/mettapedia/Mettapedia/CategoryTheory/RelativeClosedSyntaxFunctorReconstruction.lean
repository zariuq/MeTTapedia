import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorReconstructionConstructors

/-!
# Reconstruction of every generated relative closed expression

The simultaneous induction covers all forty local rules. Each formed object
and admitted arrow is read by the independent target evaluator as the exact
normalized functor image. Equation cases use their genuine typed source
quotient classes, so equalizer guards are reconstructed from the retained
commutativity trees. Declaration realization is a later consequence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping] (headers : HeaderFormation signature)

def ReconstructionResult : Judgment C symbols → Prop
  | .object code => ∀ formed : Nonempty (Derivation signature (.object code)),
      ObjectRead mapping headers ⟨code, formed⟩
  | .arrow source target code =>
      ∀ sourceFormed : Nonempty (Derivation signature (.object source)),
      ∀ targetFormed : Nonempty (Derivation signature (.object target)),
      ∀ typed : Nonempty (Derivation signature (.arrow source target code)),
        ArrowRead mapping headers
          (⟨code, typed⟩ : RawHom ⟨source, sourceFormed⟩ ⟨target, targetFormed⟩)
  | .equation source target first second =>
      ∀ sourceFormed : Nonempty (Derivation signature (.object source)),
      ∀ targetFormed : Nonempty (Derivation signature (.object target)),
      ∀ firstTyped : Nonempty (Derivation signature (.arrow source target first)),
      ∀ secondTyped : Nonempty (Derivation signature (.arrow source target second)),
        (normalizedFunctor mapping).map (classOf
          (⟨first, firstTyped⟩ : RawHom ⟨source, sourceFormed⟩ ⟨target, targetFormed⟩)) =
        (normalizedFunctor mapping).map (classOf
          (⟨second, secondTyped⟩ : RawHom ⟨source, sourceFormed⟩ ⟨target, targetFormed⟩))

theorem equation_reconstruction {source target : ObjectCode C symbols}
    {first second : ArrowCode C symbols}
    (same : Derivation signature (.equation source target first second)) :
    ReconstructionResult mapping headers (.equation source target first second) := by
  intro sourceFormed targetFormed firstTyped secondTyped
  exact congrArg (normalizedFunctor mapping).map
    (classOf_equation (first := (⟨first, firstTyped⟩ : RawHom ⟨source, sourceFormed⟩ ⟨target, targetFormed⟩))
      (second := ⟨second, secondTyped⟩) ⟨same⟩)

theorem reconstruction {judgment : Judgment C symbols} (tree : Derivation signature judgment) :
    ReconstructionResult mapping headers judgment := by
  induction tree with
  | baseObject object => exact fun _ => object_read_base mapping headers object
  | objectName origin => exact fun _ => object_read_name mapping headers origin
  | terminalObject => exact fun _ => object_read_terminal mapping headers
  | productObject first second firstIH secondIH =>
      intro formed
      exact object_read_product mapping headers ⟨_, ⟨first⟩⟩ ⟨_, ⟨second⟩⟩
        (firstIH ⟨first⟩) (secondIH ⟨second⟩)
  | exponentialObject argument result argumentIH resultIH =>
      intro formed
      exact object_read_exponential mapping headers ⟨_, ⟨argument⟩⟩ ⟨_, ⟨result⟩⟩
        (argumentIH ⟨argument⟩) (resultIH ⟨result⟩)
  | equalizerObject source target first second sourceIH targetIH firstIH secondIH =>
      intro formed
      exact object_read_equalizer mapping headers
        (⟨_, ⟨first⟩⟩ : RawHom ⟨_, ⟨source⟩⟩ ⟨_, ⟨target⟩⟩) ⟨_, ⟨second⟩⟩
        (sourceIH ⟨source⟩) (targetIH ⟨target⟩)
        (firstIH ⟨source⟩ ⟨target⟩ ⟨first⟩) (secondIH ⟨source⟩ ⟨target⟩ ⟨second⟩)
  | baseArrow arrow => exact fun _ _ _ => arrow_read_base mapping headers arrow
  | arrowName origin _source _target _ _ =>
      exact fun _ _ _ => arrow_read_name mapping headers origin
  | identity formed formedIH =>
      intro sourceFormed targetFormed typed
      exact arrow_read_identity mapping headers ⟨_, sourceFormed⟩ (formedIH sourceFormed)
  | compose before after beforeIH afterIH =>
      intro sourceFormed targetFormed typed
      have middleFormed := (Regularity.arrow_endpoints ⟨before⟩).2
      exact arrow_read_compose mapping headers
        (⟨_, ⟨before⟩⟩ : RawHom ⟨_, sourceFormed⟩ ⟨_, middleFormed⟩)
        (⟨_, ⟨after⟩⟩ : RawHom ⟨_, middleFormed⟩ ⟨_, targetFormed⟩)
        (beforeIH sourceFormed middleFormed ⟨before⟩) (afterIH middleFormed targetFormed ⟨after⟩)
  | terminalArrow formed formedIH =>
      exact fun sourceFormed _ _ => arrow_read_terminal mapping headers ⟨_, sourceFormed⟩
        (formedIH sourceFormed)
  | first left right leftIH rightIH =>
      exact fun _ _ _ => arrow_read_first mapping headers ⟨_, ⟨left⟩⟩ ⟨_, ⟨right⟩⟩
        (leftIH ⟨left⟩) (rightIH ⟨right⟩)
  | second left right leftIH rightIH =>
      exact fun _ _ _ => arrow_read_second mapping headers ⟨_, ⟨left⟩⟩ ⟨_, ⟨right⟩⟩
        (leftIH ⟨left⟩) (rightIH ⟨right⟩)
  | pair first second firstIH secondIH =>
      intro sourceFormed targetFormed typed
      have leftFormed := (Regularity.arrow_endpoints ⟨first⟩).2
      have rightFormed := (Regularity.arrow_endpoints ⟨second⟩).2
      exact arrow_read_pair mapping headers
        (⟨_, ⟨first⟩⟩ : RawHom ⟨_, sourceFormed⟩ ⟨_, leftFormed⟩)
        (⟨_, ⟨second⟩⟩ : RawHom ⟨_, sourceFormed⟩ ⟨_, rightFormed⟩)
        (firstIH sourceFormed leftFormed ⟨first⟩) (secondIH sourceFormed rightFormed ⟨second⟩)
  | evaluation argument result argumentIH resultIH =>
      exact fun _ _ _ => arrow_read_evaluation mapping headers ⟨_, ⟨argument⟩⟩ ⟨_, ⟨result⟩⟩
        (argumentIH ⟨argument⟩) (resultIH ⟨result⟩)
  | curry context argument result body contextIH argumentIH resultIH bodyIH =>
      intro sourceFormed targetFormed typed
      exact arrow_read_abstraction mapping headers ⟨_, sourceFormed⟩ ⟨_, ⟨argument⟩⟩ ⟨_, ⟨result⟩⟩
        ⟨_, ⟨body⟩⟩ (contextIH sourceFormed) (argumentIH ⟨argument⟩) (resultIH ⟨result⟩)
        (bodyIH ⟨.productObject sourceFormed.some argument⟩ ⟨result⟩ ⟨body⟩)
  | equalizerArrow source target first second sourceIH targetIH firstIH secondIH =>
      exact fun _ _ _ => arrow_read_equalizer_inclusion mapping headers
        (⟨_, ⟨first⟩⟩ : RawHom ⟨_, ⟨source⟩⟩ ⟨_, ⟨target⟩⟩) ⟨_, ⟨second⟩⟩
        (sourceIH ⟨source⟩) (targetIH ⟨target⟩)
        (firstIH ⟨source⟩ ⟨target⟩ ⟨first⟩) (secondIH ⟨source⟩ ⟨target⟩ ⟨second⟩)
  | equalizerLift source target context first second candidate commutes
      sourceIH targetIH contextIH firstIH secondIH candidateIH _ =>
      intro sourceFormed targetFormed typed
      exact arrow_read_authoredLift mapping headers
        (⟨_, ⟨first⟩⟩ : RawHom ⟨_, ⟨source⟩⟩ ⟨_, ⟨target⟩⟩) ⟨_, ⟨second⟩⟩
        (⟨_, ⟨candidate⟩⟩ : RawHom ⟨_, sourceFormed⟩ ⟨_, ⟨source⟩⟩) commutes
        (sourceIH ⟨source⟩) (targetIH ⟨target⟩) (contextIH sourceFormed)
        (firstIH ⟨source⟩ ⟨target⟩ ⟨first⟩) (secondIH ⟨source⟩ ⟨target⟩ ⟨second⟩)
        (candidateIH sourceFormed ⟨source⟩ ⟨candidate⟩)
  | reflexivity typed _ => exact equation_reconstruction mapping headers (.reflexivity typed)
  | symmetry same _ => exact equation_reconstruction mapping headers (.symmetry same)
  | transitivity before after _ _ => exact equation_reconstruction mapping headers (.transitivity before after)
  | compositionCongruence before after _ _ =>
      exact equation_reconstruction mapping headers (.compositionCongruence before after)
  | pairCongruence before after _ _ => exact equation_reconstruction mapping headers (.pairCongruence before after)
  | curryCongruence context argument result same _ _ _ _ =>
      exact equation_reconstruction mapping headers (.curryCongruence context argument result same)
  | leftIdentity source typed _ _ => exact equation_reconstruction mapping headers (.leftIdentity source typed)
  | rightIdentity target typed _ _ => exact equation_reconstruction mapping headers (.rightIdentity target typed)
  | associativity before middle after _ _ _ =>
      exact equation_reconstruction mapping headers (.associativity before middle after)
  | terminalUniqueness before after _ _ =>
      exact equation_reconstruction mapping headers (.terminalUniqueness before after)
  | firstBeta left right before after _ _ _ _ =>
      exact equation_reconstruction mapping headers (.firstBeta left right before after)
  | secondBeta left right before after _ _ _ _ =>
      exact equation_reconstruction mapping headers (.secondBeta left right before after)
  | productEta left right typed _ _ _ =>
      exact equation_reconstruction mapping headers (.productEta left right typed)
  | exponentialBeta context argument result body _ _ _ _ =>
      exact equation_reconstruction mapping headers (.exponentialBeta context argument result body)
  | exponentialEta context argument result typed _ _ _ _ =>
      exact equation_reconstruction mapping headers (.exponentialEta context argument result typed)
  | equalizerCondition source target first second _ _ _ _ =>
      exact equation_reconstruction mapping headers (.equalizerCondition source target first second)
  | equalizerBeta source target context first second candidate commutes _ _ _ _ _ _ _ =>
      exact equation_reconstruction mapping headers (.equalizerBeta source target context first second candidate commutes)
  | equalizerUniqueness before after same _ _ _ =>
      exact equation_reconstruction mapping headers (.equalizerUniqueness before after same)
  | baseIdentity object => exact equation_reconstruction mapping headers (.baseIdentity object)
  | baseComposition before after => exact equation_reconstruction mapping headers (.baseComposition before after)
  | baseEquality same => exact equation_reconstruction mapping headers (.baseEquality same)
  | declaredEquation origin first second _ _ =>
      exact equation_reconstruction mapping headers (.declaredEquation origin first second)

theorem object_reconstruction (object : Object signature) : ObjectRead mapping headers object :=
  reconstruction mapping headers object.formed.some object.formed

theorem raw_arrow_reconstruction {source target : Object signature} (raw : RawHom source target) :
    ArrowRead mapping headers raw :=
  reconstruction mapping headers raw.admitted.some source.formed target.formed raw.admitted

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
