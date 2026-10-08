import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretation

/-!
# Soundness of all generated relative closed judgments

The complete right-oriented evaluation and annotated abstraction equations
follow from the actual target Cartesian projections and closed adjunction.
Products and internal homs use the same supplied Cartesian monoidal structure;
no identification with separately selected limit objects is needed.

The final simultaneous derivation induction earns interpretation of every
local formation, arrow and equation rule from independently supplied primitive
header/equation realization. Equalizer uniqueness uses the actual evaluated
equalizer and its monic inclusion; no semantic soundness field is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

universe u v a w z

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D]

@[reassoc (attr := simp)] theorem exchange_first (left right : D) :
    exchange left right ≫ CartesianMonoidalCategory.fst right left =
      CartesianMonoidalCategory.snd left right :=
  CartesianMonoidalCategory.lift_fst _ _

@[reassoc (attr := simp)] theorem exchange_second (left right : D) :
    exchange left right ≫ CartesianMonoidalCategory.snd right left =
      CartesianMonoidalCategory.fst left right :=
  CartesianMonoidalCategory.lift_snd _ _

@[simp] theorem exchange_exchange (left right : D) :
    exchange left right ≫ exchange right left = 𝟙 (left ⊗ right) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, exchange_first, exchange_second, Category.id_comp]
  · simp only [Category.assoc, exchange_second, exchange_first, Category.id_comp]

theorem lift_exchange {context left right : D} (before : context ⟶ left)
    (after : context ⟶ right) :
    CartesianMonoidalCategory.lift before after ≫ exchange left right =
      CartesianMonoidalCategory.lift after before := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, exchange_first, CartesianMonoidalCategory.lift_snd,
      CartesianMonoidalCategory.lift_fst]
  · simp only [Category.assoc, exchange_second, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd]

variable [MonoidalClosed D]

theorem application_eq {context argument result : D}
    (function : context ⟶ (argument ⟶[D] result)) :
    CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst context argument ≫ function)
        (CartesianMonoidalCategory.snd context argument) ≫ evaluation argument result =
      exchange context argument ≫ MonoidalClosed.uncurry function := by
  have square :
      CartesianMonoidalCategory.lift (CartesianMonoidalCategory.snd context argument)
          (CartesianMonoidalCategory.fst context argument ≫ function) =
        exchange context argument ≫ (argument ◁ function) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst,
        exchange_first, CartesianMonoidalCategory.lift_fst]
    · simp only [Category.assoc, CartesianMonoidalCategory.whiskerLeft_snd,
        exchange_second_assoc, CartesianMonoidalCategory.lift_snd]
  rw [evaluation, ← Category.assoc, lift_exchange, square,
    Category.assoc, MonoidalClosed.uncurry_eq]

theorem abstraction_beta {context argument result : D} (body : context ⊗ argument ⟶ result) :
    CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst context argument ≫ abstraction body)
        (CartesianMonoidalCategory.snd context argument) ≫ evaluation argument result = body := by
  rw [application_eq, abstraction, MonoidalClosed.uncurry_curry,
    ← Category.assoc, exchange_exchange, Category.id_comp]

theorem abstraction_eta {context argument result : D}
    (function : context ⟶ (argument ⟶[D] result)) :
    abstraction (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst context argument ≫ function)
        (CartesianMonoidalCategory.snd context argument) ≫ evaluation argument result) = function := by
  rw [application_eq, abstraction, ← Category.assoc,
    exchange_exchange, Category.id_comp, MonoidalClosed.curry_uncurry]

variable [HasFiniteLimits D]

private theorem arrow_of_reads {assignment : Assignment C symbols D}
    {source target : ObjectCode C symbols} {code : ArrowCode C symbols}
    {first second : D} {arrow : first ⟶ second}
    (sourceRead : assignment.evaluateObject source = some first)
    (targetRead : assignment.evaluateObject target = some second)
    (read : assignment.evaluateArrow code = some ⟨first, second, arrow⟩) :
    Interprets assignment (.arrow source target code) :=
  ⟨⟨first, second, arrow⟩, sourceRead, targetRead, read⟩

private theorem equation_of_reads {assignment : Assignment C symbols D}
    {source target : ObjectCode C symbols} {before after : ArrowCode C symbols}
    {first second : D} {f g : first ⟶ second}
    (sourceRead : assignment.evaluateObject source = some first)
    (targetRead : assignment.evaluateObject target = some second)
    (beforeRead : assignment.evaluateArrow before = some ⟨first, second, f⟩)
    (afterRead : assignment.evaluateArrow after = some ⟨first, second, g⟩)
    (same : f = g) : Interprets assignment (.equation source target before after) := by
  subst g
  exact ⟨⟨first, second, f⟩, sourceRead, targetRead, beforeRead, afterRead⟩

variable {signature : Signature (C := C) (symbols := symbols)}

theorem sound (assignment : Assignment C symbols D) (realization : Realization signature assignment)
    {judgment : Judgment C symbols} (tree : Derivation signature judgment) :
    Interprets assignment judgment := by
  induction tree with
  | baseObject object => exact ⟨_, assignment.evaluate_base_object object⟩
  | objectName origin => exact ⟨_, assignment.evaluate_object_name origin⟩
  | terminalObject => exact ⟨_, assignment.evaluate_terminal_object⟩
  | productObject _left _right leftIH rightIH =>
    obtain ⟨left, leftRead⟩ := leftIH
    obtain ⟨right, rightRead⟩ := rightIH
    exact ⟨left ⊗ right, assignment.evaluate_product leftRead rightRead⟩
  | exponentialObject _argument _result argumentIH resultIH =>
    obtain ⟨argument, argumentRead⟩ := argumentIH
    obtain ⟨result, resultRead⟩ := resultIH
    exact ⟨argument ⟶[D] result, assignment.evaluate_exponential argumentRead resultRead⟩
  | equalizerObject _source _target _before _after sourceIH targetIH beforeIH afterIH =>
    obtain ⟨source, sourceRead⟩ := sourceIH
    obtain ⟨target, targetRead⟩ := targetIH
    obtain ⟨before, beforeRead⟩ := Interprets.arrowAt beforeIH sourceRead targetRead
    obtain ⟨after, afterRead⟩ := Interprets.arrowAt afterIH sourceRead targetRead
    exact ⟨equalizer before after,
      assignment.evaluate_equalizer before after sourceRead targetRead beforeRead afterRead⟩
  | baseArrow arrow =>
    exact arrow_of_reads (assignment.evaluate_base_object _) (assignment.evaluate_base_object _)
      (assignment.evaluate_base_arrow arrow)
  | arrowName origin _source _target _ _ =>
    exact ⟨assignment.arrow origin, realization.source origin, realization.target origin,
      assignment.evaluate_arrow_name origin⟩
  | identity _formed formedIH =>
    obtain ⟨object, objectRead⟩ := formedIH
    exact arrow_of_reads objectRead objectRead (assignment.evaluate_identity objectRead)
  | compose _before _after beforeIH afterIH =>
    obtain ⟨before, sourceRead, middleRead, beforeRead⟩ := beforeIH
    obtain ⟨after, afterSource, targetRead, afterRead⟩ := afterIH
    obtain ⟨actual, actualRead⟩ := Interprets.arrowAt
      ⟨after, afterSource, targetRead, afterRead⟩ middleRead targetRead
    exact arrow_of_reads sourceRead targetRead
      (assignment.evaluate_compose before.arrow actual beforeRead actualRead)
  | terminalArrow _source sourceIH =>
    obtain ⟨source, sourceRead⟩ := sourceIH
    exact arrow_of_reads sourceRead assignment.evaluate_terminal_object
      (assignment.evaluate_terminal_arrow sourceRead)
  | first _left _right leftIH rightIH =>
    obtain ⟨left, leftRead⟩ := leftIH
    obtain ⟨right, rightRead⟩ := rightIH
    exact arrow_of_reads (assignment.evaluate_product leftRead rightRead) leftRead
      (assignment.evaluate_first leftRead rightRead)
  | second _left _right leftIH rightIH =>
    obtain ⟨left, leftRead⟩ := leftIH
    obtain ⟨right, rightRead⟩ := rightIH
    exact arrow_of_reads (assignment.evaluate_product leftRead rightRead) rightRead
      (assignment.evaluate_second leftRead rightRead)
  | pair _before _after beforeIH afterIH =>
    obtain ⟨before, sourceRead, leftRead, beforeRead⟩ := beforeIH
    obtain ⟨after, afterSource, rightRead, afterRead⟩ := afterIH
    obtain ⟨actual, actualRead⟩ := Interprets.arrowAt
      ⟨after, afterSource, rightRead, afterRead⟩ sourceRead rightRead
    exact arrow_of_reads sourceRead (assignment.evaluate_product leftRead rightRead)
      (assignment.evaluate_pair before.arrow actual beforeRead actualRead)
  | evaluation _argument _result argumentIH resultIH =>
    obtain ⟨argument, argumentRead⟩ := argumentIH
    obtain ⟨result, resultRead⟩ := resultIH
    exact arrow_of_reads
      (assignment.evaluate_product (assignment.evaluate_exponential argumentRead resultRead)
        argumentRead) resultRead (assignment.evaluate_evaluation argumentRead resultRead)
  | curry _context _argument _result _body contextIH argumentIH resultIH bodyIH =>
    obtain ⟨context, contextRead⟩ := contextIH
    obtain ⟨argument, argumentRead⟩ := argumentIH
    obtain ⟨result, resultRead⟩ := resultIH
    obtain ⟨body, bodyRead⟩ := Interprets.arrowAt bodyIH
      (assignment.evaluate_product contextRead argumentRead) resultRead
    exact arrow_of_reads contextRead (assignment.evaluate_exponential argumentRead resultRead)
      (assignment.evaluate_abstraction body contextRead argumentRead resultRead bodyRead)
  | equalizerArrow _source _target _before _after sourceIH targetIH beforeIH afterIH =>
    obtain ⟨source, sourceRead⟩ := sourceIH
    obtain ⟨target, targetRead⟩ := targetIH
    obtain ⟨before, beforeRead⟩ := Interprets.arrowAt beforeIH sourceRead targetRead
    obtain ⟨after, afterRead⟩ := Interprets.arrowAt afterIH sourceRead targetRead
    exact arrow_of_reads
      (assignment.evaluate_equalizer before after sourceRead targetRead beforeRead afterRead)
      sourceRead
      (assignment.evaluate_equalizer_arrow before after sourceRead targetRead beforeRead afterRead)
  | equalizerLift _source _target _context _before _after _candidate _commutes
      sourceIH targetIH contextIH beforeIH afterIH candidateIH commutesIH =>
    obtain ⟨source, sourceRead⟩ := sourceIH
    obtain ⟨target, targetRead⟩ := targetIH
    obtain ⟨context, contextRead⟩ := contextIH
    obtain ⟨before, beforeRead⟩ := Interprets.arrowAt beforeIH sourceRead targetRead
    obtain ⟨after, afterRead⟩ := Interprets.arrowAt afterIH sourceRead targetRead
    obtain ⟨candidate, candidateRead⟩ := Interprets.arrowAt candidateIH contextRead sourceRead
    have commutes := Interprets.equal_arrows (candidate ≫ before) (candidate ≫ after) commutesIH
      (assignment.evaluate_compose candidate before candidateRead beforeRead)
      (assignment.evaluate_compose candidate after candidateRead afterRead)
    exact arrow_of_reads contextRead
      (assignment.evaluate_equalizer before after sourceRead targetRead beforeRead afterRead)
      (assignment.evaluate_equalizer_lift before after candidate commutes
        sourceRead targetRead contextRead beforeRead afterRead candidateRead)
  | reflexivity _typed typedIH =>
    obtain ⟨value, sourceRead, targetRead, read⟩ := typedIH
    exact ⟨value, sourceRead, targetRead, read, read⟩
  | symmetry _same sameIH =>
    obtain ⟨value, sourceRead, targetRead, beforeRead, afterRead⟩ := sameIH
    exact ⟨value, sourceRead, targetRead, afterRead, beforeRead⟩
  | transitivity _before _after beforeIH afterIH =>
    obtain ⟨before, sourceRead, targetRead, firstRead, middleRead⟩ := beforeIH
    obtain ⟨after, _sourceAfter, _targetAfter, middleAfter, lastRead⟩ := afterIH
    have same : after = before := Option.some.inj (middleAfter.symm.trans middleRead)
    subst after
    exact ⟨before, sourceRead, targetRead, firstRead, lastRead⟩
  | compositionCongruence _beforeSame _afterSame beforeIH afterIH =>
    obtain ⟨before, sourceRead, middleRead, leftRead, leftRead'⟩ := beforeIH
    obtain ⟨after, afterSource, targetRead, rightRead, rightRead'⟩ := afterIH
    obtain ⟨actual, actualRead, actualRead'⟩ := Interprets.equationAt
      ⟨after, afterSource, targetRead, rightRead, rightRead'⟩ middleRead targetRead
    exact equation_of_reads sourceRead targetRead
      (assignment.evaluate_compose before.arrow actual leftRead actualRead)
      (assignment.evaluate_compose before.arrow actual leftRead' actualRead') rfl
  | pairCongruence _beforeSame _afterSame beforeIH afterIH =>
    obtain ⟨before, sourceRead, leftRead, firstRead, firstRead'⟩ := beforeIH
    obtain ⟨after, afterSource, rightRead, secondRead, secondRead'⟩ := afterIH
    obtain ⟨actual, actualRead, actualRead'⟩ := Interprets.equationAt
      ⟨after, afterSource, rightRead, secondRead, secondRead'⟩ sourceRead rightRead
    exact equation_of_reads sourceRead (assignment.evaluate_product leftRead rightRead)
      (assignment.evaluate_pair before.arrow actual firstRead actualRead)
      (assignment.evaluate_pair before.arrow actual firstRead' actualRead') rfl
  | curryCongruence _context _argument _result _same contextIH argumentIH resultIH sameIH =>
    obtain ⟨context, contextRead⟩ := contextIH
    obtain ⟨argument, argumentRead⟩ := argumentIH
    obtain ⟨result, resultRead⟩ := resultIH
    obtain ⟨body, firstRead, secondRead⟩ := Interprets.equationAt sameIH
      (assignment.evaluate_product contextRead argumentRead) resultRead
    exact equation_of_reads contextRead (assignment.evaluate_exponential argumentRead resultRead)
      (assignment.evaluate_abstraction body contextRead argumentRead resultRead firstRead)
      (assignment.evaluate_abstraction body contextRead argumentRead resultRead secondRead) rfl
  | leftIdentity _source _typed sourceIH typedIH =>
    obtain ⟨source, sourceRead⟩ := sourceIH
    obtain ⟨value, _sourceValue, targetRead, valueRead⟩ := typedIH
    obtain ⟨arrow, arrowRead⟩ := Interprets.arrowAt
      ⟨value, _sourceValue, targetRead, valueRead⟩ sourceRead targetRead
    exact equation_of_reads sourceRead targetRead
      (assignment.evaluate_compose (𝟙 source) arrow (assignment.evaluate_identity sourceRead) arrowRead)
      arrowRead (Category.id_comp arrow)
  | rightIdentity _target _typed targetIH typedIH =>
    obtain ⟨target, targetRead⟩ := targetIH
    obtain ⟨value, sourceRead, _targetValue, valueRead⟩ := typedIH
    obtain ⟨arrow, arrowRead⟩ := Interprets.arrowAt
      ⟨value, sourceRead, _targetValue, valueRead⟩ sourceRead targetRead
    exact equation_of_reads sourceRead targetRead
      (assignment.evaluate_compose arrow (𝟙 target) arrowRead (assignment.evaluate_identity targetRead))
      arrowRead (Category.comp_id arrow)
  | associativity _before _middle _after beforeIH middleIH afterIH =>
    obtain ⟨before, sourceRead, firstMiddle, beforeRead⟩ := beforeIH
    obtain ⟨middle, middleSource, secondMiddle, middleRead⟩ := middleIH
    obtain ⟨after, afterSource, targetRead, afterRead⟩ := afterIH
    obtain ⟨f, fRead⟩ := Interprets.arrowAt
      ⟨middle, middleSource, secondMiddle, middleRead⟩ firstMiddle secondMiddle
    obtain ⟨g, gRead⟩ := Interprets.arrowAt
      ⟨after, afterSource, targetRead, afterRead⟩ secondMiddle targetRead
    exact equation_of_reads sourceRead targetRead
      (assignment.evaluate_compose (before.arrow ≫ f) g
        (assignment.evaluate_compose before.arrow f beforeRead fRead) gRead)
      (assignment.evaluate_compose before.arrow (f ≫ g) beforeRead
        (assignment.evaluate_compose f g fRead gRead)) (Category.assoc _ _ _)
  | terminalUniqueness _before _after beforeIH afterIH =>
    obtain ⟨before, sourceRead, beforeTarget, beforeRead⟩ := beforeIH
    obtain ⟨f, fRead⟩ := Interprets.arrowAt
      ⟨before, sourceRead, beforeTarget, beforeRead⟩ sourceRead assignment.evaluate_terminal_object
    obtain ⟨g, gRead⟩ := Interprets.arrowAt afterIH sourceRead assignment.evaluate_terminal_object
    exact equation_of_reads sourceRead assignment.evaluate_terminal_object fRead gRead
      (CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext f g)
  | firstBeta _left _right _before _after leftIH rightIH beforeIH afterIH =>
    obtain ⟨left, leftRead⟩ := leftIH
    obtain ⟨right, rightRead⟩ := rightIH
    obtain ⟨before, sourceRead, beforeTarget, beforeRead⟩ := beforeIH
    obtain ⟨f, fRead⟩ := Interprets.arrowAt
      ⟨before, sourceRead, beforeTarget, beforeRead⟩ sourceRead leftRead
    obtain ⟨g, gRead⟩ := Interprets.arrowAt afterIH sourceRead rightRead
    exact equation_of_reads sourceRead leftRead
      (assignment.evaluate_compose (CartesianMonoidalCategory.lift f g)
        (CartesianMonoidalCategory.fst left right) (assignment.evaluate_pair f g fRead gRead)
        (assignment.evaluate_first leftRead rightRead)) fRead
      (CartesianMonoidalCategory.lift_fst f g)
  | secondBeta _left _right _before _after leftIH rightIH beforeIH afterIH =>
    obtain ⟨left, leftRead⟩ := leftIH
    obtain ⟨right, rightRead⟩ := rightIH
    obtain ⟨before, sourceRead, beforeTarget, beforeRead⟩ := beforeIH
    obtain ⟨f, fRead⟩ := Interprets.arrowAt
      ⟨before, sourceRead, beforeTarget, beforeRead⟩ sourceRead leftRead
    obtain ⟨g, gRead⟩ := Interprets.arrowAt afterIH sourceRead rightRead
    exact equation_of_reads sourceRead rightRead
      (assignment.evaluate_compose (CartesianMonoidalCategory.lift f g)
        (CartesianMonoidalCategory.snd left right) (assignment.evaluate_pair f g fRead gRead)
        (assignment.evaluate_second leftRead rightRead)) gRead
      (CartesianMonoidalCategory.lift_snd f g)
  | productEta _left _right _typed leftIH rightIH typedIH =>
    obtain ⟨left, leftRead⟩ := leftIH
    obtain ⟨right, rightRead⟩ := rightIH
    obtain ⟨value, sourceRead, targetRead, valueRead⟩ := typedIH
    have productRead := assignment.evaluate_product leftRead rightRead
    obtain ⟨f, fRead⟩ := Interprets.arrowAt
      ⟨value, sourceRead, targetRead, valueRead⟩ sourceRead productRead
    exact equation_of_reads sourceRead productRead
      (assignment.evaluate_pair (f ≫ CartesianMonoidalCategory.fst left right)
        (f ≫ CartesianMonoidalCategory.snd left right)
        (assignment.evaluate_compose f _ fRead (assignment.evaluate_first leftRead rightRead))
        (assignment.evaluate_compose f _ fRead (assignment.evaluate_second leftRead rightRead))) fRead
      (CartesianMonoidalCategory.lift_comp_fst_snd f)
  | exponentialBeta _context _argument _result _body contextIH argumentIH resultIH bodyIH =>
    obtain ⟨context, contextRead⟩ := contextIH
    obtain ⟨argument, argumentRead⟩ := argumentIH
    obtain ⟨result, resultRead⟩ := resultIH
    have productRead := assignment.evaluate_product contextRead argumentRead
    obtain ⟨f, fRead⟩ := Interprets.arrowAt bodyIH productRead resultRead
    have curryRead := assignment.evaluate_abstraction f contextRead argumentRead resultRead fRead
    have firstRead := assignment.evaluate_compose (CartesianMonoidalCategory.fst context argument)
      (abstraction f) (assignment.evaluate_first contextRead argumentRead) curryRead
    have pairRead := assignment.evaluate_pair _ _ firstRead
      (assignment.evaluate_second contextRead argumentRead)
    exact equation_of_reads productRead resultRead
      (assignment.evaluate_compose _ _ pairRead (assignment.evaluate_evaluation argumentRead resultRead))
      fRead (abstraction_beta f)
  | exponentialEta _context _argument _result _typed contextIH argumentIH resultIH typedIH =>
    obtain ⟨context, contextRead⟩ := contextIH
    obtain ⟨argument, argumentRead⟩ := argumentIH
    obtain ⟨result, resultRead⟩ := resultIH
    have exponentialRead := assignment.evaluate_exponential argumentRead resultRead
    obtain ⟨f, fRead⟩ := Interprets.arrowAt typedIH contextRead exponentialRead
    have firstRead := assignment.evaluate_compose (CartesianMonoidalCategory.fst context argument)
      f (assignment.evaluate_first contextRead argumentRead) fRead
    have pairRead := assignment.evaluate_pair _ _ firstRead
      (assignment.evaluate_second contextRead argumentRead)
    have bodyRead := assignment.evaluate_compose _ _ pairRead
      (assignment.evaluate_evaluation argumentRead resultRead)
    exact equation_of_reads contextRead exponentialRead
      (assignment.evaluate_abstraction _ contextRead argumentRead resultRead bodyRead)
      fRead (abstraction_eta f)
  | equalizerCondition _source _target _before _after sourceIH targetIH beforeIH afterIH =>
    obtain ⟨source, sourceRead⟩ := sourceIH
    obtain ⟨target, targetRead⟩ := targetIH
    obtain ⟨before, beforeRead⟩ := Interprets.arrowAt beforeIH sourceRead targetRead
    obtain ⟨after, afterRead⟩ := Interprets.arrowAt afterIH sourceRead targetRead
    have iotaRead := assignment.evaluate_equalizer_arrow before after
      sourceRead targetRead beforeRead afterRead
    exact equation_of_reads
      (assignment.evaluate_equalizer before after sourceRead targetRead beforeRead afterRead)
      targetRead (assignment.evaluate_compose _ before iotaRead beforeRead)
      (assignment.evaluate_compose _ after iotaRead afterRead) (equalizer.condition before after)
  | equalizerBeta _source _target _context _before _after _candidate _commutes
      sourceIH targetIH contextIH beforeIH afterIH candidateIH commutesIH =>
    obtain ⟨source, sourceRead⟩ := sourceIH
    obtain ⟨target, targetRead⟩ := targetIH
    obtain ⟨context, contextRead⟩ := contextIH
    obtain ⟨before, beforeRead⟩ := Interprets.arrowAt beforeIH sourceRead targetRead
    obtain ⟨after, afterRead⟩ := Interprets.arrowAt afterIH sourceRead targetRead
    obtain ⟨candidate, candidateRead⟩ := Interprets.arrowAt candidateIH contextRead sourceRead
    have commutes := Interprets.equal_arrows (candidate ≫ before) (candidate ≫ after) commutesIH
      (assignment.evaluate_compose candidate before candidateRead beforeRead)
      (assignment.evaluate_compose candidate after candidateRead afterRead)
    have liftRead := assignment.evaluate_equalizer_lift before after candidate commutes
      sourceRead targetRead contextRead beforeRead afterRead candidateRead
    have iotaRead := assignment.evaluate_equalizer_arrow before after
      sourceRead targetRead beforeRead afterRead
    exact equation_of_reads contextRead sourceRead
      (assignment.evaluate_compose _ _ liftRead iotaRead) candidateRead (equalizer.lift_ι _ _)
  | equalizerUniqueness _before _after _same beforeIH afterIH sameIH =>
    obtain ⟨value, contextRead, targetRead, valueRead⟩ := beforeIH
    obtain ⟨source, target, f, g, targetSame, iotaRead⟩ :=
      assignment.evaluate_equalizer_shape targetRead
    rw [targetSame] at targetRead
    obtain ⟨before, beforeRead⟩ := Interprets.arrowAt
      ⟨value, contextRead, by simpa only [← targetSame] using targetRead, valueRead⟩
      contextRead targetRead
    obtain ⟨after, afterRead⟩ := Interprets.arrowAt afterIH contextRead targetRead
    have same := Interprets.equal_arrows (before ≫ equalizer.ι f g) (after ≫ equalizer.ι f g) sameIH
      (assignment.evaluate_compose before _ beforeRead iotaRead)
      (assignment.evaluate_compose after _ afterRead iotaRead)
    exact equation_of_reads contextRead targetRead beforeRead afterRead
      ((cancel_mono (equalizer.ι f g)).mp same)
  | baseIdentity object =>
    exact equation_of_reads (assignment.evaluate_base_object object)
      (assignment.evaluate_base_object object) (assignment.evaluate_base_arrow (𝟙 object))
      (assignment.evaluate_identity (assignment.evaluate_base_object object))
      (assignment.base.map_id object)
  | baseComposition before after =>
    exact equation_of_reads (assignment.evaluate_base_object _) (assignment.evaluate_base_object _)
      (assignment.evaluate_base_arrow (before ≫ after))
      (assignment.evaluate_compose _ _ (assignment.evaluate_base_arrow before)
        (assignment.evaluate_base_arrow after)) (assignment.base.map_comp before after)
  | baseEquality same =>
    cases same
    exact equation_of_reads (assignment.evaluate_base_object _) (assignment.evaluate_base_object _)
      (assignment.evaluate_base_arrow _) (assignment.evaluate_base_arrow _) rfl
  | declaredEquation origin _before _after _ _ => exact realization.equation origin

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
