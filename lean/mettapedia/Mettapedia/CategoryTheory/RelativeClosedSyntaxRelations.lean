import Mettapedia.CategoryTheory.RelativeClosedSyntax

/-!
# Generated local judgments for relative closed syntax

Object formation, arrow admission and equality are generated independently
of any target category. Equalizer formation requires genuinely parallel
admitted arrows; a lift requires its actual commutativity derivation. Curry
and evaluation have explicit context and argument annotations, with complete
beta and eta laws. Base identities and composition preserve the supplied
category diagram.

Primitive equation declarations require admission of both sides. Ordered
headers retain their actual formation trees; rank closure alone is not used
as a typing theorem. No interpretation or classifying law is a field.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax

open _root_.CategoryTheory

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}

inductive Judgment (C : Type u) [Category.{v} C] (symbols : Symbols.{a}) :
    Type (max u v a) where
  | object (code : ObjectCode C symbols)
  | arrow (source target : ObjectCode C symbols) (code : ArrowCode C symbols)
  | equation (source target : ObjectCode C symbols) (first second : ArrowCode C symbols)

inductive Derivation (signature : Signature (C := C) (symbols := symbols)) :
    Judgment C symbols → Type (max u v a) where
  | baseObject (object : C) : Derivation signature (.object (.base object))
  | objectName (origin : symbols.ObjectName) : Derivation signature (.object (.name origin))
  | terminalObject : Derivation signature (.object .terminal)
  | productObject {first second}
      (firstFormed : Derivation signature (.object first))
      (secondFormed : Derivation signature (.object second)) :
      Derivation signature (.object (.product first second))
  | exponentialObject {argument result}
      (argumentFormed : Derivation signature (.object argument))
      (resultFormed : Derivation signature (.object result)) :
      Derivation signature (.object (.exponential argument result))
  | equalizerObject {source target first second}
      (sourceFormed : Derivation signature (.object source))
      (targetFormed : Derivation signature (.object target))
      (firstTyped : Derivation signature (.arrow source target first))
      (secondTyped : Derivation signature (.arrow source target second)) :
      Derivation signature (.object (.equalizer source target first second))
  | baseArrow {source target : C} (arrow : source ⟶ target) :
      Derivation signature (.arrow (.base source) (.base target) (.base arrow))
  | arrowName (origin : symbols.ArrowName)
      (sourceFormed : Derivation signature (.object (signature.source origin)))
      (targetFormed : Derivation signature (.object (signature.target origin))) :
      Derivation signature (.arrow (signature.source origin) (signature.target origin) (.name origin))
  | identity {object} (formed : Derivation signature (.object object)) :
      Derivation signature (.arrow object object (.identity object))
  | compose {first middle last before after}
      (beforeTyped : Derivation signature (.arrow first middle before))
      (afterTyped : Derivation signature (.arrow middle last after)) :
      Derivation signature (.arrow first last (.compose before after))
  | terminalArrow {source} (formed : Derivation signature (.object source)) :
      Derivation signature (.arrow source .terminal (.terminal source))
  | first {left right}
      (leftFormed : Derivation signature (.object left))
      (rightFormed : Derivation signature (.object right)) :
      Derivation signature (.arrow (.product left right) left (.first left right))
  | second {left right}
      (leftFormed : Derivation signature (.object left))
      (rightFormed : Derivation signature (.object right)) :
      Derivation signature (.arrow (.product left right) right (.second left right))
  | pair {source left right first second}
      (firstTyped : Derivation signature (.arrow source left first))
      (secondTyped : Derivation signature (.arrow source right second)) :
      Derivation signature (.arrow source (.product left right) (.pair first second))
  | evaluation {argument result}
      (argumentFormed : Derivation signature (.object argument))
      (resultFormed : Derivation signature (.object result)) :
      Derivation signature (.arrow (.product (.exponential argument result) argument)
        result (.evaluation argument result))
  | curry {context argument result body}
      (contextFormed : Derivation signature (.object context))
      (argumentFormed : Derivation signature (.object argument))
      (resultFormed : Derivation signature (.object result))
      (bodyTyped : Derivation signature (.arrow (.product context argument) result body)) :
      Derivation signature (.arrow context (.exponential argument result)
        (.curry context argument result body))
  | equalizerArrow {source target first second}
      (sourceFormed : Derivation signature (.object source))
      (targetFormed : Derivation signature (.object target))
      (firstTyped : Derivation signature (.arrow source target first))
      (secondTyped : Derivation signature (.arrow source target second)) :
      Derivation signature (.arrow (.equalizer source target first second) source
        (.equalizerArrow source target first second))
  | equalizerLift {source target first second context candidate}
      (sourceFormed : Derivation signature (.object source))
      (targetFormed : Derivation signature (.object target))
      (contextFormed : Derivation signature (.object context))
      (firstTyped : Derivation signature (.arrow source target first))
      (secondTyped : Derivation signature (.arrow source target second))
      (candidateTyped : Derivation signature (.arrow context source candidate))
      (commutes : Derivation signature (.equation context target
        (.compose candidate first) (.compose candidate second))) :
      Derivation signature (.arrow context (.equalizer source target first second)
        (.equalizerLift source target first second context candidate))
  | reflexivity {source target arrow}
      (typed : Derivation signature (.arrow source target arrow)) :
      Derivation signature (.equation source target arrow arrow)
  | symmetry {source target first second}
      (same : Derivation signature (.equation source target first second)) :
      Derivation signature (.equation source target second first)
  | transitivity {source target first middle last}
      (before : Derivation signature (.equation source target first middle))
      (after : Derivation signature (.equation source target middle last)) :
      Derivation signature (.equation source target first last)
  | compositionCongruence {first middle last before before' after after'}
      (beforeSame : Derivation signature (.equation first middle before before'))
      (afterSame : Derivation signature (.equation middle last after after')) :
      Derivation signature (.equation first last
        (.compose before after) (.compose before' after'))
  | pairCongruence {source left right first first' second second'}
      (firstSame : Derivation signature (.equation source left first first'))
      (secondSame : Derivation signature (.equation source right second second')) :
      Derivation signature (.equation source (.product left right)
        (.pair first second) (.pair first' second'))
  | curryCongruence {context argument result first second}
      (contextFormed : Derivation signature (.object context))
      (argumentFormed : Derivation signature (.object argument))
      (resultFormed : Derivation signature (.object result))
      (same : Derivation signature (.equation (.product context argument) result first second)) :
      Derivation signature (.equation context (.exponential argument result)
        (.curry context argument result first) (.curry context argument result second))
  | leftIdentity {source target arrow}
      (sourceFormed : Derivation signature (.object source))
      (typed : Derivation signature (.arrow source target arrow)) :
      Derivation signature (.equation source target (.compose (.identity source) arrow) arrow)
  | rightIdentity {source target arrow}
      (targetFormed : Derivation signature (.object target))
      (typed : Derivation signature (.arrow source target arrow)) :
      Derivation signature (.equation source target (.compose arrow (.identity target)) arrow)
  | associativity {first second third fourth before middle after}
      (beforeTyped : Derivation signature (.arrow first second before))
      (middleTyped : Derivation signature (.arrow second third middle))
      (afterTyped : Derivation signature (.arrow third fourth after)) :
      Derivation signature (.equation first fourth
        (.compose (.compose before middle) after) (.compose before (.compose middle after)))
  | terminalUniqueness {source first second}
      (firstTyped : Derivation signature (.arrow source .terminal first))
      (secondTyped : Derivation signature (.arrow source .terminal second)) :
      Derivation signature (.equation source .terminal first second)
  | firstBeta {source left right first second}
      (leftFormed : Derivation signature (.object left))
      (rightFormed : Derivation signature (.object right))
      (firstTyped : Derivation signature (.arrow source left first))
      (secondTyped : Derivation signature (.arrow source right second)) :
      Derivation signature (.equation source left
        (.compose (.pair first second) (.first left right)) first)
  | secondBeta {source left right first second}
      (leftFormed : Derivation signature (.object left))
      (rightFormed : Derivation signature (.object right))
      (firstTyped : Derivation signature (.arrow source left first))
      (secondTyped : Derivation signature (.arrow source right second)) :
      Derivation signature (.equation source right
        (.compose (.pair first second) (.second left right)) second)
  | productEta {source left right arrow}
      (leftFormed : Derivation signature (.object left))
      (rightFormed : Derivation signature (.object right))
      (typed : Derivation signature (.arrow source (.product left right) arrow)) :
      Derivation signature (.equation source (.product left right)
        (.pair (.compose arrow (.first left right)) (.compose arrow (.second left right))) arrow)
  | exponentialBeta {context argument result body}
      (contextFormed : Derivation signature (.object context))
      (argumentFormed : Derivation signature (.object argument))
      (resultFormed : Derivation signature (.object result))
      (bodyTyped : Derivation signature (.arrow (.product context argument) result body)) :
      Derivation signature (.equation (.product context argument) result
        (.compose (.pair
          (.compose (.first context argument) (.curry context argument result body))
          (.second context argument)) (.evaluation argument result)) body)
  | exponentialEta {context argument result arrow}
      (contextFormed : Derivation signature (.object context))
      (argumentFormed : Derivation signature (.object argument))
      (resultFormed : Derivation signature (.object result))
      (typed : Derivation signature (.arrow context (.exponential argument result) arrow)) :
      Derivation signature (.equation context (.exponential argument result)
        (.curry context argument result
          (.compose (.pair (.compose (.first context argument) arrow) (.second context argument))
            (.evaluation argument result))) arrow)
  | equalizerCondition {source target first second}
      (sourceFormed : Derivation signature (.object source))
      (targetFormed : Derivation signature (.object target))
      (firstTyped : Derivation signature (.arrow source target first))
      (secondTyped : Derivation signature (.arrow source target second)) :
      Derivation signature (.equation (.equalizer source target first second) target
        (.compose (.equalizerArrow source target first second) first)
        (.compose (.equalizerArrow source target first second) second))
  | equalizerBeta {source target first second context candidate}
      (sourceFormed : Derivation signature (.object source))
      (targetFormed : Derivation signature (.object target))
      (contextFormed : Derivation signature (.object context))
      (firstTyped : Derivation signature (.arrow source target first))
      (secondTyped : Derivation signature (.arrow source target second))
      (candidateTyped : Derivation signature (.arrow context source candidate))
      (commutes : Derivation signature (.equation context target
        (.compose candidate first) (.compose candidate second))) :
      Derivation signature (.equation context source
        (.compose (.equalizerLift source target first second context candidate)
          (.equalizerArrow source target first second)) candidate)
  | equalizerUniqueness {source target first second context before after}
      (beforeTyped : Derivation signature (.arrow context (.equalizer source target first second) before))
      (afterTyped : Derivation signature (.arrow context (.equalizer source target first second) after))
      (same : Derivation signature (.equation context source
        (.compose before (.equalizerArrow source target first second))
        (.compose after (.equalizerArrow source target first second)))) :
      Derivation signature (.equation context (.equalizer source target first second) before after)
  | baseIdentity (object : C) : Derivation signature (.equation (.base object) (.base object)
      (.base (𝟙 object)) (.identity (.base object)))
  | baseComposition {first middle last : C} (before : first ⟶ middle) (after : middle ⟶ last) :
      Derivation signature (.equation (.base first) (.base last)
        (.base (before ≫ after)) (.compose (.base before) (.base after)))
  | baseEquality {source target : C} {first second : source ⟶ target} (same : first = second) :
      Derivation signature (.equation (.base source) (.base target) (.base first) (.base second))
  | declaredEquation (origin : symbols.EquationName)
      (leftTyped : Derivation signature (.arrow (signature.equationSource origin)
        (signature.equationTarget origin) (signature.left origin)))
      (rightTyped : Derivation signature (.arrow (signature.equationSource origin)
        (signature.equationTarget origin) (signature.right origin))) :
      Derivation signature (.equation (signature.equationSource origin)
        (signature.equationTarget origin) (signature.left origin) (signature.right origin))

structure HeaderFormation (signature : Signature (C := C) (symbols := symbols)) where
  source : ∀ origin, Derivation signature (.object (signature.source origin))
  target : ∀ origin, Derivation signature (.object (signature.target origin))
  left : ∀ origin, Derivation signature (.arrow (signature.equationSource origin)
    (signature.equationTarget origin) (signature.left origin))
  right : ∀ origin, Derivation signature (.arrow (signature.equationSource origin)
    (signature.equationTarget origin) (signature.right origin))

namespace Derivation

/-- Every declaration occurrence in the actual tree precedes the supplied
stage, including occurrences used only inside equation proofs. -/
def bounded {signature : Signature (C := C) (symbols := symbols)}
    {judgment : Judgment C symbols} (tree : Derivation signature judgment) (bound : Nat) : Prop :=
  match tree with
  | .baseObject _ => True
  | .objectName origin => signature.objectRank origin < bound
  | .terminalObject => True
  | .productObject leftTree rightTree => leftTree.bounded bound ∧ rightTree.bounded bound
  | .exponentialObject argument result => argument.bounded bound ∧ result.bounded bound
  | .equalizerObject source target leftTree rightTree =>
      source.bounded bound ∧ target.bounded bound ∧ leftTree.bounded bound ∧ rightTree.bounded bound
  | .baseArrow _ => True
  | .arrowName origin source target =>
      signature.arrowRank origin < bound ∧ source.bounded bound ∧ target.bounded bound
  | .identity formed => formed.bounded bound
  | .compose leftTree rightTree => leftTree.bounded bound ∧ rightTree.bounded bound
  | .terminalArrow formed => formed.bounded bound
  | .first left right => left.bounded bound ∧ right.bounded bound
  | .second left right => left.bounded bound ∧ right.bounded bound
  | .pair leftTree rightTree => leftTree.bounded bound ∧ rightTree.bounded bound
  | .evaluation argument result => argument.bounded bound ∧ result.bounded bound
  | .curry context argument result body =>
      context.bounded bound ∧ argument.bounded bound ∧ result.bounded bound ∧ body.bounded bound
  | .equalizerArrow source target leftTree rightTree =>
      source.bounded bound ∧ target.bounded bound ∧ leftTree.bounded bound ∧ rightTree.bounded bound
  | .equalizerLift source target context leftTree rightTree candidate commutes =>
      source.bounded bound ∧ target.bounded bound ∧ context.bounded bound ∧ leftTree.bounded bound ∧
      rightTree.bounded bound ∧ candidate.bounded bound ∧ commutes.bounded bound
  | .reflexivity typed => typed.bounded bound
  | .symmetry same => same.bounded bound
  | .transitivity before after => before.bounded bound ∧ after.bounded bound
  | .compositionCongruence before after => before.bounded bound ∧ after.bounded bound
  | .pairCongruence leftTree rightTree => leftTree.bounded bound ∧ rightTree.bounded bound
  | .curryCongruence context argument result same =>
      context.bounded bound ∧ argument.bounded bound ∧ result.bounded bound ∧ same.bounded bound
  | .leftIdentity source typed => source.bounded bound ∧ typed.bounded bound
  | .rightIdentity target typed => target.bounded bound ∧ typed.bounded bound
  | .associativity before middle after => before.bounded bound ∧ middle.bounded bound ∧ after.bounded bound
  | .terminalUniqueness leftTree rightTree => leftTree.bounded bound ∧ rightTree.bounded bound
  | .firstBeta left right leftTree rightTree =>
      left.bounded bound ∧ right.bounded bound ∧ leftTree.bounded bound ∧ rightTree.bounded bound
  | .secondBeta left right leftTree rightTree =>
      left.bounded bound ∧ right.bounded bound ∧ leftTree.bounded bound ∧ rightTree.bounded bound
  | .productEta left right typed => left.bounded bound ∧ right.bounded bound ∧ typed.bounded bound
  | .exponentialBeta context argument result body =>
      context.bounded bound ∧ argument.bounded bound ∧ result.bounded bound ∧ body.bounded bound
  | .exponentialEta context argument result typed =>
      context.bounded bound ∧ argument.bounded bound ∧ result.bounded bound ∧ typed.bounded bound
  | .equalizerCondition source target leftTree rightTree =>
      source.bounded bound ∧ target.bounded bound ∧ leftTree.bounded bound ∧ rightTree.bounded bound
  | .equalizerBeta source target context leftTree rightTree candidate commutes =>
      source.bounded bound ∧ target.bounded bound ∧ context.bounded bound ∧ leftTree.bounded bound ∧
      rightTree.bounded bound ∧ candidate.bounded bound ∧ commutes.bounded bound
  | .equalizerUniqueness before after same =>
      before.bounded bound ∧ after.bounded bound ∧ same.bounded bound
  | .baseIdentity _ => True
  | .baseComposition _ _ => True
  | .baseEquality _ => True
  | .declaredEquation origin left right =>
      signature.equationRank origin < bound ∧ left.bounded bound ∧ right.bounded bound

theorem bounded_monotone {signature : Signature (C := C) (symbols := symbols)}
    {judgment : Judgment C symbols} (tree : Derivation signature judgment)
    {earlier later : Nat} (increase : earlier ≤ later) :
    tree.bounded earlier → tree.bounded later := by
  induction tree <;> simp only [bounded] at *
  all_goals
    have rank_increase : ∀ {rank : Nat}, rank < earlier → rank < later :=
      fun below => Nat.lt_of_lt_of_le below increase
    aesop

end Derivation

/-- Staged declaration formation includes the actual proof trees, whose
every primitive occurrence is earlier than the declaration being formed.
This is stronger than checking names in the raw header expressions. -/
structure OrderedHeaderFormation (signature : Signature (C := C) (symbols := symbols)) where
  formation : HeaderFormation signature
  source_before : ∀ origin,
    (formation.source origin).bounded (signature.arrowRank origin)
  target_before : ∀ origin,
    (formation.target origin).bounded (signature.arrowRank origin)
  left_before : ∀ origin,
    (formation.left origin).bounded (signature.equationRank origin)
  right_before : ∀ origin,
    (formation.right origin).bounded (signature.equationRank origin)

end Mettapedia.CategoryTheory.RelativeClosedSyntax
