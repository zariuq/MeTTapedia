import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryInterpretation
import Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformationCoherenceControls

/-!
# Generated tuples under a nonconstant theory change

The object presheaf has genuinely different parallel-arrow actions.
Exchanging those arrows changes every supplied tuple component while
the canonical generated-context square retains binding positions.
A substitution duplicating one variable changes the authored variable's result.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.TheoryInterpretationControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open ObjectInterpretation TheoryInterpretation
open Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformationCoherenceControls (witnessDiagram exchange)

abbrev Worlds := WalkingParallelPair

def objects : Worldsᵒᵖ ⥤ Type :=
  walkingParallelPairOpEquiv.inverse ⋙ witnessDiagram

def supplied : (context objects 2).obj (Opposite.op WalkingParallelPair.one) :=
  ⟨⟨PUnit.unit, (8 : Nat)⟩, (13 : Nat)⟩

def constants (name : Empty) : objects.sections := nomatch name

def exchangedConstants (name : Empty) : (exchange.op ⋙ objects).sections := nomatch name

abbrev exchangePoint : (context (exchange.op ⋙ objects) 2).obj
    (Opposite.op WalkingParallelPair.one) := supplied

def route : Opposite.op WalkingParallelPair.one ⟶ Opposite.op WalkingParallelPair.zero :=
  Quiver.Hom.op WalkingParallelPairHom.left

theorem original_route_increments :
    (context objects 2).map route supplied =
      ⟨⟨PUnit.unit, (9 : Nat)⟩, (14 : Nat)⟩ := rfl

theorem exchanged_route_resets :
    (context (exchange.op ⋙ objects) 2).map route exchangePoint =
      ⟨⟨PUnit.unit, (1 : Nat)⟩, (1 : Nat)⟩ := rfl

/-- Identical world objects do not identify the two generated-context
actions on actual theory arrows. -/
theorem arrow_action_changes :
    (context objects 2).map route supplied ≠
      (context (exchange.op ⋙ objects) 2).map route exchangePoint := by
  intro same
  have last := congrArg Sigma.snd same
  change (14 : Nat) = 1 at last
  exact (by decide : (14 : Nat) ≠ 1) last

theorem newest_survives :
    (term (exchange.op ⋙ objects) exchangedConstants
      (ObjectTerm.var (0 : Fin 2))).app (Opposite.op WalkingParallelPair.one) exchangePoint = (13 : Nat) := rfl

theorem older_survives :
    (term (exchange.op ⋙ objects) exchangedConstants
      (ObjectTerm.var (1 : Fin 2))).app (Opposite.op WalkingParallelPair.one) exchangePoint = (8 : Nat) := rfl

def swap : ObjectSubstitution Empty 2 2 :=
  fun index => Fin.cases (.var 1) (fun _ => .var 0) index

def duplicate : ObjectSubstitution Empty 2 2 := fun _ => .var 0

theorem swapped_tuple :
    (substitution (exchange.op ⋙ objects) exchangedConstants swap).app
      (Opposite.op WalkingParallelPair.one) exchangePoint =
        ⟨⟨PUnit.unit, (13 : Nat)⟩, (8 : Nat)⟩ := rfl

theorem substitution_square :
    substitution (exchange.op ⋙ objects) exchangedConstants swap ≫
        contextMap exchange objects 2 =
      contextMap exchange objects 2 ≫ Functor.whiskerLeft exchange.op
        (substitution objects constants swap) :=
  substitution_restriction exchange objects constants swap

theorem duplicated_tuple :
    (substitution (exchange.op ⋙ objects) exchangedConstants duplicate).app
      (Opposite.op WalkingParallelPair.one) exchangePoint =
        ⟨⟨PUnit.unit, (13 : Nat)⟩, (13 : Nat)⟩ := rfl

theorem duplicate_changes_result :
    substitution (exchange.op ⋙ objects) exchangedConstants swap ≠
      substitution (exchange.op ⋙ objects) exchangedConstants duplicate := by
  intro same
  have result := congrArg (fun replacement =>
    (replacement.app (Opposite.op WalkingParallelPair.one) exchangePoint).2) same
  change (8 : Nat) = 13 at result
  exact (by decide : (8 : Nat) ≠ 13) result

end Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.TheoryInterpretationControls
