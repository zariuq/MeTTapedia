import Mettapedia.Machines.Cursor.LetStructuralLaws

/-!
# A qualified effect-law characterization of constant singleton searches

Under equality of complete finite traces and availability of setters to every
world, discardability and commutation with those setters characterize a total
world-independent singleton search. The conclusion is earned by constructor
inversion and contextual equations, not supplied as a semantic premise.

The observer includes answer/final worlds and every retained continuation.
It does not automatically observe hidden machine actions or instruction cost;
such observations must be carried by the selected world/trace. Restricting
setters or weakening observation can admit additional computations. This is
not a syntactic closed/pure/singleton criterion or a universal language policy.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetStructuralCharacterization

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)
open LetPlacement (yieldOne yield_bind append_done)
open LetStructuralLaws (discard leftThenRight rightThenLeft)

variable {World Value : Type}

def erase (trace : Trace World Value) : Trace World Unit :=
  trace.bind (fun _ => yieldOne ())

theorem erase_done_iff (trace : Trace World Value) (world : World) :
    erase trace = .done world ↔ trace = .done world := by
  cases trace with
  | done final => simp [erase, Trace.bind]
  | answer value here later => simp [erase, Trace.bind, yieldOne, Trace.append]

/-- Equality of the complete erased residual prevents a hidden further
answer or a world change after the first answer, even on another resumption world. -/
theorem erase_singleton_iff (trace : Trace World Value) (world : World) :
    erase trace = .answer () world .done ↔
      ∃ value, trace = .answer value world .done := by
  constructor
  · intro erased
    cases trace with
    | done final => simp [erase, Trace.bind] at erased
    | answer value here later =>
        change Trace.answer () here (fun next => erase (later next)) =
          Trace.answer () world Trace.done at erased
        have parts := Trace.answer.inj erased
        have sameWorld : here = world := parts.2.1
        have residual : later = Trace.done := by
          funext next
          apply (erase_done_iff (later next) next).mp
          exact congrFun parts.2.2 next
        exact ⟨value, by rw [sameWorld, residual]⟩
  · rintro ⟨value, rfl⟩
    rfl

def setWorld (target : World) : Search World Unit := fun _ =>
  .answer () target .done

def Discardable (code : Search World Value) : Prop := LetStructuralLaws.discard code = yieldOne ()

def CommutesSetters (code : Search World Value) : Prop :=
  ∀ target, leftThenRight code (setWorld target) = rightThenLeft code (setWorld target)

/-- Discardability alone earns a same-world singleton at every input. It
does not require that the returned value be independent of that input. -/
theorem discardable_singleton_at (code : Search World Value) (discardable : Discardable code)
    (world : World) : ∃ value, code world = .answer value world .done := by
  apply (erase_singleton_iff (code world) world).mp
  exact congrFun discardable world

/-- With two actual singleton traces, the setter equation equates their
values. Setter effects are retained in both orders at the same target world. -/
theorem singleton_values_equal (code : Search World Value) (firstWorld secondWorld : World)
    (first second : Value)
    (atFirst : code firstWorld = .answer first firstWorld .done)
    (atSecond : code secondWorld = .answer second secondWorld .done)
    (commutes : leftThenRight code (setWorld secondWorld) =
      rightThenLeft code (setWorld secondWorld)) : first = second := by
  have compared := congrFun commutes firstWorld
  simp only [leftThenRight, rightThenLeft, Search.bind, setWorld,
    Trace.bind, Trace.append, atFirst, atSecond, yieldOne] at compared
  exact congrArg Prod.fst (Trace.answer.inj compared).1

theorem laws_imply_constant (inhabited : Nonempty World) (code : Search World Value)
    (discardable : Discardable code) (commutes : CommutesSetters code) :
    ∃ value, code = yieldOne value := by
  rcases inhabited with ⟨initial⟩
  obtain ⟨chosen, atInitial⟩ := discardable_singleton_at code discardable initial
  refine ⟨chosen, ?_⟩
  funext world
  obtain ⟨value, atWorld⟩ := discardable_singleton_at code discardable world
  have same := singleton_values_equal code world initial value chosen atWorld atInitial (commutes initial)
  simpa only [same, yieldOne] using atWorld

/-- These are semantic structural laws under the explicitly stated observer
and setter capabilities; no syntactic classification is inferred. -/
theorem constant_iff_structural_laws (inhabited : Nonempty World) (code : Search World Value) :
    (∃ value, code = yieldOne value) ↔ Discardable code ∧ CommutesSetters code := by
  constructor
  · rintro ⟨value, rfl⟩
    exact ⟨LetStructuralLaws.discard_constant value,
      fun target => LetStructuralLaws.constant_commutes value (setWorld target)⟩
  · rintro ⟨discardable, commutes⟩
    exact laws_imply_constant inhabited code discardable commutes

theorem constant_value_unique (inhabited : Nonempty World) (code : Search World Value)
    (first second : Value) (one : code = yieldOne first) (two : code = yieldOne second) :
    first = second := by
  rcases inhabited with ⟨world⟩
  have same := congrFun (one.symm.trans two) world
  exact (Trace.answer.inj same).1

def readWorld : Search Nat Nat := fun world => .answer world world .done

example : Discardable readWorld := by
  funext world
  simp [LetStructuralLaws.discard, Search.bind, readWorld, yieldOne, Trace.bind, Trace.append]

example : (leftThenRight readWorld (setWorld 1) 0).drain = ([(0, ())], 1) ∧
    (rightThenLeft readWorld (setWorld 1) 0).drain = ([(1, ())], 1) := by decide

/-- Commuting only with a no-change operation does not force a fixed value. -/
example : leftThenRight readWorld (yieldOne ()) = rightThenLeft readWorld (yieldOne ()) := by
  simp [leftThenRight, rightThenLeft, yield_bind]

def noAnswer : Search Nat Nat := fun _ => .done 0

/-- Commutation by itself does not imply a total answer. -/
example : CommutesSetters noAnswer := by
  intro target
  funext world
  simp [leftThenRight, rightThenLeft, noAnswer, setWorld, Search.bind,
    Trace.bind, Trace.append]

example : (discard noAnswer 0).drain = ([], 0) ∧
    (yieldOne (World := Nat) () 0).drain = ([()], 0) := by decide

example : Discardable (yieldOne (World := Nat) 7) ∧ CommutesSetters (yieldOne (World := Nat) 7) :=
  (constant_iff_structural_laws ⟨0⟩ (yieldOne 7)).mp ⟨7, rfl⟩

/-- A completed drain in the unchanged world misses a retained continuation
that behaves differently after the caller changes the resumption world. -/
def worldSensitiveTail : Search Bool Nat := fun initial =>
  .answer 7 initial fun resumed =>
    if resumed = initial then .done resumed else .answer 8 resumed .done

example : (worldSensitiveTail false).drain = ([7], false) ∧
    (LetStructuralLaws.discard worldSensitiveTail false).drain = ([()], false) := by decide

example : erase (worldSensitiveTail false) ≠ .answer () false .done := by
  intro same
  have tail := congrFun (Trace.answer.inj same).2.2 true
  change Trace.answer () true Trace.done = Trace.done true at tail
  cases tail

def emptyWorldCode : Search Empty Empty := fun world => nomatch world

/-- Inhabited-world scope matters: in an empty world type the two equations
are vacuous, while an empty result type supplies no constant value. -/
example : Discardable emptyWorldCode ∧ CommutesSetters emptyWorldCode ∧
    ¬ ∃ value, emptyWorldCode = yieldOne value := by
  refine ⟨?_, ?_, ?_⟩
  · funext world; cases world
  · intro target; cases target
  · rintro ⟨value, _⟩; cases value

end Mettapedia.Machines.Cursor.LetStructuralCharacterization
