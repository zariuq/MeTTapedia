import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface
import Mettapedia.Logic.LinearLogic.KnowledgeTensorInitial

/-!
# A zoned reading of a step, and its theorem

A step has opaque states and firings indexed by states; the zoned calculus has frames, knowledge,
atoms and declared transitions. A **zoned reading** relates them. It reads a state as a frame,
knowledge at that frame and owned atoms; it names the declared transition a firing uses; and it
has two laws, one firing at a time:

* `forth`: an admitted firing is a firing of the transition it uses, between the readings of its
  state and of its result;
* `back`: a firing of a declared transition from the reading of a state, reaching good
  knowledge, is an admitted firing that uses it, and reaches the reading of its result.

"Good" is the consistency of knowledge. It is inherited by weaker knowledge and reflected by
transport, so it is asked only of the last knowledge.

* `ZonedReading.run_iff_proves`: **for every step with a zoned reading, the runs that end in a
  good state are exactly the graded proofs** from the reading of the start, whose grade admits
  the empty extra context and whose final knowledge is good, with the same uses in the same
  order.

The step, its frames and the zoned system are arbitrary. The two steps of the calculus are
instances (`KnowledgeTensorCoreReadingInstances`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

open Mettapedia.Logic.LinearLogic
open _root_.CategoryTheory
open KnowledgeTensor (ZonedSystem IndexedSystem)

universe uO uT uH uOcc uS uF uFr uHm uK uAtom uRule

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {Frame : Type uFr} [Category.{uHm} Frame] {K : Frame → Type uK} [∀ a, SemilatticeInf (K a)]
  {Atom : Frame → Type uAtom} {Rule : Frame → Type uRule}

/-- A zoned reading of a step. -/
structure ZonedReading (P : Step X O State Firing) (sys : ZonedSystem Frame K Atom Rule) where
  /-- A state read as a frame, knowledge at it and owned atoms. -/
  Reads : State → (a : Frame) → K a → Multiset (Atom a) → Prop
  /-- The declared transition a firing uses, with its frame. -/
  use : {s : State} → Firing s → Sigma Rule
  /-- Consistent knowledge. -/
  Good : {a : Frame} → K a → Prop
  /-- A state whose knowledge is consistent. -/
  good : State → Prop
  good_of_le : ∀ {a : Frame} {stronger weaker : K a}, stronger ≤ weaker → Good stronger →
    Good weaker
  good_of_know : ∀ {a b : Frame} (step : a ⟶ b) (k : K a), Good (sys.know step k) → Good k
  reads_good : ∀ {s : State} {a : Frame} {k : K a} {Γ : Multiset (Atom a)},
    Reads s a k Γ → (good s ↔ Good k)
  forth : ∀ {s : State} {a : Frame} {k : K a} {Γ : Multiset (Atom a)} (f : Firing s)
    (allowed : P.Admits f), Reads s a k Γ →
    ∃ (declaration : Rule a) (k' : K (sys.target declaration))
      (Γ' : Multiset (Atom (sys.target declaration))),
      use f = ⟨a, declaration⟩ ∧ sys.FiresUnder 0 declaration k Γ k' Γ' ∧
        Reads (P.result f allowed) (sys.target declaration) k' Γ'
  back : ∀ {s : State} {a : Frame} {k : K a} {Γ : Multiset (Atom a)} (declaration : Rule a)
    {k' : K (sys.target declaration)} {Γ' : Multiset (Atom (sys.target declaration))},
    Reads s a k Γ → sys.FiresUnder 0 declaration k Γ k' Γ' → Good k' →
    ∃ (f : Firing s) (allowed : P.Admits f), use f = ⟨a, declaration⟩ ∧
      Reads (P.result f allowed) (sys.target declaration) k' Γ'

namespace ZonedReading

variable {P : Step X O State Firing} {sys : ZonedSystem Frame K Atom Rule}
  (R : ZonedReading P sys)

/-- The uses of a run: the declared transitions its firings use, in order. -/
def uses {s : State} (run : P.Run s) : List (Sigma Rule) :=
  run.word.map fun event => R.use event.2

/-- **A run is a run of the zoned calculus**, with the same uses, between the readings of its
start and of its end. -/
theorem runUnder_of_run : ∀ {s : State} (run : P.Run s) {a : Frame} {k : K a}
    {Γ : Multiset (Atom a)}, R.Reads s a k Γ →
    ∃ (b : Frame) (along : a ⟶ b) (k' : K b) (Γ' : Multiset (Atom b)),
      sys.RunUnder a 0 k Γ (R.uses run) b along k' Γ' ∧ R.Reads run.last b k' Γ'
  | _, .nil _, a, k, Γ, reads => ⟨a, 𝟙 a, k, Γ, ZonedSystem.RunUnder.done a 0 k Γ, reads⟩
  | _, .cons f allowed rest, a, k, Γ, reads => by
      obtain ⟨declaration, k₁, Γ₁, used, fires, after⟩ := R.forth f allowed reads
      obtain ⟨b, along, k', Γ', later, ends⟩ := runUnder_of_run rest after
      have carried : sys.carried (sys.extend declaration) (0 : Multiset (Atom a)) = 0 :=
        IndexedSystem.carried_zero _
      have later' : sys.RunUnder (sys.target declaration)
          (sys.carried (sys.extend declaration) (0 : Multiset (Atom a))) k₁ Γ₁ (R.uses rest) b along
          k' Γ' := carried.symm ▸ later
      have zoned := ZonedSystem.RunUnder.fire fires later'
      refine ⟨b, sys.extend declaration ≫ along, k', Γ', ?_, ends⟩
      show sys.RunUnder a 0 k Γ (R.use f :: R.uses rest) b _ k' Γ'
      rw [used]
      exact zoned

/-- **A run of the zoned calculus from the reading of a state that ends in good knowledge is a
run of the step**, with the same uses, ending in a good state. -/
theorem run_of_runUnder : ∀ (word : List (Sigma Rule)) {s : State} {a b : Frame} {k : K a}
    {Γ : Multiset (Atom a)} {along : a ⟶ b} {k' : K b} {Γ' : Multiset (Atom b)},
    R.Reads s a k Γ → sys.RunUnder a 0 k Γ word b along k' Γ' → R.Good k' →
      ∃ run : P.Run s, R.uses run = word ∧ R.good run.last
  | [], s, _, _, k, _, along, _, _, reads, zoned, consistent => by
      have refined := ZonedSystem.RunUnder.refines zoned
      exact ⟨.nil s, rfl,
        (R.reads_good reads).mpr (R.good_of_know along k (R.good_of_le refined consistent))⟩
  | use :: rest, s, a, b, k, Γ, _, k', Γ', reads, zoned, consistent => by
      obtain ⟨declaration, k₁, Γ₁, onward, rfl, rfl, fires, later⟩ :=
        ZonedSystem.RunUnder.cons_inv zoned
      have refined := ZonedSystem.RunUnder.refines later
      have between : R.Good k₁ := R.good_of_know onward k₁ (R.good_of_le refined consistent)
      obtain ⟨f, allowed, used, after⟩ := R.back declaration reads fires between
      have carried : sys.carried (sys.extend declaration) (0 : Multiset (Atom a)) = 0 :=
        IndexedSystem.carried_zero _
      have later' : sys.RunUnder (sys.target declaration) 0 k₁ Γ₁ rest b onward k' Γ' :=
        carried ▸ later
      obtain ⟨run, word, ends⟩ := run_of_runUnder rest after later' consistent
      refine ⟨.cons f allowed run, ?_, ends⟩
      show R.use f :: R.uses run = ⟨a, declaration⟩ :: rest
      rw [used, word]

/-- **Runs are graded proofs, for every step with a zoned reading.** A run with given uses that
ends in a good state exists exactly when a graded proof exists, from the reading of the start,
whose grade admits the empty extra context and whose final knowledge is good. -/
theorem run_iff_proves {s : State} {a : Frame} {k : K a} {Γ : Multiset (Atom a)}
    (reads : R.Reads s a k Γ) (word : List (Sigma Rule)) :
    (∃ run : P.Run s, R.uses run = word ∧ R.good run.last) ↔
      ∃ (b : Frame) (along : a ⟶ b) (k' : K b) (Γ' : Multiset (Atom b))
        (grade : Multiset (Atom a) → Prop),
        grade 0 ∧ sys.Proves a 0 k Γ grade word b along k' Γ' ∧ R.Good k' := by
  constructor
  · rintro ⟨run, rfl, fine⟩
    obtain ⟨b, along, k', Γ', zoned, ends⟩ := R.runUnder_of_run run reads
    obtain ⟨grade, atZero, proof⟩ := ZonedSystem.RunUnder.proves zoned
    exact ⟨b, along, k', Γ', grade, atZero, proof, (R.reads_good ends).mp fine⟩
  · rintro ⟨b, along, k', Γ', grade, atZero, proof, consistent⟩
    have zoned := ZonedSystem.Proves.run proof 0 atZero
    rw [add_zero] at zoned
    exact R.run_of_runUnder word reads zoned consistent

end ZonedReading

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
