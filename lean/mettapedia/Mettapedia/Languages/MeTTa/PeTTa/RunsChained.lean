import Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
import Mettapedia.Languages.MeTTa.PeTTa.StreamingBindingReachability

/-!
# One store for the evaluation, bindings of its own for each alternative

`RunsAsFirings.streaming_store_run` shows that the store effects of a PeTTa evaluation are
one run of the ordered-store step. The bindings are not part of that run, and they cannot
be: alternatives bind the same variable differently. This module states what holds
instead, on top of the binding invariant of the streaming machine
(`Streaming.BindingInvariant`) and the soundness of its unifier (`Unifying.unifyTerms_sound`).

* `scan_sound`: every occurrence a `match` reads comes with a unifier that is idempotent,
  refines the bindings the `match` ran under, and makes the pattern equal to the
  occurrence's atom renamed for its own use. So what a read tells its alternative is the
  equation between the pattern and the renamed atom, and the alternative's bindings after
  the read are a solved form of it.
* `reached_match_tells`: in any state an evaluation reaches, an alternative about to run
  a written `match` has idempotent bindings that refine the entry's, and so has each
  alternative the `match` goes on with, by `scan_sound`.
* `streaming_chained`: for any number of steps of an evaluation against a loaded program,
  the store effects are one run of the ordered-store step (its word the steps' requests,
  its last occurrences the reached store), and every pending alternative, saved frame,
  collected answer and completed answer has idempotent bindings that refine the entry's.
  The store is chained through all alternatives; each alternative's bindings are its own.
* `no_common_refinement`, `Controls.addEach_answers_apart`: two alternatives need not have
  a common refinement. The two answers of `addEach` bind the same variable to `a` and to
  `b`, though both of their rows are in the one store.

Not proved here: each alternative's segment as a run of a step whose firings carry the
told equations as knowledge. That needs the unifier's refusal and most-generality, which
the tree has for the destination-equation models (`UnifyingConstraintRefusal`,
`UnifyingConstraintReadout`), carried over to the models of the step's frames.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open Mettapedia.Languages.MeTTa.ContextualTransform
open PeTTaStoreSelection (atomFrames)
open PeTTaQueryInterpretation (scan)
open Unifying (resolve)
open NamedSpaces (Handle)

/-- **What a read tells.** Each packet of a scan is an occurrence of the scanned rows, at
some position, with a unifier that is idempotent, refines the bindings the scan ran under,
and makes the pattern equal to the occurrence's atom renamed for that position's use. -/
theorem scan_sound {O : Type} (label : O → Atom) (bindings : Subst) (pattern : Atom)
    (idempotent : Unifying.Idempotent bindings) :
    ∀ (use : Nat) (rows : List O) (packets : List (O × Subst)),
      scan label bindings pattern use rows = some packets →
      ∀ packet ∈ packets, ∃ index, rows[index]? = some packet.1 ∧
        Unifying.Idempotent packet.2 ∧ Unifying.Refines bindings packet.2 ∧
        resolve packet.2 pattern =
          resolve packet.2 (Unifying.rename (use + index) (label packet.1))
  | _, [], packets, scanned, packet, member => by
      simp only [scan, Option.some.injEq] at scanned
      subst scanned
      cases member
  | use, occurrence :: rest, packets, scanned, packet, member => by
      cases later : scan label bindings pattern (use + 1) rest with
      | none => simp [scan, later] at scanned
      | some remaining =>
          have inherited := scan_sound label bindings pattern idempotent (use + 1) rest
            remaining later
          have fromRest : packet ∈ remaining → ∃ index,
              (occurrence :: rest)[index]? = some packet.1 ∧
              Unifying.Idempotent packet.2 ∧ Unifying.Refines bindings packet.2 ∧
              resolve packet.2 pattern =
                resolve packet.2 (Unifying.rename (use + index) (label packet.1)) := by
            intro found
            obtain ⟨index, at_, valid, refined, solved⟩ := inherited packet found
            refine ⟨index + 1, by simpa using at_, valid, refined, ?_⟩
            rw [solved]
            congr 2
            omega
          cases matched : Unifying.unify bindings pattern
              (Unifying.rename use (label occurrence)) with
          | ok bound =>
              simp [scan, later, matched] at scanned
              subst scanned
              rcases List.mem_cons.mp member with here | found
              · subst here
                obtain ⟨valid, refined, solved⟩ := Unifying.unifyTerms_sound _ bindings bound
                  pattern (Unifying.rename use (label occurrence)) idempotent matched
                exact ⟨0, rfl, valid, refined, by simpa using solved⟩
              · exact fromRest found
          | clash =>
              simp [scan, later, matched] at scanned
              subst scanned
              exact fromRest member
          | exhausted => simp [scan, later, matched] at scanned

/-- **An alternative about to run a written `match`, in any state an evaluation reaches**:
its bindings are idempotent and refine the entry's, and every occurrence the `match` reads
gives an alternative whose bindings are idempotent, refine the entry's and the reader's,
and solve the equation between the pattern and the occurrence's renamed atom. -/
theorem reached_match_tells {O : Type} (label : O → Atom)
    (registry : SpaceSemantics.Program) (fuel : Nat) (world : Streaming.World)
    (expression : Atom) (answer : Unifying.Answer) (others : List Unifying.Answer)
    (frames : List Streaming.Frame)
    (pending : Streaming.Job.execute ⟨.returned (answer :: others), frames⟩ ∈
      (Streaming.advance registry fuel (Streaming.enter world expression)).agenda)
    (pattern : Atom) (use : Nat) (rows : List O) (packets : List (O × Subst))
    (scanned : scan label answer.bindings pattern use rows = some packets) :
    Unifying.BindingRefines [] answer.bindings ∧
    ∀ packet ∈ packets, ∃ index, rows[index]? = some packet.1 ∧
      Unifying.BindingRefines [] packet.2 ∧ Unifying.Refines answer.bindings packet.2 ∧
      resolve packet.2 pattern =
        resolve packet.2 (Unifying.rename (use + index) (label packet.1)) := by
  have task := Streaming.BindingInvariant.reached_task_refines registry fuel world expression
    ⟨.returned (answer :: others), frames⟩ pending
  have mine : Unifying.BindingRefines [] answer.bindings := by
    simp only [Unifying.ControlRefines] at task
    exact task answer (List.mem_cons_self ..)
  refine ⟨mine, ?_⟩
  intro packet member
  obtain ⟨index, at_, valid, refined, solved⟩ :=
    scan_sound label answer.bindings pattern mine.1 use rows packets scanned packet member
  exact ⟨index, at_, ⟨valid, mine.2.trans refined⟩, refined, solved⟩

/-- **One store, bindings of its own for each alternative.** For any number of steps of
an evaluation against a loaded program: the store effects are one run of the ordered-store
step from the program's rows, with the steps' requests as its word and the reached store
tracked by its last occurrences; and everything the machine holds at that point (pending
alternatives, saved frames, collected and completed answers) has idempotent bindings that
refine the entry's. -/
theorem streaming_chained (registry program : SpaceSemantics.Program) (expression : Atom)
    (fuel : Nat) :
    (∃ run : (OrderedStore.step atomFrames PUnit.unit rowSupply.label).Run
        (([] : EquationStore Atom), Row.load 0 (SpaceSemantics.loadedAtoms program)),
      run.word.map (fun firing => (firing.2 : OrderedStore.Publication Atom Row)) =
        requests rowSupply registry fuel
          (Streaming.enter { state := Effects.loaded program } expression)
          (Row.load 0 (SpaceSemantics.loadedAtoms program)) ∧
      run.last.1 = [] ∧
      Tracks rowSupply run.last.2
        (Streaming.advance registry fuel
          (Streaming.enter { state := Effects.loaded program } expression)).world.state) ∧
    Streaming.BindingInvariant.stateRefines []
      (Streaming.advance registry fuel
        (Streaming.enter { state := Effects.loaded program } expression)) :=
  ⟨evaluation_store_run registry program expression fuel,
    Streaming.BindingInvariant.every_request_prefix_refines registry fuel _ expression⟩

/-- Two substitutions that resolve one variable to different symbols have no common
refinement. -/
theorem no_common_refinement {first second : Subst} {name one other : String}
    (left : resolve first (.var name) = .symbol one)
    (right : resolve second (.var name) = .symbol other) (different : one ≠ other) :
    ¬ ∃ common : Subst, Unifying.Refines first common ∧ Unifying.Refines second common := by
  rintro ⟨common, viaFirst, viaSecond⟩
  have one_ := viaFirst (.var name)
  have other_ := viaSecond (.var name)
  rw [left] at one_
  rw [right] at other_
  have same : (Atom.symbol one) = .symbol other := by
    have a : resolve common (.symbol one) = .symbol one := rfl
    have b : resolve common (.symbol other) = .symbol other := rfl
    rw [← a, ← b, one_, other_]
  exact different (Atom.symbol.inj same)

namespace Controls

/-- The two answers of `addEach` bind the variable of its `let` to `a` and to `b`. -/
theorem addEach_answers :
    (Streaming.advance registry 60 (Streaming.enter { state := store } addEach)).answers.map
        (fun answer => resolve answer.bindings (.var "x#0")) = [a, b] := by
  decide +kernel

/-- Negative: the bindings of the two answers of `addEach` have no common refinement,
though both of their rows are in the one store (`addEach_store`). -/
theorem addEach_answers_apart (first second : Unifying.Answer)
    (answers : (Streaming.advance registry 60
      (Streaming.enter { state := store } addEach)).answers = [first, second]) :
    ¬ ∃ common : Subst, Unifying.Refines first.bindings common ∧
      Unifying.Refines second.bindings common := by
  have resolved := addEach_answers
  rw [answers] at resolved
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at resolved
  exact no_common_refinement (name := "x#0") (one := "a") (other := "b") resolved.1 resolved.2
    (by decide)

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
