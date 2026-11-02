import Mettapedia.Languages.MeTTa.PeTTa.FoldSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.AggregationSource
import Mettapedia.Machines.InferredWordFold
import Mettapedia.GSLT.Dynamics.RegionPortfolio

/-!
# Uniform source-to-algebra refinement for a captured natural fold

The source body is elaborated once, with one accumulator slot and one item
slot. The existing coefficient test infers an input-only weight. Its source
derivation proves the callback law for every accumulator and input, and the
host-driver induction proves the whole fold. This is not inference from a
finite sequence of sampled callback values.

The captured five-argument host surface belongs to `FoldSource`. The older
`Eval` dispatcher has not thereby acquired a fold primitive. This module's
source theorem names that separate driver boundary explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.AdditiveFoldSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open FoldSource SpaceSemantics
open MeTTaIL.WireKit (number)
open Mettapedia.Machines.AdditiveFoldInference (Weight)

def environment (accumulatorName itemName : String) : AggregationSource.Environment 1 :=
  fun name => if name = accumulatorName then some (.register 0)
    else if name = itemName then some .inputValue else none

structure Certified (caller : Subst) (accumulatorName itemName : String) (body : Atom) where
  distinct : accumulatorName ≠ itemName
  freshAccumulator : caller.lookup accumulatorName = none
  freshItem : caller.lookup itemName = none
  algebra : AggregationSource.SourceCertificate (environment accumulatorName itemName) (fun _ => body)

def infer (caller : Subst) (accumulatorName itemName : String) (body : Atom) :
    Option (Certified caller accumulatorName itemName body) := do
  if distinct : accumulatorName ≠ itemName then
    if freshAccumulator : caller.lookup accumulatorName = none then
      if freshItem : caller.lookup itemName = none then
        let algebra ← AggregationSource.inferSource (environment accumulatorName itemName) (fun _ => body)
        return ⟨distinct, freshAccumulator, freshItem, algebra⟩
      else none
    else none
  else none

def Certified.weight {caller : Subst} {accumulatorName itemName : String} {body : Atom}
    (certificate : Certified caller accumulatorName itemName body) : Weight :=
  certificate.algebra.additive.weights 0

def callback (caller : Subst) (accumulatorName itemName : String) (body : Atom) : Callback :=
  .inline caller accumulatorName itemName body

theorem captured {caller : Subst} {accumulatorName itemName : String} {body : Atom}
    (certificate : Certified caller accumulatorName itemName body) (accumulator item : Nat) :
    AggregationSource.Captured (environment accumulatorName itemName)
      (bindings (callback caller accumulatorName itemName body) (number accumulator) (number item))
      (fun _ => accumulator) item := by
  intro name role found
  unfold environment at found
  split_ifs at found with first second
  · subst name
    cases found
    simp [bindings, callback, Subst.lookup, AggregationSource.Role.value]
  · subst name
    cases found
    simp [bindings, callback, Subst.lookup, AggregationSource.Role.value, certificate.distinct]

theorem uniform_callback {caller : Subst} {accumulatorName itemName : String} {body : Atom}
    (certificate : Certified caller accumulatorName itemName body) (program : Program)
    (state : Effects.State) (accumulator item : Nat) :
    Invokes program (callback caller accumulatorName itemName body) state
      (number accumulator) (number item) (number (accumulator + certificate.weight.eval item)) :=
  AggregationSource.source_translation certificate.algebra program _ state
    (fun _ => accumulator) item (captured certificate accumulator item) 0

def aggregate (weight : Weight) (items : List Nat) (initial : Nat) : Nat :=
  initial + (items.map weight.eval).sum

theorem uniform_fold {caller : Subst} {accumulatorName itemName : String} {body : Atom}
    (certificate : Certified caller accumulatorName itemName body) (program : Program)
    (state : Effects.State) (items : List Nat) (initial : Nat) :
    Evaluates program (callback caller accumulatorName itemName body) state (items.map number)
      (number initial) (number (aggregate certificate.weight items initial)) := by
  induction items generalizing initial with
  | nil =>
      simpa [aggregate] using (Evaluates.nil (program := program)
        (callback := callback caller accumulatorName itemName body) (state := state) (number initial))
  | cons item rest ih =>
      simpa [aggregate, Nat.add_assoc] using Evaluates.cons
        (uniform_callback certificate program state initial item)
        (ih (initial + certificate.weight.eval item))

theorem whole_fold_exact {caller : Subst} {accumulatorName itemName : String} {body : Atom}
    (certificate : Certified caller accumulatorName itemName body) (program : Program)
    (state : Effects.State) (items : List Nat) (initial : Nat) (answer : Atom) :
    Evaluates program (callback caller accumulatorName itemName body) state (items.map number)
      (number initial) answer ↔ answer = number (aggregate certificate.weight items initial) := by
  constructor
  · intro evaluated
    exact evaluates_unique evaluated (uniform_fold certificate program state items initial)
  · rintro rfl
    exact uniform_fold certificate program state items initial

theorem surface_returns {caller : Subst} {accumulatorName itemName : String} {body : Atom}
    (certificate : Certified caller accumulatorName itemName body) (program : Program)
    (state : Effects.State) (listName initialName : String) (items : List Nat) (initial : Nat)
    (listFound : caller.lookup listName = some (.expression (items.map number)))
    (initialFound : caller.lookup initialName = some (number initial)) :
    SurfaceEvaluates program caller state (inlineSurface listName initialName accumulatorName itemName body)
      (number (aggregate certificate.weight items initial)) :=
  .inline listName initialName accumulatorName itemName body (items.map number) (number initial) _
    listFound initialFound certificate.distinct certificate.freshAccumulator certificate.freshItem
    (uniform_fold certificate program state items initial)

theorem aggregate_append (weight : Weight) (first later : List Nat) (initial : Nat) :
    aggregate weight (first ++ later) initial = aggregate weight later (aggregate weight first initial) := by
  simp [aggregate, Nat.add_assoc]

theorem aggregate_perm (weight : Weight) {first second : List Nat} (same : first.Perm second) (initial : Nat) :
    aggregate weight first initial = aggregate weight second initial := by
  unfold aggregate
  rw [(same.map weight.eval).sum_eq]

def words (weight : Weight) (items : List Nat) (initial : Nat) : Option Nat :=
  (Mettapedia.Machines.InferredWordFold.prepareWords (fun _ : Fin 1 => initial)
    (fun _ => (items.map weight.eval).sum)).map fun plan =>
      Mettapedia.Machines.InferredWordFold.executeWords plan 0

theorem words_exact (weight : Weight) (items : List Nat) (initial value : Nat)
    (accepted : words weight items initial = some value) : value = aggregate weight items initial := by
  obtain ⟨plan, prepared, result⟩ := Option.map_eq_some_iff.mp accepted
  have exactWords := Mettapedia.Machines.InferredWordFold.prepareWords_correct _ _ _ prepared
  rw [← result, exactWords]
  rfl

theorem words_source_exact {caller : Subst} {accumulatorName itemName : String} {body : Atom}
    (certificate : Certified caller accumulatorName itemName body) (program : Program)
    (state : Effects.State) (items : List Nat) (initial value : Nat)
    (accepted : words certificate.weight items initial = some value) :
    Evaluates program (callback caller accumulatorName itemName body) state (items.map number)
      (number initial) (number value) := by
  rw [words_exact _ _ _ _ accepted]
  exact uniform_fold certificate program state items initial

def natural : Atom → Option Nat
  | .grounded (.int (.ofNat value)) => some value
  | _ => none

theorem natural_exact (atom : Atom) (value : Nat) (decoded : natural atom = some value) :
    atom = number value := by
  cases atom with
  | grounded value =>
      cases value with
      | int integer => cases integer <;> cases decoded; rfl
      | bool | string | custom => cases decoded
  | var | symbol | expression => cases decoded

def naturals (items : List Atom) : Option (List Nat) := items.mapM natural

theorem naturals_exact (items : List Atom) (values : List Nat) (decoded : naturals items = some values) :
    items = values.map number := by
  induction items generalizing values with
  | nil => cases decoded; rfl
  | cons item rest ih =>
      simp only [naturals, List.mapM_cons, Option.bind_eq_bind] at decoded
      obtain ⟨value, first, tail⟩ := Option.bind_eq_some_iff.mp decoded
      obtain ⟨more, later, same⟩ := Option.bind_eq_some_iff.mp tail
      have valuesEq : value :: more = values := Option.some.inj same
      rw [← valuesEq]
      simp [natural_exact item value first, ih more later]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.AdditiveFoldSource
