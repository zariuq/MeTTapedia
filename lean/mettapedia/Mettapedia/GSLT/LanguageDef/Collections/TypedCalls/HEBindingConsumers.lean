import Mettapedia.Languages.MeTTa.HE.BindingProjection
import Mettapedia.Languages.MeTTa.HE.Matching
import Mettapedia.Languages.MeTTa.HE.Eval

/-!
# Consumer-qualified binding projection

The value and binding environment of an outcome are different observations.
Mapping a successful argument value to unit does not discard its environment
or its occurrence. Full erasure is valid precisely for consumers independent
of that environment. The existing equality-aware projection is sufficient
for a consumer's complete retained read list, including aliases and misses.

The matching controls use the actual HE matcher and binding resolver. They
show why matching under an empty record can select a different branch.
These are continuation/projection laws, not a native case/nop implementation
or a complete source-level adequacy theorem for those library functions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBindingConsumers

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

abbrev Consumer (Answer : Type) := ResultPair → List Answer

def erase (reply : ResultPair) : ResultPair := (reply.1, Bindings.empty)

def eraseBindings (replies : ResultSet) : ResultSet := replies.map erase

def consume {Answer : Type} (client : Consumer Answer) (replies : ResultSet) : List Answer :=
  replies.flatMap client

/-- A checkable obligation belongs to the continuation, not merely the
returned value's syntactic support. -/
def IgnoresBindings {Answer : Type} (client : Consumer Answer) : Prop :=
  ∀ value bindings, client (value, bindings) = client (value, Bindings.empty)

/-- Exact order and multiplicity are preserved for every producer batch iff
the continuation cannot distinguish any erased environment. -/
theorem erasure_safe_iff {Answer : Type} (client : Consumer Answer) :
    (∀ replies, consume client (eraseBindings replies) = consume client replies) ↔
      IgnoresBindings client := by
  constructor
  · intro safe value bindings
    have one := safe [(value, bindings)]
    simpa only [consume, eraseBindings, erase, List.map_cons, List.map_nil,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] using one.symm
  · intro independent replies
    simp only [consume, eraseBindings, List.flatMap_map]
    apply List.flatMap_congr
    intro reply _
    exact (independent reply.1 reply.2).symm

/-- Ignore a successful argument's payload while retaining its bindings and
its position. Error/stopped argument handling precedes this body operation. -/
def unitValues (replies : ResultSet) : ResultSet :=
  replies.map fun reply => (Atom.unit, reply.2)

theorem unitValues_environments (replies : ResultSet) :
    (unitValues replies).map Prod.snd = replies.map Prod.snd := by
  simp [unitValues, List.map_map]

theorem unitValues_length (replies : ResultSet) :
    (unitValues replies).length = replies.length := by simp [unitValues]

theorem unitValues_append (first later : ResultSet) :
    unitValues (first ++ later) = unitValues first ++ unitValues later := by
  simp [unitValues]

/-- Replacing values does not change any binding-only continuation. This
does not assert that the environment may then be forgotten. -/
theorem unitValues_consume {Answer : Type} (client : Bindings → List Answer)
    (replies : ResultSet) :
    consume (fun reply => client reply.2) (unitValues replies) =
      consume (fun reply => client reply.2) replies := by
  simp [consume, unitValues, List.flatMap_map]

/-- Capture each alternative separately under the same saved read contract. -/
def projectReplies (reads : BindingProjection.Applications) (replies : ResultSet) : ResultSet :=
  replies.map fun reply => (reply.1, BindingProjection.forApplications reply.2 reads)

def observeReplies (reads : BindingProjection.Applications) (replies : ResultSet) :
    List (Atom × List Atom) :=
  replies.map fun reply => (reply.1, BindingProjection.observe reply.2 reads)

/-- The actual projection algorithm preserves the complete observation of
every alternative, in order. It does not combine their binding stores. -/
theorem observe_projectReplies (reads : BindingProjection.Applications) (replies : ResultSet) :
    observeReplies reads (projectReplies reads replies) = observeReplies reads replies := by
  simp only [observeReplies, projectReplies, List.map_map]
  apply List.map_congr_left
  intro reply _
  exact congrArg (fun observations => (reply.1, observations))
    (BindingProjection.observe_forApplications reply.2 reads)

/-- A projection for the whole saved continuation also preserves an ordered
subsequence of its reads, for example one branch selected afterward. -/
theorem observe_projectReplies_sublist (all selected : BindingProjection.Applications)
    (included : selected.Sublist all) (replies : ResultSet) :
    observeReplies selected (projectReplies all replies) = observeReplies selected replies := by
  simp only [observeReplies, projectReplies, List.map_map]
  apply List.map_congr_left
  intro reply _
  exact congrArg (fun observations => (reply.1, observations))
    (BindingProjection.observe_forApplications_sublist reply.2 all selected included)

/-- A consumer that uses just these observed atoms may process the projected
record without changing its complete output list. -/
theorem consumer_after_projection {Answer : Type}
    (reads : BindingProjection.Applications) (client : Atom → List Atom → List Answer)
    (replies : ResultSet) :
    consume (fun reply => client reply.1 (BindingProjection.observe reply.2 reads))
      (projectReplies reads replies) =
    consume (fun reply => client reply.1 (BindingProjection.observe reply.2 reads)) replies := by
  simp only [consume, projectReplies, List.flatMap_map]
  apply List.flatMap_congr
  intro reply _
  exact congrArg (client reply.1) (BindingProjection.observe_forApplications reply.2 reads)

namespace Controls

def five : Atom := .grounded (.int 5)
def ok : Atom := .symbol "ok"
def bound (n : Int) : Bindings := Bindings.empty.assign "y" (.grounded (.int n))
def future : BindingProjection.Applications := [(.var "y", 8)]
def readY : Consumer Atom := fun reply => [reply.2.applyFull (.var "y") 8]

theorem captured_assignment_visible :
    consume readY [(ok, bound 5)] = [five] ∧
      consume readY (eraseBindings [(ok, bound 5)]) = [.var "y"] := by decide

theorem unit_still_carries_assignment :
    consume readY (unitValues [(ok, bound 5)]) = [five] := by decide

theorem unit_does_not_license_erasure : ¬ IgnoresBindings readY := by
  intro independent
  have same := independent Atom.unit (bound 5)
  have different : readY (Atom.unit, bound 5) ≠ readY (Atom.unit, Bindings.empty) := by decide
  exact different same

theorem independent_alternatives_remain_distinct :
    consume readY (unitValues [(ok, bound 1), (ok, bound 2)]) =
      [.grounded (.int 1), .grounded (.int 2)] := by decide

theorem no_input_is_not_one_unit : unitValues [] ≠ [(Atom.unit, Bindings.empty)] := by decide

/-- The value contains no variable, but the selected pattern reads a bound
one. The actual matching gate changes before a branch body is even chosen. -/
theorem bindings_constrain_pattern_selection :
    matchAtoms ok ((bound 5).applyFull (.var "y") 8) 8 = [] ∧
      matchAtoms ok (Bindings.empty.applyFull (.var "y") 8) 8 ≠ [] := by decide

theorem retained_projection_keeps_caller :
    consume readY (unitValues (projectReplies future [(ok, bound 5)])) = [five] := by decide

theorem projecting_only_unit_loses_caller :
    consume readY (projectReplies [(Atom.unit, 8)] (unitValues [(ok, bound 5)])) = [.var "y"] := by
  decide

/-- A genuine value-only observer may erase the environments. -/
theorem value_observation_can_erase (replies : ResultSet) :
    consume (fun reply => [reply.1]) (eraseBindings replies) =
      consume (fun reply => [reply.1]) replies :=
  (erasure_safe_iff _).mpr (fun _ _ => rfl) replies

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBindingConsumers
