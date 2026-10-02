import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.TransactionResources
import Mettapedia.GSLT.Causality.ResourceWaves
import Mettapedia.GSLT.Causality.ResourceGrouping
import Mettapedia.GSLT.Core.ResourceAwareControl

/-!
# Finite waves of actual guarded-space transactions

Each entry retains a command, its selected atoms and its shared binding
environment. The independent network semantics below checks the actual
snapshot observations, linear claims and continuation emissions. Its exact
correspondence with resource execution makes finite-wave selection applicable
to transactions sharing the same space.

The batch certificate uses the existing observation-control interface.
Complete-bag demand permits bulk activation of the supplied batch; it does
not certify discovery of all matches or exploration of conflicting choices.
First-witness demand retains its controlled execution promise. This is a theorem about guarded-space
transactions, not an implementation correspondence for any complete dialect.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.TransactionWaves

open Mettapedia.GSLT
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ResourceAwareControl
open SpaceInteraction
open SpaceInteraction.GuardedTransaction
open TransactionResources

variable {Location Atom Pattern Environment : Type}
variable [DecidableEq Location] [DecidableEq Atom]
variable (selects : Selection Location Atom Pattern Environment)
variable (enabled : Command Location Atom Pattern Environment → Prop)

/-- One particular matching instance executes by the original network rules.
The selected environment determines the continuation; a worker cannot replace
it with a different successful match. -/
def ChosenStep (entry : (transactions selects enabled).Entry)
    (source target : Network Location Atom) : Prop :=
  ∃ residual,
    ObservesSnapshot entry.1.1.guards entry.2.1.1 source ∧
    Consumes entry.1.1.guards entry.2.1.1 source residual ∧
    target = publishAll (entry.1.1.continuation entry.2.1.2) residual

/-- A chosen transaction is a genuine firing of its original command. -/
theorem chosenStep_fires (entry : (transactions selects enabled).Entry)
    {source target : Network Location Atom}
    (step : ChosenStep selects enabled entry source target) :
    Fires selects entry.1.1 source target := by
  obtain ⟨residual, observed, consumed, rfl⟩ := step
  exact .fire entry.2.2.2 observed consumed

/-- Two-sided, binding-preserving correspondence for one transaction. The
network rule is defined by observations and claims, independently of the
resource successor. -/
theorem chosenStep_networkOf_iff (entry : (transactions selects enabled).Entry)
    (M : Multiset (Location × Atom)) (target : Network Location Atom) :
    ChosenStep selects enabled entry (networkOf M) target ↔
      (transactions selects enabled).Enables M entry.2 ∧
        target = networkOf ((transactions selects enabled).fire M entry.2) := by
  constructor
  · rintro ⟨residual, observed, consumed, rfl⟩
    obtain ⟨lengths, claimed, rfl⟩ := consumes_sound consumed M rfl
    have seen := (observes_iff _ _ M lengths).mp observed
    refine ⟨(snapshot_enables_iff _ _ M).mpr ⟨claimed, seen⟩, ?_⟩
    exact publishAll_networkOf _ _
  · rintro ⟨fits, rfl⟩
    obtain ⟨claimed, seen⟩ := (snapshot_enables_iff _ _ M).mp fits
    refine ⟨networkOf (M - claims entry.1.1.guards entry.2.1.1),
      (observes_iff _ _ M entry.2.2.1).mpr seen,
      consumes_complete _ _ M entry.2.2.1 claimed, ?_⟩
    exact (publishAll_networkOf _ _).symm

/-- Execute fixed matching instances through the independently defined
guarded network semantics. -/
def ChosenTrace : List (transactions selects enabled).Entry →
    Network Location Atom → Network Location Atom → Prop
  | [], source, target => target = source
  | entry :: rest, source, target =>
      ∃ middle, ChosenStep selects enabled entry source middle ∧
        ChosenTrace rest middle target

/-- Exact correspondence extends to every finite sequence, retaining command
and environment choices instead of merely comparing final answers. -/
theorem chosenTrace_networkOf_iff :
    ∀ (entries : List (transactions selects enabled).Entry)
      (M : Multiset (Location × Atom)) (target : Network Location Atom),
    ChosenTrace selects enabled entries (networkOf M) target ↔
      ∃ N, target = networkOf N ∧ (transactions selects enabled).Fires entries M N
  | [], M, target => by
      constructor
      · intro equal
        exact ⟨M, equal, rfl⟩
      · rintro ⟨N, equal, fires⟩
        change N = M at fires
        simpa [ChosenTrace, fires] using equal
  | entry :: rest, M, target => by
      constructor
      · rintro ⟨middle, step, suffix⟩
        obtain ⟨fits, rfl⟩ := (chosenStep_networkOf_iff selects enabled entry M middle).mp step
        obtain ⟨N, equal, fires⟩ :=
          (chosenTrace_networkOf_iff rest _ target).mp suffix
        exact ⟨N, equal, fits, fires⟩
      · rintro ⟨N, equal, fits, fires⟩
        refine ⟨networkOf ((transactions selects enabled).fire M entry.2),
          (chosenStep_networkOf_iff selects enabled entry M _).mpr ⟨fits, rfl⟩, ?_⟩
        exact (chosenTrace_networkOf_iff rest _ target).mpr ⟨N, equal, fires⟩

/-- Every chosen trace is an actual run of the guarded transaction GSLT. -/
theorem chosenTrace_multistep :
    ∀ (entries : List (transactions selects enabled).Entry)
      {source target : Network Location Atom},
    ChosenTrace selects enabled entries source target →
      (theory selects enabled).MultiStep source target
  | [], source, target, equal => by
      change target = source at equal
      subst target
      exact GSLT.MultiStep.refl (S := theory selects enabled) source
  | entry :: rest, source, target, trace => by
      obtain ⟨middle, step, suffix⟩ := trace
      exact .step ⟨entry.1.1, entry.1.2, chosenStep_fires selects enabled entry step⟩
        (chosenTrace_multistep rest suffix)

/-- A selected wave executes in every order with exactly one residual
network, even when all its commands use a single space. -/
theorem selectedWave_every_order (M : Multiset (Location × Atom))
    (candidates order : List (transactions selects enabled).Entry)
    (permutation : ((transactions selects enabled).selectWave M candidates).1.Perm order) :
    ChosenTrace selects enabled order (networkOf M)
      (networkOf ((transactions selects enabled).waveTarget M
        ((transactions selects enabled).selectWave M candidates).1)) :=
  (chosenTrace_networkOf_iff selects enabled order M _).mpr
    ⟨_, rfl, (transactions selects enabled).selectWave_every_order permutation⟩

/-- A chosen trace has one terminal network. Alternative environments remain
different entries and are never silently identified by this theorem. -/
theorem chosenTrace_functional (entries : List (transactions selects enabled).Entry)
    (M : Multiset (Location × Atom)) {first second : Network Location Atom}
    (firstRun : ChosenTrace selects enabled entries (networkOf M) first)
    (secondRun : ChosenTrace selects enabled entries (networkOf M) second) :
    first = second := by
  obtain ⟨N, rfl, firstFires⟩ := (chosenTrace_networkOf_iff selects enabled entries M first).mp firstRun
  obtain ⟨N', rfl, secondFires⟩ := (chosenTrace_networkOf_iff selects enabled entries M second).mp secondRun
  exact congrArg networkOf ((transactions selects enabled).fires_functional entries firstFires secondFires)

/-- The existing batch interface observes complete residual networks. -/
def executionSemantics : ExecutionSemantics (transactions selects enabled).Entry
    (Network Location Atom) (Network Location Atom) where
  run source entries target := ChosenTrace selects enabled entries source target
  observe := id

/-- A permutation-invariant candidate observation, with an independently
declared completion demand. -/
def batchContract (completion : CompletionDemand) :
    Contract (transactions selects enabled).Entry Unit
      (Multiset (transactions selects enabled).Entry) where
  observer := { observe := fun entries => (entries : Multiset _) }
  demand := { completion := completion }

/-- Construct the full wave certificate from the executable selector and its
proved correspondence. Resource funding observes the located occurrence bag. -/
def certifySelectedWave (M : Multiset (Location × Atom))
    (candidates : List (transactions selects enabled).Entry)
    (completion : CompletionDemand)
    (nonempty : ((transactions selects enabled).selectWave M candidates).1 ≠ []) :
    CertifiedBatch (batchContract selects enabled completion)
      (executionSemantics selects enabled) (networkOf M)
      (networkOf ((transactions selects enabled).waveTarget M
        ((transactions selects enabled).selectWave M candidates).1))
      (Multiset (Location × Atom))
      (fun entry => (transactions selects enabled).consume entry.2) M
      ((transactions selects enabled).selectWave M candidates).1 where
  nonempty := nonempty
  candidateInvariant := by
    intro order permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · exact selectedWave_every_order selects enabled M candidates _ (.refl _)
    · intro order permutation
      exact ⟨_, selectedWave_every_order selects enabled M candidates order permutation.symm, rfl⟩
  resources :=
    { frame := M - (transactions selects enabled).stepConsume
        ((transactions selects enabled).selectWave M candidates).1
      source_eq := by
        have conservation := (transactions selects enabled).selectWave_consumption_conservation M candidates
        simpa [batchDemand, System.stepConsume, add_comm] using conservation.symm }

/-! ## Same-space commands and demand controls -/

namespace Controls

open SpaceInteraction.GuardedTransaction.Canary
open TransactionResources.Controls (secondDirective)

/-- A join claims both worker results and installs the next phase's marker. -/
def joinCommand : Command CanaryLocation CanaryAtom CanaryAtom Unit where
  guards := [⟨.consume, .output, .answer⟩, ⟨.consume, .output, .done⟩]
  continuation _ := [⟨.control, .done⟩]

def allowed (command : Command CanaryLocation CanaryAtom CanaryAtom Unit) : Prop :=
  command = mixedCommand ∨ command = secondDirective ∨ command = joinCommand

abbrev work := transactions exactSelection allowed

def firstEntry : work.Entry :=
  ⟨⟨mixedCommand, Or.inl rfl⟩,
    ⟨([.exec, .fact], ()), rfl, .cons rfl (.cons rfl .nil)⟩⟩

def secondEntry : work.Entry :=
  ⟨⟨secondDirective, Or.inr (Or.inl rfl)⟩,
    ⟨([.nextExec, .fact], ()), rfl, .cons rfl (.cons rfl .nil)⟩⟩

def joinEntry : work.Entry :=
  ⟨⟨joinCommand, Or.inr (Or.inr rfl)⟩,
    ⟨([.answer, .done], ()), rfl, .cons rfl (.cons rfl .nil)⟩⟩

def initial : Multiset (CanaryLocation × CanaryAtom) :=
  {(.control, .exec), (.control, .nextExec), (.data, .fact)}

def final : Multiset (CanaryLocation × CanaryAtom) :=
  {(.control, .nextExec), (.data, .fact), (.output, .answer), (.output, .done)}

/-- Two directives at one location share a persistent read and form one
collectively funded wave. Location inequality is not necessary. -/
theorem same_space_two_directives :
    work.selectWave initial [firstEntry, secondEntry] =
      ([firstEntry, secondEntry], []) := by
  rfl

/-- The aggregate successor is computed from consumption and emissions,
independently of the proposed final network. -/
theorem same_space_target : work.waveTarget initial [firstEntry, secondEntry] = final := by
  decide +kernel

/-- Both worker orders execute the actual command observations, claims and
continuations, reaching the same nonempty network. -/
theorem same_space_both_orders :
    ChosenTrace exactSelection allowed [firstEntry, secondEntry]
        (networkOf initial) (networkOf final) ∧
      ChosenTrace exactSelection allowed [secondEntry, firstEntry]
        (networkOf initial) (networkOf final) := by
  constructor
  · have run := selectedWave_every_order exactSelection allowed initial
      [firstEntry, secondEntry] [firstEntry, secondEntry]
      (by rw [same_space_two_directives])
    simpa only [same_space_two_directives, same_space_target] using run
  · have run := selectedWave_every_order exactSelection allowed initial
      [firstEntry, secondEntry] [secondEntry, firstEntry]
      (by rw [same_space_two_directives]; exact List.Perm.swap _ _ [])
    simpa only [same_space_two_directives, same_space_target] using run

/-- These are actual GSLT executions, not merely equality of an encoded
reference function and itself. -/
theorem same_space_native_run :
    (theory exactSelection allowed).MultiStep (networkOf initial) (networkOf final) :=
  chosenTrace_multistep exactSelection allowed _ same_space_both_orders.1

def completeCertificate :=
  certifySelectedWave exactSelection allowed initial [firstEntry, secondEntry]
    .completeBag (by rw [same_space_two_directives]; simp)

def firstCertificate :=
  certifySelectedWave exactSelection allowed initial [firstEntry, secondEntry]
    .first (by rw [same_space_two_directives]; simp)

/-- Serializability and resource funding do not widen the request's declared
completion promise. -/
theorem demand_remains_explicit :
    (completeCertificate.plan .general).activation = .bulk ∧
      (firstCertificate.plan .general).activation = .controlled :=
  ⟨completeCertificate.completeBag_dispatches_bulk rfl,
    firstCertificate.first_remains_controlled rfl⟩

/-- Atomic validation retains a competing occurrence as deferred work; it
does not license consuming one directive twice in the same wave. -/
theorem same_directive_cannot_be_claimed_twice :
    work.selectWave initial [firstEntry, firstEntry] = ([firstEntry], [firstEntry]) := by
  rfl

def joined : Multiset (CanaryLocation × CanaryAtom) :=
  {(.control, .nextExec), (.data, .fact), (.control, .done)}

/-- No worker alone satisfies the join. Claiming both tokens is a genuine
dependency, even though the two producers can run concurrently. -/
theorem join_requires_both_results :
    ¬ work.Enables initial joinEntry.2 ∧
      ¬ work.Enables (work.fire initial firstEntry.2) joinEntry.2 ∧
      ¬ work.Enables (work.fire initial secondEntry.2) joinEntry.2 ∧
      work.Enables final joinEntry.2 := by
  simp only [System.Enables]
  decide +kernel

/-- Work generated by a wave is revalidated in the next wave, rather than
executed speculatively at the old snapshot. -/
theorem join_is_deferred_then_selected :
    work.selectWave initial [firstEntry, secondEntry, joinEntry] =
        ([firstEntry, secondEntry], [joinEntry]) ∧
      work.selectWave final [joinEntry] = ([joinEntry], []) :=
  ⟨rfl, rfl⟩

/-- The complete fork/join is a native guarded-network run. The retained
persistent fact and residual directive survive the join. -/
theorem fork_then_join_native_run :
    (theory exactSelection allowed).MultiStep (networkOf initial) (networkOf joined) := by
  have execution : work.Fires [firstEntry, secondEntry, joinEntry] initial joined := by
    simp only [System.Fires, System.Enables]
    decide +kernel
  exact chosenTrace_multistep exactSelection allowed _
    ((chosenTrace_networkOf_iff exactSelection allowed _ initial _).mpr
      ⟨joined, rfl, execution⟩)

end Controls

/-! ## Relational joins through the existing MeTTaIL matcher -/

namespace Relational

open Mettapedia.OSLF.MeTTaIL.Match

abbrev Data := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-- A collective selection uses the existing ordered matcher. Binding merges
enforce repeated variables across guards, including guards at one location. -/
def patternSelection (L : Type) : Selection L Data Data Bindings :=
  fun guards atoms bindings =>
    bindings ∈ matchArgs (guards.map Guard.pattern) atoms

instance decidablePatternSelection (L : Type) (guards : List (Guard L Data))
    (atoms : List Data) (bindings : Bindings) :
    Decidable (patternSelection L guards atoms bindings) :=
  inferInstanceAs (Decidable (bindings ∈ matchArgs (guards.map Guard.pattern) atoms))

/-- Match a finite catalogue of input vectors, retaining every matching
environment and its selected atoms. This does not consume the source data. -/
def discoverMatches {L : Type} (guards : List (Guard L Data))
    (vectors : List (List Data)) : List (List Data × Bindings) :=
  vectors.flatMap fun atoms =>
    (matchArgs (guards.map Guard.pattern) atoms).map fun bindings => (atoms, bindings)

/-- Discovery is sound and complete for the supplied input-vector catalogue
and the existing matcher, rather than for an assumed unification oracle. -/
theorem mem_discoverMatches {L : Type} (guards : List (Guard L Data))
    (vectors : List (List Data)) (atoms : List Data) (bindings : Bindings) :
    (atoms, bindings) ∈ discoverMatches guards vectors ↔
      atoms ∈ vectors ∧ patternSelection L guards atoms bindings := by
  simp only [discoverMatches, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨selected, member, environment, matched, sameAtoms, sameBindings⟩
    subst selected
    subst environment
    exact ⟨member, matched⟩
  · rintro ⟨member, matched⟩
    exact ⟨atoms, member, bindings, matched, rfl, rfl⟩

namespace Controls

open SpaceInteraction.GuardedTransaction.Canary (CanaryLocation)

def node (name : String) : Data := .apply name []
def edge (source target : String) : Data := .apply "Edge" [node source, node target]
def path (source target : String) : Data := .apply "TwoHop" [node source, node target]

def query : Command CanaryLocation Data Data Bindings where
  guards :=
    [⟨.observe, .data, .apply "Edge" [node "a", .fvar "middle"]⟩,
      ⟨.observe, .data, .apply "Edge" [.fvar "middle", .fvar "end"]⟩]
  continuation bindings :=
    [⟨.output, applyBindings bindings (.apply "TwoHop" [node "a", .fvar "end"])⟩]

def queryEnabled (command : Command CanaryLocation Data Data Bindings) : Prop :=
  command = query

abbrev querySystem := transactions (patternSelection CanaryLocation) queryEnabled

def bindingC : Bindings := [("end", node "c"), ("middle", node "b")]
def bindingD : Bindings := [("end", node "d"), ("middle", node "b")]

def entryC : querySystem.Entry :=
  ⟨⟨query, rfl⟩, ⟨([edge "a" "b", edge "b" "c"], bindingC), rfl, by decide +kernel⟩⟩

def entryD : querySystem.Entry :=
  ⟨⟨query, rfl⟩, ⟨([edge "a" "b", edge "b" "d"], bindingD), rfl, by decide +kernel⟩⟩

def dataRows : List Data := [edge "a" "b", edge "b" "c", edge "b" "d", edge "e" "c"]

def initial : Multiset (CanaryLocation × Data) :=
  (dataRows : Multiset Data).map fun atom => (.data, atom)

def final : Multiset (CanaryLocation × Data) :=
  initial + {(.output, path "a" "c"), (.output, path "a" "d")}

def inputVectors : List (List Data) :=
  (dataRows.product dataRows).map fun pair => [pair.1, pair.2]

/-- The actual matcher explores every ordered pair of rows. It finds both
valid paths and rejects a pair whose middle node disagrees. -/
theorem all_bindings_discovered :
    discoverMatches query.guards inputVectors =
      [([edge "a" "b", edge "b" "c"], bindingC),
        ([edge "a" "b", edge "b" "d"], bindingD)] := by
  decide +kernel

/-- A common variable is a join condition, not a second unrelated binder. -/
theorem wrong_middle_rejected :
    matchArgs (query.guards.map Guard.pattern) [edge "a" "b", edge "e" "c"] = [] := by
  decide +kernel

/-- Alternative bindings share one persistent edge and still form a wave. -/
theorem both_bindings_form_wave :
    querySystem.selectWave initial [entryC, entryD] = ([entryC, entryD], []) := by
  rfl

theorem both_bindings_target : querySystem.waveTarget initial [entryC, entryD] = final := by
  decide +kernel

/-- Both successful bindings execute together in either order, publishing
their distinct answers without taking either shared premise. -/
theorem both_bindings_execute :
    ChosenTrace (patternSelection CanaryLocation) queryEnabled [entryC, entryD]
        (networkOf initial) (networkOf final) ∧
      ChosenTrace (patternSelection CanaryLocation) queryEnabled [entryD, entryC]
        (networkOf initial) (networkOf final) := by
  constructor
  · have execution := selectedWave_every_order (patternSelection CanaryLocation)
      queryEnabled initial [entryC, entryD] [entryC, entryD]
      (by rw [both_bindings_form_wave])
    simpa only [both_bindings_form_wave, both_bindings_target] using execution
  · have execution := selectedWave_every_order (patternSelection CanaryLocation)
      queryEnabled initial [entryC, entryD] [entryD, entryC]
      (by rw [both_bindings_form_wave]; exact List.Perm.swap _ _ [])
    simpa only [both_bindings_form_wave, both_bindings_target] using execution

/-- The whole stored relation survives the query, including the distractor. -/
theorem original_rows_survive : networkOf final .data = networkOf initial .data := by
  decide +kernel

end Controls

end Relational

/-! ## Symmetric matching of complementary partial terms -/

namespace SymmetricControls

open SpaceInteraction.DirectCommBridge
open Mettapedia.OSLF.MeTTaIL.Match

def offered : GuardedParty :=
  ⟨.apply "Assignment" [.fvar "person", tSym "Rust"],
    .apply "Assigned" [.fvar "person"]⟩

def requested : GuardedParty :=
  ⟨.apply "Assignment" [tSym "Ada", .fvar "skill"],
    .apply "Use" [.fvar "skill"]⟩

def sharedBinding : Bindings := [("skill", tSym "Rust"), ("person", tSym "Ada")]

/-- Both parties contribute unknowns; the existing symmetric unifier solves
them together instead of matching one ground message against one pattern. -/
theorem complementary_terms_unify :
    unifyPattern? offered.term requested.term = some sharedBinding := by
  decide +kernel

/-- A conflicting concrete skill prevents contact. -/
theorem incompatible_terms_do_not_unify :
    unifyPattern? offered.term (.apply "Assignment" [tSym "Ada", tSym "Python"]) = none := by
  decide +kernel

/-- The actual direct COMM rule substitutes into both continuations. -/
theorem complementary_parties_contact (location : Name) :
    DirectComm (pPar [guardedProcess location offered, guardedProcess location requested])
      (pPar [.apply "Assigned" [nQuote (tSym "Ada")],
        .apply "Use" [nQuote (tSym "Rust")]]) := by
  have contact := DirectComm.contact (location := location)
    (left := offered) (right := requested) complementary_terms_unify
  simpa [offered, requested, sharedBinding, applyDot, dotBindings, applyBindings] using contact

/-- This contact also executes through the same guarded transaction rules as
the persistent relational query and the finite resource waves. -/
theorem complementary_contact_is_transaction (location : Name) :
    Fires directSelection (directCommand location offered requested)
      (directSource location offered requested)
      (directTarget location offered requested sharedBinding) :=
  direct_contact_fires complementary_terms_unify

end SymmetricControls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.TransactionWaves
