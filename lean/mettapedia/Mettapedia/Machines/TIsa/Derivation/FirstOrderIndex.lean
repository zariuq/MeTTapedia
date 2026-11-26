import Mettapedia.Machines.TIsa.Derivation.FirstOrderTerms
import Mettapedia.Machines.TIsa.Derivation.OccurrenceIndex
import Mettapedia.Machines.TIsa.Derivation.IndexedMachine

/-!
# A head and argument index for the first-order matcher

An application supplies its head before matching. An argument
supplies a key when the bindings already instantiate it. No new
matcher is needed: both tests are justified by the substitution
which realizes an accepted match. Collisions in a key encoding can
invite extra comparisons but cannot erase a match.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.FirstOrderTerms

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

variable {σ : LPSignature}

abbrev Head (σ : LPSignature) := Sum σ.constants σ.functionSymbols

def valueHead : GroundTerm σ → Head σ
  | .const c => .inl c
  | .app f _ => .inr f

def valueArgument (value : GroundTerm σ) (position : ℕ) : Option (GroundTerm σ) :=
  match value with
  | .const _ => none
  | .app f arguments =>
    if present : position < σ.functionArity f then some (arguments ⟨position, present⟩) else none

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def requestedHead (bindings : Bindings σ) : Term σ → Option (Head σ)
  | .var x => (lookup bindings x).map valueHead
  | .const c => some (.inl c)
  | .app f _ => some (.inr f)

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
def requestedArgument (bindings : Bindings σ) : Term σ → Option (ℕ × GroundTerm σ)
  | .app f arguments =>
    (List.finRange (σ.functionArity f)).findSome? fun i =>
      (instantiate bindings (arguments i)).map fun value => (i.val, value)
  | _ => none

private theorem realized {bindings next : Bindings σ} {pattern : Term σ} {value : GroundTerm σ}
    (hit : extend bindings pattern value = some next) :
    ∃ τ : Subst σ, Denotes bindings τ ∧ τ.applyTerm pattern = value.toTerm := by
  obtain ⟨τ, agrees⟩ := semantics.extend_inhabited bindings pattern value next hit
  exact ⟨τ, (semantics.extend_iff bindings pattern value τ).mp ⟨next, hit, agrees⟩⟩

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem requested_head_sound {bindings : Bindings σ} {pattern : Term σ} {value : GroundTerm σ}
    {key : Head σ} {τ : Subst σ} (denoted : Denotes bindings τ)
    (solved : τ.applyTerm pattern = value.toTerm)
    (selected : requestedHead bindings pattern = some key) : valueHead value = key := by
  cases pattern with
  | var x =>
    obtain ⟨ground, held, rfl⟩ := Option.map_eq_some_iff.mp selected
    have identical := GroundTerm.toTerm_injective ((denoted x ground (lookup_some held)).symm.trans solved)
    rw [identical]
  | const c =>
    cases value with
    | const d =>
      have same : c = d := Term.const.inj solved
      exact (congrArg Sum.inl same).symm.trans (Option.some.inj selected)
    | app _ _ => cases solved
  | app f args =>
    cases value with
    | const _ => cases solved
    | app g vals =>
      have same : f = g := (Term.app.inj solved).1
      exact (congrArg Sum.inr same).symm.trans (Option.some.inj selected)

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem requested_argument_sound {bindings : Bindings σ} {pattern : Term σ} {value : GroundTerm σ}
    {position : ℕ} {key : GroundTerm σ} {τ : Subst σ} (denoted : Denotes bindings τ)
    (solved : τ.applyTerm pattern = value.toTerm)
    (selected : requestedArgument bindings pattern = some (position, key)) :
    valueArgument value position = some key := by
  cases pattern with
  | var _ => cases selected
  | const _ => cases selected
  | app f arguments =>
    obtain ⟨i, _, found⟩ := List.exists_of_findSome?_eq_some selected
    obtain ⟨chosen, ready, equal⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    cases value with
    | const _ => cases solved
    | app g values =>
      have heads : f = g := (Term.app.inj solved).1
      subst g
      have sameArgs := eq_of_heq (Term.app.inj solved).2
      have atPosition := congrFun sameArgs i
      have same := GroundTerm.toTerm_injective
        (atPosition.symm.trans (instantiate_sound bindings τ denoted _ _ ready))
      simp only [valueArgument, dif_pos i.isLt, same]

def indexKeys {H A : Type*} (encodeHead : Head σ → H) (encodeArgument : GroundTerm σ → A) :
    IndexKeys (matcher (σ := σ)) H A where
  head := encodeHead ∘ valueHead
  argument value position := (valueArgument value position).map encodeArgument
  needHead bindings pattern := (requestedHead bindings pattern).map encodeHead
  needArgument bindings pattern :=
    (requestedArgument bindings pattern).map (fun ⟨position, value⟩ => (position, encodeArgument value))
  head_sound hit required := by
    obtain ⟨τ, denoted, solved⟩ := realized hit
    obtain ⟨_, occurs, rfl⟩ := Option.map_eq_some_iff.mp required
    exact congrArg encodeHead (requested_head_sound denoted solved occurs)
  argument_sound hit required := by
    obtain ⟨τ, denoted, solved⟩ := realized hit
    obtain ⟨⟨ordinal, key⟩, occurs, paired⟩ := Option.map_eq_some_iff.mp required
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj paired
    rw [requested_argument_sound denoted solved occurs]
    rfl

section Examples

private abbrev signature : LPSignature where
  constants := ℕ
  vars := ℕ
  relationSymbols := Empty
  relationArity := fun _ => 0
  functionSymbols := Bool
  functionArity := fun _ => 2

private instance : DecidableEq signature.vars := inferInstanceAs (DecidableEq ℕ)
private instance : DecidableEq signature.constants := inferInstanceAs (DecidableEq ℕ)
private instance : DecidableEq signature.functionSymbols := inferInstanceAs (DecidableEq Bool)

private def pairV (f : Bool) (a b : ℕ) : GroundTerm signature :=
  .app f (fun i => .const (if i.val = 0 then a else b))

private def pairP (f : Bool) (a b : Term signature) : Term signature :=
  .app f (fun i => if i.val = 0 then a else b)

private def shared : Term signature := pairP true (.var 0) (.var 1)

private def encode : Head signature → ℕ
  | .inl c => c + 2
  | .inr f => if f then 0 else 1

private def keys : IndexKeys (matcher (σ := signature)) ℕ ℕ :=
  indexKeys encode (encode ∘ valueHead)

private def store : Store (GroundTerm signature) :=
  ⟨[(0, pairV false 41 0), (1, pairV true 41 8), (2, pairV true 84 8),
    (3, pairV true 41 8)], 4⟩

private def rule : Rule (Term signature) :=
  ⟨PUnit.unit, ⟨[], [pairP false (.var 0) (.const 0), shared], [], [], [.var 1]⟩, []⟩

/-- The head bucket contains three edges; after learning the source,
the argument bucket contains two equal edge values at different IDs. -/
theorem bound_argument_skips_only_the_other_edge :
    let index := OccurrenceIndex.build keys 2 store
    (OccurrenceIndex.query keys index [] shared).map Prod.fst = [1, 2, 3] ∧
      (OccurrenceIndex.query keys index [(0, .const 41)] shared).map Prod.fst = [1, 3] := by
  dsimp only
  constructor <;> rw [OccurrenceIndex.query_eq_filter] <;> decide +kernel

theorem indexed_rule_keeps_both_derivations :
    (firingsUsing matcher (OccurrenceIndex.access keys 2) [rule] store).map (fun f => f.2.read) =
      [[0, 1], [0, 3]] := by
  rw [OccurrenceIndex.firings_exact]
  decide +kernel

theorem indexed_rule_publishes_the_same_first_answer :
    StepsUsing matcher [rule] (OccurrenceIndex.access keys 2) (.run 1 store)
      (.halt (.exhausted (store.add (.const 8)))) := by
  apply (indexed_machine_run_iff _ _ _ _ _ _).mpr
  decide +kernel

private def someBindings : Bindings signature := [(0, .const 41)]

private def collapsed : List (ℕ × GroundTerm signature) :=
  (OccurrenceIndex.query keys (OccurrenceIndex.build keys 2 store) someBindings shared).take 1

/-- Keeping just one occurrence per equal payload is not even an
alternative access path for this read. -/
theorem collapsing_equal_edges_loses_a_match :
    ¬∃ wrong : CandidateAccess (matcher (σ := signature)),
      wrong.read store someBindings shared = collapsed := by
  rintro ⟨wrong, collapsedRead⟩
  let before : Match (GroundTerm signature) (Bindings signature) :=
    ⟨someBindings, [], [], [], []⟩
  have equal := wrong.exact store .read shared before
  change (wrong.read store someBindings shared).filterMap _ = _ at equal
  rw [collapsedRead] at equal
  have counted := congrArg List.length equal
  change (collapsed.filterMap (attempt (matcher (σ := signature)) .read shared before)).length =
    (store.occurrences.filterMap (attempt (matcher (σ := signature)) .read shared before)).length at counted
  unfold collapsed at counted
  rw [OccurrenceIndex.query_eq_filter] at counted
  exact (by decide +kernel : ¬_) counted

end Examples

end Mettapedia.Machines.TIsa.Derivation.FirstOrderTerms
