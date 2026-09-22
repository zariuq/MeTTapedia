import Mettapedia.GSLT.Parsing.PlainBnfNameIndexOrdered
import Mettapedia.GSLT.Parsing.PlainBnfOrderedGraphDiscovery
import Mathlib.Data.String.Basic

/-!
# Indexed known names with unchanged ordered observations

The ordered name list remains the observation. The existing first-binding
two/three-tree is auxiliary lookup state, with each name stored as its own
payload. Construction and append establish the index invariant, including
initial and appended duplicate names. No grammar syntax or scheduling changes.

The indexed sweep and discovery execution reuse the existing finite grammar
carrier and source-order scheduler. Their exact ordered observations are
proved equal to that independent reference. Authored-rule, name-codec, and
generated-runtime correspondence remain separate obligations.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfIndexedKnownNames

universe uN
variable {Name : Type uN} [LinearOrder Name]

structure State (Name : Type uN) where
  names : List Name
  index : PlainBnfNameIndex.Tree Name Name
  deriving Repr

def empty : State Name := ⟨[], .empty⟩

def append (state : State Name) (name : Name) : State Name :=
  ⟨state.names ++ [name], PlainBnfNameIndex.insertFirst name name state.index⟩

def seed : List Name → State Name → State Name
  | [], state => state
  | name :: rest, state => seed rest (append state name)

def ofList (names : List Name) : State Name := seed names empty

def lookup (state : State Name) (name : Name) : Option Name :=
  PlainBnfNameIndex.lookup name state.index

def known (state : State Name) (name : Name) : Bool := (lookup state name).isSome

structure Valid (state : State Name) : Prop where
  ordered : PlainBnfNameIndex.Ordered state.index
  lookup_exact : ∀ name, lookup state name = if name ∈ state.names then some name else none

theorem empty_valid : Valid (empty : State Name) :=
  ⟨List.Pairwise.nil, by intro name; simp [lookup, empty, PlainBnfNameIndex.lookup]⟩

theorem append_valid (state : State Name) (valid : Valid state) (name : Name) :
    Valid (append state name) := by
  refine ⟨PlainBnfNameIndex.insertFirst_ordered name name state.index valid.ordered, ?_⟩
  intro query
  change PlainBnfNameIndex.lookup query (PlainBnfNameIndex.insertFirst name name state.index) = _
  rw [PlainBnfNameIndex.lookup_insertFirst query name name state.index valid.ordered]
  change (if query = name then some ((lookup state name).getD name) else lookup state query) = _
  rw [valid.lookup_exact name, valid.lookup_exact query]
  by_cases same : query = name
  · subst query
    by_cases present : name ∈ state.names <;> simp [append, present]
  · simp [append, same]

theorem seed_valid (names : List Name) (state : State Name) (valid : Valid state) :
    Valid (seed names state) := by
  induction names generalizing state with
  | nil => exact valid
  | cons name rest ih => exact ih (append state name) (append_valid state valid name)

theorem seed_names (names : List Name) (state : State Name) :
    (seed names state).names = state.names ++ names := by
  induction names generalizing state with
  | nil => simp [seed]
  | cons name rest ih => simp [seed, ih, append, List.append_assoc]

theorem ofList_valid (names : List Name) : Valid (ofList names) :=
  seed_valid names empty empty_valid

@[simp] theorem ofList_names (names : List Name) : (ofList names).names = names := by
  simp [ofList, seed_names, empty]

theorem lookup_ofList (names : List Name) (name : Name) :
    lookup (ofList names) name = if name ∈ names then some name else none := by
  simpa using (ofList_valid names).lookup_exact name

/-- Exact found-name payload, not just successful membership. -/
theorem lookup_append (state : State Name) (valid : Valid state) (name query : Name) :
    lookup (append state name) query =
      if query ∈ state.names ++ [name] then some query else none :=
  (append_valid state valid name).lookup_exact query

theorem known_exact (state : State Name) (valid : Valid state) :
    known state = fun name => decide (name ∈ state.names) := by
  funext name
  by_cases present : name ∈ state.names <;> simp [known, valid.lookup_exact, present]

open PlainBnfOrderedGraphDiscovery

theorem known_append {size : Nat} (state : State (Fin size)) (valid : Valid state)
    (position : Fin size) :
    known (append state position) = publish (known state) position := by
  rw [known_exact _ (append_valid state valid position), known_exact state valid]
  funext other
  by_cases same : other = position <;> simp [append, publish, same]

structure Result (size : Nat) where
  state : State (Fin size)
  discoveries : List (Fin size)

def sweepIndexed {size : Nat} (grammar : Grammar size) :
    List (Fin size) → State (Fin size) → Result size
  | [], state => ⟨state, []⟩
  | position :: rest, state =>
      if ready grammar (known state) position then
        let after := sweepIndexed grammar rest (append state position)
        ⟨after.state, position :: after.discoveries⟩
      else sweepIndexed grammar rest state

/-- The concrete indexed sweep preserves both its validity and every public
ordered result. It changes name lookup, not the pass schedule. -/
theorem sweepIndexed_exact {size : Nat} (grammar : Grammar size) (positions : List (Fin size))
    (state : State (Fin size)) (valid : Valid state) :
    Valid (sweepIndexed grammar positions state).state ∧
      (sweepIndexed grammar positions state).discoveries =
        (sweep grammar positions (known state)).discoveries ∧
      (sweepIndexed grammar positions state).state.names =
        state.names ++ (sweep grammar positions (known state)).discoveries ∧
      known (sweepIndexed grammar positions state).state =
        (sweep grammar positions (known state)).known := by
  induction positions generalizing state with
  | nil => simp [sweepIndexed, sweep, valid]
  | cons position rest ih =>
      cases enabled : ready grammar (known state) position with
      | false => simpa [sweepIndexed, sweep, enabled] using ih state valid
      | true =>
          have after := ih (append state position) (append_valid state valid position)
          rw [known_append state valid position] at after
          simpa [sweepIndexed, sweep, enabled, append, List.append_assoc] using after

/-- No input index hypothesis: the actual tree is constructed from the
initial list before executing the sweep. Duplicate initial names survive. -/
theorem sweep_ofList_observation {size : Nat} (grammar : Grammar size)
    (positions names : List (Fin size)) :
    (sweepIndexed grammar positions (ofList names)).state.names =
      names ++ (sweep grammar positions (fun position => decide (position ∈ names))).discoveries := by
  have result := (sweepIndexed_exact grammar positions (ofList names) (ofList_valid names)).2.2.1
  simpa [known_exact _ (ofList_valid names)] using result

def runIndexed {size : Nat} (grammar : Grammar size) :
    Nat → State (Fin size) → Nat → Nat → List (Event size)
  | 0, _, _, _ => []
  | fuel + 1, state, round, cursor =>
      match nextEvent grammar (known state) round cursor with
      | none => []
      | some event =>
          event :: runIndexed grammar fuel (append state event.position)
            event.round (event.position.val + 1)

theorem runIndexed_exact {size : Nat} (grammar : Grammar size) (fuel : Nat)
    (state : State (Fin size)) (valid : Valid state) (round cursor : Nat) :
    runIndexed grammar fuel state round cursor = runEvents grammar fuel (known state) round cursor := by
  induction fuel generalizing state round cursor with
  | zero => rfl
  | succ fuel ih =>
      simp only [runIndexed, runEvents]
      cases selected : nextEvent grammar (known state) round cursor with
      | none => rfl
      | some event =>
          dsimp only
          rw [ih (append state event.position) (append_valid state valid event.position),
            known_append state valid event.position]

/-- Exact event ordering from the genuinely constructed index, for any
finite discovery prefix and any starting source cursor. -/
theorem run_ofList_exact {size : Nat} (grammar : Grammar size) (fuel : Nat)
    (names : List (Fin size)) (round cursor : Nat) :
    runIndexed grammar fuel (ofList names) round cursor =
      runEvents grammar fuel (fun position => decide (position ∈ names)) round cursor := by
  rw [runIndexed_exact grammar fuel (ofList names) (ofList_valid names),
    known_exact _ (ofList_valid names)]
  simp

theorem duplicate_names_retained :
    (append (ofList [2, 1, 2]) (2 : Nat)).names = [2, 1, 2, 2] ∧
      lookup (append (ofList [2, 1, 2]) (2 : Nat)) 2 = some 2 := by decide

theorem unicode_names_retain_their_payload :
    (ofList ["λ", "a", "λ", "雪"]).names = ["λ", "a", "λ", "雪"] ∧
      lookup (ofList ["λ", "a", "λ", "雪"]) "λ" = some "λ" ∧
      lookup (ofList ["λ", "a", "λ", "雪"]) "missing" = none := by decide

/-- Traversing the ordered map is not the public name-list observation. -/
theorem index_order_is_not_discovery_order :
    (ofList [2, 1]).names = [2, 1] ∧
      PlainBnfNameIndex.bindings (ofList [2, 1]).index = [(1, 1), (2, 2)] := by decide

private def wrongPayload : State Nat := ⟨[2], .two .empty 2 9 .empty⟩

theorem wrong_payload_is_not_valid : ¬ Valid wrongPayload := by
  intro valid
  have found := valid.lookup_exact 2
  simp [wrongPayload, lookup, PlainBnfNameIndex.lookup] at found

private def cascade : Grammar 3 := fun position =>
  if position = 1 then [⟨[0], true⟩] else [⟨[], true⟩]

theorem indexed_cascade_preserves_order :
    (sweepIndexed cascade (List.finRange 3) (ofList [])).state.names = [0, 1, 2] ∧
      runIndexed cascade 3 (ofList []) 0 0 = [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩] := by decide

private def seededDependency : Grammar 2 := fun position =>
  if position = 0 then [⟨[], false⟩] else [⟨[0], true⟩]

/-- The index actually supplies execution's membership decisions. A stale
index paired with an apparently correct list loses a real discovery. -/
theorem stale_index_changes_execution :
    runIndexed seededDependency 2 ⟨[0], .empty⟩ 0 0 = [] ∧
      runIndexed seededDependency 2 (ofList [0]) 0 0 = [⟨0, 1⟩] := by decide

end Mettapedia.GSLT.Parsing.PlainBnfIndexedKnownNames
