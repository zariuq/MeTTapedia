import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.ReadWordTriangle
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.HEWorldRemoval
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.ServiceFootprints

/-!
# Honest writes on HE's world machine: rows with stable identities

`RowWorlds` labels a row with its position. That is honest for reads, but not for writes: HE's
`add-atom` puts the new atom in **front** of the space (`HE.Space.add`), so every row's position
moves, and a positional encoding of the add takes and remakes every row. It then writes into the
region of every query, related or not (`Controls.positions_renumber`). Here a row carries a stable
identity instead (`KeyedWorld`: an atom with an identity no other row has), and HE's world machine
runs on keyed rows:

* `keyedServices`: HE's native `add-atom` makes one row with a fresh identity, in front; HE's native
  `remove-atom` removes the first row holding the atom, and every other row keeps its identity.
  They are HE's own space operations with identities attached: the space a keyed world presents
  (`keyedView`) moves exactly by `HE.Space.add` and `HE.Space.remove` (`keyed_refines`).
* `add_writes_one`, `remove_takes_one`: **honest write footprints**. HE's add fires the commit that
  makes exactly the new row, which is fresh; HE's removal fires the commit that takes exactly one
  row.
* `he_adds_row`, `he_removes_row`: these are steps of HE's world machine
  (`HEOnTheStep.heWorldMachine`), through its native rule.
* `world_core_transfer`: every other move of HE's world machine reads its world only through the
  rows of its region (`HEFootprints.heRegion`), as on the read-only machine.

## Zar's race on HE's world machine

`he_world_race`: for an open complete query over a region (an equation query's region, for
instance) and HE's add of a row with a fresh identity: if the added atom is inside the region, the
add spoils the query, the query as it was is disabled after the add, and the query asked again
holds one row more; if it is outside, the add and the query are independent and the region is
unchanged. `double_race` instantiates it with the equation query of `(double 4)`: another copy of
`(= (double 4) 8)` spoils it, `(p a)` commutes.

## The query on keyed rows: positions are inert

HE's equation works record the position of their row, and HE's add moves every position. Still:

* `frontier_keyed_transfer`: an equation query's frontier is determined, up to those recorded
  positions, by the rows of its region in order (`frontier_reposition`, `rowResults_reposition`);
* `equationsCons_position_free`, `invocationEquationsCons_position_free`: no rule reads a work's
  position.

So a write outside the region leaves what the query passes on unchanged, though the configuration
records the shifted positions.

## Controls

* `Controls.positions_renumber` (negative, for positions as identities): adding `(q b)`, outside the
  region of the query `(double 4)`, renumbers `(= (double 4) 8)` from position `1` to `2`; the
  positional write takes the row at position `1` and so writes into the query's region, while with
  identities the add of `(q b)` is independent of the query.
* `Controls.removal_separates` (separating write control): on `(p a)` stored twice, HE's removal on
  keyed rows takes exactly one row and presents HE's `Space.remove`; PeTTa's removal request takes
  both rows.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace HonestWrites

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldLocalStepWith LocalStep)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation UnscopedControl
  managedContextControl)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup WorldServices Frame)
open HEOnTheStep (heWorldMachine)
open MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.MeTTa.PeTTa

/-! ## Keyed rows -/

/-- **A world of rows with stable identities**: each row is an atom with an identity. HE's order
of the space is the order of the list. -/
abbrev KeyedWorld := List (Atom × ℕ)

/-- **The space a keyed world presents to HE**: its atoms, in order. -/
def keyedView : KeyedWorld → Unit → Space := fun world _ => ⟨world.map Prod.fst⟩

/-- Remove the first row holding an atom; every other row keeps its identity. -/
def removeFirst : KeyedWorld → Atom → KeyedWorld
  | [], _ => []
  | row :: rest, atom => if row.1 = atom then rest else row :: removeFirst rest atom

/-- **HE's world services on keyed rows**: `add-atom` makes one row with a fresh identity, in front;
`remove-atom` removes the first row holding the atom. Both answer `()`. -/
def keyedServices : WorldServices Unit KeyedWorld where
  contextPayload _ := .custom "Space" "self"
  nativeCall _ world name _ argument frame results after :=
    results = [(WorldRemoval.unitValue, frame)] ∧
      ((name = .symbol "add-atom" ∧ ∃ id, id ∉ world.map Prod.snd ∧ after = (argument, id) :: world) ∨
        (name = .symbol "remove-atom" ∧ after = removeFirst world argument))

theorem removeFirst_head (atom : Atom) (i : ℕ) (rest : KeyedWorld) :
    removeFirst ((atom, i) :: rest) atom = rest := by
  simp [removeFirst]

theorem removeFirst_skip {a atom : Atom} (different : ¬ a = atom) (i : ℕ) (rest : KeyedWorld) :
    removeFirst ((a, i) :: rest) atom = (a, i) :: removeFirst rest atom := by
  simp [removeFirst, different]

theorem map_removeFirst (world : KeyedWorld) (atom : Atom) :
    (removeFirst world atom).map Prod.fst = (world.map Prod.fst).erase atom := by
  induction world with
  | nil => rfl
  | cons row rest ih =>
      by_cases same : row.1 = atom
      · simp [removeFirst, same]
      · simp [removeFirst, same, ih]

/-- **The keyed services are HE's space operations, with identities attached**: the presented
space moves by `HE.Space.add` or by `HE.Space.remove`. -/
theorem keyed_refines {world after : KeyedWorld} {name function argument : Atom} {frame : Frame}
    {results : List Result}
    (call : keyedServices.nativeCall () world name function argument frame results after) :
    results = [(WorldRemoval.unitValue, frame)] ∧
      ((name = .symbol "add-atom" ∧ keyedView after () = (keyedView world ()).add argument) ∨
        (name = .symbol "remove-atom" ∧ keyedView after () = (keyedView world ()).remove argument)) := by
  obtain ⟨answered, (⟨named, id, _, rfl⟩ | ⟨named, rfl⟩)⟩ := call
  · exact ⟨answered, Or.inl ⟨named, rfl⟩⟩
  · exact ⟨answered, Or.inr ⟨named, congrArg Space.mk (map_removeFirst world argument)⟩⟩

/-! ## Honest write footprints -/

/-- **An add writes one row**: HE's add fires the commit that makes exactly the new row, and the
new row is fresh. -/
theorem add_writes_one {world : KeyedWorld} {atom : Atom} {id : ℕ}
    (fresh : id ∉ world.map Prod.snd) :
    ((atom, id) :: world).toFinset =
        fire world.toFinset (Commit.makeOne (atom, id) : Commit (Atom × ℕ) Atom) ∧
      (atom, id) ∉ world.toFinset := by
  refine ⟨?_, fun member => fresh (List.mem_map.mpr ⟨_, List.mem_toFinset.mp member, rfl⟩)⟩
  ext o
  simp only [List.toFinset_cons, Finset.mem_insert, mem_fire, Commit.makeOne_taken,
    Commit.makeOne_made, Finset.notMem_empty, not_false_eq_true, and_true, Finset.mem_singleton]
  tauto

/-- **A removal takes one row**: removing the first row holding an atom that the world holds fires
the commit that takes exactly one row holding it. -/
theorem remove_takes_one : ∀ {world : KeyedWorld}, (world.map Prod.snd).Nodup →
    ∀ {atom : Atom}, atom ∈ world.map Prod.fst →
      ∃ id, (atom, id) ∈ world ∧ (removeFirst world atom).toFinset =
        fire world.toFinset (Commit.takeOne (atom, id) : Commit (Atom × ℕ) Atom)
  | [], _, _, member => by simp at member
  | (a, i) :: rest, distinct, atom, member => by
      have restDistinct : (rest.map Prod.snd).Nodup := (List.nodup_cons.mp distinct).2
      have rowFresh : i ∉ rest.map Prod.snd := (List.nodup_cons.mp distinct).1
      by_cases same : a = atom
      · subst same
        have notIn : (a, i) ∉ rest := fun inRest => rowFresh (List.mem_map.mpr ⟨_, inRest, rfl⟩)
        refine ⟨i, List.mem_cons_self, ?_⟩
        rw [removeFirst_head]
        ext o
        simp only [List.mem_toFinset, mem_fire, List.toFinset_cons, Finset.mem_insert,
          Commit.takeOne_taken, Commit.takeOne_made, Finset.mem_singleton, Finset.notMem_empty,
          or_false]
        constructor
        · intro inRest
          exact ⟨Or.inr inRest, fun same => notIn (same ▸ inRest)⟩
        · rintro ⟨same | inRest, other⟩
          · exact absurd same other
          · exact inRest
      · have later : atom ∈ rest.map Prod.fst := by
          rcases List.mem_cons.mp member with head | inRest
          · exact absurd head.symm same
          · exact inRest
        obtain ⟨id, inRest, removed⟩ := remove_takes_one restDistinct later
        refine ⟨id, List.mem_cons_of_mem _ inRest, ?_⟩
        have other : (a, i) ≠ (atom, id) := fun equal => same (congrArg Prod.fst equal)
        rw [removeFirst_skip same, List.toFinset_cons, removed]
        ext o
        simp only [Finset.mem_insert, mem_fire, List.toFinset_cons, Commit.takeOne_taken,
          Commit.takeOne_made, Finset.mem_singleton, Finset.notMem_empty, or_false]
        constructor
        · rintro (rfl | ⟨inRest', notTaken⟩)
          · exact ⟨Or.inl rfl, other⟩
          · exact ⟨Or.inr inRest', notTaken⟩
        · rintro ⟨rfl | inRest', notTaken⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨inRest', notTaken⟩

/-! ## The steps of HE's world machine -/

/-- `(call-native add-atom space a)` as pending minimal work. -/
def addCall (atom : Atom) (live : List Atom) (scope : List String) (caller : Option Atom)
    (readiness : Entry.Status) (activation : Frame) : Control Unit :=
  .work (.minimal live scope caller (.expression readiness [.symbol "call-native",
    .symbol "add-atom", .symbol "space", Entry.Value.ofAtom atom]) activation)

/-- `(call-native remove-atom space a)` as pending minimal work. -/
def removeCall (atom : Atom) (live : List Atom) (scope : List String) (caller : Option Atom)
    (readiness : Entry.Status) (activation : Frame) : Control Unit :=
  .work (.minimal live scope caller (.expression readiness [.symbol "call-native",
    .symbol "remove-atom", .symbol "space", Entry.Value.ofAtom atom]) activation)

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-- **HE's world machine adds a row**, with any fresh identity, in front. -/
theorem he_adds_row {world : KeyedWorld} {atom : Atom} {id : ℕ} (fresh : id ∉ world.map Prod.snd)
    (live : List Atom) (scope : List String) (caller : Option Atom) (readiness : Entry.Status)
    (activation : Frame) (stack : List Continuation) (emitted : List Result) :
    (heWorldMachine keyedView keyedServices dispatch lookup policy ()).Step
      ⟨world, addCall atom live scope caller readiness activation, stack, emitted⟩
      ⟨(atom, id) :: world, .returning [(WorldRemoval.unitValue, activation)], stack, emitted⟩ :=
  .internal (WorldLocalStepWith.native
    ⟨rfl, Or.inl ⟨by simp [Entry.Value.erase], id, fresh, by rw [Entry.Value.erase_ofAtom]⟩⟩)

/-- **HE's world machine removes one row**: the first one holding the atom. -/
theorem he_removes_row (world : KeyedWorld) (atom : Atom) (live : List Atom) (scope : List String)
    (caller : Option Atom) (readiness : Entry.Status) (activation : Frame)
    (stack : List Continuation) (emitted : List Result) :
    (heWorldMachine keyedView keyedServices dispatch lookup policy ()).Step
      ⟨world, removeCall atom live scope caller readiness activation, stack, emitted⟩
      ⟨removeFirst world atom, .returning [(WorldRemoval.unitValue, activation)], stack, emitted⟩ :=
  .internal (WorldLocalStepWith.native
    ⟨rfl, Or.inr ⟨by simp [Entry.Value.erase], by rw [Entry.Value.erase_ofAtom]⟩⟩)

/-- **Reads stay honest on keyed rows**: every move of HE's world machine through its ordinary
rules depends on the keyed world only through the rows of its region, with their positions in the
presented space. -/
theorem world_core_transfer {w w₀ : KeyedWorld} {before after : Control Unit}
    {flatBefore flatAfter : Control} {stack remaining : List Continuation}
    (unscoped : UnscopedControl before flatBefore) (managed : managedContextControl before = false)
    (step : LocalStep (keyedView w ()) dispatch lookup policy (flatBefore, stack) (flatAfter, remaining))
    (unscoped' : UnscopedControl after flatAfter)
    (same : regionRows (heRegion policy flatBefore flatAfter) (w.map Prod.fst) =
      regionRows (heRegion policy flatBefore flatAfter) (w₀.map Prod.fst)) :
    WorldLocalStepWith .historical keyedView keyedServices dispatch lookup policy w₀ ()
      (before, stack) w₀ (after, remaining) :=
  .core unscoped managed (localStep_transfer step same) unscoped'

/-! ## Zar's race on HE's world machine -/

/-- **The race on keyed rows.** An add of a row with a fresh identity, against a complete query
over `region`: inside, it spoils the query, the query as it was is disabled after the add, and the
query asked again holds the new row too; outside, they are independent and the region is
unchanged. -/
theorem keyed_race {world : KeyedWorld} {atom : Atom} {id : ℕ} (fresh : id ∉ world.map Prod.snd)
    (region : Atom → Bool) :
    (region atom = true →
        Spoils Prod.fst (Commit.makeOne (atom, id))
            (queryCommit region (regionOf Prod.fst world.toFinset region)) ∧
          ¬ Enabled Prod.fst ((atom, id) :: world).toFinset
            (queryCommit region (regionOf Prod.fst world.toFinset region)) ∧
          Enabled Prod.fst ((atom, id) :: world).toFinset
            (queryCommit region (regionOf Prod.fst ((atom, id) :: world).toFinset region)) ∧
          regionOf Prod.fst ((atom, id) :: world).toFinset region =
            insert (atom, id) (regionOf Prod.fst world.toFinset region)) ∧
      (region atom = false →
        Independent Prod.fst (queryCommit region (regionOf Prod.fst world.toFinset region))
            (Commit.makeOne (atom, id) : Commit (Atom × ℕ) Atom) ∧
          regionOf Prod.fst ((atom, id) :: world).toFinset region =
            regionOf Prod.fst world.toFinset region) := by
  obtain ⟨written, notIn⟩ := add_writes_one (atom := atom) fresh
  refine ⟨fun inside => ?_, fun outside => ?_⟩
  · have race := add_into_region_race Prod.fst (region := region) notIn inside
    rw [written]
    exact ⟨race.1, race.2.2.2.2.1, race.2.2.2.2.2.1, race.2.2.2.2.2.2.1⟩
  · have commutes := add_outside_region_commutes Prod.fst (region := region) notIn outside
    rw [written]
    exact ⟨commutes.1, commutes.2.2.2.2⟩

/-- **Zar's race on HE's world machine.** HE's add of a row with a fresh identity is a step of HE's
world machine whose write is exactly that row; against an open complete query over `region` it
races exactly when the atom is inside the region (`keyed_race`). -/
theorem he_world_race {world : KeyedWorld} {atom : Atom} {id : ℕ} (fresh : id ∉ world.map Prod.snd)
    (region : Atom → Bool) (live : List Atom) (scope : List String) (caller : Option Atom)
    (readiness : Entry.Status) (activation : Frame) (stack : List Continuation)
    (emitted : List Result) :
    (heWorldMachine keyedView keyedServices dispatch lookup policy ()).Step
        ⟨world, addCall atom live scope caller readiness activation, stack, emitted⟩
        ⟨(atom, id) :: world, .returning [(WorldRemoval.unitValue, activation)], stack, emitted⟩ ∧
      ((atom, id) :: world).toFinset =
        fire world.toFinset (Commit.makeOne (atom, id) : Commit (Atom × ℕ) Atom) ∧
      (region atom = true →
        Spoils Prod.fst (Commit.makeOne (atom, id))
            (queryCommit region (regionOf Prod.fst world.toFinset region)) ∧
          ¬ Enabled Prod.fst ((atom, id) :: world).toFinset
            (queryCommit region (regionOf Prod.fst world.toFinset region))) ∧
      (region atom = false →
        Independent Prod.fst (queryCommit region (regionOf Prod.fst world.toFinset region))
            (Commit.makeOne (atom, id) : Commit (Atom × ℕ) Atom)) :=
  ⟨he_adds_row fresh live scope caller readiness activation stack emitted,
    (add_writes_one fresh).1,
    fun inside => ⟨((keyed_race fresh region).1 inside).1, ((keyed_race fresh region).1 inside).2.1⟩,
    fun outside => ((keyed_race fresh region).2 outside).1⟩

/-- **The race on the equation query of `(double 4)`.** On the keyed program
`{(p a) #0, (= (double 4) 8) #1}`: adding another copy of `(= (double 4) 8)` with identity `2` spoils
the query; adding `(p a)` with identity `2` commutes with it. -/
theorem double_race (live : List Atom) :
    Spoils Prod.fst (Commit.makeOne (Instance.doubleEight, 2) : Commit (Atom × ℕ) Atom)
        (queryCommit (eqRegion live Instance.doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty)
          (regionOf Prod.fst ([(RunsAsFirings.Controls.p RunsAsFirings.Controls.a, 0),
            (Instance.doubleEight, 1)] : KeyedWorld).toFinset
            (eqRegion live Instance.doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty))) ∧
      Independent Prod.fst
        (queryCommit (eqRegion live Instance.doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty)
          (regionOf Prod.fst ([(RunsAsFirings.Controls.p RunsAsFirings.Controls.a, 0),
            (Instance.doubleEight, 1)] : KeyedWorld).toFinset
            (eqRegion live Instance.doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty)))
        (Commit.makeOne (RunsAsFirings.Controls.p RunsAsFirings.Controls.a, 2) :
          Commit (Atom × ℕ) Atom) := by
  have fresh : (2 : ℕ) ∉ ([(RunsAsFirings.Controls.p RunsAsFirings.Controls.a, 0),
      (Instance.doubleEight, 1)] : KeyedWorld).map Prod.snd := by decide
  constructor
  · exact ((keyed_race (atom := Instance.doubleEight) fresh _).1 (Instance.he_inside live)).1
  · exact ((keyed_race (atom := RunsAsFirings.Controls.p RunsAsFirings.Controls.a) fresh _).2
      (Instance.he_pa_outside live _ _)).1

/-! ## The query on keyed rows: positions are inert -/

section Query

open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationRowResultsRel
  EquationWork)

/-- What a work says, without the position of its row. -/
def content (work : EquationWork) :
    Atom × Atom × Atom × Atom × Mettapedia.Languages.MeTTa.HE.Bindings :=
  (work.left, work.right, work.pattern, work.body, work.bindings)

/-- A row's block of works at one position is a block at any other position, with the same
contents: the position enters a work only as recorded data. -/
theorem rowResults_reposition {live : List Atom} {query : Atom}
    {incoming : Mettapedia.Languages.MeTTa.HE.Bindings} {position : ℕ} {row : Atom}
    {block : List EquationWork}
    (derived : EquationRowResultsRel live query incoming position row block) (position' : ℕ) :
    ∃ block', EquationRowResultsRel live query incoming position' row block' ∧
      block'.map content = block.map content :=
  match derived with
  | .irrelevant _ _ notEquation => ⟨[], .irrelevant position' _ notEquation, rfl⟩
  | .miss _ left right pattern body alpha noHit =>
      ⟨[], .miss position' left right pattern body alpha noHit, rfl⟩
  | .hit _ left right pattern body matched output alpha matching merged =>
      ⟨_, .hit position' left right pattern body matched output alpha matching merged, rfl⟩

theorem frontier_reposition {live : List Atom} {query : Atom}
    {incoming : Mettapedia.Languages.MeTTa.HE.Bindings} :
    ∀ (rows rows' : List (Atom × ℕ)), rows.map Prod.fst = rows'.map Prod.fst →
      ∀ works, FrontierOver live query incoming rows works →
        ∃ works', FrontierOver live query incoming rows' works' ∧
          works'.map content = works.map content
  | [], [], _, works, ⟨blocks, paired, flat⟩ => by
      cases paired
      subst flat
      exact ⟨[], ⟨[], .nil, rfl⟩, rfl⟩
  | [], _ :: _, same, _, _ => by simp at same
  | _ :: _, [], same, _, _ => by simp at same
  | (row, position) :: rows, (row', position') :: rows', same, works, ⟨blocks, paired, flat⟩ => by
      simp only [List.map_cons, List.cons.injEq] at same
      obtain ⟨rfl, sameRest⟩ := same
      obtain ⟨block, blocks', here, rest, rfl⟩ := List.forall₂_cons_left_iff.mp paired
      obtain ⟨block', here', sameBlock⟩ := rowResults_reposition
        (here : EquationRowResultsRel live query incoming position row block) position'
      obtain ⟨works'', ⟨blocks'', rest'', flat''⟩, sameWorks⟩ :=
        frontier_reposition rows rows' sameRest blocks'.flatten ⟨blocks', rest, rfl⟩
      refine ⟨block' ++ works'', ⟨block' :: blocks'', .cons here' rest'', by
        rw [List.flatten_cons, flat'']⟩, ?_⟩
      subst flat
      rw [List.flatten_cons, List.map_append, List.map_append, sameBlock, sameWorks]

/-- **An equation query's frontier is determined, up to the positions its works record, by the rows
of its region in order.** On keyed rows a write outside the region keeps those rows in order, even
when HE's add puts the new row in front and so moves every position. -/
theorem frontier_keyed_transfer {space space₀ : Space} {live : List Atom} {query : Atom}
    {incoming : Mettapedia.Languages.MeTTa.HE.Bindings} {works : List EquationWork}
    (same : space.atoms.filter (eqRegion live query incoming) =
      space₀.atoms.filter (eqRegion live query incoming))
    (frontier : EquationFrontierRel space live query incoming works) :
    ∃ works₀, EquationFrontierRel space₀ live query incoming works₀ ∧
      works₀.map content = works.map content := by
  rw [frontier_iff, frontierOver_filter_iff] at frontier
  have sameRows : (regionRows (eqRegion live query incoming) space.atoms).map Prod.fst =
      (regionRows (eqRegion live query incoming) space₀.atoms).map Prod.fst := by
    rw [ServiceFootprints.map_fst_regionRows, ServiceFootprints.map_fst_regionRows, same]
  obtain ⟨works₀, covered, contents⟩ := frontier_reposition _ _ sameRows works frontier
  refine ⟨works₀, ?_, contents⟩
  rw [frontier_iff, frontierOver_filter_iff]
  exact covered

/-- **No rule reads a work's position**: HE's move on pending equation works is the same move when the
first work records another position. -/
theorem equationsCons_position_free {admission : Completed.ArgumentService} {space : Space}
    {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy} {live : List Atom}
    {scope : List String} {original : Entry.Value} {expected : Atom} {activation : Frame}
    {work : EquationWork} {works : List EquationWork} {stack : List Continuation}
    {c' : Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Control}
    {s' : List Continuation}
    (step : Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.LocalStepWith admission space
      dispatch lookup policy
      (.work (.equations live scope original expected activation (work :: works)), stack) (c', s'))
    (position : ℕ) :
    Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.LocalStepWith admission space dispatch
      lookup policy
      (.work (.equations live scope original expected activation
        ({ work with position := position } :: works)), stack) (c', s') := by
  cases step
  exact .equationsCons ‹_› ‹_›

/-- The same for an invocation's equation works. -/
theorem invocationEquationsCons_position_free {admission : Completed.ArgumentService}
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}
    {live : List Atom} {scope : List String} {original : Entry.Value} {activation : Frame}
    {work : EquationWork} {works : List EquationWork} {stack : List Continuation}
    {c' : Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Control}
    {s' : List Continuation}
    (step : Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.LocalStepWith admission space
      dispatch lookup policy
      (.work (.invocationEquations live scope original activation (work :: works)), stack) (c', s'))
    (position : ℕ) :
    Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.LocalStepWith admission space dispatch
      lookup policy
      (.work (.invocationEquations live scope original activation
        ({ work with position := position } :: works)), stack) (c', s') := by
  cases step
  exact .invocationEquationsCons ‹_› ‹_›

end Query

/-! ## Controls -/

namespace Controls

open RunsAsFirings.Controls (p a)

/-- `(q b)`. -/
def qb : Atom := .expression [.symbol "q", .symbol "b"]

/-- The honest write of a world change under positional labels: it takes the positioned rows that
disappear and makes those that appear. -/
def positionalWrite (before after : List Atom) : Commit (Atom × ℕ) (Atom × ℕ) :=
  ⟨before.zipIdx.toFinset \ after.zipIdx.toFinset, ∅, after.zipIdx.toFinset \ before.zipIdx.toFinset,
    []⟩

/-- **Negative control: positions are not identities.** HE's add of `(q b)` puts it in front, so
`(= (double 4) 8)` moves from position `1` to `2`; the positional write of the add takes the row at
position `1`, writing into the region of the query `(double 4)` and spoiling it, though `(q b)` is
outside that region. With identities the same add is independent of the query. -/
theorem positions_renumber (live : List Atom) :
    ((Space.ofList Instance.program).add qb).atoms.zipIdx =
        [(qb, 0), (p a, 1), (Instance.doubleEight, 2)] ∧
      (Instance.doubleEight, 1) ∈ (positionalWrite Instance.program
        ((Space.ofList Instance.program).add qb).atoms).taken ∧
      Spoils id (positionalWrite Instance.program ((Space.ofList Instance.program).add qb).atoms)
        (queryCommit
          (fun row : Atom × ℕ =>
            eqRegion live Instance.doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty row.1)
          (regionOf id Instance.program.zipIdx.toFinset (fun row : Atom × ℕ =>
            eqRegion live Instance.doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty row.1))) ∧
      eqRegion live Instance.doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty qb = false ∧
      Independent Prod.fst
        (queryCommit (eqRegion live Instance.doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty)
          (regionOf Prod.fst ([(p a, 0), (Instance.doubleEight, 1)] : KeyedWorld).toFinset
            (eqRegion live Instance.doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty)))
        (Commit.makeOne (qb, 2) : Commit (Atom × ℕ) Atom) := by
  have taken : (Instance.doubleEight, 1) ∈ (positionalWrite Instance.program
      ((Space.ofList Instance.program).add qb).atoms).taken := by
    decide +kernel
  have qbOutside : eqRegion live Instance.doubleFour Mettapedia.Languages.MeTTa.HE.Bindings.empty qb =
      false := eqRegion_not_equation fun _ _ same => by simp [qb] at same
  have fresh : (2 : ℕ) ∉ ([(p a, 0), (Instance.doubleEight, 1)] : KeyedWorld).map Prod.snd := by
    decide
  refine ⟨by decide +kernel, taken, ?_, qbOutside, ?_⟩
  · exact Or.inr ⟨_, List.mem_singleton_self _, _, Finset.mem_union_left _ taken,
      Instance.he_inside live⟩
  · exact ((keyed_race (atom := qb) fresh _).2 qbOutside).1

/-- **Separating write control: one occurrence against every copy.** On `(p a)` stored twice, HE's
world machine on keyed rows removes the first row only: the presented space is HE's `Space.remove`,
and the write is the commit taking exactly one row. PeTTa's removal request takes both rows. -/
theorem removal_separates :
    removeFirst [(WorldRemoval.pa, 0), (WorldRemoval.pa, 1)] WorldRemoval.pa = [(WorldRemoval.pa, 1)] ∧
      keyedView [(WorldRemoval.pa, 1)] () =
        (keyedView [(WorldRemoval.pa, 0), (WorldRemoval.pa, 1)] ()).remove WorldRemoval.pa ∧
      ([(WorldRemoval.pa, 1)] : KeyedWorld).toFinset =
        fire ([(WorldRemoval.pa, 0), (WorldRemoval.pa, 1)] : KeyedWorld).toFinset
          (Commit.takeOne (WorldRemoval.pa, 0) : Commit (Atom × ℕ) Atom) ∧
      (Commit.takeOne (WorldRemoval.pa, 0) : Commit (Atom × ℕ) Atom).taken.card = 1 ∧
      (RunsAsFirings.requests RunsAsFirings.rowSupply HEOnTheStep.NamedDifferences.noProgram 30
          (Mettapedia.Languages.MeTTa.PeTTa.Streaming.enter
            { state := HEOnTheStep.NamedDifferences.dupStore } HEOnTheStep.NamedDifferences.removePa)
          (RunsAsFirings.Row.load 0 HEOnTheStep.NamedDifferences.dupAtoms)).map
          RunsAsFirings.Controls.shape =
        [([⟨0, .self, WorldRemoval.pa⟩, ⟨1, .self, WorldRemoval.pa⟩], [], [])] := by
  exact ⟨removeFirst_head _ _ _, congrArg Space.mk (by decide +kernel), by decide +kernel,
    Finset.card_singleton _, HEOnTheStep.NamedDifferences.removal.2.1⟩

end Controls

#print axioms map_removeFirst
#print axioms keyed_refines
#print axioms add_writes_one
#print axioms remove_takes_one
#print axioms he_adds_row
#print axioms he_removes_row
#print axioms world_core_transfer
#print axioms he_world_race
#print axioms double_race
#print axioms frontier_reposition
#print axioms frontier_keyed_transfer
#print axioms equationsCons_position_free
#print axioms invocationEquationsCons_position_free
#print axioms Controls.positions_renumber
#print axioms Controls.removal_separates

end HonestWrites

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
