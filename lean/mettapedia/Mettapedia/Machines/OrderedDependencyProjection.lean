import Mettapedia.Machines.OrderedDependencyStore

/-!
# Projection-specific dependency certificates

Each projection selects an ordered observation from a member's own contents.
Content publication compares the old and new projected segments and notifies
the owner and its reverse-indexed readers. Topology publication invalidates all
projections of the changed view, but not older flattened importers.

Full-query, equation and declaration clocks therefore have distinct meanings.
The executable checker is proved sound along the actual update algorithm,
including adaptive read-only programs and empty projected observations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyProjection

open OrderedDependencyStore

universe u v w x

structure State (Entry : Type u) (Projection : Type v) (size : Nat) where
  store : Store Entry size
  clocks : Projection → Fin size → Nat

variable {Entry : Type u} {Projection : Type v} {Value : Type w} {Answer : Type x}
  {size : Nat}

def initial (identity : Nat) (own : Fin size → List Entry) : State Entry Projection size :=
  ⟨OrderedDependencyStore.initial identity own, fun _ _ => 0⟩

/-- Independent declarative composition of projected own segments. -/
def view (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (reader : Fin size) (slot : Projection) : List Value :=
  (s.store.members reader).own.filterMap (project slot) ++
    (s.store.members reader).deps.flatMap fun source =>
      (s.store.members source).own.filterMap (project slot)

/-- The implementation collects source contents, then applies the projection. -/
def query (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (reader : Fin size) (slot : Projection) : List Value :=
  (OrderedDependencyStore.query s.store reader).filterMap (project slot)

theorem query_eq_view (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (reader : Fin size) (slot : Projection) :
    query project s reader slot = view project s reader slot := by
  simp [query, OrderedDependencyStore.query_eq_view, OrderedDependencyStore.view,
    view, List.filterMap_flatMap]

def update [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (writer : Fin size)
    (contents : List Entry) (rewrites : Bool) : State Entry Projection size :=
  { store := contentUpdate s.store writer contents rewrites
    clocks := fun slot reader =>
      if (reader = writer ∨ reader ∈ s.store.observers writer) ∧
          contents.filterMap (project slot) ≠
            (s.store.members writer).own.filterMap (project slot)
      then s.clocks slot reader + 1 else s.clocks slot reader }

theorem update_observers [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (h : ObserverInvariant s.store)
    (writer : Fin size) (contents : List Entry) (rewrites : Bool) :
    ObserverInvariant (update project s writer contents rewrites).store :=
  contentUpdate_observers s.store h writer contents rewrites

theorem update_clock_mono [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (writer reader : Fin size)
    (contents : List Entry) (rewrites : Bool) (slot : Projection) :
    s.clocks slot reader ≤ (update project s writer contents rewrites).clocks slot reader := by
  simp only [update]
  split <;> omega

theorem update_view_of_segment_eq [DecidableEq Value]
    (project : Projection → Entry → Option Value) (s : State Entry Projection size)
    (writer reader : Fin size) (contents : List Entry) (rewrites : Bool) (slot : Projection)
    (same : contents.filterMap (project slot) =
      (s.store.members writer).own.filterMap (project slot)) :
    view project (update project s writer contents rewrites) reader slot =
      view project s reader slot := by
  simp only [view, update, contentUpdate]
  congr 1
  · by_cases equal : reader = writer <;> simp [equal, same]
  · apply List.flatMap_congr
    intro member included
    by_cases equal : member = writer <;> simp [equal, same]

theorem update_view_of_clock_eq [DecidableEq Value]
    (project : Projection → Entry → Option Value) (s : State Entry Projection size)
    (h : ObserverInvariant s.store) (writer reader : Fin size)
    (contents : List Entry) (rewrites : Bool) (slot : Projection)
    (same : (update project s writer contents rewrites).clocks slot reader =
      s.clocks slot reader) :
    view project (update project s writer contents rewrites) reader slot =
      view project s reader slot := by
  by_cases segment : contents.filterMap (project slot) =
      (s.store.members writer).own.filterMap (project slot)
  · exact update_view_of_segment_eq project s writer reader contents rewrites slot segment
  · have different : reader ≠ writer := by
      intro equality
      simp [update, equality, segment] at same
    have unread : writer ∉ (s.store.members reader).deps := by
      intro included
      have observer := (h writer reader).mpr included
      simp [update, observer, segment] at same
    rw [← query_eq_view, ← query_eq_view]
    simp only [query, update, OrderedDependencyStore.query_eq_view,
      contentUpdate_unrelated s.store different unread contents rewrites]

def setDeps (s : State Entry Projection size) (reader : Fin size)
    (deps : List (Fin size)) : State Entry Projection size :=
  if deps = (s.store.members reader).deps then s else
  { store := setDependencies s.store reader deps
    clocks := fun slot observer =>
      if observer = reader then s.clocks slot observer + 1 else s.clocks slot observer }

theorem setDeps_observers (s : State Entry Projection size) (h : ObserverInvariant s.store)
    (reader : Fin size) (deps : List (Fin size)) : ObserverInvariant (setDeps s reader deps).store := by
  unfold setDeps
  split
  · exact h
  · exact setDependencies_observers s.store h reader deps

theorem setDeps_clock_mono (s : State Entry Projection size)
    (changed reader : Fin size) (deps : List (Fin size)) (slot : Projection) :
    s.clocks slot reader ≤ (setDeps s changed deps).clocks slot reader := by
  unfold setDeps
  split
  · exact Nat.le_refl _
  · dsimp
    split <;> omega

theorem setDeps_view_of_clock_eq (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (changed reader : Fin size)
    (deps : List (Fin size)) (slot : Projection)
    (same : (setDeps s changed deps).clocks slot reader = s.clocks slot reader) :
    view project (setDeps s changed deps) reader slot = view project s reader slot := by
  by_cases unchanged : deps = (s.store.members changed).deps
  · simp [setDeps, unchanged]
  · have different : reader ≠ changed := by
      intro equality
      subst reader
      simp [setDeps, unchanged] at same
    rw [← query_eq_view, ← query_eq_view]
    simp only [query, setDeps, unchanged, ↓reduceIte,
      OrderedDependencyStore.query_eq_view,
      setDependencies_unrelated s.store different deps]

def endLifetime (s : State Entry Projection size) (source : Fin size) :
    State Entry Projection size :=
  { store := OrderedDependencyStore.retire s.store source
    clocks := fun slot reader => if reader = source ∨ reader ∈ s.store.observers source
      then s.clocks slot reader + 1 else s.clocks slot reader }

theorem endLifetime_clock_mono (s : State Entry Projection size)
    (source reader : Fin size) (slot : Projection) :
    s.clocks slot reader ≤ (endLifetime s source).clocks slot reader := by
  simp only [endLifetime]
  split <;> omega

theorem endLifetime_view_of_clock_eq (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (h : ObserverInvariant s.store)
    (source reader : Fin size) (slot : Projection)
    (same : (endLifetime s source).clocks slot reader = s.clocks slot reader) :
    view project (endLifetime s source) reader slot = view project s reader slot := by
  have different : reader ≠ source := by
    intro equality
    simp [endLifetime, equality] at same
  have unread : source ∉ (s.store.members reader).deps := by
    intro included
    have observer := (h source reader).mpr included
    simp [endLifetime, observer] at same
  rw [← query_eq_view, ← query_eq_view]
  simp only [query, endLifetime, OrderedDependencyStore.query_eq_view,
    OrderedDependencyStore.retire_unrelated s.store different unread]

def step [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) : Action Entry size → State Entry Projection size
  | .append writer suffix => update project s writer ((s.store.members writer).own ++ suffix) false
  | .replace writer contents => update project s writer contents true
  | .link reader source => if source ∈ (s.store.members reader).deps then s else
      setDeps s reader ((s.store.members reader).deps ++ [source])
  | .unlink reader source => setDeps s reader
      ((s.store.members reader).deps.filter fun member => member ≠ source)
  | .retire source => endLifetime s source
  | .importModule reader source => setDeps s reader (moduleDependencies s.store reader source)

theorem setDeps_store (s : State Entry Projection size) (reader : Fin size)
    (deps : List (Fin size)) : (setDeps s reader deps).store =
      setDependencies s.store reader deps := by
  unfold setDeps
  split
  · rename_i unchanged
    simp [setDependencies, unchanged]
  · rfl

/-- Projection notification augments the real store transition; it does not
substitute a separate storage or dependency algorithm. -/
theorem step_store [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (action : Action Entry size) :
    (step project s action).store = OrderedDependencyStore.step s.store action := by
  cases action with
  | append writer suffix => rfl
  | replace writer contents => rfl
  | link reader source =>
      simp only [step, OrderedDependencyStore.step, link]
      split
      · rfl
      · exact setDeps_store s reader _
  | unlink reader source => exact setDeps_store s reader _
  | retire source => rfl
  | importModule reader source => exact setDeps_store s reader _

theorem step_observers [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (h : ObserverInvariant s.store) (action : Action Entry size) :
    ObserverInvariant (step project s action).store := by
  cases action with
  | append writer suffix => exact update_observers project s h writer _ false
  | replace writer contents => exact update_observers project s h writer contents true
  | link reader source =>
      simp only [step]
      split
      · exact h
      · exact setDeps_observers s h reader _
  | unlink reader source => exact setDeps_observers s h reader _
  | retire source => exact OrderedDependencyStore.retire_observers s.store h source
  | importModule reader source => exact setDeps_observers s h reader _

theorem step_clock_mono [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (action : Action Entry size)
    (reader : Fin size) (slot : Projection) :
    s.clocks slot reader ≤ (step project s action).clocks slot reader := by
  cases action with
  | append writer suffix => exact update_clock_mono project s writer reader _ false slot
  | replace writer contents => exact update_clock_mono project s writer reader contents true slot
  | link changed source =>
      simp only [step]
      split
      · exact Nat.le_refl _
      · exact setDeps_clock_mono s changed reader _ slot
  | unlink changed source => exact setDeps_clock_mono s changed reader _ slot
  | retire source => exact endLifetime_clock_mono s source reader slot
  | importModule changed source => exact setDeps_clock_mono s changed reader _ slot

theorem step_view_of_clock_eq [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (h : ObserverInvariant s.store) (action : Action Entry size)
    (reader : Fin size) (slot : Projection)
    (same : (step project s action).clocks slot reader = s.clocks slot reader) :
    view project (step project s action) reader slot = view project s reader slot := by
  cases action with
  | append writer suffix => exact update_view_of_clock_eq project s h writer reader _ false slot same
  | replace writer contents => exact update_view_of_clock_eq project s h writer reader contents true slot same
  | link changed source =>
      simp only [step] at same ⊢
      split at same
      · simp_all
      · rename_i absent
        simp only [absent, ↓reduceIte]
        exact setDeps_view_of_clock_eq project s changed reader _ slot same
  | unlink changed source => exact setDeps_view_of_clock_eq project s changed reader _ slot same
  | retire source => exact endLifetime_view_of_clock_eq project s h source reader slot same
  | importModule changed source => exact setDeps_view_of_clock_eq project s changed reader _ slot same

def execute [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) : List (Action Entry size) → State Entry Projection size
  | [] => s
  | action :: rest => execute project (step project s action) rest

theorem execute_store [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (actions : List (Action Entry size)) :
    (execute project s actions).store = OrderedDependencyStore.execute s.store actions := by
  induction actions generalizing s with
  | nil => rfl
  | cons action rest ih =>
      simp only [execute, OrderedDependencyStore.execute, ih, step_store]

theorem execute_observers [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (h : ObserverInvariant s.store)
    (actions : List (Action Entry size)) : ObserverInvariant (execute project s actions).store := by
  induction actions generalizing s with
  | nil => exact h
  | cons action rest ih => exact ih (step project s action) (step_observers project s h action)

theorem execute_clock_mono [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (actions : List (Action Entry size))
    (reader : Fin size) (slot : Projection) :
    s.clocks slot reader ≤ (execute project s actions).clocks slot reader := by
  induction actions generalizing s with
  | nil => exact Nat.le_refl _
  | cons action rest ih => exact (step_clock_mono project s action reader slot).trans (ih _)

theorem execute_view_of_clock_eq [DecidableEq Value]
    (project : Projection → Entry → Option Value) (s : State Entry Projection size)
    (h : ObserverInvariant s.store) (actions : List (Action Entry size))
    (reader : Fin size) (slot : Projection)
    (same : (execute project s actions).clocks slot reader = s.clocks slot reader) :
    view project (execute project s actions) reader slot = view project s reader slot := by
  induction actions generalizing s with
  | nil => rfl
  | cons action rest ih =>
      have first := step_clock_mono project s action reader slot
      have later := execute_clock_mono project (step project s action) rest reader slot
      have unchanged : (step project s action).clocks slot reader = s.clocks slot reader := by
        simp only [execute] at same
        omega
      have tail : (execute project (step project s action) rest).clocks slot reader =
          (step project s action).clocks slot reader := by
        simpa [execute, unchanged] using same
      exact (ih (step project s action) (step_observers project s h action) tail).trans
        (step_view_of_clock_eq project s h action reader slot unchanged)

structure Stamp (Projection : Type v) (size : Nat) where
  identity : Nat
  reader : Fin size
  generation : Nat
  slot : Projection
  clock : Nat
  deriving DecidableEq

def stamp (s : State Entry Projection size) (reader : Fin size) (slot : Projection) :
    Stamp Projection size :=
  ⟨s.store.identity, reader, (s.store.members reader).generation, slot, s.clocks slot reader⟩

def checkStamp [DecidableEq Projection] (s : State Entry Projection size)
    (certificate : Stamp Projection size) : Bool :=
  decide (certificate = stamp s certificate.reader certificate.slot)

theorem validated_query [DecidableEq Value] [DecidableEq Projection]
    (project : Projection → Entry → Option Value) (s : State Entry Projection size)
    (h : ObserverInvariant s.store) (actions : List (Action Entry size))
    (reader : Fin size) (slot : Projection)
    (valid : checkStamp (execute project s actions) (stamp s reader slot) = true) :
    query project (execute project s actions) reader slot = query project s reader slot := by
  have same := of_decide_eq_true valid
  have clock := congrArg Stamp.clock same
  simp only [stamp] at clock
  rw [query_eq_view, query_eq_view]
  exact execute_view_of_clock_eq project s h actions reader slot clock.symm

/-- Actual adaptive reads determine the stamps, preserving repeated and empty
observations. Unread projections do not have to be certified. -/
def programStamps (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (reader : Fin size)
    (program : ReadOnlyQuery.Program Projection (List Value) Answer) : List (Stamp Projection size) :=
  (ReadOnlyQuery.run (query project s reader) program).reads.map fun read => stamp s reader read.1

theorem validated_program [DecidableEq Value] [DecidableEq Projection]
    (project : Projection → Entry → Option Value) (s : State Entry Projection size)
    (h : ObserverInvariant s.store) (actions : List (Action Entry size)) (reader : Fin size)
    (program : ReadOnlyQuery.Program Projection (List Value) Answer)
    (valid : (programStamps project s reader program).all
      (checkStamp (execute project s actions)) = true) :
    ReadOnlyQuery.run (query project (execute project s actions) reader) program =
      ReadOnlyQuery.run (query project s reader) program := by
  apply ReadOnlyQuery.run_eq_of_agrees
  intro read included
  have checked : checkStamp (execute project s actions) (stamp s reader read.1) = true :=
    (List.all_eq_true.mp valid) _ (List.mem_map.mpr ⟨read, included, rfl⟩)
  rw [validated_query project s h actions reader read.1 checked]
  exact ReadOnlyQuery.run_agrees (query project s reader) program read included

namespace Controls

inductive Slot where
  | equation
  | declaration
  deriving DecidableEq

inductive Record where
  | data (value : Nat)
  | equation (value : Nat)
  | declaration (value : Nat)
  deriving DecidableEq

def project : Slot → Record → Option Nat
  | .equation, .equation value => some value
  | .declaration, .declaration value => some value
  | _, _ => none

def base : State Record Slot 3 :=
  step project (initial 901 fun source =>
    if source = 0 then [.data 42] else if source = 2 then [.equation 7, .equation 7] else [])
    (.link 0 2)

def withData : State Record Slot 3 := step project base (.append 2 [.data 8])

theorem data_change_preserves_equation_stamp :
    checkStamp withData (stamp base 0 .equation) = true ∧
    query project withData 0 .equation = [7, 7] ∧
    OrderedDependencyStore.checkRead withData.store
      (OrderedDependencyStore.readStamp base.store 0) = false := by
  decide

def withDeclaration : State Record Slot 3 := step project base (.append 2 [.declaration 9])

theorem equation_stamp_cannot_certify_declarations :
    checkStamp withDeclaration (stamp base 0 .equation) = true ∧
    checkStamp withDeclaration (stamp base 0 .declaration) = false ∧
    query project base 0 .declaration = [] ∧
    query project withDeclaration 0 .declaration = [9] := by
  decide

def missingDeclarationNotification : State Record Slot 3 :=
  { withDeclaration with clocks := base.clocks }

theorem omitted_declaration_clock_accepts_changed_result :
    checkStamp missingDeclarationNotification (stamp base 0 .declaration) = true ∧
    query project missingDeclarationNotification 0 .declaration ≠
      query project base 0 .declaration := by
  decide

theorem empty_equation_query_is_certified :
    query project base 1 .equation = [] ∧
    checkStamp (step project base (.append 1 [.equation 11])) (stamp base 1 .equation) = false ∧
    query project (step project base (.append 1 [.equation 11])) 1 .equation = [11] := by
  decide

theorem topology_change_expires_projection :
    query project (step project base (.unlink 0 2)) 0 .equation = [] ∧
    checkStamp (step project base (.unlink 0 2)) (stamp base 0 .equation) = false := by
  decide

def typedProgram : ReadOnlyQuery.Program Slot (List Nat) (List Nat × List Nat) :=
  .read .equation fun equations => .read .declaration fun declarations =>
    .pure (equations, declarations)

theorem typed_program_rejects_declaration_change :
    (programStamps project base 0 typedProgram).all (checkStamp withDeclaration) = false ∧
    (ReadOnlyQuery.run (query project base 0) typedProgram).answer = ([7, 7], []) ∧
    (ReadOnlyQuery.run (query project withDeclaration 0) typedProgram).answer = ([7, 7], [9]) := by
  decide

theorem retirement_expires_importer_program :
    (programStamps project base 0 typedProgram).all
      (checkStamp (step project base (.retire 2))) = false ∧
    (ReadOnlyQuery.run (query project (step project base (.retire 2)) 0)
      typedProgram).answer = ([], []) := by
  decide

end Controls

end Mettapedia.Machines.OrderedDependencyProjection
