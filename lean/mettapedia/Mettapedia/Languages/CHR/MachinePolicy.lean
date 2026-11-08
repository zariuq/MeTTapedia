import Mettapedia.Languages.CHR.MachineSearchPhase
import Mettapedia.Languages.CHR.MachineStore
import Mettapedia.Languages.CHR.MachineTick
import Mettapedia.Languages.CHR.MachineSkip
import Mettapedia.Languages.CHR.PartnerSelection

/-! The machine tries partners newest first. When every slot of the store
lists its occurrences newest first, the complete selections a search
enumerates come in strictly decreasing newest-first preference of their head
identifiers. The machine decides on the first of them that is fresh and whose
guards hold, so every selection it passes over without deciding is either
stale or rejected by its guards, and none it passes over is preferred to its
decision. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

open PartnerSelection (newerIds newerIds_irrefl)

/-- Every slot lists its occurrences newest first. -/
def Descending (store : Store) : Prop :=
  ∀ entry ∈ store, entry.2.Pairwise fun newer older => older.id < newer.id

theorem slot_descending {store : Store} (descending : Descending store) (key : Key) :
    (slot key store).Pairwise fun newer older => older.id < newer.id := by
  induction store with
  | nil => exact List.Pairwise.nil
  | cons entry rest ih =>
    rcases entry with ⟨other, occurrences⟩
    unfold slot
    split
    · exact descending (other, occurrences) List.mem_cons_self
    · exact ih fun entry inside => descending entry (List.mem_cons_of_mem _ inside)

theorem candidates_descending {store : Store} (descending : Descending store) (index position active : Nat)
    (values : List Value) (head : Head) :
    (candidates index position active values head store).Pairwise fun newer older => older.id < newer.id := by
  unfold candidates
  split
  · exact List.pairwise_singleton _ _
  · exact slot_descending descending _

theorem newerIds_append (common first second : List Nat) :
    newerIds (common ++ first) (common ++ second) = newerIds first second := by
  induction common with
  | nil => rfl
  | cons head rest ih => simp [newerIds, ih]

theorem newerIds_lt (newer older : Nat) (first second : List Nat) (smaller : older < newer) :
    newerIds (newer :: first) (older :: second) = true := by
  have different : (newer == older) = false := by simp; omega
  simp [newerIds, different, smaller]

section Enumeration

variable (store : Store) (position active : Nat) (values : List Value)

/-- Every selection a search reaches from `picks` extends it by one pick per
remaining head. -/
theorem selections_extend : ∀ (index : Nat) (heads : List Head) (environment : Environment) (picks : List Pick)
    (used : List Nat), ∀ reached ∈ selections store position active values index heads environment picks used,
      ∃ more, reached.2 = picks ++ more ∧ more.length = heads.length
  | _, [], environment, picks, _, reached, inside => by
    simp [selections] at inside
    subst inside
    exact ⟨[], by simp, rfl⟩
  | index, head :: later, environment, picks, used, reached, inside => by
    rw [selections_cons, List.mem_flatMap] at inside
    obtain ⟨candidate, _, contributed⟩ := inside
    unfold contribution at contributed
    split at contributed
    · simp at contributed
    · split at contributed
      · simp at contributed
      · rename_i bound _
        obtain ⟨more, extended, counted⟩ := selections_extend (index + 1) later bound
          (picks ++ [⟨Head.key head, candidate.id⟩]) (candidate.id :: used) reached contributed
        exact ⟨⟨Head.key head, candidate.id⟩ :: more, by simp [extended], by simp [counted]⟩

/-- **The search enumerates newest first.** -/
theorem selections_sorted (descending : Descending store) : ∀ (index : Nat) (heads : List Head)
    (environment : Environment) (picks : List Pick) (used : List Nat),
    (selections store position active values index heads environment picks used).Pairwise
      fun first second => newerIds (ids first.2) (ids second.2) = true
  | _, [], environment, picks, _ => by simp [selections]
  | index, head :: later, environment, picks, used => by
    rw [selections_cons, List.pairwise_flatMap]
    refine ⟨fun candidate _ => ?_, ?_⟩
    · unfold contribution
      split
      · exact List.Pairwise.nil
      · split
        · exact List.Pairwise.nil
        · exact selections_sorted descending (index + 1) later _ _ _
    · refine List.Pairwise.imp_of_mem ?_ (candidates_descending descending index position active values head)
      intro newer older _ _ older_lt first firstInside second secondInside
      unfold contribution at firstInside secondInside
      split at firstInside
      · simp at firstInside
      split at firstInside
      · simp at firstInside
      split at secondInside
      · simp at secondInside
      split at secondInside
      · simp at secondInside
      rename_i firstBound _ _ secondBound _
      obtain ⟨firstMore, firstExtended, _⟩ := selections_extend store position active values (index + 1) later _ _ _
        first firstInside
      obtain ⟨secondMore, secondExtended, _⟩ := selections_extend store position active values (index + 1) later _ _ _
        second secondInside
      rw [firstExtended, secondExtended]
      simp only [ids, List.map_append, List.map_cons, List.append_assoc, List.singleton_append]
      rw [newerIds_append]
      exact newerIds_lt _ _ _ _ older_lt

end Enumeration

#print axioms selections_sorted

/-! ## The decision passes over only rejected selections -/

theorem newerIds_asymm : ∀ (first second : List Nat), newerIds first second = true → newerIds second first = false
  | [], [], forward => by simp [newerIds] at forward
  | [], _ :: _, _ => by simp [newerIds]
  | _ :: _, [], forward => by simp [newerIds] at forward
  | newer :: more, older :: rest, forward => by
    by_cases same : newer = older
    · subst same
      simp only [newerIds, beq_self_eq_true, if_true] at forward ⊢
      exact newerIds_asymm more rest forward
    · have one : (newer == older) = false := beq_eq_false_iff_ne.mpr same
      have two : (older == newer) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
      simp only [newerIds, one, two, Bool.false_eq_true, if_false, decide_eq_true_eq, decide_eq_false_iff_not]
        at forward ⊢
      omega

/-- A selection the decision passes over: stale, or rejected by its guards. -/
def Rejected (occurrence : At) (history : List CHR.Key) (selection : Environment × List Pick) : Prop :=
  (occurrence.body.propagation ∧ (⟨occurrence.rule, ids selection.2⟩ : CHR.Key) ∈ history) ∨
    guardsEval selection.1 occurrence.body.guards = .ok false

/-- **The machine fires the preferred usable selection.** Every selection
preferred to the one the decision fires is rejected. -/
theorem judge_preferred (occurrence : At) (history : List CHR.Key) :
    ∀ (listed : List (Environment × List Pick)) (chosen : Environment × List Pick),
      listed.Pairwise (fun first second => newerIds (ids first.2) (ids second.2) = true) →
      judge occurrence history listed = .ok (some chosen) →
      ∀ other ∈ listed, newerIds (ids other.2) (ids chosen.2) = true → Rejected occurrence history other
  | [], _, _, decided => by simp [judge] at decided
  | (environment, picks) :: rest, chosen, sorted, decided => by
    rw [List.pairwise_cons] at sorted
    intro other inside preferred
    unfold judge at decided
    split at decided
    · rename_i stale
      rcases List.mem_cons.mp inside with same | later
      · subst same
        exact .inl stale
      · exact judge_preferred occurrence history rest chosen sorted.2 decided other later preferred
    · split at decided
      · cases decided
      · rename_i holds
        simp only [Except.ok.injEq, Option.some.injEq] at decided
        subst decided
        rcases List.mem_cons.mp inside with same | later
        · subst same
          simp [newerIds_irrefl] at preferred
        · have earlier := sorted.1 other later
          simp [newerIds_asymm _ _ earlier] at preferred
      · rename_i rejected
        rcases List.mem_cons.mp inside with same | later
        · subst same
          exact .inr rejected
        · exact judge_preferred occurrence history rest chosen sorted.2 decided other later preferred

/-- **A faulting guard is the preferred one not passed over.** Every
selection preferred to the one whose guards fault is rejected. -/
theorem judge_fault_preferred (occurrence : At) (history : List CHR.Key) (reason : ArithmeticFault) :
    ∀ listed : List (Environment × List Pick),
      listed.Pairwise (fun first second => newerIds (ids first.2) (ids second.2) = true) →
      judge occurrence history listed = .error reason →
      ∃ faulting ∈ listed, ¬ (occurrence.body.propagation ∧ (⟨occurrence.rule, ids faulting.2⟩ : CHR.Key) ∈ history) ∧
        guardsEval faulting.1 occurrence.body.guards = .error reason ∧
        ∀ other ∈ listed, newerIds (ids other.2) (ids faulting.2) = true → Rejected occurrence history other
  | [], _, decided => by simp [judge] at decided
  | (environment, picks) :: rest, sorted, decided => by
    rw [List.pairwise_cons] at sorted
    unfold judge at decided
    split at decided
    · rename_i stale
      obtain ⟨faulting, inside, fresh, faults, preferred⟩ :=
        judge_fault_preferred occurrence history reason rest sorted.2 decided
      refine ⟨faulting, List.mem_cons_of_mem _ inside, fresh, faults, fun other member better => ?_⟩
      rcases List.mem_cons.mp member with same | later
      · subst same
        exact .inl stale
      · exact preferred other later better
    · rename_i fresh
      split at decided
      · rename_i actual faults
        simp only [Except.error.injEq] at decided
        subst decided
        refine ⟨(environment, picks), List.mem_cons_self, fresh, faults, fun other member better => ?_⟩
        rcases List.mem_cons.mp member with same | later
        · subst same
          simp [newerIds_irrefl] at better
        · have earlier := sorted.1 other later
          simp [newerIds_asymm _ _ earlier] at better
      · cases decided
      · rename_i rejected
        obtain ⟨faulting, inside, freshFaulting, faults, preferred⟩ :=
          judge_fault_preferred occurrence history reason rest sorted.2 decided
        refine ⟨faulting, List.mem_cons_of_mem _ inside, freshFaulting, faults, fun other member better => ?_⟩
        rcases List.mem_cons.mp member with same | later
        · subst same
          exact .inr rejected
        · exact preferred other later better

#print axioms judge_preferred
#print axioms judge_fault_preferred

/-! ## Ticks keep every slot newest first -/

theorem put_descending {store : Store} (descending : Descending store) (key : Key) {occurrences : List Occ}
    (sorted : occurrences.Pairwise fun newer older => older.id < newer.id) :
    Descending (put key occurrences store) := by
  induction store with
  | nil =>
    intro entry inside
    simp only [put, List.mem_cons, List.not_mem_nil, or_false] at inside
    subst inside
    exact sorted
  | cons first rest ih =>
    rcases first with ⟨other, old⟩
    unfold put
    split
    · intro entry inside
      rcases List.mem_cons.mp inside with same | later
      · subst same
        exact sorted
      · exact descending entry (List.mem_cons_of_mem _ later)
    · intro entry inside
      rcases List.mem_cons.mp inside with same | later
      · subst same
        exact descending _ List.mem_cons_self
      · exact ih (fun entry inside => descending entry (List.mem_cons_of_mem _ inside)) entry later

theorem removePicks_descending : ∀ (picks : List Pick) (store : Store), Descending store →
    Descending (removePicks picks store)
  | [], _, descending => descending
  | pick :: rest, _, descending => removePicks_descending rest _
      (put_descending descending pick.key ((slot_descending descending pick.key).sublist (without_sublist _ _)))

theorem introduce_store_shape (table : Table) (head : Head) (environment : Environment) (resume : Task)
    (original tail : List Task) (state : State) (seeds : List Nat) :
    (introduce table head environment resume original tail state seeds).store = state.store ∨
      ∃ values, (introduce table head environment resume original tail state seeds).store =
        put (Head.key head) (⟨state.next, values⟩ :: slot (Head.key head) state.store) state.store := by
  unfold introduce
  split
  · exact .inl rfl
  · exact .inr ⟨_, rfl⟩

theorem goal_store (table : Table) (environment : Environment) (current : Goal) (goals : List Goal)
    (tail : List Task) (state : State) :
    (goal table environment current goals tail state).store = state.store ∨
      ∃ values, (goal table environment current goals tail state).store =
        put (Head.key (match current with | .tell head => head | _ => ⟨"", []⟩))
          (⟨state.next, values⟩ :: slot (Head.key (match current with | .tell head => head | _ => ⟨"", []⟩))
            state.store) state.store := by
  cases current with
  | tell head => exact introduce_store_shape table head environment _ _ tail state _
  | assign index expression =>
    refine .inl ?_
    simp only [goal]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | fail => exact .inl (by simp [goal])

theorem scan_store (active : Nat) (key : Key) (values : List Value) (remaining : List At) (tail : List Task)
    (state : State) : (scan active key values remaining tail state).store = state.store := by
  unfold scan
  split
  · rfl
  · split
    · rfl
    · simp only
      split <;> rfl

theorem complete_store (active : Nat) (key : Key) (values : List Value) (occurrence : At) (after : List At)
    (stay : List Frame) (environment : Environment) (picks : List Pick) (tail : List Task) (state : State) :
    (complete active key values occurrence after stay environment picks tail state).store = state.store ∨
      (complete active key values occurrence after stay environment picks tail state).store =
        removePicks (picks.drop occurrence.body.kept.length) state.store := by
  unfold complete
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · exact .inr rfl
    · exact .inl rfl

theorem search_store (active : Nat) (key : Key) (values : List Value) (occurrence : At) (after : List At)
    (frames : List Frame) (tail : List Task) (state : State) :
    (search active key values occurrence after frames tail state).store = state.store ∨
      ∃ picks, (search active key values occurrence after frames tail state).store =
        removePicks picks state.store := by
  unfold search
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · split
      · exact .inl rfl
      · split
        · exact .inl rfl
        · split
          · exact .inl rfl
          · split
            · rcases complete_store active key values occurrence after _ _ _ tail state with same | removed
              · exact .inl same
              · exact .inr ⟨_, removed⟩
            · exact .inl rfl

theorem fresh_slot {state : State} (fresh : ∀ stored ∈ contents state.store, stored.id < state.next) (key : Key) :
    ∀ occurrence ∈ slot key state.store, occurrence.id < state.next :=
  fun _ inside => fresh _ (member_of_slot inside)

theorem added_descending {store : Store} (descending : Descending store) (key : Key) (next : Nat)
    (values : List Value) (fresh : ∀ occurrence ∈ slot key store, occurrence.id < next) :
    Descending (put key (⟨next, values⟩ :: slot key store) store) :=
  put_descending descending key (List.Pairwise.cons (fun occurrence inside => fresh occurrence inside)
    (slot_descending descending key))

/-- **Every tick keeps every slot newest first.** -/
theorem tick_descending (table : Table) (state : State) (descending : Descending state.store)
    (fresh : ∀ stored ∈ contents state.store, stored.id < state.next) : Descending (tick table state).store := by
  unfold tick
  split
  · rename_i task tail _ _
    cases task with
    | seeds heads =>
      cases heads with
      | nil => exact descending
      | cons head heads =>
        rcases introduce_store_shape table head [] _ _ tail state _ with same | ⟨values, added⟩
        · rw [same]; exact descending
        · rw [added]; exact added_descending descending _ _ values (fresh_slot fresh _)
    | goals environment goals =>
      cases goals with
      | nil => exact descending
      | cons current goals =>
        rcases goal_store table environment current goals tail state with same | ⟨values, added⟩
        · rw [same]; exact descending
        · rw [added]; exact added_descending descending _ _ values (fresh_slot fresh _)
    | scan active key values remaining =>
      show Descending (scan active key values remaining tail state).store
      rw [scan_store]
      exact descending
    | search active key values occurrence after frames =>
      show Descending (search active key values occurrence after frames tail state).store
      rcases search_store active key values occurrence after frames tail state with same | ⟨picks, removed⟩
      · rw [same]; exact descending
      · rw [removed]; exact removePicks_descending picks _ descending
  · exact descending

#print axioms tick_descending

/-- Every bounded run keeps every slot newest first, along with the
simulation it refines. -/
theorem advance_descending (program : Program) :
    ∀ (budget : Nat) (state : State) (abstract : CHR.State), Simulates program state abstract →
      Descending state.store → Descending (advance (table program) budget state).store
  | 0, _, _, _, descending => descending
  | budget + 1, state, abstract, simulates, descending => by
    unfold advance
    split
    · obtain ⟨middle, _, related⟩ := tick_simulates program state abstract simulates
      exact advance_descending program budget _ middle related (tick_descending _ state descending simulates.fresh)
    · exact descending

theorem start_descending (seeds : List Head) : Descending (start seeds).store := by
  intro entry inside
  simp [start] at inside

/-- **Every machine run from the seeds keeps every slot newest first.** -/
theorem run_descending (program : Program) (constraints : List Constraint) (budget : Nat) :
    Descending (advance (table program) budget (start (constraints.map Constraint.asHead))).store :=
  advance_descending program budget _ _ (start_simulates program constraints) (start_descending _)

#print axioms run_descending

/-! ## The decision in operational terms -/

/-- Every operational selection preferred to `reference` is unusable when
every enumerated selection preferred to it is rejected. -/
theorem preferred_unusable (store : Store) (coherent : Coherent store) (occurrence : At)
    (history : List CHR.Key) (active : Nat) (values : List Value)
    (activeStored : ∀ stored ∈ contents store, stored.id = active → stored.constraint.arguments = values)
    (reference : List Nat)
    (rejectedPreferred : ∀ selection ∈ selections store occurrence.head active values 0 occurrence.body.heads [] [] [],
      newerIds (ids selection.2) reference = true →
        Stale occurrence history selection ∨ guardsEval selection.1 occurrence.body.guards = .ok false)
    (operational : List Occurrence) (permuted : operational.Perm (contents store))
    (environment : Environment) (selection : Selection)
    (matched : selection.Matches occurrence.body environment operational)
    (activeAt : selection.ActiveAt active occurrence.head)
    (preferred : newerIds (selection.heads.map Occurrence.id) reference = true) :
    ¬ selection.Fresh occurrence.body occurrence.rule history ∨
      guardsEval environment occurrence.body.guards = .ok false := by
  obtain ⟨split, distinct, keptMatch, removedMatch, keysDistinct, onlyRule⟩ := matched
  have instantiated : List.Forall₂ (fun head stored => head.instantiate environment = some stored.constraint)
      occurrence.body.heads selection.heads := forall₂_append keptMatch removedMatch
  have stored : ∀ chosen ∈ selection.heads, chosen ∈ contents store := by
    intro chosen member
    apply permuted.subset
    apply split.symm.subset
    simp only [Selection.heads, List.mem_append] at member ⊢
    rcases member with kept | removed
    · exact .inl (.inl kept)
    · exact .inl (.inr removed)
  have fitting := allFit_intro store occurrence.head active values environment 0 occurrence.body.heads
    selection.heads instantiated stored (located_of_active distinct activeAt)
    (fun chosen member same => activeStored chosen (stored chosen member) same) coherent
  obtain ⟨bound, reached, grown⟩ := selections_complete store occurrence.head active values environment 0
    occurrence.body.heads selection.heads [] [] [] instantiated fitting distinct (by simp)
    (fun index value inside => by simp [lookup] at inside)
  have lengths := forall₂_length instantiated
  have sameIds : ids ([] ++ picksOf occurrence.body.heads selection.heads) = selection.heads.map Occurrence.id := by
    simpa using ids_picksOf occurrence.body.heads selection.heads lengths
  have rejected := rejectedPreferred _ reached (by simp only at sameIds ⊢; rw [sameIds]; exact preferred)
  rcases rejected with stale | guarded
  · left
    intro fresh
    obtain ⟨propagating, recorded⟩ := stale
    simp only at recorded
    rw [sameIds] at recorded
    have empty : occurrence.body.removed = [] := by
      simpa [Rule.propagation] using propagating
    exact fresh empty recorded
  · right
    have reachedFacts := selections_sound store occurrence.head active values 0 occurrence.body.heads [] [] []
      bound _ reached
    obtain ⟨found, _, instantiatedFound, _, _, _⟩ := reachedFacts.occurrences
    have agree : Agree bound environment := by
      intro index
      cases inBound : lookup bound index with
      | some value => exact (grown index value inBound).symm
      | none =>
        cases inEnvironment : lookup environment index with
        | none => rfl
        | some value =>
          exfalso
          have inRule := onlyRule (index, value) (mem_of_lookup inEnvironment)
          simp only [Rule.variables, List.mem_flatMap] at inRule
          obtain ⟨head, headMember, inHead⟩ := inRule
          obtain ⟨arguments, instantiatedHead⟩ := forall₂_instantiates instantiatedFound head headMember
          have isBound := instantiateTerms_bound head.arguments arguments instantiatedHead index
            (by simpa [Head.variables] using inHead)
          rw [inBound] at isBound
          simp at isBound
    simpa [guardsEval_agree agree] using guarded

/-- **The machine fires newest first.** When the search decides on a
selection, no operational selection that matches, is fresh and is not
rejected by its guards is preferred to it. -/
theorem decided_preferred (store : Store) (coherent : Coherent store) (descending : Descending store)
    (occurrence : At) (history : List CHR.Key) (active : Nat) (values : List Value)
    (activeStored : ∀ stored ∈ contents store, stored.id = active → stored.constraint.arguments = values)
    (chosen : Environment × List Pick)
    (decided : judge occurrence history
      (selections store occurrence.head active values 0 occurrence.body.heads [] [] []) = .ok (some chosen))
    (operational : List Occurrence) (permuted : operational.Perm (contents store))
    (environment : Environment) (selection : Selection)
    (matched : selection.Matches occurrence.body environment operational)
    (activeAt : selection.ActiveAt active occurrence.head)
    (preferred : newerIds (selection.heads.map Occurrence.id) (ids chosen.2) = true) :
    ¬ selection.Fresh occurrence.body occurrence.rule history ∨
      guardsEval environment occurrence.body.guards = .ok false :=
  preferred_unusable store coherent occurrence history active values activeStored (ids chosen.2)
    (fun listed inside newer => judge_preferred occurrence history _ chosen
      (selections_sorted store occurrence.head active values descending 0 occurrence.body.heads [] [] []) decided
      listed inside newer) operational permuted environment selection matched activeAt preferred

/-- **A faulting guard is the newest-first one.** When the search faults, the
faulting selection is fresh, its guards fault, and no operational selection
preferred to it is usable. -/
theorem fault_preferred (store : Store) (coherent : Coherent store) (descending : Descending store)
    (occurrence : At) (history : List CHR.Key) (active : Nat) (values : List Value)
    (activeStored : ∀ stored ∈ contents store, stored.id = active → stored.constraint.arguments = values)
    (reason : ArithmeticFault)
    (decided : judge occurrence history
      (selections store occurrence.head active values 0 occurrence.body.heads [] [] []) = .error reason) :
    ∃ faulting ∈ selections store occurrence.head active values 0 occurrence.body.heads [] [] [],
      guardsEval faulting.1 occurrence.body.guards = .error reason ∧
      ∀ (operational : List Occurrence), operational.Perm (contents store) →
        ∀ (environment : Environment) (selection : Selection), selection.Matches occurrence.body environment operational →
          selection.ActiveAt active occurrence.head →
          newerIds (selection.heads.map Occurrence.id) (ids faulting.2) = true →
          ¬ selection.Fresh occurrence.body occurrence.rule history ∨
            guardsEval environment occurrence.body.guards = .ok false := by
  obtain ⟨faulting, inside, _, faults, preferred⟩ := judge_fault_preferred occurrence history reason _
    (selections_sorted store occurrence.head active values descending 0 occurrence.body.heads [] [] []) decided
  exact ⟨faulting, inside, faults, fun operational permuted environment selection matched activeAt newer =>
    preferred_unusable store coherent occurrence history active values activeStored (ids faulting.2)
      (fun listed member better => preferred listed member better) operational permuted environment selection
      matched activeAt newer⟩

#print axioms decided_preferred
#print axioms fault_preferred

/-- In a newest-first enumeration, everything preferred to an entry comes
before it. -/
theorem preferred_before {listed : List (Environment × List Pick)}
    (sorted : listed.Pairwise fun first second => newerIds (ids first.2) (ids second.2) = true)
    {consumed rest : List (Environment × List Pick)} {chosen : Environment × List Pick}
    (split : consumed ++ chosen :: rest = listed) :
    ∀ other ∈ listed, newerIds (ids other.2) (ids chosen.2) = true → other ∈ consumed := by
  intro other inside newer
  rw [← split] at sorted inside
  rcases List.mem_append.mp inside with early | late
  · exact early
  · exfalso
    rcases List.mem_cons.mp late with same | later
    · subst same
      simp [newerIds_irrefl] at newer
    · have ordered := (List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 other later
      simp [newerIds_asymm _ _ ordered] at newer

#print axioms preferred_before

end Mettapedia.Languages.CHR.Machine
