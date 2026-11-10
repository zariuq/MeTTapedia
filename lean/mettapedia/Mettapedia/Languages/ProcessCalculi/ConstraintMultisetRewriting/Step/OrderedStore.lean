import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Ordered occurrence publication as a transform effect

The state retains an ordered list of distinct occurrence identities beside
its equation store. Payload equality does not identify occurrences. Publication
contracts the selected identities and appends made occurrences in their declared
order. Its finite-set projection is exactly the existing occurrence firing.

The frame and knowledge are arbitrary, not an empty or constant surrogate for
the transform interface. This store-only profile leaves them unchanged. It
adds no policy for source matching, scheduling, receipts, or concurrent writes.
The contextual-derived-forms lane owns this adapter; core interfaces are reused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStore

open MeTTaCalculus.OccurrenceCommits (Commit PredicateQuery Enabled fire)

universe uO uT uH uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (a : Obj) (O : Type uOcc) [DecidableEq O]

abbrev State := EquationStore (Tm a) × List O

structure Publication (R : Type*) (O : Type uOcc) where
  selection : Selection O
  observations : List (PredicateQuery O R)

variable {O}

def Publication.commit {R : Type*} (request : Publication R O) : Commit O R :=
  { request.selection.commit (T := R) with queries := request.observations }

def survivors (rows taken : List O) : List O :=
  rows.filter fun occurrence => decide (occurrence ∉ taken)

def publish (rows : List O) (selected : Selection O) : List O :=
  survivors rows selected.taken ++ selected.made

theorem publish_present (rows : List O) (selected : Selection O) :
    (publish rows selected).toFinset = fire rows.toFinset (selected.commit (T := Unit)) := by
  ext occurrence
  simp only [publish, survivors, List.toFinset_append, Finset.mem_union,
    List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
    fire, Selection.commit, Finset.mem_sdiff]

def Shapes (rows : List O) (selected : Selection O) : Prop :=
  rows.Nodup ∧ selected.taken.Nodup ∧ selected.made.Nodup

/-- Project only physical enabling; predicate observations remain an
independent obligation of admission, not of the prepared physical effect. -/
theorem physical_enabled {R : Type*} {label : O → R} {rows : List O}
    {request : Publication R O} (enabled : Enabled label rows.toFinset request.commit) :
    Enabled (fun _ : O => ()) rows.toFinset (request.selection.commit (T := Unit)) := by
  refine ⟨enabled.taken_subset, enabled.kept_subset, enabled.apart, enabled.fresh, ?_⟩
  intro query member
  simp only [Selection.commit, List.not_mem_nil] at member

/-- Knowledge and scope are retained, while the occurrence effect is real
stable contraction and ordered append. No source-evaluator equivalence is
assumed in constructing this effect. -/
def effect : EffectCore X O (State (Tm := Tm) a O) (fun _ => Publication (Tm a) O) where
  frame _ := a
  knowledge state := state.1
  present state := state.2.toFinset
  selection request := request.selection
  target _ := a
  extension _ := X.id a
  information {state} _ := state.1
  information_refines _ := by
    intro b substitution solved
    exact (Frames.models_congr (fun term => Frames.act_comp_id substitution term) _).mp solved
  Shapes {state} request := Shapes state.2 request.selection
  preparedResult {state} request _ := (state.1, publish state.2 request.selection)
  present_preparedResult request _ := publish_present _ request.selection
  preparedSettle _ _ := X.id a
  result_refines _ _ := by
    intro b substitution solved
    exact (Frames.models_congr (fun term => Frames.act_comp_id substitution term) _).mp solved

def step (label : O → Tm a) : Step X O (State (Tm := Tm) a O) (fun _ => Publication (Tm a) O) where
  toEffectCore := effect X a
  Admits {state} request := Shapes state.2 request.selection ∧
    Enabled label state.2.toFinset request.commit ∧ X.Solvable state.1
  admitted_prepares _ admitted :=
    ⟨admitted.1, physical_enabled admitted.2.1, admitted.2.2⟩

theorem admits_exact (label : O → Tm a) (state : State (Tm := Tm) a O)
    (request : Publication (Tm a) O) :
    (step X a label).Admits (s := state) request ↔
      Shapes state.2 request.selection ∧
      Enabled label state.2.toFinset request.commit ∧ X.Solvable state.1 := Iff.rfl

theorem knowledge_exact : (effect X a (O := O)).ExactKnowledge := by
  intro state request prepared b substitution solved
  exact (Frames.models_congr (fun term => (Frames.act_comp_id substitution term).symm) _).mp solved

theorem result_rows (label : O → Tm a) {state : State (Tm := Tm) a O}
    {request : Publication (Tm a) O} (admitted : (step X a label).Admits (s := state) request) :
    ((step X a label).result request admitted).2 = publish state.2 request.selection := rfl

theorem result_knowledge (label : O → Tm a) {state : State (Tm := Tm) a O}
    {request : Publication (Tm a) O} (admitted : (step X a label).Admits (s := state) request) :
    ((step X a label).result request admitted).1 = state.1 := rfl

/-- The target's ordered observation contains exactly the surviving old
occurrences followed by the made occurrences. This retains equal payload copies. -/
theorem result_observation (label : O → Tm a) {state : State (Tm := Tm) a O}
    {request : Publication (Tm a) O} (admitted : (step X a label).Admits (s := state) request) :
    (((step X a label).result request admitted).2.map label) =
      (state.2.filter fun occurrence => decide (occurrence ∉ request.selection.taken)).map label ++
        request.selection.made.map label := by
  rw [result_rows]
  simp only [publish, survivors, List.map_append]

theorem result_nodup (label : O → Tm a) {state : State (Tm := Tm) a O}
    {request : Publication (Tm a) O} (admitted : (step X a label).Admits (s := state) request) :
    ((step X a label).result request admitted).2.Nodup := by
  rw [result_rows]
  have shaped := admitted.1
  have fresh := admitted.2.1.fresh
  apply List.nodup_append.mpr
  refine ⟨shaped.1.filter _, shaped.2.2, ?_⟩
  intro occurrence retained other made same
  subst other
  have old := (List.mem_filter.mp retained).1
  exact Finset.disjoint_left.mp fresh (by simpa [Publication.commit, Selection.commit] using made)
    (by simpa using old)

/-- The physical effect preserves a read-only ordered store. Any answer or
binding observation remains the observer's work rather than disappearing. -/
theorem reads_only (rows read : List O) :
    publish rows ⟨[], read, []⟩ = rows := by simp [publish, survivors]

theorem append_only (rows made : List O) :
    publish rows ⟨[], [], made⟩ = rows ++ made := by simp [publish, survivors]

theorem selected_removal (select : O → Bool) (rows : List O) :
    publish rows ⟨rows.filter select, [], []⟩ = rows.filter (fun occurrence => !select occurrence) := by
  simp only [publish, survivors, List.append_nil]
  apply List.filter_congr
  intro occurrence member
  simp [member]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStore
