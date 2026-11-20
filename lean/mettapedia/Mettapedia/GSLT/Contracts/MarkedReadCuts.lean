import Mettapedia.GSLT.Contracts.DependencyClaims
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves
import Mathlib.Data.Finset.Sort

/-!
# A common validating cut for explicitly marked reads

Marks retain the observations of actual pure adaptive queries. A joint read
does not require a shared origin stamp, but it does require one admissible
cut that realizes all the retained observations. No mark authorizes a
take, an output, or a live replay of effects.

The occurrence instance uses the existing executable commit words, with
the explicit observation order of increasing physical occurrence number.
Neither that order nor this finite, fixed-label instance is a requirement
on other presentations of the step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Dependencies.MarkedReadCuts

open Mettapedia.Machines.ReadOnlyQuery (Program Observation Reads run run_agrees run_eq_of_agrees)
open Mettapedia.Machines
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
  (Commit Executable fireList executable_append_iff)

universe u v w

variable {Atom : Type u} {K : Type v}

/-- The admissible cuts that agree with the recorded dependencies. The caller
supplies the cut carrier and interpretation; no wall-clock order is assumed. -/
def validatingCuts (view : K → Store Atom) (dependencies : List (Dep Atom)) : Set K :=
  {k | Valid dependencies (view k)}

instance decidableValidatingCut [DecidableEq Atom]
    (view : K → Store Atom) (dependencies : List (Dep Atom)) (cut : K) :
    Decidable (cut ∈ validatingCuts view dependencies) :=
  inferInstanceAs (Decidable (Valid dependencies (view cut)))

theorem valid_append_iff (first second : List (Dep Atom)) (store : Store Atom) :
    Valid (first ++ second) store ↔ Valid first store ∧ Valid second store := by
  simp [Valid, List.mem_append, or_imp, forall_and]

@[simp] theorem validatingCuts_nil (view : K → Store Atom) :
    validatingCuts view [] = Set.univ := by
  ext k
  simp [validatingCuts, Valid]

theorem validatingCuts_append (view : K → Store Atom) (first second : List (Dep Atom)) :
    validatingCuts view (first ++ second) =
      validatingCuts view first ∩ validatingCuts view second := by
  ext k
  exact valid_append_iff first second (view k)

/-- Restricting the available cuts commutes with validation. This also
applies to an explicit subhistory selection, without changing its rows. -/
theorem validatingCuts_reindex {J : Type*} (view : K → Store Atom) (index : J → K)
    (dependencies : List (Dep Atom)) :
    validatingCuts (view ∘ index) dependencies = index ⁻¹' validatingCuts view dependencies :=
  rfl

/-- An explicit origin cut and the pure query read there. Different marks
can have different answer types. The capture is the existing interpreter's
observation at the origin, not an independently supplied answer. -/
structure Mark (Atom : Type u) (K : Type v) where
  origin : K
  Answer : Type w
  query : Program (Atom → Bool) (Store Atom) Answer

def Mark.observe (mark : Mark.{u,v,w} Atom K) (view : K → Store Atom) (cut : K) :
    Observation (Atom → Bool) (Store Atom) mark.Answer :=
  run (fun q => matchingRows q (view cut)) mark.query

/-- The receipts are precisely the reads of the marked executions. Their
order and multiplicity are kept; flattening does not choose a cut. -/
def markedReads (view : K → Store Atom) (marks : List (Mark.{u,v,w} Atom K)) :
    Reads (Atom → Bool) (Store Atom) :=
  marks.flatMap fun mark => (mark.observe view mark.origin).reads

theorem validatingCuts_marked_append (view : K → Store Atom)
    (first second : List (Mark.{u,v,w} Atom K)) :
    validatingCuts view (readDependencies (markedReads view (first ++ second))) =
      validatingCuts view (readDependencies (markedReads view first)) ∩
        validatingCuts view (readDependencies (markedReads view second)) := by
  unfold markedReads
  rw [List.flatMap_append, readDependencies_append, validatingCuts_append]

/-- At a cut with unambiguous identifiers, validating the combined receipt
is necessary and sufficient to replay every marked answer AND its actual
adaptive read path. This is not merely an equality of final answers. -/
theorem cut_replays_iff (view : K → Store Atom) (marks : List (Mark.{u,v,w} Atom K))
    (cut : K) (consistent : PayloadConsistent (view cut)) :
    cut ∈ validatingCuts view (readDependencies (markedReads view marks)) ↔
      ∀ mark ∈ marks, mark.observe view cut = mark.observe view mark.origin := by
  change Valid (readDependencies (markedReads view marks)) (view cut) ↔ _
  rw [valid_readDependencies_iff _ consistent]
  constructor
  · intro agree mark included
    apply run_eq_of_agrees
    intro entry member
    apply agree entry
    exact List.mem_flatMap.mpr ⟨mark, included, member⟩
  · intro replay entry member
    obtain ⟨mark, included, readAtOrigin⟩ := List.mem_flatMap.mp member
    have readAtCut : entry ∈ (mark.observe view cut).reads := by
      rw [replay mark included]
      exact readAtOrigin
    exact run_agrees (fun q => matchingRows q (view cut)) mark.query entry readAtCut

/-- The second captured query may be selected by the first captured answer,
even when the two origins differ. A joint validating cut then replays the
ordinary bind, in the original read order. The reverse direction validates
the exact recorded reads, not just the final answer. -/
theorem cut_replays_bind_iff {First : Type w} {Answer : Type*}
    (view : K → Store Atom) (first second cut : K)
    (program : Program (Atom → Bool) (Store Atom) First)
    (next : First → Program (Atom → Bool) (Store Atom) Answer)
    (consistent : PayloadConsistent (view cut)) :
    let read := fun atCut query => matchingRows query (view atCut)
    let head := run (read first) program
    let tail := run (read second) (next head.answer)
    Valid (readDependencies (head.reads ++ tail.reads)) (view cut) ↔
      run (read cut) (ReadOnlyQuery.bind program next) =
        ⟨tail.answer, head.reads ++ tail.reads⟩ := by
  let read := fun atCut query => matchingRows query (view atCut)
  let head := run (read first) program
  let tail := run (read second) (next head.answer)
  change Valid (readDependencies (head.reads ++ tail.reads)) (view cut) ↔
    run (read cut) (ReadOnlyQuery.bind program next) =
      ⟨tail.answer, head.reads ++ tail.reads⟩
  rw [valid_readDependencies_iff _ consistent]
  constructor
  · intro agree
    obtain ⟨firstAgrees, secondAgrees⟩ :=
      (ReadOnlyQuery.agrees_append (read cut) head.reads tail.reads).mp agree
    have firstReplay : run (read cut) program = head :=
      run_eq_of_agrees (read first) (read cut) program firstAgrees
    have secondReplay : run (read cut) (next head.answer) = tail :=
      run_eq_of_agrees (read second) (read cut) (next head.answer) secondAgrees
    simp only [ReadOnlyQuery.run_bind, firstReplay, secondReplay]
  · intro replay
    have agree := run_agrees (read cut) (ReadOnlyQuery.bind program next)
    rw [replay] at agree
    exact agree

/-! ## Occurrence runs, read in an explicit order -/

/-- Observe identified rows by increasing occurrence number. Equal payloads
at distinct occurrences are still distinct list entries. -/
def orderedRows (label : Nat → Atom) (present : Finset Nat) : Store Atom :=
  (present.sort (· ≤ ·)).map fun o => (o, label o)

theorem orderedRows_consistent (label : Nat → Atom) (present : Finset Nat) :
    PayloadConsistent (orderedRows label present) := by
  intro first firstMem second secondMem same
  unfold orderedRows at firstMem secondMem
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp firstMem
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp secondMem
  exact congrArg label same

/-- The fixed-label occurrence instance retains a witness of the existing
executable word. It defines no additional reduction. -/
structure History (Atom : Type u) where
  label : Nat → Atom
  initial : Finset Nat
  word : List (Commit Nat Atom)
  executed : Executable label initial word

namespace History

abbrev Cut (h : History Atom) := Fin (h.word.length + 1)

def presentAt (h : History Atom) (cut : h.Cut) : Finset Nat :=
  fireList h.initial (h.word.take cut.val)

def view (h : History Atom) (cut : h.Cut) : Store Atom :=
  orderedRows h.label (h.presentAt cut)

theorem prefix_executable (h : History Atom) (cut : h.Cut) :
    Executable h.label h.initial (h.word.take cut.val) := by
  have split : Executable h.label h.initial (h.word.take cut.val ++ h.word.drop cut.val) := by
    simpa only [List.take_append_drop] using h.executed
  exact (executable_append_iff.mp split).1

theorem cut_replays_iff (h : History Atom) (marks : List (Mark.{u,0,w} Atom h.Cut)) (cut : h.Cut) :
    cut ∈ validatingCuts h.view (readDependencies (markedReads h.view marks)) ↔
      ∀ mark ∈ marks, mark.observe h.view cut = mark.observe h.view mark.origin :=
  MarkedReadCuts.cut_replays_iff h.view marks cut (orderedRows_consistent h.label (h.presentAt cut))

end History

/-! ## Successful existence can retain less than the full trace -/

/-- The Boolean observer using the ordinary complete read. Its full
observation would also include the entire list of matching rows. -/
def anyQuery (q : Atom → Bool) : Program (Atom → Bool) (Store Atom) Bool :=
  .read q fun rows => .pure (!rows.isEmpty)

/-- A short-circuit search for an actual occurrence, without collecting the
whole answer list. On success we may retain just its presence dependency. -/
def anyWitness (q : Atom → Bool) (store : Store Atom) : Option (Nat × Atom) :=
  store.find? fun row => q row.2

theorem any_answer_eq_isSome (q : Atom → Bool) (store : Store Atom) :
    (run (fun query => matchingRows query store) (anyQuery q)).answer =
      (anyWitness q store).isSome := by
  let accepts (entry : Nat × Atom) : Bool := q entry.2
  change (!(store.filter accepts).isEmpty) = (store.find? accepts).isSome
  induction store with
  | nil => rfl
  | cons row rest ih =>
      cases hit : accepts row with
      | false =>
          have miss : ¬ accepts row := by simp [hit]
          rw [List.filter_cons_of_neg miss, List.find?_cons_of_neg miss, ih]
      | true =>
          rw [List.filter_cons_of_pos hit, List.find?_cons_of_pos hit]
          rfl

theorem anyWitness_facts {q : Atom → Bool} {store : Store Atom} {row : Nat × Atom}
    (saved : anyWitness q store = some row) : row ∈ store ∧ q row.2 = true := by
  have found : store.find? (fun entry => q entry.2) = some row := saved
  obtain ⟨hit, _, _, rfl, _⟩ := List.find?_eq_some_iff_append.mp found
  exact ⟨List.mem_append_right _ List.mem_cons_self, hit⟩

theorem anyWitness_valid_origin {q : Atom → Bool} {store : Store Atom} {row : Nat × Atom}
    (saved : anyWitness q store = some row) : Valid [.present row.1 row.2] store := by
  intro dependency member
  obtain rfl := List.mem_singleton.mp member
  exact (anyWitness_facts saved).1

/-- A still-present witness licenses the successful Boolean answer, not
replay of the full observation. An empty result has no such witness. -/
theorem any_answer_of_witness {q : Atom → Bool} {origin current : Store Atom} {row : Nat × Atom}
    (saved : anyWitness q origin = some row) (valid : Valid [.present row.1 row.2] current) :
    (run (fun query => matchingRows query current) (anyQuery q)).answer = true := by
  have member : row ∈ current := valid _ (List.mem_singleton_self _)
  have hit := (anyWitness_facts saved).2
  rw [any_answer_eq_isSome]
  cases checked : anyWitness q current with
  | some witness => rfl
  | none =>
      have none : current.find? (fun entry => q entry.2) = none := checked
      have noHit := List.find?_eq_none.mp none row member
      exact False.elim (noHit hit)

/-- In a bundle, weakening one successful Boolean observation to its
actual witness retains exact replay of all the other full marks. -/
theorem cut_replays_with_any {view : K → Store Atom} {cut origin : K}
    (marks : List (Mark.{u,v,w} Atom K)) (q : Atom → Bool) {row : Nat × Atom}
    (consistent : PayloadConsistent (view cut)) (saved : anyWitness q (view origin) = some row)
    (valid : cut ∈ validatingCuts view
      (readDependencies (markedReads view marks) ++ [.present row.1 row.2])) :
    (∀ mark ∈ marks, mark.observe view cut = mark.observe view mark.origin) ∧
      (run (fun query => matchingRows query (view cut)) (anyQuery q)).answer = true := by
  obtain ⟨complete, witness⟩ := (valid_append_iff _ _ _).mp valid
  exact ⟨(cut_replays_iff view marks cut consistent).mp complete, any_answer_of_witness saved witness⟩

#print axioms validatingCuts_append
#print axioms cut_replays_iff
#print axioms cut_replays_bind_iff
#print axioms History.prefix_executable
#print axioms History.cut_replays_iff
#print axioms any_answer_eq_isSome
#print axioms any_answer_of_witness
#print axioms cut_replays_with_any

end Mettapedia.GSLT.Contracts.Dependencies.MarkedReadCuts
