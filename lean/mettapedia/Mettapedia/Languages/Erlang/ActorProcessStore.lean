import Mettapedia.Languages.Erlang.ActorIdentityPreservation

/-! Pid-keyed views of the source's indexed process store. Uniqueness is
derived from reachable actor configurations; replacing the first matching
pid agrees with replacing the source's selected physical list position. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang.ActorProcessStore

def get (identity : Nat) (processes : List LocalProcess) : Option LocalProcess :=
  processes.find? fun process => identity == process.identity

def put (identity : Nat) (replacement : LocalProcess) : List LocalProcess → List LocalProcess
  | [] => []
  | process :: rest =>
      if identity = process.identity then replacement :: rest else process :: put identity replacement rest

theorem canonical_unique {system : ActorSystem} (valid : system.CanonicalPids) :
    (system.processes.map LocalProcess.identity).Nodup := by
  rw [valid.identities]
  exact List.nodup_range

private theorem same_key_same_process {processes : List LocalProcess}
    (unique : (processes.map LocalProcess.identity).Nodup)
    {first second : LocalProcess} (firstMember : first ∈ processes) (secondMember : second ∈ processes)
    (same : first.identity = second.identity) : first = second := by
  induction processes with
  | nil => cases firstMember
  | cons process rest ih =>
    obtain ⟨absent, distinct⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp firstMember with rfl | inTailFirst
    · rcases List.mem_cons.mp secondMember with rfl | inTailSecond
      · rfl
      · exact (absent (List.mem_map.mpr ⟨second, inTailSecond, same.symm⟩)).elim
    · rcases List.mem_cons.mp secondMember with rfl | inTailSecond
      · exact (absent (List.mem_map.mpr ⟨first, inTailFirst, same⟩)).elim
      · exact ih distinct inTailFirst inTailSecond

theorem get_of_member {identity : Nat} {process : LocalProcess} {processes : List LocalProcess}
    (unique : (processes.map LocalProcess.identity).Nodup) (member : process ∈ processes)
    (same : identity = process.identity) : get identity processes = some process := by
  unfold get
  cases selected : processes.find? (fun candidate => identity == candidate.identity) with
  | none =>
    have absent := List.find?_eq_none.mp selected process member
    simp [same] at absent
  | some selectedProcess =>
    have found : identity = selectedProcess.identity := by simpa using List.find?_some selected
    have equal := same_key_same_process unique (List.mem_of_find?_eq_some selected) member (found.symm.trans same)
    rw [equal]

theorem get_source_index {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {process : LocalProcess} (found : system.processes[index]? = some process) :
    get index system.processes = some process := by
  apply get_of_member (canonical_unique valid)
  · exact List.mem_of_getElem? found
  · exact (valid.at found).symm

theorem get_source_index_iff {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {process : LocalProcess} :
    get index system.processes = some process ↔ system.processes[index]? = some process := by
  constructor
  · intro selected
    have member := List.mem_of_find?_eq_some selected
    obtain ⟨position, bounded, same⟩ := List.mem_iff_getElem.mp member
    have found : system.processes[position]? = some process := by
      rw [List.getElem?_eq_getElem bounded, same]
    have keyed : index = process.identity := by simpa only [get, beq_iff_eq] using List.find?_some selected
    have physical := valid.at found
    rw [keyed, physical]
    exact found
  · exact get_source_index valid

theorem put_at {processes : List LocalProcess} (unique : (processes.map LocalProcess.identity).Nodup)
    {index : Nat} {process : LocalProcess} (found : processes[index]? = some process)
    (replacement : LocalProcess) : put process.identity replacement processes = processes.set index replacement := by
  induction processes generalizing index with
  | nil => cases found
  | cons first rest ih =>
    obtain ⟨absent, distinct⟩ := List.nodup_cons.mp unique
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst process
      simp [put]
    | succ index =>
      change rest[index]? = some process at found
      have apart : process.identity ≠ first.identity := by
        intro same
        exact absent (List.mem_map.mpr ⟨process, List.mem_of_getElem? found, same⟩)
      simpa only [put, if_neg apart, List.set_cons_succ] using congrArg (List.cons first) (ih distinct found)

theorem put_source_index {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {process : LocalProcess} (found : system.processes[index]? = some process)
    (replacement : LocalProcess) : put index replacement system.processes = system.processes.set index replacement := by
  calc
    put index replacement system.processes = put process.identity replacement system.processes := by rw [valid.at found]
    _ = system.processes.set index replacement := put_at (canonical_unique valid) found replacement

end Mettapedia.Languages.Erlang.ActorProcessStore
