import Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapSnapshot
import Mettapedia.Machines.TIsa.StoreInstructions.PackedWorklist

/-!
# A packed work list with retained term roots

The reference transition shares the graph map with the
equation suffix. Range preservation is a consequence of
successful remapping, not of reserving a worst-case number
of future graph nodes. The root vector is ordered and may
contain any number of repeated handles.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedRootedWorklist

open PackedTerms (Arena)
open PackedWorklist (Worklist)
open NativeRemapSnapshot (Extension)

abbrev Outcome := PackedWorklist.State

def Valid (arena : Arena) (words : Array Word) : Prop :=
  ∀ handle ∈ words.toList, handle.toNat < arena.nodes.size

theorem Valid.keep {source target : Arena} (more : Extension source target) {words : Array Word}
    (valid : Valid source words) : Valid target words :=
  fun handle present => (valid handle present).trans_le more.node_size

private theorem rewrite_valid {source target next : Arena} {mapped : Array Word} {name replacement handle result : Word}
    (retained : Extension source target) (valid : replacement.toNat < source.nodes.size)
    (rewritten : PackedSubstitution.rewrite source target mapped name replacement handle = some (next, result)) :
    result.toNat < next.nodes.size := by
  obtain ⟨node, read, branch⟩ := Option.bind_eq_some_iff.mp rewritten
  have inRange := (Array.getElem?_eq_some_iff.mp read).choose.trans_le retained.node_size
  by_cases variableTag : node.header.tag = 0
  · simp only [if_pos variableTag] at branch
    obtain ⟨rfl, current⟩ := Prod.mk.inj (Option.some.inj branch)
    rw [← current]
    split
    · exact valid.trans_le retained.node_size
    · exact inRange
  · by_cases constantTag : node.header.tag = 1
    · simp only [if_neg variableTag, if_pos constantTag] at branch
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj branch)
      exact inRange
    · by_cases app : node.header.tag = 2
      · simp only [if_neg variableTag, if_neg constantTag, if_pos app] at branch
        obtain ⟨words, _, later⟩ := Option.bind_eq_some_iff.mp branch
        obtain ⟨changed, _, finished⟩ := Option.bind_eq_some_iff.mp later
        by_cases same : changed = words
        · rw [if_pos same] at finished
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj finished)
          exact inRange
        · rw [if_neg same] at finished
          unfold PackedTerms.append at finished
          split at finished
          next fit =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj finished)
            simp only [PackedTerms.root, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit.1, PackedTerms.place, Array.size_push]
            omega
          next => cases finished
      · rw [if_neg variableTag, if_neg constantTag, if_neg app] at branch
        cases branch

theorem scan_valid (source : Arena) (name replacement : Word) (remaining : ℕ) (prior after : PackedSubstitution.State)
    (retained : Extension source prior.target) (roots : Valid prior.target prior.mapped)
    (replacementFits : replacement.toNat < source.nodes.size)
    (mapped : PackedSubstitution.scan source name replacement remaining prior = some after) :
    Valid after.target after.mapped := by
  induction remaining generalizing prior with
  | zero =>
    obtain rfl := Option.some.inj mapped
    exact roots
  | succ fuel ih =>
    obtain ⟨middle, updated, tail⟩ := Option.bind_eq_some_iff.mp mapped
    obtain ⟨handle, rewritten, moved⟩ := NativeRemapSnapshot.advance_readout source name replacement prior middle updated
    obtain ⟨extended, _⟩ := NativeRemapSnapshot.advance_extends source name replacement prior middle updated
    have safe : Valid middle.target middle.mapped := by
      intro word present
      rw [moved, Array.push_eq_append, Array.toList_append, List.mem_append] at present
      rcases present with prev | newest
      · exact (roots word prev).trans_le extended.node_size
      · have same : word = handle := List.mem_singleton.mp newest
        subst word
        exact rewrite_valid retained replacementFits rewritten
    exact ih middle (retained.trans extended) safe tail

theorem substitute_valid {source : Arena} {name replacement : Word} {result : PackedSubstitution.State}
    (known : replacement.toNat < source.nodes.size)
    (scanned : PackedSubstitution.substitute source name replacement = some result) :
    result.mapped.size = source.nodes.size ∧ Valid result.target result.mapped := by
  have length := (NativeRemapSnapshot.scan_extends source name replacement source.nodes.size ⟨source, #[]⟩ result scanned).2
  exact ⟨by simpa using length, scan_valid source name replacement source.nodes.size ⟨source, #[]⟩ result
    (Extension.refl _) (by intro word absent; simp at absent) known scanned⟩

theorem translate_valid {source target : Arena} {mapping roots : Array Word}
    (width : mapping.size = source.nodes.size) (safe : Valid target mapping) (held : Valid source roots) :
    ∃ translated, PackedSubstitution.translate mapping roots = some translated ∧ Valid target translated := by
  have load {inputs : List Word} (inside : ∀ address ∈ inputs, address.toNat < mapping.size) :
      ∃ values, inputs.mapM (fun value => mapping[value.toNat]?) = some values ∧
        ∀ value ∈ values, value.toNat < target.nodes.size := by
    induction inputs with
    | nil => exact ⟨[], rfl, fun _ absent => (List.not_mem_nil absent).elim⟩
    | cons first later ih =>
      have limit := inside first List.mem_cons_self
      obtain ⟨tail, translated, valid⟩ := ih (fun address seen => inside address (List.mem_cons_of_mem _ seen))
      refine ⟨mapping[first.toNat] :: tail, ?_, ?_⟩
      · simp only [List.mapM_cons, Array.getElem?_eq_getElem limit, translated, bind, pure, Option.bind_some]
      · intro value member
        rcases List.mem_cons.mp member with here | there
        · subst value
          exact safe _ (Array.mem_toList_iff.mpr (Array.getElem_mem _))
        · exact valid _ there
  obtain ⟨values, read, valid⟩ := load (inputs := roots.toList) (fun handle seen => width.symm ▸ held handle seen)
  exact ⟨values.toArray, by simp [PackedSubstitution.translate, read], by simpa only [Valid, List.toList_toArray] using valid⟩

def advance (work : Worklist) (roots : Array Word) : Option (Outcome × Array Word) :=
  match work.pending with
  | [] => some (.solved work.arena work.trail, roots)
  | (left, right) :: pending => do
    let action ← PackedUnifierAction.inspect work.arena left right
    match action with
    | .discard => some (.working { work with pending }, roots)
    | .decompose pairs => some (.working { work with pending := pairs ++ pending }, roots)
    | .refuse why => some (.inconsistent why, roots)
    | .bindVar name value => do
      let result ← PackedSubstitution.substitute work.arena name value
      let later ← PackedSubstitution.remapPending result.mapped pending
      let new ← PackedSubstitution.translate result.mapped roots
      some (.working ⟨result.target, later, (name, value) :: work.trail⟩, new)

def step (state : Outcome) (roots : Array Word) : Option (Outcome × Array Word) :=
  match state with
  | .working work => advance work roots
  | .solved .. | .inconsistent .. => some (state, roots)

def run : ℕ → Outcome → Array Word → Option (Outcome × Array Word)
  | 0, state, roots => some (state, roots)
  | fuel + 1, state, roots => (step state roots).bind fun (next, held) => run fuel next held

theorem terminal_run (fuel : ℕ) (state : Outcome) (roots : Array Word)
    (terminal : PackedWorklist.terminal state = true) : run fuel state roots = some (state, roots) := by
  have stay : step state roots = some (state, roots) := by cases state <;> simp_all [step, PackedWorklist.terminal]
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, stay, Option.bind_some] using ih

private theorem binding_value {source : Arena} {name replacement left right : Word}
    (accepted : PackedUnifierAction.inspect source left right = some (.bindVar name replacement)) :
    replacement.toNat < source.nodes.size := by
  obtain ⟨l, readL, more⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨r, readR, branch⟩ := Option.bind_eq_some_iff.mp more
  cases route : UnifierHeaders.dispatch l.header r.header
  case bindLeft =>
    rw [route] at branch
    obtain ⟨occurs, _, chosen⟩ := Option.map_eq_some_iff.mp branch
    cases occurs
    · have equal : right = replacement := (PackedUnifierAction.Encoded.bindVar.inj chosen).2
      rw [← equal]
      exact (Array.getElem?_eq_some_iff.mp readR).choose
    · cases chosen
  case bindRight =>
    rw [route] at branch
    obtain ⟨occurs, _, chosen⟩ := Option.map_eq_some_iff.mp branch
    cases occurs
    · have equal : left = replacement := (PackedUnifierAction.Encoded.bindVar.inj chosen).2
      rw [← equal]
      exact (Array.getElem?_eq_some_iff.mp readL).choose
    · cases chosen
  case expand =>
    rw [route] at branch
    obtain ⟨ls, _, following⟩ := Option.bind_eq_some_iff.mp branch
    obtain ⟨rs, _, same⟩ := Option.bind_eq_some_iff.mp following
    split at same <;> cases same
  all_goals simp [route] at branch

theorem bind_valid {source : Arena} {name replacement left right : Word} {result : PackedSubstitution.State}
    (accepted : PackedUnifierAction.inspect source left right = some (.bindVar name replacement))
    (scanned : PackedSubstitution.substitute source name replacement = some result) {roots : Array Word}
    (held : Valid source roots) :
    ∃ moved, PackedSubstitution.translate result.mapped roots = some moved ∧ Valid result.target moved := by
  obtain ⟨length, range⟩ := substitute_valid (binding_value accepted) scanned
  exact translate_valid length range held

theorem advance_other {source : Arena} {left right : Word} {pending history : PackedWorklist.Words}
    {action : PackedUnifierAction.Encoded} (looked : PackedUnifierAction.inspect source left right = some action)
    {result : Outcome} (advanced : PackedWorklist.advance ⟨source, (left, right) :: pending, history⟩ = some result)
    (notBound : ∀ name value, action ≠ .bindVar name value) (roots : Array Word) :
    advance ⟨source, (left, right) :: pending, history⟩ roots = some (result, roots) := by
  cases action with
  | bindVar name value => exact (notBound name value rfl).elim
  | discard => simp [PackedWorklist.advance, looked] at advanced; simp [advance, looked, ← advanced]
  | decompose pairs => simp [PackedWorklist.advance, looked] at advanced; simp [advance, looked, ← advanced]
  | refuse why => simp [PackedWorklist.advance, looked] at advanced; simp [advance, looked, ← advanced]

namespace Examples

private def pair : Arena := ⟨#[⟨⟨0, 7⟩, 0, 0⟩, ⟨⟨1, 5⟩, 0, 0⟩], #[]⟩

theorem a_binding_moves_both_slots :
    (run 2 (.working ⟨pair, [(0, 1)], []⟩) #[0, 0]).map Prod.snd = some #[1, 1] := by decide +kernel

theorem a_binding_does_not_silently_drop_an_invalid_slot :
    (run 2 (.working ⟨pair, [(0, 1)], []⟩) #[0, 2]).isNone = true := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedRootedWorklist
