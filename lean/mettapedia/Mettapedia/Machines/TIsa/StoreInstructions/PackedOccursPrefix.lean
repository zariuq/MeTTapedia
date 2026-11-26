import Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurs

/-!
# An occurrence check need only visit through the target

Appending to a completed prefix cannot change an earlier mark.
The target's readout can therefore use the prefix ending at its
handle, with storage proportional to that prefix's length.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedOccursPrefix

open Mettapedia.Logic.LP
open PackedOccurs (scan mark)
open PackedTerms (Arena Node segment)

theorem scan_append (query : Word) (edges : Array Word) (first later : List Node) (before : Array Bool) :
    scan query edges (first ++ later) before = (scan query edges first before).bind (scan query edges later) := by
  induction first generalizing before with
  | nil => rfl
  | cons node rest ih =>
    simp only [List.cons_append, scan]
    cases h : segment edges node with
    | none => rfl
    | some children =>
      cases tagged : mark query before node.header children with
      | none => simp [tagged]
      | some bit => simpa only [tagged] using ih (before.push bit)

theorem scan_size (query : Word) (edges : Array Word) (nodes : List Node) (before after : Array Bool)
    (scanned : scan query edges nodes before = some after) :
    after.size = before.size + nodes.length := by
  induction nodes generalizing before with
  | nil =>
    obtain rfl := Option.some.inj scanned
    simp
  | cons node tail ih =>
    unfold scan at scanned
    cases segmentRead : segment edges node with
    | none => simp [segmentRead] at scanned
    | some children =>
      cases result : mark query before node.header children with
      | none => simp [segmentRead, result] at scanned
      | some bit =>
        have length := ih (before.push bit) (by simpa only [segmentRead, result] using scanned)
        simpa only [Array.size_push, List.length_cons, Nat.add_assoc, Nat.add_comm 1 tail.length] using length

theorem scan_keeps (query : Word) (edges : Array Word) (nodes : List Node) (before after : Array Bool)
    (scanned : scan query edges nodes before = some after) (i : ℕ) (inside : i < before.size) :
    after[i]? = before[i]? := by
  induction nodes generalizing before with
  | nil =>
    obtain rfl := Option.some.inj scanned
    rfl
  | cons node tail ih =>
    unfold scan at scanned
    cases segmentRead : segment edges node with
    | none => simp [segmentRead] at scanned
    | some children =>
      cases result : mark query before node.header children with
      | none => simp [segmentRead, result] at scanned
      | some bit =>
        rw [ih (before.push bit) (by simpa only [segmentRead, result] using scanned) (by simp; omega)]
        rw [Array.getElem?_push, if_neg (Nat.ne_of_lt inside)]

theorem mapM_coordinates {A B : Type*} (read : A → Option B) (inputs : List A) (outputs : List B)
    (computed : inputs.mapM read = some outputs) :
    outputs.length = inputs.length ∧ ∀ i : ℕ, (inputs[i]?).bind read = outputs[i]? := by
  induction inputs generalizing outputs with
  | nil =>
    obtain rfl := Option.some.inj computed
    simp
  | cons first rest ih =>
    rw [List.mapM_cons] at computed
    obtain ⟨before, actual, later⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨after, tail, returned⟩ := Option.bind_eq_some_iff.mp later
    obtain rfl := Option.some.inj returned
    obtain ⟨size, coordinates⟩ := ih after tail
    refine ⟨by simp only [List.length_cons, size], fun i => ?_⟩
    cases i with
    | zero => exact actual
    | succ i => exact coordinates i

theorem child_coordinates (marks : Array Bool) (edges : Array Word) (children : List Bool)
    (computed : PackedOccurs.childrenBits marks edges = some children) :
    children.length = edges.size ∧ ∀ (i : Fin edges.size),
      marks[edges[i].toNat]? = children[i.val]? := by
  obtain ⟨width, coordinates⟩ := mapM_coordinates (fun w : Word => marks[w.toNat]?) edges.toList children computed
  refine ⟨by simpa only [Array.length_toList] using width, ?_⟩
  intro i
  have atIndex := coordinates i.val
  rw [Array.getElem?_toList, Array.getElem?_eq_getElem i.isLt, Option.bind_some] at atIndex
  exact atIndex

def findPrefix (query : Word) (arena : Arena) (root : Word) : Option Bool :=
  if root.toNat < arena.nodes.size then
    (scan query arena.children (arena.nodes.toList.take (root.toNat + 1)) #[]).bind fun bits => bits[root.toNat]?
  else none

theorem prefix_marks (query : Word) (arena : Arena) (count : ℕ) (inside : count ≤ arena.nodes.size)
    (marks : Array Bool) (computed : scan query arena.children arena.nodes.toList #[] = some marks) :
    ∃ first, scan query arena.children (arena.nodes.toList.take count) #[] = some first ∧
      first.size = count ∧ ∀ i < count, first[i]? = marks[i]? := by
  rw [← List.take_append_drop count arena.nodes.toList, scan_append] at computed
  obtain ⟨first, found, rest⟩ := Option.bind_eq_some_iff.mp computed
  have size := scan_size query arena.children (arena.nodes.toList.take count) #[] first found
  simp only [Array.size_empty, Nat.zero_add, List.length_take, Array.length_toList, Nat.min_eq_left inside] at size
  exact ⟨first, found, size, fun i inPrefix =>
    (scan_keeps query arena.children (arena.nodes.toList.drop count) first marks rest i (by rwa [size])).symm⟩

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars]

theorem find_prefix_exact (symbols : UnifierHeaders.Symbols σ) (arena : Arena) (v : σ.vars) (query : Word)
    (registered : symbols.vars.encode v = some query) (root : Word) (term : Term σ)
    (known : PackedTerms.lookup symbols arena root = some term) :
    findPrefix query arena root = some (term.occursIn v) := by
  obtain ⟨terms, unpacked, read⟩ := Option.bind_eq_some_iff.mp known
  have within := (Array.getElem?_eq_some_iff.mp read).choose
  rw [PackedTerms.decode_size symbols arena unpacked] at within
  have marked := PackedOccurs.scan_exact symbols v query registered arena.children arena.nodes.toList #[] terms unpacked
  simp only [Array.map_empty] at marked
  obtain ⟨first, found, _, readFirst⟩ := prefix_marks query arena (root.toNat + 1) (by omega) _ marked
  simp only [findPrefix, if_pos within, found, Option.bind_some, readFirst root.toNat (by omega),
    Array.getElem?_map, read, Option.map_some]

namespace Examples

private def separated : Arena :=
  ⟨#[⟨⟨0, 9⟩, 0, 0⟩, ⟨⟨2, 1⟩, 0, 1⟩, ⟨⟨2, 1⟩, 1, 1⟩], #[0, 2]⟩

theorem the_target_needs_no_later_marks : findPrefix 9 separated 1 = some true := by decide +kernel

theorem the_same_forward_link_is_invalid_if_it_is_the_target : findPrefix 9 separated 2 = none := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedOccursPrefix
