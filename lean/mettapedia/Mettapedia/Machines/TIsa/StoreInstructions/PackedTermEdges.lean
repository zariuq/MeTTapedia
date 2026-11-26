import Mettapedia.Machines.TIsa.StoreInstructions.PackedTerms

/-!
# Reading an application's children by packed handles

The child span points into the part of the term arena preceding
the application. The same handles still return those children
after the whole arena has been loaded. Their order and arity
are the ones in the decoded application.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedTermEdges

open Mettapedia.Logic.LP
open UnifierHeaders (Symbols ofTerm)
open PackedTerms (Arena Node segment build buildHead decodeNode decodeNodes resolveChildren lookup)

universe u p
variable {σ : LPSignature.{u,u,p,u}}

def childTerms : Term σ → List (Term σ)
  | .app f arguments => (List.finRange (σ.functionArity f)).map arguments
  | _ => []

theorem node_at (symbols : Symbols σ) (arena : Arena) (handle : Word) (term : Term σ)
    (known : lookup symbols arena handle = some term) :
    ∃ node, arena.nodes[handle.toNat]? = some node := by
  obtain ⟨terms, decoded, addressed⟩ := Option.bind_eq_some_iff.mp known
  have present := (Array.getElem?_eq_some_iff.mp addressed).choose
  rw [PackedTerms.decode_size symbols arena decoded] at present
  exact ⟨arena.nodes[handle.toNat], Array.getElem?_eq_getElem present⟩

private theorem node_prefix (symbols : Symbols σ) (edges : Array Word) (nodes : List Node)
    (old full : Array (Term σ)) (assembled : decodeNodes symbols edges nodes old = some full)
    (index : ℕ) (node : Node) (term : Term σ) (located : nodes[index]? = some node)
    (resolved : full[old.size + index]? = some term) :
    ∃ earlier : Array (Term σ), earlier.size = old.size + index ∧
      decodeNode symbols earlier edges node = some term ∧
      ∀ i : ℕ, i < earlier.size → full[i]? = earlier[i]? := by
  induction nodes generalizing old index with
  | nil => simp at located
  | cons front rest ih =>
    cases read : decodeNode symbols old edges front with
    | none => simp [decodeNodes, read] at assembled
    | some head =>
      have further : decodeNodes symbols edges rest (old.push head) = some full := by
        simpa only [decodeNodes, read] using assembled
      cases index with
      | zero =>
        have raw : front = node := Option.some.inj located
        subst node
        have stays := PackedTerms.prefix_unchanged symbols edges rest (old.push head) full further old.size (by simp)
        rw [Array.getElem?_push_size] at stays
        have exact : head = term := Option.some.inj (stays.symm.trans resolved)
        subst term
        refine ⟨old, by simp, read, fun i inside => ?_⟩
        have retained := PackedTerms.prefix_unchanged symbols edges rest (old.push head) full further i (by simp; omega)
        rwa [Array.getElem?_push, if_neg (Nat.ne_of_lt inside)] at retained
      | succ index =>
        have offset : (old.push head).size + index = old.size + (index + 1) := by
          rw [Array.size_push]; omega
        obtain ⟨earlier, size, found, stays⟩ := ih (old.push head) further index located (by rwa [offset])
        exact ⟨earlier, size.trans offset, found, stays⟩

theorem mapM_keep {A B : Type*} (before after : A → Option B)
    (kept : ∀ key value, before key = some value → after key = some value) (keys : List A)
    {values : List B} (found : keys.mapM before = some values) : keys.mapM after = some values := by
  induction keys generalizing values with
  | nil => exact found
  | cons first rest ih =>
    rw [List.mapM_cons] at found
    obtain ⟨value, read, later⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨values', restRead, returned⟩ := Option.bind_eq_some_iff.mp later
    simp only [List.mapM_cons, kept first value read, bind, Option.bind_some, ih restRead]
    exact returned

private theorem list_from_array (terms : List (Term σ)) (arity : ℕ) (length : terms.length = arity) :
    (List.finRange arity).map (fun i => terms.toArray[i.val]'(length.symm ▸ i.isLt)) = terms := by
  subst arity
  exact List.map_get_finRange terms

private theorem build_application (symbols : Symbols σ) (earlier : Array (Term σ)) (node : Node)
    (words : Array Word) (f : σ.functionSymbols) (args : Fin (σ.functionArity f) → Term σ)
    (finished : build symbols earlier node.header words = some (.app f args)) :
    (words.toList.mapM fun code => earlier[code.toNat]?) = some (childTerms (.app f args)) := by
  have authentically := PackedTerms.builds_canonical symbols earlier node.header words finished
  have canonical : symbols.pack (.app f) = some node.header := authentically
  have tag := UnifierHeaders.roundtrip symbols canonical
  have expanded : buildHead earlier words (.app f) = some (.app f args) := by
    simpa only [build, tag, if_pos canonical] using finished
  unfold buildHead at expanded
  cases collected : resolveChildren earlier words with
  | none => simp [collected] at expanded
  | some values =>
    by_cases arity : values.size = σ.functionArity f
    · simp only [collected, dif_pos arity] at expanded
      have exact := congrArg childTerms (Option.some.inj expanded)
      obtain ⟨children, valuesRead, rfl⟩ := Option.map_eq_some_iff.mp collected
      change (List.finRange (σ.functionArity f)).map (fun i => children.toArray[i.val]'_) =
        childTerms (.app f args) at exact
      rw [list_from_array children _ arity] at exact
      rw [← exact]
      exact valuesRead
    · simp [collected, arity] at expanded

theorem mapM_exists_of_mem {A B : Type*} (read : A → Option B) (keys : List A)
    {values : List B} (found : keys.mapM read = some values) (key : A) (inKeys : key ∈ keys) :
    ∃ value, read key = some value := by
  induction keys generalizing values with
  | nil => simp at inKeys
  | cons first rest ih =>
    rw [List.mapM_cons] at found
    obtain ⟨value, now, later⟩ := Option.bind_eq_some_iff.mp found
    rw [List.mem_cons] at inKeys
    rcases inKeys with rfl | occurs
    · exact ⟨value, now⟩
    · obtain ⟨_, continues, _⟩ := Option.bind_eq_some_iff.mp later
      exact ih continues occurs

/-- Every edge of a successfully decoded application is strictly
backward. The same ordered span can be interpreted through the full
decoded arena without changing any child. -/
theorem children_before (symbols : Symbols σ) (arena : Arena) (handle : Word)
    (f : σ.functionSymbols) (arguments : Fin (σ.functionArity f) → Term σ) (node : Node)
    (found : lookup symbols arena handle = some (.app f arguments))
    (located : arena.nodes[handle.toNat]? = some node) :
    ∃ words, segment arena.children node = some words ∧
      words.toList.mapM (lookup symbols arena) = some (childTerms (.app f arguments)) ∧
      (∀ address ∈ words.toList, address.toNat < handle.toNat) := by
  obtain ⟨full, assembled, resolved⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨earlier, size, readNode, kept⟩ := node_prefix symbols arena.children arena.nodes.toList #[] full assembled
    handle.toNat node (.app f arguments) (by simpa using located) (by simpa using resolved)
  cases children : segment arena.children node with
  | none => simp [decodeNode, children] at readNode
  | some words =>
    have wordRead := build_application symbols earlier node words f arguments (by
      simpa only [decodeNode, children] using readNode)
    refine ⟨words, rfl, ?_, ?_⟩
    · apply mapM_keep (fun code : Word => earlier[code.toNat]?) (lookup symbols arena) ?_ words.toList wordRead
      intro address value here
      have bounds := (Array.getElem?_eq_some_iff.mp here).choose
      simpa only [lookup, assembled, Option.bind_some, kept address.toNat bounds] using here
    · intro address mem
      obtain ⟨_, accessed⟩ := mapM_exists_of_mem (fun code : Word => earlier[code.toNat]?) words.toList wordRead address mem
      have bounds := (Array.getElem?_eq_some_iff.mp accessed).choose
      simpa only [size, Array.size_empty, Nat.zero_add] using bounds

theorem children_exact (symbols : Symbols σ) (arena : Arena) (handle : Word)
    (f : σ.functionSymbols) (arguments : Fin (σ.functionArity f) → Term σ) (node : Node)
    (found : lookup symbols arena handle = some (.app f arguments))
    (located : arena.nodes[handle.toNat]? = some node) :
    ∃ words, segment arena.children node = some words ∧
      words.toList.mapM (lookup symbols arena) = some (childTerms (.app f arguments)) := by
  obtain ⟨words, segmentRead, children, _⟩ := children_before symbols arena handle f arguments node found located
  exact ⟨words, segmentRead, children⟩

end Mettapedia.Machines.TIsa.StoreInstructions.PackedTermEdges
