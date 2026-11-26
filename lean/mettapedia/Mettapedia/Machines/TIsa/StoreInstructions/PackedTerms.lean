import Mettapedia.Machines.TIsa.StoreInstructions.UnifierHeaders

/-!
# A flat arena for finite open terms

A term handle selects a header and a span of child handles.
The child array is shared by all headers. Decoding proceeds in
allocation order, so an application can read only earlier terms.
Symbol words must be canonical in their own kind: equal decoded
heads must compare equal in the native head gate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedTerms

open Mettapedia.Logic.LP
open UnifierHeaders (Header Head Symbols ofTerm)

structure Node where
  header : Header
  childrenAt : Word
  childrenCount : Word
  deriving DecidableEq, Repr

structure Arena where
  nodes : Array Node
  children : Array Word
  deriving Repr

def empty : Arena := ⟨#[], #[]⟩

def segment (edges : Array Word) (node : Node) : Option (Array Word) :=
  let start := node.childrenAt.toNat
  let finish := start + node.childrenCount.toNat
  if finish ≤ edges.size then some (edges.extract start finish) else none

theorem segment_width (edges : Array Word) (node : Node) (words : Array Word)
    (read : segment edges node = some words) :
    words.size = node.childrenCount.toNat ∧ node.childrenAt.toNat + words.size ≤ edges.size := by
  by_cases bounds : node.childrenAt.toNat + node.childrenCount.toNat ≤ edges.size
  · simp only [segment, if_pos bounds] at read
    obtain rfl := Option.some.inj read
    simp only [Array.size_extract, Nat.min_eq_left bounds, Nat.add_sub_cancel_left]
    exact ⟨True.intro, bounds⟩
  · simp [segment, bounds] at read

theorem segment_at (edges : Array Word) (node : Node) (words : Array Word) (i : Fin words.size)
    (read : segment edges node = some words) :
    edges[node.childrenAt.toNat + i.val]? = some words[i] := by
  have stop := (segment_width edges node words read).2
  have bound := i.isLt
  rw [Array.getElem?_eq_getElem (by omega)]
  by_cases valid : node.childrenAt.toNat + node.childrenCount.toNat ≤ edges.size
  · simp only [segment, if_pos valid] at read
    obtain rfl := Option.some.inj read
    exact congrArg some (Array.getElem_extract bound).symm
  · simp [segment, valid] at read

theorem segment_preserved (edges more : Array Word) (node : Node) {children : Array Word}
    (known : segment edges node = some children) : segment (edges ++ more) node = some children := by
  by_cases fits : node.childrenAt.toNat + node.childrenCount.toNat ≤ edges.size
  · simp only [segment, if_pos fits] at known
    have inExtended : node.childrenAt.toNat + node.childrenCount.toNat ≤ (edges ++ more).size := by
      simp only [Array.size_append]
      omega
    have startInside : node.childrenAt.toNat ≤ edges.size := by omega
    simp only [segment, if_pos inExtended]
    rw [Array.extract_append, Nat.sub_eq_zero_of_le fits, Nat.sub_eq_zero_of_le startInside]
    simpa using known
  · simp [segment, fits] at known

universe u p
variable {σ : LPSignature.{u,u,p,u}}

def resolveChildren (decoded : Array (Term σ)) (children : Array Word) : Option (Array (Term σ)) :=
  (children.toList.mapM (fun code => decoded[code.toNat]?)).map List.toArray

def buildHead (decoded : Array (Term σ)) (children : Array Word) : Head σ → Option (Term σ)
  | .var v => if children.isEmpty then some (.var v) else none
  | .const c => if children.isEmpty then some (.const c) else none
  | .app f =>
    match resolveChildren decoded children with
    | none => none
    | some terms =>
      if arity : terms.size = σ.functionArity f then
        some (.app f fun i => terms[i.val]'(arity.symm ▸ i.isLt))
      else none

def build (symbols : Symbols σ) (decoded : Array (Term σ)) (header : Header)
    (children : Array Word) : Option (Term σ) :=
  match symbols.unpack header with
  | none => none
  | some head => if symbols.pack head = some header then buildHead decoded children head else none

private theorem built_head (decoded : Array (Term σ)) (children : Array Word) (head : Head σ)
    {term : Term σ} (found : buildHead decoded children head = some term) : ofTerm term = head := by
  cases head with
  | var v =>
    simp only [buildHead] at found
    split at found
    · obtain rfl := Option.some.inj found; rfl
    · cases found
  | const c =>
    simp only [buildHead] at found
    split at found
    · obtain rfl := Option.some.inj found; rfl
    · cases found
  | app f =>
    simp only [buildHead] at found
    cases resolved : resolveChildren decoded children with
    | none => simp [resolved] at found
    | some terms =>
      by_cases arity : terms.size = σ.functionArity f
      · simp only [resolved, dif_pos arity] at found
        obtain rfl := Option.some.inj found
        rfl
      · simp [resolved, arity] at found

theorem builds_canonical (symbols : Symbols σ) (decoded : Array (Term σ)) (header : Header) (children : Array Word)
    {term : Term σ} (found : build symbols decoded header children = some term) :
    symbols.pack (ofTerm term) = some header := by
  unfold build at found
  cases unpacked : symbols.unpack header with
  | none => simp [unpacked] at found
  | some head =>
    by_cases authentic : symbols.pack head = some header
    · simp only [unpacked, if_pos authentic] at found
      exact (congrArg symbols.pack (built_head decoded children head found)).trans authentic
    · simp [unpacked, authentic] at found

def decodeNode (symbols : Symbols σ) (decoded : Array (Term σ)) (edges : Array Word)
    (node : Node) : Option (Term σ) :=
  match segment edges node with
  | none => none
  | some children => build symbols decoded node.header children

def decodeNodes (symbols : Symbols σ) (edges : Array Word) :
    List Node → Array (Term σ) → Option (Array (Term σ))
  | [], decoded => some decoded
  | node :: rest, decoded =>
    match decodeNode symbols decoded edges node with
    | none => none
    | some term => decodeNodes symbols edges rest (decoded.push term)

def decode (symbols : Symbols σ) (arena : Arena) : Option (Array (Term σ)) :=
  decodeNodes symbols arena.children arena.nodes.toList #[]

theorem decode_empty (symbols : Symbols σ) : decode symbols empty = some #[] := rfl

theorem decoded_size (symbols : Symbols σ) (edges : Array Word) (nodes : List Node)
    (old : Array (Term σ)) {output : Array (Term σ)} (found : decodeNodes symbols edges nodes old = some output) :
    output.size = old.size + nodes.length := by
  induction nodes generalizing old with
  | nil =>
    obtain rfl := Option.some.inj found
    simp
  | cons first rest ih =>
    unfold decodeNodes at found
    cases read : decodeNode symbols old edges first with
    | none => simp [read] at found
    | some term =>
      rw [read] at found
      rw [ih (old.push term) found, Array.size_push, List.length_cons]
      omega

theorem decode_size (symbols : Symbols σ) (arena : Arena) {terms : Array (Term σ)}
    (ready : decode symbols arena = some terms) : terms.size = arena.nodes.size := by
  simpa using decoded_size symbols arena.children arena.nodes.toList #[] ready

private theorem nodes_kept (symbols : Symbols σ) (edges more : Array Word) (nodes : List Node)
    (old output : Array (Term σ)) (known : decodeNodes symbols edges nodes old = some output) :
    decodeNodes symbols (edges ++ more) nodes old = some output := by
  induction nodes generalizing old with
  | nil => exact known
  | cons first rest ih =>
    cases portion : segment edges first with
    | none => simp [decodeNodes, decodeNode, portion] at known
    | some children =>
      have same := segment_preserved edges more first portion
      simp only [decodeNodes, decodeNode, portion] at known
      simp only [decodeNodes, decodeNode, same]
      cases built : build symbols old first.header children with
      | none => simp [built] at known
      | some term =>
        exact ih (old.push term) (by simpa only [built] using known)

private theorem decode_append (symbols : Symbols σ) (edges : Array Word) (first later : List Node)
    (old : Array (Term σ)) :
    decodeNodes symbols edges (first ++ later) old =
      (decodeNodes symbols edges first old).bind (decodeNodes symbols edges later) := by
  induction first generalizing old with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.cons_append, decodeNodes]
    cases decodeNode symbols old edges first with
    | none => rfl
    | some term => exact ih (old.push term)

def CanAppend (arena : Arena) (children : Array Word) : Prop :=
  arena.nodes.size < 2 ^ 64 ∧ arena.children.size + children.size < 2 ^ 64

instance (arena : Arena) (children : Array Word) : Decidable (CanAppend arena children) :=
  inferInstanceAs (Decidable (_ ∧ _))

def newNode (arena : Arena) (header : Header) (children : Array Word) : Node :=
  ⟨header, BitVec.ofNat 64 arena.children.size, BitVec.ofNat 64 children.size⟩

def place (arena : Arena) (header : Header) (children : Array Word) : Arena :=
  ⟨arena.nodes.push (newNode arena header children), arena.children ++ children⟩

def root (arena : Arena) : Word := BitVec.ofNat 64 arena.nodes.size

def append (arena : Arena) (header : Header) (children : Array Word) : Option (Arena × Word) :=
  if CanAppend arena children then some (place arena header children, root arena) else none

theorem new_segment (arena : Arena) (header : Header) (children : Array Word) (fits : CanAppend arena children) :
    segment (arena.children ++ children) (newNode arena header children) = some children := by
  have bound := fits.2
  have start : (BitVec.ofNat 64 arena.children.size).toNat = arena.children.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have count : (BitVec.ofNat 64 children.size).toNat = children.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold segment newNode
  dsimp only
  rw [start, count, if_pos (by rw [Array.size_append]), Array.extract_append_right]
  simp

theorem place_exact (symbols : Symbols σ) (arena : Arena) (stored : Header) (children : Array Word)
    (fits : CanAppend arena children) {old : Array (Term σ)} (ready : decode symbols arena = some old)
    {term : Term σ} (formed : build symbols old stored children = some term) :
    decode symbols (place arena stored children) = some (old.push term) := by
  have grown := nodes_kept symbols arena.children children arena.nodes.toList #[] old ready
  have built : decodeNode symbols old (arena.children ++ children) (newNode arena stored children) = some term := by
    unfold decodeNode
    rw [new_segment arena stored children fits]
    exact formed
  simp only [decode, place, Array.toList_push, decode_append, grown, Option.bind_some]
  simp only [decodeNodes, built]

def lookup (symbols : Symbols σ) (arena : Arena) (handle : Word) : Option (Term σ) :=
  (decode symbols arena).bind (fun terms => terms[handle.toNat]?)

theorem append_result (symbols : Symbols σ) (arena : Arena) (stored : Header) (children : Array Word)
    {extended : Arena} {handle : Word} (made : append arena stored children = some (extended, handle))
    {old : Array (Term σ)} (ready : decode symbols arena = some old)
    {term : Term σ} (formed : build symbols old stored children = some term) :
    lookup symbols extended handle = some term ∧
      ∀ earlier : Word, earlier.toNat < arena.nodes.size → lookup symbols extended earlier = lookup symbols arena earlier := by
  unfold append at made
  split at made
  next fits =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj made)
    have same := place_exact symbols arena stored children fits ready formed
    have count := decode_size symbols arena ready
    constructor
    · have index : (root arena).toNat = old.size := by
        rw [root, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits.1, count]
      rw [lookup, same, Option.bind_some, index, Array.getElem?_push_size]
    · intro earlier bound
      rw [lookup, same, Option.bind_some, lookup, ready, Option.bind_some, Array.getElem?_push]
      exact if_neg (by omega)
  next _ => cases made

theorem prefix_unchanged (symbols : Symbols σ) (edges : Array Word) (nodes : List Node)
    (old out : Array (Term σ)) (done : decodeNodes symbols edges nodes old = some out)
    (index : ℕ) (inside : index < old.size) : out[index]? = old[index]? := by
  induction nodes generalizing old with
  | nil =>
    obtain rfl := Option.some.inj done
    rfl
  | cons front rest ih =>
    cases found : decodeNode symbols old edges front with
    | none => simp [decodeNodes, found] at done
    | some term =>
      have steps : decodeNodes symbols edges rest (old.push term) = some out := by
        simpa only [decodeNodes, found] using done
      have newer : index < (old.push term).size := by simp; omega
      rw [ih (old.push term) steps newer, Array.getElem?_push, if_neg (Nat.ne_of_lt inside)]

private theorem node_canonical (symbols : Symbols σ) (decoded : Array (Term σ)) (edges : Array Word)
    (node : Node) {term : Term σ} (found : decodeNode symbols decoded edges node = some term) :
    symbols.pack (ofTerm term) = some node.header := by
  cases children : segment edges node with
  | none => simp [decodeNode, children] at found
  | some kids => exact builds_canonical symbols decoded node.header kids (by
      simpa only [decodeNode, children] using found)

theorem headers_exact (symbols : Symbols σ) (edges : Array Word) (nodes : List Node)
    (old out : Array (Term σ)) (decoded : decodeNodes symbols edges nodes old = some out)
    (index : ℕ) (node : Node) (term : Term σ) (located : nodes[index]? = some node)
    (readTerm : out[old.size + index]? = some term) : symbols.pack (ofTerm term) = some node.header := by
  induction nodes generalizing old index with
  | nil => simp at located
  | cons front rest ih =>
    cases checked : decodeNode symbols old edges front with
    | none => simp [decodeNodes, checked] at decoded
    | some built =>
      have steps : decodeNodes symbols edges rest (old.push built) = some out := by
        simpa only [decodeNodes, checked] using decoded
      cases index with
      | zero =>
        have sameNode : front = node := Option.some.inj located
        subst node
        have initial : out[old.size]? = (old.push built)[old.size]? :=
          prefix_unchanged symbols edges rest (old.push built) out steps old.size (by simp)
        have sameTerm : built = term := by
          rw [Array.getElem?_push_size] at initial
          exact Option.some.inj (initial.symm.trans readTerm)
        subst term
        exact node_canonical symbols old edges front checked
      | succ index =>
        apply ih (old.push built) steps index located
        show out[(old.push built).size + index]? = some term
        simpa only [Array.size_push, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 index] using readTerm

theorem lookup_header (symbols : Symbols σ) (arena : Arena) (handle : Word) (term : Term σ) (node : Node)
    (found : lookup symbols arena handle = some term) (native : arena.nodes[handle.toNat]? = some node) :
    symbols.pack (ofTerm term) = some node.header := by
  obtain ⟨decoded, ready, selected⟩ := Option.bind_eq_some_iff.mp found
  exact headers_exact symbols arena.children arena.nodes.toList #[] decoded ready handle.toNat node term
    (by simpa using native) (by simpa using selected)

def codebook (decoded : Array (Term σ)) [DecidableEq (Term σ)] :
    PackedOccurrences.Codes (Term σ) where
  encode value :=
    let index := decoded.toList.idxOf value
    if index < decoded.size ∧ index < 2 ^ 64 then some (BitVec.ofNat 64 index) else none
  decode word := decoded[word.toNat]?
  reads := by
    intro value word encoded
    by_cases fits : decoded.toList.idxOf value < decoded.size ∧ decoded.toList.idxOf value < 2 ^ 64
    · have same : BitVec.ofNat 64 (decoded.toList.idxOf value) = word := Option.some.inj (by
        simpa only [if_pos fits] using encoded)
      subst word
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits.2]
      have index : decoded.toList.idxOf value < decoded.toList.length := by simpa using fits.1
      have exact : decoded.toList[decoded.toList.idxOf value]? = some value := by
        rw [List.getElem?_eq_getElem index]
        exact congrArg some (List.getElem_idxOf index)
      simpa using exact
    · change (if _ then _ else _) = some word at encoded
      rw [if_neg fits] at encoded
      cases encoded

end Mettapedia.Machines.TIsa.StoreInstructions.PackedTerms
