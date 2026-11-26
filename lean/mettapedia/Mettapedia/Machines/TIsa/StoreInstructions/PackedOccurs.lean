import Mettapedia.Machines.TIsa.StoreInstructions.PackedTerms

/-!
# An occurs check on the packed acyclic term graph

For a fixed variable, one bit per allocated node is enough.
Variables compare symbol words, constants contribute false,
and compound terms take the disjunction of their child bits.
The scan never expands a shared subgraph into a tree.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurs

open Mettapedia.Logic.LP
open UnifierHeaders (Header Head Symbols Kind)
open PackedTerms (Arena segment build buildHead decodeNode decodeNodes resolveChildren)

def childrenBits (bits : Array Bool) (children : Array Word) : Option (List Bool) :=
  children.toList.mapM fun code => bits[code.toNat]?

def mark (query : Word) (bits : Array Bool) (header : Header) (children : Array Word) : Option Bool :=
  if header.tag = 0 then some (query == header.symbol)
  else if header.tag = 1 then some false
  else if header.tag = 2 then (childrenBits bits children).map (List.any · id)
  else none

def scan (query : Word) (edges : Array Word) :
    List PackedTerms.Node → Array Bool → Option (Array Bool)
  | [], bits => some bits
  | node :: tail, bits =>
    match segment edges node with
    | none => none
    | some children =>
      match mark query bits node.header children with
      | none => none
      | some found => scan query edges tail (bits.push found)

def find (query : Word) (arena : Arena) (root : Word) : Option Bool :=
  (scan query arena.children arena.nodes.toList #[]).bind (fun bits => bits[root.toNat]?)

private theorem mapM_mapResult {A B C : Type*} (inputs : List A) (read : A → Option B) (map : B → C) :
    (inputs.mapM fun input => (read input).map map) = (inputs.mapM read).map (List.map map) := by
  induction inputs with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.mapM_cons]
    cases answered : read first with
    | none => rfl
    | some before =>
      change ((rest.mapM fun input => (read input).map map).bind (fun later => some (map before :: later))) = _
      rw [ih]
      cases rest.mapM read <;> rfl

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars]

private theorem any_finRange (v : σ.vars) (terms : List (Term σ)) (width : ℕ) (equal : terms.length = width) :
    terms.any (fun term => term.occursIn v) =
      (List.finRange width).any (fun index => (terms[index.val]'(equal.symm ▸ index.isLt)).occursIn v) := by
  subst width
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_finRange, true_and]
  constructor
  · rintro ⟨term, listed, contains⟩
    obtain ⟨index, within, read⟩ := List.getElem_of_mem listed
    exact ⟨⟨index, within⟩, read.symm ▸ contains⟩
  · rintro ⟨index, contains⟩
    exact ⟨terms[index.val], List.getElem_mem index.isLt, contains⟩

private theorem all_children (decoded : Array (Term σ)) (children : Array Word) (v : σ.vars) :
    childrenBits (decoded.map (fun term => term.occursIn v)) children =
      (children.toList.mapM fun code => decoded[code.toNat]?).map (List.map (fun term => term.occursIn v)) := by
  unfold childrenBits
  simp only [Array.getElem?_map]
  exact mapM_mapResult _ _ _

theorem mark_exact (symbols : Symbols σ) (v : σ.vars) (query : Word) (key : symbols.vars.encode v = some query)
    (decoded : Array (Term σ)) (header : Header) (children : Array Word)
    {term : Term σ} (formed : build symbols decoded header children = some term) :
    mark query (decoded.map fun t => t.occursIn v) header children = some (term.occursIn v) := by
  have encoded := PackedTerms.builds_canonical symbols decoded header children formed
  cases term with
  | var name =>
    obtain ⟨word, registered, rfl⟩ := Option.map_eq_some_iff.mp encoded
    have agree : (query == word) = (v == name) :=
      Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, beq_iff_eq]; exact UnifierHeaders.equal_codes symbols.vars key registered)
    simp [mark, Kind.word, Term.occursIn, agree]
  | const name =>
    obtain ⟨word, _, rfl⟩ := Option.map_eq_some_iff.mp encoded
    simp [mark, Kind.word, Term.occursIn]
  | app f arguments =>
    have shape := UnifierHeaders.roundtrip symbols encoded
    have headEncoded : symbols.pack (.app f) = some header := encoded
    have built : buildHead decoded children (.app f) = some (.app f arguments) := by
      simpa only [build, shape, if_pos headEncoded, UnifierHeaders.ofTerm] using formed
    simp only [buildHead] at built
    cases picked : resolveChildren decoded children with
    | none => simp [picked] at built
    | some values =>
      by_cases arity : values.size = σ.functionArity f
      · simp only [picked, dif_pos arity] at built
        have equalTerms := Option.some.inj built
        obtain ⟨word, _, rfl⟩ := Option.map_eq_some_iff.mp encoded
        have ready : (children.toList.mapM (fun code => decoded[code.toNat]?)).map List.toArray = some values := picked
        obtain ⟨terms, read, rfl⟩ := Option.map_eq_some_iff.mp ready
        have native := all_children decoded children v
        rw [read, Option.map_some] at native
        rw [← equalTerms]
        simp only [mark, Kind.word, show (2 : Word) ≠ 0 by decide, show (2 : Word) ≠ 1 by decide,
          if_false, if_true, native, Option.map_some, List.any_map, Function.comp_def, id_eq, Term.occursIn]
        congr 1
        have width : terms.length = σ.functionArity f := arity
        exact any_finRange v terms _ width
      · simp [picked, arity] at built

theorem scan_exact (symbols : Symbols σ) (v : σ.vars) (query : Word) (key : symbols.vars.encode v = some query)
    (edges : Array Word) (nodes : List PackedTerms.Node) (old terms : Array (Term σ))
    (decoded : decodeNodes symbols edges nodes old = some terms) :
    scan query edges nodes (old.map fun t => t.occursIn v) = some (terms.map fun t => t.occursIn v) := by
  induction nodes generalizing old with
  | nil =>
    obtain rfl := Option.some.inj decoded
    rfl
  | cons front rest ih =>
    cases part : segment edges front with
    | none => simp [decodeNodes, decodeNode, part] at decoded
    | some children =>
      cases valid : build symbols old front.header children with
      | none => simp [decodeNodes, decodeNode, part, valid] at decoded
      | some here =>
        have continuation : decodeNodes symbols edges rest (old.push here) = some terms := by
          simpa only [decodeNodes, decodeNode, part, valid] using decoded
        simp only [scan, part, mark_exact symbols v query key old front.header children valid]
        simpa only [Array.map_push] using ih (old.push here) continuation

theorem find_exact (symbols : Symbols σ) (arena : Arena) (v : σ.vars) (query : Word)
    (registered : symbols.vars.encode v = some query) (root : Word) (term : Term σ)
    (known : PackedTerms.lookup symbols arena root = some term) :
    find query arena root = some (term.occursIn v) := by
  obtain ⟨terms, unpacked, read⟩ := Option.bind_eq_some_iff.mp known
  have mapped := scan_exact symbols v query registered arena.children arena.nodes.toList #[] terms unpacked
  simp only [find, Array.map_empty] at mapped ⊢
  rw [mapped, Option.bind_some, Array.getElem?_map, read, Option.map_some]

namespace Examples

private def positive : Arena := ⟨#[⟨⟨0, 9⟩, 0, 0⟩, ⟨⟨2, 1⟩, 0, 1⟩], #[0]⟩

theorem an_occurrence_in_a_child_is_seen : find 9 positive 1 = some true := by decide +kernel
theorem an_unrelated_variable_is_absent : find 7 positive 1 = some false := by decide +kernel

private def cyclic : Arena := ⟨#[⟨⟨2, 1⟩, 0, 1⟩], #[0]⟩

theorem a_forward_link_is_not_a_negative_answer : find 9 cyclic 0 = none := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurs
