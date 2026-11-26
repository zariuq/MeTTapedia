import Mettapedia.Machines.TIsa.StoreInstructions.PackedUnifierAction

/-!
# Substitution with shared older term handles

One elimination translates application edges through the handle map of
earlier terms. It appends a new application only if an edge changed.
The old arena is still available for other work lists and suspensions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedSubstitution

open Mettapedia.Logic.LP
open UnifierHeaders (Header Symbols)
open PackedTerms (Arena Node build buildHead decode lookup resolveChildren segment)
open PackedTermEdges (childTerms)

def translate (mapped : Array Word) (words : Array Word) : Option (Array Word) :=
  (words.toList.mapM (fun address => mapped[address.toNat]?)).map List.toArray

def rewrite (source target : Arena) (mapped : Array Word) (name replacement handle : Word) :
    Option (Arena × Word) := do
  let node ← source.nodes[handle.toNat]?
  if node.header.tag = 0 then
    some (target, if node.header.symbol = name then replacement else handle)
  else if node.header.tag = 1 then some (target, handle)
  else if node.header.tag = 2 then
    let words ← segment source.children node
    let newer ← translate mapped words
    if newer = words then some (target, handle)
    else PackedTerms.append target node.header newer
  else none

universe u p
variable {σ : LPSignature.{u,u,p,u}}

private theorem retarget {A B C D : Type*} (source : A → Option B) (address : A → Option C)
    (target : C → Option D) (move : B → D) (keys : List A) {values : List B}
    (sourceRead : keys.mapM source = some values)
    (known : ∀ key ∈ keys, ∀ value, source key = some value →
      ∃ moved, address key = some moved ∧ target moved = some (move value)) :
    ∃ mapped, keys.mapM address = some mapped ∧ mapped.mapM target = some (values.map move) := by
  induction keys generalizing values with
  | nil =>
    obtain rfl := Option.some.inj sourceRead
    exact ⟨[], rfl, rfl⟩
  | cons first rest ih =>
    rw [List.mapM_cons] at sourceRead
    obtain ⟨value, read, later⟩ := Option.bind_eq_some_iff.mp sourceRead
    obtain ⟨tail, tailRead, returned⟩ := Option.bind_eq_some_iff.mp later
    obtain rfl := Option.some.inj returned
    obtain ⟨moved, addressOf, targetRead⟩ := known first (by simp) value read
    obtain ⟨movedTail, addresses, contents⟩ := ih tailRead
      (fun key mem => known key (List.mem_cons_of_mem _ mem))
    exact ⟨moved :: movedTail, by simp [List.mapM_cons, addressOf, addresses],
      by simp [List.mapM_cons, targetRead, contents]⟩

theorem translate_exact (source target : Word → Option (Term σ)) (mapped words : Array Word)
    (move : Term σ → Term σ) {terms : List (Term σ)} (read : words.toList.mapM source = some terms)
    (mappedReads : ∀ address ∈ words.toList, ∀ term, source address = some term →
      ∃ moved, mapped[address.toNat]? = some moved ∧ target moved = some (move term)) :
    ∃ newer, translate mapped words = some newer ∧
      newer.toList.mapM target = some (terms.map move) := by
  obtain ⟨newer, translated, reads⟩ := retarget source (fun address => mapped[address.toNat]?) target
    move words.toList read mappedReads
  exact ⟨newer.toArray, by simp [translate, translated], by simpa only [List.toList_toArray] using reads⟩

theorem build_application (symbols : Symbols σ) (decoded : Array (Term σ)) (header : Header)
    (words : Array Word) (f : σ.functionSymbols) (args : Fin (σ.functionArity f) → Term σ)
    (canonical : symbols.pack (.app f) = some header)
    (reads : words.toList.mapM (fun address => decoded[address.toNat]?) = some (childTerms (.app f args))) :
    build symbols decoded header words = some (.app f args) := by
  have shape := UnifierHeaders.roundtrip symbols canonical
  have arity : (childTerms (.app f args)).toArray.size = σ.functionArity f := by simp [childTerms]
  have resolved : resolveChildren decoded words = some (childTerms (.app f args)).toArray := by
    simp only [resolveChildren, reads, Option.map_some]
  simp only [build, shape, if_pos canonical, buildHead]
  simp only [resolved, dif_pos arity, Option.some.injEq]
  apply congrArg (Term.app f)
  funext i
  simp [childTerms]

def Keeps (symbols : Symbols σ) (before after : Arena) : Prop :=
  ∀ address value, lookup symbols before address = some value → lookup symbols after address = some value

private theorem mapped_width {A B : Type*} (read : A → Option B) (keys : List A) {values : List B}
    (found : keys.mapM read = some values) : values.length = keys.length := by
  induction keys generalizing values with
  | nil =>
    obtain rfl := Option.some.inj found
    rfl
  | cons first rest ih =>
    rw [List.mapM_cons] at found
    obtain ⟨value, _, later⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨tail, reads, returned⟩ := Option.bind_eq_some_iff.mp later
    obtain rfl := Option.some.inj returned
    simp only [List.length_cons, ih reads]

/-- One postorder substitution step produces the exact substituted term.
The remap of earlier handles covers all edges the instruction can read.
Capacity is charged only for one possible application, not for its tree
expansion. The input arena remains valid after the step. -/
theorem rewrite_exact [DecidableEq σ.vars] (symbols : Symbols σ) (source target : Arena)
    (mapped : Array Word) (v : σ.vars) (name replacement original : Word) (value term : Term σ)
    (named : symbols.vars.encode v = some name)
    (replace : lookup symbols target replacement = some value)
    (existsTerm : lookup symbols source original = some term)
    (extendsSource : Keeps symbols source target)
    (prior : ∀ address, address.toNat < original.toNat → ∀ child,
      lookup symbols source address = some child →
      ∃ moved, mapped[address.toNat]? = some moved ∧
        lookup symbols target moved = some ((Subst.single v value).applyTerm child))
    (capacity : target.nodes.size < 2 ^ 64 ∧
      target.children.size + (childTerms term).length < 2 ^ 64) :
    ∃ next handle, rewrite source target mapped name replacement original = some (next, handle) ∧
      lookup symbols next handle = some ((Subst.single v value).applyTerm term) ∧
      Keeps symbols target next ∧ next.nodes.size ≤ target.nodes.size + 1 ∧
      next.children.size ≤ target.children.size + (childTerms term).length := by
  obtain ⟨node, placed⟩ := PackedTermEdges.node_at symbols source original term existsTerm
  have old := extendsSource original term existsTerm
  have authentic := PackedTerms.lookup_header symbols source original term node existsTerm placed
  cases term with
  | var w =>
    obtain ⟨code, registered, exactHeader⟩ := Option.map_eq_some_iff.mp authentic
    have varTag : node.header.tag = 0 := (congrArg Header.tag exactHeader).symm
    have symbol : node.header.symbol = code := (congrArg Header.symbol exactHeader).symm
    have same := UnifierHeaders.equal_codes symbols.vars registered named
    by_cases equal : w = v
    · refine ⟨target, replacement, ?_, ?_, fun _ _ h => h, by omega, by omega⟩
      · simp [rewrite, placed, varTag, symbol, same.mpr equal]
      · simpa only [Subst.applyTerm, Subst.single, if_pos equal] using replace
    · refine ⟨target, original, ?_, ?_, fun _ _ h => h, by omega, by omega⟩
      · have different : code ≠ name := fun h => equal (same.mp h)
        simp [rewrite, placed, varTag, symbol, different]
      · simpa only [Subst.applyTerm, Subst.single, if_neg equal] using old
  | const c =>
    obtain ⟨_, _, exactHeader⟩ := Option.map_eq_some_iff.mp authentic
    have tag : node.header.tag = 1 := (congrArg Header.tag exactHeader).symm
    exact ⟨target, original, by simp [rewrite, placed, tag], old, fun _ _ h => h, by omega, by omega⟩
  | app f args =>
    let move := (Subst.single v value).applyTerm
    let changed := fun index => move (args index)
    have canonical : symbols.pack (.app f) = some node.header := authentic
    obtain ⟨_, _, exactHeader⟩ := Option.map_eq_some_iff.mp authentic
    have tag : node.header.tag = 2 := (congrArg Header.tag exactHeader).symm
    obtain ⟨words, portion, before, order⟩ := PackedTermEdges.children_before symbols source original f args
      node existsTerm placed
    obtain ⟨newer, retargeted, contents⟩ := translate_exact (lookup symbols source) (lookup symbols target)
      mapped words move before (fun address present => prior address (order address present))
    have changedChildren : (childTerms (.app f args)).map move = childTerms (.app f changed) := by
      simp only [childTerms, List.map_map, Function.comp_def, changed]
    rw [changedChildren] at contents
    obtain ⟨decoded, ready, _⟩ := Option.bind_eq_some_iff.mp replace
    have decodeGet : lookup symbols target = fun address => decoded[address.toNat]? := by
      funext address
      simp only [lookup, ready, Option.bind_some]
    have readNew : build symbols decoded node.header newer = some (.app f changed) :=
      build_application symbols decoded node.header newer f changed canonical (by
        simpa only [decodeGet] using contents)
    by_cases retained : newer = words
    · have originalContents := PackedTermEdges.mapM_keep
        (lookup symbols source) (lookup symbols target) extendsSource words.toList before
      have readOld : build symbols decoded node.header words = some (.app f args) :=
        build_application symbols decoded node.header words f args canonical (by
          simpa only [decodeGet] using originalContents)
      rw [retained] at readNew
      have exactTerm := Option.some.inj (readOld.symm.trans readNew)
      refine ⟨target, original, by simp [rewrite, placed, tag, portion, retargeted, retained],
        ?_, fun _ _ h => h, by omega, by omega⟩
      change lookup symbols target original = some (.app f changed)
      rwa [← exactTerm]
    · have wordsSize : newer.size = (childTerms (.app f args)).length := by
        have width := mapped_width (lookup symbols target) newer.toList contents
        simpa only [← changedChildren, List.length_map, Array.length_toList] using width.symm
      have fits : PackedTerms.CanAppend target newer := ⟨capacity.1, by rw [wordsSize]; exact capacity.2⟩
      let next := PackedTerms.place target node.header newer
      let handle := PackedTerms.root target
      have append : PackedTerms.append target node.header newer = some (next, handle) := if_pos fits
      have result := PackedTerms.append_result symbols target node.header newer append ready readNew
      refine ⟨next, handle, by simp [rewrite, placed, tag, portion, retargeted, retained, append],
        result.1, ?_, by simp [next, PackedTerms.place], by simp [next, PackedTerms.place, wordsSize]⟩
      intro address t located
      obtain ⟨_, read⟩ := PackedTermEdges.node_at symbols target address t located
      exact (result.2 address (Array.getElem?_eq_some_iff.mp read).choose).trans located

theorem child_width_le (symbols : Symbols σ) (arena : Arena) (original : Word) (term : Term σ)
    (read : lookup symbols arena original = some term) : (childTerms term).length ≤ arena.children.size := by
  cases term with
  | var v => simp [childTerms]
  | const c => simp [childTerms]
  | app f args =>
    obtain ⟨node, located⟩ := PackedTermEdges.node_at symbols arena original (.app f args) read
    obtain ⟨words, found, contents⟩ := PackedTermEdges.children_exact symbols arena original f args node read located
    have size := mapped_width (lookup symbols arena) words.toList contents
    by_cases fits : node.childrenAt.toNat + node.childrenCount.toNat ≤ arena.children.size
    · simp only [PackedTerms.segment, if_pos fits] at found
      obtain rfl := Option.some.inj found
      rw [size, Array.length_toList, Array.size_extract]
      omega
    · simp [PackedTerms.segment, fits] at found

structure State where
  target : Arena
  mapped : Array Word
  deriving Repr

def advance (source : Arena) (name replacement : Word) (state : State) : Option State := do
  let (arena, handle) ← rewrite source state.target state.mapped name replacement
    (BitVec.ofNat 64 state.mapped.size)
  some ⟨arena, state.mapped.push handle⟩

def scan (source : Arena) (name replacement : Word) : ℕ → State → Option State
  | 0, state => some state
  | n + 1, state => (advance source name replacement state).bind (scan source name replacement n)

def substitute (arena : Arena) (name replacement : Word) : Option State :=
  scan arena name replacement arena.nodes.size ⟨arena, #[]⟩

structure Prefix (symbols : Symbols σ) (source : Arena) (move : Term σ → Term σ)
    (remaining : ℕ) (state : State) : Prop where
  keeps : Keeps symbols source state.target
  visits : state.mapped.size + remaining = source.nodes.size
  translated : ∀ address : Word, address.toNat < state.mapped.size → ∀ term,
    lookup symbols source address = some term →
    ∃ target, state.mapped[address.toNat]? = some target ∧
      lookup symbols state.target target = some (move term)
  roomInNodes : state.target.nodes.size + remaining < 2 ^ 64
  roomInEdges : state.target.children.size + remaining * source.children.size < 2 ^ 64
  nodesUsed : state.target.nodes.size ≤ source.nodes.size + state.mapped.size
  edgesUsed : state.target.children.size ≤ source.children.size + state.mapped.size * source.children.size

theorem scan_exact [DecidableEq σ.vars] (symbols : Symbols σ) (source : Arena)
    (variableName : σ.vars) (name replacement : Word) (value : Term σ)
    (named : symbols.vars.encode variableName = some name)
    (replacementRead : lookup symbols source replacement = some value)
    (addressable : source.nodes.size < 2 ^ 64) (remaining : ℕ) (current : State)
    (knownPrefix : Prefix symbols source (Subst.single variableName value).applyTerm remaining current) :
    ∃ output, scan source name replacement remaining current = some output ∧
      Prefix symbols source (Subst.single variableName value).applyTerm 0 output := by
  induction remaining generalizing current with
  | zero => exact ⟨current, rfl, knownPrefix⟩
  | succ remaining ih =>
    let address : Word := BitVec.ofNat 64 current.mapped.size
    have cursor : address.toNat = current.mapped.size := by
      have fits : current.mapped.size < 2 ^ 64 := by have visits := knownPrefix.visits; omega
      change (BitVec.ofNat 64 current.mapped.size).toNat = current.mapped.size
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    obtain ⟨terms, decoded, _⟩ := Option.bind_eq_some_iff.mp replacementRead
    have existsTerm : address.toNat < terms.size := by
      rw [cursor, PackedTerms.decode_size symbols source decoded]
      have visits := knownPrefix.visits
      omega
    let term := terms[address.toNat]
    have found : lookup symbols source address = some term := by
      simp only [lookup, decoded, Option.bind_some, Array.getElem?_eq_getElem existsTerm, term]
    have room : current.target.nodes.size < 2 ^ 64 ∧
        current.target.children.size + (childTerms term).length < 2 ^ 64 := by
      have nodes := knownPrefix.roomInNodes
      have edges := knownPrefix.roomInEdges
      rw [Nat.succ_mul] at edges
      have width := child_width_le symbols source address term found
      exact ⟨by omega, by omega⟩
    obtain ⟨arena, moved, ran, movedTerm, keeps, nodeSpace, edgeSpace⟩ := rewrite_exact symbols source
      current.target current.mapped variableName name replacement address value term named
      (knownPrefix.keeps replacement value replacementRead) found knownPrefix.keeps
      (fun earlier less => knownPrefix.translated earlier (cursor ▸ less)) room
    let next : State := ⟨arena, current.mapped.push moved⟩
    have advanced : advance source name replacement current = some next := by
      simp [advance, address, ran, next]
    have nextPrefix : Prefix symbols source (Subst.single variableName value).applyTerm remaining next := by
      constructor
      · intro address value previously
        exact keeps address value (knownPrefix.keeps address value previously)
      · have visits := knownPrefix.visits
        simp only [next, Array.size_push]
        omega
      · intro earlier precedes child accessed
        have inRange : earlier.toNat < current.mapped.size + 1 := by
          simpa only [next, Array.size_push] using precedes
        by_cases atTip : earlier.toNat = current.mapped.size
        · have same : earlier = address := BitVec.eq_of_toNat_eq (atTip.trans cursor.symm)
          subst earlier
          have sameTerm := Option.some.inj (accessed.symm.trans found)
          subst child
          exact ⟨moved, by simp [next, cursor], movedTerm⟩
        · obtain ⟨previous, mapped, meaning⟩ := knownPrefix.translated earlier (by omega) child accessed
          exact ⟨previous, by simp only [next, Array.getElem?_push, if_neg atTip, mapped],
            keeps previous _ meaning⟩
      · have fits := knownPrefix.roomInNodes
        change arena.nodes.size + remaining < 2 ^ 64
        omega
      · have fits := knownPrefix.roomInEdges
        rw [Nat.succ_mul] at fits
        have width := child_width_le symbols source address term found
        change arena.children.size + remaining * source.children.size < 2 ^ 64
        omega
      · have used := knownPrefix.nodesUsed
        simp only [next, Array.size_push]
        omega
      · have used := knownPrefix.edgesUsed
        have width := child_width_le symbols source address term found
        simp only [next, Array.size_push, Nat.add_mul, Nat.one_mul]
        omega
    obtain ⟨output, finished, exact⟩ := ih next nextPrefix
    exact ⟨output, by simp only [scan, advanced, Option.bind_some, finished], exact⟩

/-- A single graph scan implements substitution throughout the arena.
The numeric hypothesis reserves a node and at most the size of the
original edge array per visit; it does not depend on unfolded tree size. -/
theorem substitute_exact [DecidableEq σ.vars] (symbols : Symbols σ) (source : Arena)
    (variableName : σ.vars) (name replacement : Word) (value : Term σ)
    (named : symbols.vars.encode variableName = some name)
    (replacementRead : lookup symbols source replacement = some value)
    (nodeBudget : source.nodes.size + source.nodes.size < 2 ^ 64)
    (edgeBudget : source.children.size + source.nodes.size * source.children.size < 2 ^ 64) :
    ∃ output, substitute source name replacement = some output ∧
      Prefix symbols source (Subst.single variableName value).applyTerm 0 output :=
  scan_exact symbols source variableName name replacement value named replacementRead (by omega)
    source.nodes.size ⟨source, #[]⟩
    ⟨fun _ _ h => h, by simp, fun _ inside => by simp at inside, nodeBudget, edgeBudget, by simp, by simp⟩

def mappedPair (mapping : Array Word) (addresses : Word × Word) : Option (Word × Word) :=
  (mapping[addresses.1.toNat]?).bind fun l => (mapping[addresses.2.toNat]?).map fun r => (l, r)

def remapPending (mapping : Array Word) (pending : List (Word × Word)) : Option (List (Word × Word)) :=
  pending.mapM (mappedPair mapping)

theorem in_completed_mapping (symbols : Symbols σ) (source : Arena) (substitution : Subst σ)
    (final : State) (complete : Prefix symbols source substitution.applyTerm 0 final)
    (address : Word) (term : Term σ) (read : lookup symbols source address = some term) :
    ∃ newer, final.mapped[address.toNat]? = some newer ∧
      lookup symbols final.target newer = some (substitution.applyTerm term) := by
  obtain ⟨_, found⟩ := PackedTermEdges.node_at symbols source address term read
  have kept : final.mapped.size = source.nodes.size := by simpa using complete.visits
  exact complete.translated address (kept ▸ (Array.getElem?_eq_some_iff.mp found).choose) term read

/-- The work list can be rewritten using only the completed handle
map. The original ordering, including duplicate equations, is kept. -/
theorem remap_pending_exact (symbols : Symbols σ) (source : Arena) (substitution : Subst σ)
    (final : State) (complete : Prefix symbols source substitution.applyTerm 0 final)
    (pending : List (Word × Word)) {equations : List (Term σ × Term σ)}
    (known : pending.mapM (PackedUnifierAction.pair (lookup symbols source)) = some equations) :
    ∃ mapped, remapPending final.mapped pending = some mapped ∧
      mapped.mapM (PackedUnifierAction.pair (lookup symbols final.target)) = some (substitution.applyEqs equations) := by
  apply retarget (PackedUnifierAction.pair (lookup symbols source)) (mappedPair final.mapped)
    (PackedUnifierAction.pair (lookup symbols final.target))
    (fun (l, r) => (substitution.applyTerm l, substitution.applyTerm r)) pending known
  intro (left, right) _ eqn read
  unfold PackedUnifierAction.pair at read
  obtain ⟨l, fromLeft, later⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨r, fromRight, rfl⟩ := Option.map_eq_some_iff.mp later
  obtain ⟨newL, relocatedL, termL⟩ := in_completed_mapping symbols source substitution final complete left l fromLeft
  obtain ⟨newR, relocatedR, termR⟩ := in_completed_mapping symbols source substitution final complete right r fromRight
  exact ⟨(newL, newR), by simp [mappedPair, relocatedL, relocatedR],
    by simp [PackedUnifierAction.pair, termL, termR]⟩

namespace Examples

private def arena : Arena :=
  ⟨#[⟨⟨0, 7⟩, 0, 0⟩, ⟨⟨1, 42⟩, 0, 0⟩, ⟨⟨2, 1⟩, 0, 1⟩, ⟨⟨2, 1⟩, 1, 1⟩], #[0, 1]⟩

theorem variable_replacement_keeps_the_old_arena :
    (rewrite arena arena #[] 7 1 0).map (fun pair => (pair.1.nodes.size, pair.2)) = some (4, 1) := by
  decide +kernel

theorem a_changed_application_gets_one_new_handle :
    (rewrite arena arena #[1, 1] 7 1 2).map (fun pair => (pair.1.children, pair.2)) = some (#[0, 1, 1], 4) := by
  decide +kernel

theorem unchanged_application_keeps_its_handle :
    (rewrite arena arena #[1, 1] 7 1 3).map (fun pair => (pair.1.nodes.size, pair.2)) = some (4, 3) := by
  decide +kernel

theorem missing_mapping_is_not_skipped :
    (rewrite arena arena #[] 7 1 3).isNone = true := by decide +kernel

theorem one_scan_shares_unchanged_subterms :
    (substitute arena 7 1).map (fun state => (state.target.nodes.size, state.mapped)) = some (5, #[1, 1, 4, 3]) := by
  decide +kernel

theorem map_does_not_merge_duplicate_equations :
    (substitute arena 7 1).bind (fun state => remapPending state.mapped [(2, 0), (2, 0), (3, 1)]) =
      some [(4, 1), (4, 1), (3, 1)] := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedSubstitution
