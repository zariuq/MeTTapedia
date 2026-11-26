import Mettapedia.Machines.TIsa.StoreInstructions.NativeTermArena
import Mettapedia.Machines.TIsa.StoreInstructions.PackedSubstitution

/-!
# Two initialized views of one append-only term arena

A remap visits a fixed source while its result grows. These
views share physical addresses precisely because neither
published prefix is copied or overwritten.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapSnapshot

open PackedTerms (Arena)
open MemoryBinding (Native)

structure Extension (old new : Arena) : Prop where
  nodes : ∃ extra : Array PackedTerms.Node, new.nodes = old.nodes ++ extra
  edges : ∃ extra : Array Word, new.children = old.children ++ extra

theorem Extension.refl (arena : Arena) : Extension arena arena :=
  ⟨⟨#[], by simp⟩, ⟨#[], by simp⟩⟩

theorem Extension.trans {first second last : Arena} (left : Extension first second) (right : Extension second last) :
    Extension first last := by
  obtain ⟨addedNodes, nodes⟩ := left.nodes
  obtain ⟨moreNodes, more⟩ := right.nodes
  obtain ⟨addedEdges, edges⟩ := left.edges
  obtain ⟨moreEdges, later⟩ := right.edges
  exact ⟨⟨addedNodes ++ moreNodes, by rw [more, nodes, Array.append_assoc]⟩,
    ⟨addedEdges ++ moreEdges, by rw [later, edges, Array.append_assoc]⟩⟩

theorem Extension.node_size {old new : Arena} (extension : Extension old new) : old.nodes.size ≤ new.nodes.size := by
  obtain ⟨tail, extended⟩ := extension.nodes
  rw [extended, Array.size_append]
  omega

theorem Extension.edge_size {old new : Arena} (extension : Extension old new) : old.children.size ≤ new.children.size := by
  obtain ⟨tail, extended⟩ := extension.edges
  rw [extended, Array.size_append]
  omega

theorem Extension.node_at {old new : Arena} (extension : Extension old new) (i : ℕ) (inside : i < old.nodes.size) :
    new.nodes[i]'(inside.trans_le extension.node_size) = old.nodes[i] := by
  obtain ⟨tail, extended⟩ := extension.nodes
  simp only [extended, Array.getElem_append_left inside]

theorem Extension.edge_at {old new : Arena} (extension : Extension old new) (i : ℕ) (inside : i < old.children.size) :
    new.children[i]'(inside.trans_le extension.edge_size) = old.children[i] := by
  obtain ⟨tail, extended⟩ := extension.edges
  simp only [extended, Array.getElem_append_left inside]

theorem place_extends (arena : Arena) (header : UnifierHeaders.Header) (words : Array Word) :
    Extension arena (PackedTerms.place arena header words) :=
  ⟨⟨#[PackedTerms.newNode arena header words], Array.push_eq_append⟩, ⟨words, rfl⟩⟩

theorem append_extends {old new : Arena} {header : UnifierHeaders.Header} {words : Array Word} {handle : Word}
    (added : PackedTerms.append old header words = some (new, handle)) :
    Extension old new := by
  unfold PackedTerms.append at added
  split at added
  · obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj added)
    exact place_extends _ _ _
  · cases added

theorem rewrite_extends (source target : Arena) (mapped : Array Word) (query replacement original : Word)
    {output : Arena} {handle : Word}
    (rewritten : PackedSubstitution.rewrite source target mapped query replacement original = some (output, handle)) :
    Extension target output := by
  unfold PackedSubstitution.rewrite at rewritten
  obtain ⟨node, _, action⟩ := Option.bind_eq_some_iff.mp rewritten
  by_cases variableTag : node.header.tag = 0
  · simp only [if_pos variableTag] at action
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj action)
    exact Extension.refl _
  · by_cases constantTag : node.header.tag = 1
    · simp only [if_neg variableTag, if_pos constantTag] at action
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj action)
      exact Extension.refl _
    · by_cases applicationTag : node.header.tag = 2
      · simp only [if_neg variableTag, if_neg constantTag, if_pos applicationTag] at action
        obtain ⟨words, _, copied⟩ := Option.bind_eq_some_iff.mp action
        obtain ⟨newer, translated, external⟩ := Option.bind_eq_some_iff.mp copied
        by_cases unchanged : newer = words
        · simp only [if_pos unchanged] at external
          obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj external)
          exact Extension.refl _
        · rw [if_neg unchanged] at external
          exact append_extends external
      · simp only [if_neg variableTag, if_neg constantTag, if_neg applicationTag] at action
        cases action

theorem ready_restrict {nodeCapacity edgeCapacity : ℕ} {layout : NativeTermArena.Layout nodeCapacity edgeCapacity}
    {old new : Arena} {before : Native} (extension : Extension old new)
    (source : NativeTermArena.Ready layout new before) :
    NativeTermArena.Ready layout old before := by
  have nodes := extension.node_size.trans source.nodesFit
  have edges := extension.edge_size.trans source.edgesFit
  refine ⟨nodes, edges, ?_, ?_⟩
  · intro i col
    have stored := source.node ⟨i.val, i.isLt.trans_le extension.node_size⟩ col
    change X86PlacedMemory.Reads before ((layout.record ⟨i.val, i.isLt.trans_le nodes⟩).cell col).address
      (NativeTermArena.field (new.nodes[i.val]'(i.isLt.trans_le extension.node_size)) col) at stored
    rw [extension.node_at i.val i.isLt] at stored
    exact stored
  · intro i
    have stored := source.child ⟨i.val, i.isLt.trans_le extension.edge_size⟩
    change X86PlacedMemory.Reads before ((layout.child ⟨i.val, i.isLt.trans_le edges⟩).cell 0).address
      (new.children[i.val]'(i.isLt.trans_le extension.edge_size)) at stored
    rw [extension.edge_at i.val i.isLt] at stored
    exact stored

inductive RewriteCase (source : Arena) (node : PackedTerms.Node) (mapping : Array Word)
    (target : Arena) (original : Word) : Arena → Word → Prop
  | leaf (tag : node.header.tag = 0 ∨ node.header.tag = 1) (handle : Word) :
      RewriteCase source node mapping target original target handle
  | unchanged (children : Array Word) (tag : node.header.tag = 2)
      (span : PackedTerms.segment source.children node = some children)
      (mapped : PackedSubstitution.translate mapping children = some children) :
      RewriteCase source node mapping target original target original
  | changed (children newer : Array Word) (tag : node.header.tag = 2)
      (span : PackedTerms.segment source.children node = some children)
      (mapped : PackedSubstitution.translate mapping children = some newer) (different : newer ≠ children) :
      RewriteCase source node mapping target original
        (PackedTerms.place target node.header newer) (PackedTerms.root target)

theorem rewrite_case (source target : Arena) (mapping : Array Word) (query replacement original : Word)
    {node : PackedTerms.Node} (found : source.nodes[original.toNat]? = some node)
    {next : Arena} {handle : Word}
    (run : PackedSubstitution.rewrite source target mapping query replacement original = some (next, handle)) :
    RewriteCase source node mapping target original next handle := by
  simp only [PackedSubstitution.rewrite, found, bind, Option.bind_some] at run
  by_cases v : node.header.tag = 0
  · rw [if_pos v] at run
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj run)
    exact .leaf (Or.inl v) _
  · by_cases k : node.header.tag = 1
    · rw [if_neg v, if_pos k] at run
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj run)
      exact .leaf (Or.inr k) _
    · have app : node.header.tag = 2 := by
        by_contra nonApp
        rw [if_neg v, if_neg k, if_neg nonApp] at run
        cases run
      rw [if_neg v, if_neg k, if_pos app] at run
      obtain ⟨children, span, later⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨newer, mapped, returned⟩ := Option.bind_eq_some_iff.mp later
      by_cases same : newer = children
      · rw [if_pos same] at returned
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj returned)
        exact .unchanged children app span (same ▸ mapped)
      · rw [if_neg same] at returned
        unfold PackedTerms.append at returned
        split at returned
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj returned)
          exact .changed children newer app span mapped same
        · cases returned

theorem advance_readout (source : Arena) (query replacement : Word) (before after : PackedSubstitution.State)
    (run : PackedSubstitution.advance source query replacement before = some after) :
    ∃ handle, PackedSubstitution.rewrite source before.target before.mapped query replacement
        (BitVec.ofNat 64 before.mapped.size) = some (after.target, handle) ∧
      after.mapped = before.mapped.push handle := by
  obtain ⟨result, rewrite, actual⟩ := Option.bind_eq_some_iff.mp run
  obtain rfl := Option.some.inj actual
  exact ⟨result.2, rewrite, rfl⟩

theorem advance_extends (source : Arena) (query replacement : Word) (before after : PackedSubstitution.State)
    (run : PackedSubstitution.advance source query replacement before = some after) :
    Extension before.target after.target ∧ after.mapped.size = before.mapped.size + 1 := by
  obtain ⟨handle, found, mapped⟩ := advance_readout source query replacement before after run
  exact ⟨rewrite_extends _ _ _ _ _ _ found, by rw [mapped, Array.size_push]⟩

theorem scan_extends (source : Arena) (query replacement : Word) (remaining : ℕ) (before after : PackedSubstitution.State)
    (run : PackedSubstitution.scan source query replacement remaining before = some after) :
    Extension before.target after.target ∧ after.mapped.size = before.mapped.size + remaining := by
  induction remaining generalizing before with
  | zero =>
    obtain rfl := Option.some.inj run
    exact ⟨Extension.refl _, by simp⟩
  | succ n ih =>
    obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨added, newSize⟩ := advance_extends source query replacement before middle first
    obtain ⟨rest, finalSize⟩ := ih middle later
    exact ⟨added.trans rest, by omega⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapSnapshot
