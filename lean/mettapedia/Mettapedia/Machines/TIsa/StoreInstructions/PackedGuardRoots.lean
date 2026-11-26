import Mettapedia.Machines.TIsa.StoreInstructions.PackedRemapCoordinates
import Mettapedia.Machines.TIsa.StoreInstructions.PackedWorklist

/-!
# Normalizing the roots that a guard will inspect

Trail entries are stored newest first. Each entry already
names its replacement in the arena of that elimination.
Append-only storage preserves those meanings. Replaying the
trail in chronological order transports the pattern and the
occurrence vector together, using one graph map per binding.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedGuardRoots

open Mettapedia.Logic.LP
open PackedTerms (Arena lookup)
open UnifierHeaders (Symbols)
open PackedSubstitution (Keeps)
open Derivation.FiniteUnifier (Trail readTrail)

structure State where
  arena : Arena
  pattern : Word
  occurrences : Array Word

def applyBinding (state : State) (name replacement : Word) : Option State := do
  let translated ← PackedSubstitution.substitute state.arena name replacement
  let pattern ← translated.mapped[state.pattern.toNat]?
  let occurrences ← PackedSubstitution.translate translated.mapped state.occurrences
  some ⟨translated.target, pattern, occurrences⟩

def State.roots (state : State) : Array Word := #[state.pattern] ++ state.occurrences

/-- Pattern and occurrences can use one array remap; splitting
off the pattern does not call for another graph traversal. -/
theorem applyBinding_uses_one_map (state next : State) (name replacement : Word)
    (result : PackedSubstitution.State)
    (computed : PackedSubstitution.substitute state.arena name replacement = some result)
    (rewritten : applyBinding state name replacement = some next) :
    next.arena = result.target ∧ PackedSubstitution.translate result.mapped state.roots = some next.roots := by
  cases needle : result.mapped[state.pattern.toNat]? with
  | none => simp [applyBinding, computed, needle, bind] at rewritten
  | some pattern =>
    cases directory : PackedSubstitution.translate result.mapped state.occurrences with
    | none => simp [applyBinding, computed, needle, directory, bind] at rewritten
    | some occurrences =>
      simp [applyBinding, computed, needle, directory, bind] at rewritten
      subst next
      constructor
      · rfl
      · obtain ⟨words, read, rfl⟩ := Option.map_eq_some_iff.mp directory
        unfold State.roots PackedSubstitution.translate
        rw [Array.toList_append]
        change ((state.pattern :: state.occurrences.toList).mapM (fun word => result.mapped[word.toNat]?)).map
          List.toArray = some (#[pattern] ++ words.toArray)
        simp only [List.mapM_cons, needle, read, bind, pure, Option.bind_some, Option.map_some]
        exact congrArg some (List.toArray_cons pattern words)

def replay : PackedWorklist.Words → State → Option State
  | [], state => some state
  | (name, replacement) :: older, state =>
    (replay older state).bind fun prior => applyBinding prior name replacement

universe u p
variable {σ : LPSignature.{u,u,p,u}}

inductive Canonical (symbols : Symbols σ) (snapshot : Arena) : PackedWorklist.Words → Trail σ → Prop
  | empty : Canonical symbols snapshot [] []
  | binding {code root : Word} {variableName : σ.vars} {term : Term σ} {raw : PackedWorklist.Words} {trail : Trail σ} :
      symbols.vars.encode variableName = some code →
      lookup symbols snapshot root = some term →
      Canonical symbols snapshot raw trail →
      Canonical symbols snapshot ((code, root) :: raw) ((variableName, term) :: trail)

theorem Canonical.read {symbols : Symbols σ} {snapshot : Arena} {raw : PackedWorklist.Words} {trail : Trail σ}
    (canonical : Canonical symbols snapshot raw trail) :
    PackedWorklist.readTrail symbols snapshot raw = some trail := by
  induction canonical with
  | empty => rfl
  | binding named stored _ older =>
    unfold PackedWorklist.readTrail at older ⊢
    simp only [List.mapM_cons, PackedWorklist.readBinding, (symbols.vars.reads named), stored,
      Option.bind_some, Option.map_some, bind, pure, older]

structure Decodes (symbols : Symbols σ) (state : State) (pattern : Term σ) (occurrences : List (Term σ)) : Prop where
  patternWord : lookup symbols state.arena state.pattern = some pattern
  occurrenceWords : state.occurrences.toList.mapM (lookup symbols state.arena) = some occurrences

/-- Reading one initialized slot and decoding the whole
vector agree at that slot, even if other slots share its handle. -/
theorem Decodes.coordinates {symbols : Symbols σ} {state : State} {pattern : Term σ}
    {occurrences : List (Term σ)} (decoded : Decodes symbols state pattern occurrences) :
    ∃ width : state.occurrences.size = occurrences.length,
      ∀ i : Fin state.occurrences.size,
        lookup symbols state.arena state.occurrences[i] = some (occurrences[i.val]'(width ▸ i.isLt)) := by
  obtain ⟨length, read⟩ := PackedOccursPrefix.mapM_coordinates (lookup symbols state.arena)
    state.occurrences.toList occurrences decoded.occurrenceWords
  have width : state.occurrences.size = occurrences.length := by simpa using length.symm
  refine ⟨width, fun i => ?_⟩
  have exact := read i.val
  rw [Array.getElem?_toList, Array.getElem?_eq_getElem i.isLt, Option.bind_some,
    List.getElem?_eq_getElem (width ▸ i.isLt)] at exact
  exact exact

variable [DecidableEq σ.vars]

private theorem readTrail_suffix (suffix : Subst σ) (trail : Trail σ) :
    readTrail suffix trail = suffix ∘ₛ readTrail (Subst.id σ) trail := by
  induction trail generalizing suffix with
  | nil => simp [readTrail, Subst.comp_id_right]
  | cons first rest ih =>
    change readTrail (suffix ∘ₛ Subst.single first.1 first.2) rest =
      suffix ∘ₛ readTrail (Subst.id σ ∘ₛ Subst.single first.1 first.2) rest
    rw [Subst.comp_id_left, ih (suffix ∘ₛ Subst.single first.1 first.2), ih (Subst.single first.1 first.2)]
    exact Subst.comp_assoc _ _ _

theorem readTrail_cons (variableName : σ.vars) (term : Term σ) (trail : Trail σ) :
    readTrail (Subst.id σ) ((variableName, term) :: trail) =
      Subst.single variableName term ∘ₛ readTrail (Subst.id σ) trail := by
  change readTrail (Subst.id σ ∘ₛ Subst.single variableName term) trail = _
  rw [Subst.comp_id_left, readTrail_suffix]

theorem binding_exact (symbols : Symbols σ) (current : State) (name replacement : Word)
    (variableName : σ.vars) (term pattern : Term σ) (occurrences : List (Term σ))
    (named : symbols.vars.encode variableName = some name) (binding : lookup symbols current.arena replacement = some term)
    (decoded : Decodes symbols current pattern occurrences) (budget : PackedWorklist.Room current.arena) :
    ∃ updated, applyBinding current name replacement = some updated ∧ Keeps symbols current.arena updated.arena ∧
      updated.arena.nodes.size ≤ current.arena.nodes.size + current.arena.nodes.size ∧
      updated.arena.children.size ≤ current.arena.children.size + current.arena.nodes.size * current.arena.children.size ∧
      updated.occurrences.size = current.occurrences.size ∧
      Decodes symbols updated ((Subst.single variableName term).applyTerm pattern)
        (occurrences.map (Subst.single variableName term).applyTerm) := by
  obtain ⟨translated, scanned, represented⟩ :=
    PackedSubstitution.substitute_exact symbols current.arena variableName name replacement term named binding budget.1 budget.2
  have size : translated.mapped.size = current.arena.nodes.size := by simpa using represented.visits
  have lookupMoved (address : Word) (value : Term σ) (loaded : lookup symbols current.arena address = some value) :
      ∃ shifted, translated.mapped[address.toNat]? = some shifted ∧
        lookup symbols translated.target shifted = some ((Subst.single variableName term).applyTerm value) := by
    obtain ⟨_, found⟩ := PackedTermEdges.node_at symbols current.arena address value loaded
    exact represented.translated address (size.symm ▸ (Array.getElem?_eq_some_iff.mp found).choose) value loaded
  obtain ⟨patternWord, patternMapped, loadedPattern⟩ := lookupMoved current.pattern pattern decoded.patternWord
  obtain ⟨newer, mapped, values⟩ := PackedSubstitution.translate_exact
    (lookup symbols current.arena) (lookup symbols translated.target) translated.mapped current.occurrences
    (Subst.single variableName term).applyTerm decoded.occurrenceWords (fun address _ => lookupMoved address)
  have sameWidth := (PackedRemapCoordinates.coordinates translated.mapped current.occurrences newer mapped).1
  refine ⟨⟨translated.target, patternWord, newer⟩, ?_, represented.keeps, ?_, ?_, sameWidth, ⟨loadedPattern, values⟩⟩
  · simp only [applyBinding, scanned, patternMapped, mapped, bind, Option.bind_some]
  · simpa only [size] using represented.nodesUsed
  · simpa only [size] using represented.edgesUsed

/-- A single ordered root vector yields the exact normalized
operands, without coalescing occurrences or touching their
raw identities. The slack is available to the caller after replay. -/
theorem replay_exact (symbols : Symbols σ) (snapshot : Arena) (raw : PackedWorklist.Words) (trail : Trail σ)
    (canonical : Canonical symbols snapshot raw trail) (current : State) (pattern : Term σ) (occurrences : List (Term σ))
    (decoded : Decodes symbols current pattern occurrences) (snapshotHeld : Keeps symbols snapshot current.arena)
    (slack : ℕ) (budget : PackedWorklist.Reserve (raw.length + slack) current.arena.nodes.size current.arena.children.size) :
    ∃ updated, replay raw current = some updated ∧ Keeps symbols snapshot updated.arena ∧
      updated.occurrences.size = current.occurrences.size ∧
      PackedWorklist.Reserve slack updated.arena.nodes.size updated.arena.children.size ∧
      Decodes symbols updated ((readTrail (Subst.id σ) trail).applyTerm pattern)
        (occurrences.map (readTrail (Subst.id σ) trail).applyTerm) := by
  induction canonical generalizing slack with
  | empty =>
    refine ⟨current, rfl, snapshotHeld, rfl, by simpa only [List.length_nil, Nat.zero_add] using budget, ?_⟩
    have identity : (Subst.id σ).applyTerm = id := funext Subst.applyTerm_id
    simpa [readTrail, identity] using decoded
  | @binding name replacement variableName term raw trail named held canonical ih =>
    have earlierBudget : PackedWorklist.Reserve (raw.length + (slack + 1)) current.arena.nodes.size current.arena.children.size := by
      convert budget using 1
      simp [Nat.add_assoc, Nat.add_comm]
    obtain ⟨older, ran, kept, width, available, read⟩ := ih (slack + 1) earlierBudget
    have laterBudget : PackedWorklist.Reserve slack (older.arena.nodes.size + older.arena.nodes.size)
        (older.arena.children.size + older.arena.nodes.size * older.arena.children.size) := available
    obtain ⟨out, steps, preserves, sizeNodes, sizeEdges, sizeWords, result⟩ := binding_exact
      symbols older name replacement variableName term _ _ named (kept replacement term held) read
      (PackedWorklist.reserve_current slack _ _ laterBudget)
    refine ⟨out, ?_, fun address value read => preserves address value (kept address value read), sizeWords.trans width,
      PackedWorklist.reserve_mono slack sizeNodes sizeEdges laterBudget, ?_⟩
    · simp only [replay, ran, Option.bind_some, steps]
    · have commute : (Subst.single variableName term ∘ₛ readTrail (Subst.id σ) trail).applyTerm =
          (Subst.single variableName term).applyTerm ∘ (readTrail (Subst.id σ) trail).applyTerm :=
        funext (Subst.applyTerm_comp _ _)
      simpa only [List.map_map, readTrail_cons, commute, Function.comp_def] using result

namespace Examples

private def snapshot : Arena :=
  ⟨#[⟨⟨0, 7⟩, 0, 0⟩, ⟨⟨1, 9⟩, 0, 0⟩], #[]⟩

theorem two_occurrences_can_share_one_normalized_handle :
    (replay [(7, 1)] ⟨snapshot, 0, #[0, 0]⟩).map (fun out => (out.pattern, out.occurrences)) = some (1, #[1, 1]) := by
  decide +kernel

theorem out_of_range_root_is_not_dropped_from_the_scan :
    (replay [(7, 1)] ⟨snapshot, 0, #[0, 2]⟩).isNone = true := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedGuardRoots
