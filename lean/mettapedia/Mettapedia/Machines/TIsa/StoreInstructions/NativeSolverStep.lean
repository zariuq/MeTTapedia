import Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverImage

/-!
# One fetched transition of the packed finite unifier

The boundaries of the emitted loop represent working,
solved, and inconsistent states. The load-time and capacity
exits are separate from both logical forms of inconsistency.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverStep

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls footprint)
open NativeArenaGeometry (Region)
open NativeTrailReserve (Descriptor)
open NativeSolverImage (Exits Placed targets bind_target)
open NativeBindingStep (Live)
open NativeBindingMemory (Geometry)
open NativeAgendaLoop (Within)
open NativeSubstitutionMemory (Includes)
open PackedWorklist (Worklist Words)
open PackedEquations (Arena readWords)
open PackedUnifierAction (Encoded)
open Derivation.FiniteUnifier (Conflict)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Outcome := PackedWorklist.State

def arenaOf : Outcome → Option PackedTerms.Arena
  | .working work => some work.arena
  | .solved terms _ => some terms
  | .inconsistent _ => none

def Extends (before : PackedTerms.Arena) (after : Outcome) : Prop :=
  ∀ next, arenaOf after = some next → NativeRemapSnapshot.Extension before next

private theorem extends_self {before : PackedTerms.Arena} {after : Outcome}
    (same : arenaOf after = some before) : Extends before after := by
  intro seen result
  obtain rfl := Option.some.inj (same.symm.trans result)
  exact NativeRemapSnapshot.Extension.refl _

private theorem extends_failure (before : PackedTerms.Arena) (why : Conflict) : Extends before (.inconsistent why) :=
  fun _ impossible => nomatch impossible

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register :=
  NativeBindingStep.clobbers ∪ NativeBindingSelection.clobbers ∪ (NativeAgendaDispatch.clobbers ∪ NativeDecompose.clobbers)

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def Route (chosen : UnifierHeaders.Exit) : Encoded → Prop
  | .discard => chosen = .discard
  | .decompose _ => chosen = .expand
  | .refuse .heads => chosen = .clash
  | .refuse .occurs | .bindVar _ _ => ∃ side : NativeBindEntry.Side, chosen = side.exiting

private theorem binding_route (terms : PackedTerms.Arena) (name value : Word) (side : NativeBindEntry.Side)
    (act : Encoded) (found : PackedUnifierAction.binding terms name value = some act) :
    Route side.exiting act := by
  unfold PackedUnifierAction.binding at found
  obtain ⟨observed, _, result⟩ := Option.map_eq_some_iff.mp found
  obtain rfl := result
  cases observed <;> exact ⟨side, rfl⟩

theorem route (terms : PackedTerms.Arena) (left right : Word) (act : Encoded)
    (examined : PackedUnifierAction.inspect terms left right = some act) :
    Route (NativeTermDispatch.choose terms left right) act := by
  unfold PackedUnifierAction.inspect at examined
  obtain ⟨l, locatedL, rest⟩ := Option.bind_eq_some_iff.mp examined
  obtain ⟨r, locatedR, resulting⟩ := Option.bind_eq_some_iff.mp rest
  simp only [NativeTermDispatch.choose, locatedL, locatedR]
  generalize chosen : UnifierHeaders.dispatch l.header r.header = exit at resulting ⊢
  cases exit with
  | malformed => cases resulting
  | discard => obtain rfl := Option.some.inj resulting; rfl
  | clash => obtain rfl := Option.some.inj resulting; rfl
  | bindLeft => exact binding_route terms l.header.symbol right .left act resulting
  | bindRight => exact binding_route terms r.header.symbol left .right act resulting
  | expand =>
    obtain ⟨ls, _, more⟩ := Option.bind_eq_some_iff.mp resulting
    obtain ⟨rs, _, returned⟩ := Option.bind_eq_some_iff.mp more
    split at returned
    · obtain rfl := Option.some.inj returned
      rfl
    · cases returned

def agendaDemand (remaining : Words) : Encoded → ℕ
  | .decompose pairs => pairs.length
  | .bindVar _ _ => remaining.length
  | _ => 0

def trailDemand : Encoded → ℕ
  | .bindVar _ _ => 1
  | _ => 0

def mapDemand (terms : PackedTerms.Arena) : Encoded → ℕ
  | .bindVar _ _ | .refuse .occurs => terms.nodes.size
  | _ => 0

variable {nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Descriptor}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {exits : Exits}

inductive Writes (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Descriptor)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc) : Finset ℕ → Prop
  | idle : Writes term map frame agenda trail ∅
  | graph {bytes : Finset ℕ} : Includes term map frame.substitution bytes → Writes term map frame agenda trail bytes
  | pending {lo hi : ℕ} {bytes : Finset ℕ} : Within agenda lo hi bytes → Writes term map frame agenda trail bytes
  | binding {lo hi : ℕ} {bytes : Finset ℕ} : Within trail lo hi bytes → Writes term map frame agenda trail bytes
  | header : Writes term map frame agenda trail (NativeBindingPublish.header agenda)
  | trailHeader : Writes term map frame agenda trail (NativeBindingPublish.header trail)
  | headers : Writes term map frame agenda trail (NativeBindingPublish.written agenda trail)
  | union {left right : Finset ℕ} : Writes term map frame agenda trail left → Writes term map frame agenda trail right →
      Writes term map frame agenda trail (left ∪ right)

structure Resident (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Descriptor)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc)
    (work : Worklist) (native : Native) where
  equations : Arena
  bindings : Arena
  root : Word
  live : Live term map frame agenda trail work.arena equations root bindings native
  pending : readWords equations root = some work.pending
  history : readWords bindings (NativeBindingTrail.root bindings) = some work.trail

def conflictAt (exits : Exits) : Conflict → ℕ
  | .heads => exits.heads
  | .occurs => exits.cycle

def Arrived (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Descriptor)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc)
    (image : NativeImage.View) (base : BitVec 48) (start : ℕ) (exits : Exits) (agendaUsed trailUsed : ℕ)
    (native : Native) : Outcome → Prop
  | .working work => ∃ resident : Resident term map frame agenda trail work native,
      resident.equations.size = agendaUsed ∧ resident.bindings.size = trailUsed ∧ Nonempty (At image native base start)
  | .solved terms bindings => ∃ packed : Arena, NativeTermArena.Ready term terms native ∧
      NativeAgendaRecords.Ready trail packed native ∧
      readWords packed (NativeBindingTrail.root packed) = some bindings ∧
      NativeSubstitutionFrame.Ready term map frame.substitution terms native ∧ NativeBindingStep.Aux term frame agenda trail native ∧
      lookup native 12 = some 0 ∧ lookup native 13 = some 1 ∧ Nonempty (At image native base exits.solved)
  | .inconsistent why => Nonempty (At image native base (conflictAt exits why))

private theorem decomposition_space (space : Geometry term map frame agenda trail image base) :
    NativeDecompose.Geometry agenda term image base := by
  have sepNodes := space.substitute.agendaNode
  have sepEdges := space.substitute.agendaEdge
  have publish := space.publishGeometry
  refine ⟨⟨space.agendaCode, ?_, ?_⟩, space.agendaHeader, ?_, ?_⟩
  · intro i j d col
    exact (agenda.words.separate_arenas term.nodes sepNodes (3 * (d.val + 1)) 3 (4 * i.val) 4
      (by decide) (by decide) (by have := d.isLt; omega) (by have := i.isLt; omega)
      (by decide) (by decide) col j).symm
  · intro i d col
    exact (agenda.words.separate_arenas term.edges sepEdges (3 * (d.val + 1)) 3 i.val 1
      (by decide) (by decide) (by have := d.isLt; omega) i.isLt (by decide) (by decide) col 0).symm
  · exact fun i j => (Finset.disjoint_union_right.mp (publish.node i j)).2
  · exact fun i => (Finset.disjoint_union_right.mp (publish.edge i)).2

private theorem Live.after_expand (space : Geometry term map frame agenda trail image base)
    {terms : PackedTerms.Arena} {old updated bindings : Arena} {priorRoot nextRoot : Word} {before after : Native}
    (live : Live term map frame agenda trail terms old priorRoot bindings before)
    (next : NativeAgendaDispatch.Context agenda term updated terms nextRoot after)
    {writes : Finset ℕ} (confined : Within agenda old.size updated.size writes)
    (run : X86StateFrame.Frame (NativeAgendaDispatch.clobbers ∪ NativeDecompose.clobbers)
      (writes ∪ NativeBindingPublish.header agenda) before after) :
    Live term map frame agenda trail terms updated nextRoot bindings after := by
  have descriptor (i : Fin 8) : Disjoint (footprint (frame.cell i).address) (writes ∪ NativeBindingPublish.header agenda) :=
    Finset.disjoint_union_right.mpr ⟨NativePendingFill.Within.separate confined _ (fun j col _ _ =>
      NativeBindingMemory.frame_record space.agendaFrame i j col), NativeBindingMemory.frame_header space.agendaFrame i⟩
  have trailHeader : Disjoint (NativeBindingPublish.header trail) writes := by
    apply NativePendingFill.Within.separate confined
    intro i col _ _
    exact (NativeBindingMemory.record_header_apart space.trailAgenda.symm i col).symm
  have trailRecord (i : Fin tc) (j : Fin 3) :
      Disjoint (footprint ((trail.record i).cell j).address) writes := by
    apply NativePendingFill.Within.separate confined
    intro k col _ _
    exact trail.words.separate_arenas agenda.words space.trailAgenda (3 * (i.val + 1)) 3 (3 * (k.val + 1)) 3
      (by decide) (by decide) (by have := i.isLt; omega) (by have := k.isLt; omega) (by decide) (by decide) j col
  refine ⟨next, live.staged.kept run (by decide) (fun i => by rw [frame.substitution_cell]; exact descriptor _),
    ⟨live.trailReady.fits,
      live.trailReady.count.preserved run (Finset.disjoint_union_right.mpr ⟨trailHeader,
        NativeBindingMemory.header_apart space.trailAgenda⟩),
      fun i j => (live.trailReady.node i j).preserved run (Finset.disjoint_union_right.mpr ⟨trailRecord _ j,
        NativeBindingMemory.record_header_apart space.trailAgenda _ j⟩)⟩, ?_⟩
  exact ⟨live.aux.pool.preserved run (Finset.disjoint_union_right.mpr ⟨NativeBindingMemory.meta_kept 1 confined,
      NativeBindingMemory.meta_immutable agenda 1 (by decide)⟩),
    live.aux.agendaLimit.preserved run (Finset.disjoint_union_right.mpr ⟨NativeBindingMemory.meta_kept 2 confined,
      NativeBindingMemory.meta_immutable agenda 2 (by decide)⟩),
    live.aux.trailLimit.preserved run (Finset.disjoint_union_right.mpr ⟨NativeBindingMemory.meta_apart space.trailAgenda 2 confined,
      NativeBindingMemory.meta_header_apart space.trailAgenda 2⟩),
    live.aux.trailPtr.preserved run (descriptor 7)⟩

private theorem fetched_pop (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {before : Native} (code : NativeSolverImage.CorePlaced image start exits) (point : At image before base start) (controls : Controls before)
    (terms : PackedTerms.Arena) (equations : Arena) (root left right : Word) (pending : Words)
    (live : NativeAgendaDispatch.Context agenda term equations terms root before)
    (held : readWords equations root = some ((left, right) :: pending)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps older, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame NativeAgendaDispatch.clobbers ∅ before after ∧
      lookup after 11 = some older ∧ readWords equations older = some pending ∧
      Nonempty (At image after base ((targets start exits).at (NativeTermDispatch.choose terms left right))) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨node, selected, both, tail⟩ := NativeAgendaRecords.top_of_read equations root ((left, right) :: pending) held
  obtain ⟨a, ran, framed, out⟩ := NativeAgendaDispatch.fetched other extra vector point controls code.dispatch live
  simp only [NativeAgendaDispatch.Arrival, selected] at out
  obtain ⟨cursor, _, _, _, ⟨hopped⟩⟩ := out
  rw [(Prod.mk.inj both).1, (Prod.mk.inj both).2] at hopped
  exact ⟨a, _, node.older, ran, framed, cursor, tail, ⟨hopped⟩⟩

theorem fetched_empty (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {before : Native} (code : NativeSolverImage.CorePlaced image start exits) (point : At image before base start) (controls : Controls before)
    (terms : PackedTerms.Arena) (history : Words)
    (physical : Resident term map frame agenda trail ⟨terms, [], history⟩ before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      lookup after 13 = lookup before 13 ∧
      Arrived term map frame agenda trail image base start exits physical.equations.size physical.bindings.size after (.solved terms history) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have empty := NativeAgendaRecords.top_of_read physical.equations physical.root [] physical.pending
  obtain ⟨after, ran, framed, arrived⟩ :=
    NativeAgendaDispatch.fetched other extra vector point controls code.dispatch physical.live.dispatch
  simp only [NativeAgendaDispatch.Arrival, empty] at arrived
  rw [NativeAgendaDispatch.cost, empty, Nat.add_zero, NativeAgendaRead.cost_empty _ _ empty] at ran
  exact ⟨after, ran, framed.mono (by decide) (Finset.Subset.refl _), framed.lookup 13 (by decide), physical.bindings,
    physical.live.dispatch.termReady.preserved framed, physical.live.trailReady.preserved framed,
    physical.history, physical.live.staged.preserved framed (by decide), physical.live.aux.preserved framed,
    (framed.lookup 12 (by decide)).trans physical.live.dispatch.zero,
    (framed.lookup 13 (by decide)).trans physical.live.dispatch.one, arrived.2⟩

structure Room (nc ec mc ac tc : ℕ) (terms : PackedTerms.Arena) (agendaUsed trailUsed : ℕ)
    (pending : Words) (action : Encoded) (result : Outcome) : Prop where
  nodes : PackedWorklist.nodeCount result ≤ nc
  edges : PackedWorklist.edgeCount result ≤ ec
  map : mapDemand terms action ≤ mc
  agenda : agendaUsed + agendaDemand pending action ≤ ac
  trail : trailUsed + trailDemand action ≤ tc

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

abbrev Transition (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Descriptor)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc)
    (image : NativeImage.View) (base : BitVec 48) (start : ℕ) (exits : Exits)
    (before : Native) (terms : PackedTerms.Arena) (a t : ℕ)
    (result : Outcome) : Prop :=
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers bytes before after ∧ Writes term map frame agenda trail bytes ∧
      NativeTermArena.Ready term terms after ∧ Extends terms result ∧
      lookup after 13 = some 1 ∧
      Arrived term map frame agenda trail image base start exits (a)
        (t) after result

/-- The shared dispatch runs every branch that does not
install a new binding, with or without retained roots. -/
theorem fetched_other (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {before : Native} (code : NativeSolverImage.CorePlaced image start exits) (point : At image before base start) (controls : Controls before)
    (space : Geometry term map frame agenda trail image base)
    (terms : PackedTerms.Arena) (left right : Word) (pending history : Words)
    (resident : Resident term map frame agenda trail ⟨terms, (left, right) :: pending, history⟩ before)
    (symbols : UnifierHeaders.Symbols σ) (lTerm rTerm : Term σ)
    (leftRead : PackedTerms.lookup symbols terms left = some lTerm) (rightRead : PackedTerms.lookup symbols terms right = some rTerm)
    (action : Encoded) (examined : PackedUnifierAction.inspect terms left right = some action) (result : Outcome)
    (advanced : PackedWorklist.advance ⟨terms, (left, right) :: pending, history⟩ = some result)
    (bounds : Room nc ec mc ac tc terms resident.equations.size resident.bindings.size pending action result)
    (noBind : ∀ name value, action ≠ .bindVar name value) :
    Transition other extra vector term map frame agenda trail image base start exits before terms
      (resident.equations.size + agendaDemand pending action) (resident.bindings.size + trailDemand action) result := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have actual := route terms left right action examined
  let ordinary := resident.live.dispatch
  cases action with
  | discard =>
    have same : PackedWorklist.State.working ⟨terms, pending, history⟩ = result := by
      apply Option.some.inj
      simpa [PackedWorklist.advance, examined] using advanced
    subst result
    obtain ⟨after, steps, older, ran, readFrame, cursor, tail, ⟨atDiscard⟩⟩ :=
      fetched_pop other extra vector code point controls terms resident.equations resident.root left right pending ordinary resident.pending
    have resumes : At image after base start := by
      simpa only [show NativeTermDispatch.choose terms left right = .discard from actual, NativeTermDispatch.Targets.at,
        NativeSolverImage.targets] using atDiscard
    have next : Live term map frame agenda trail terms resident.equations older resident.bindings after :=
      ⟨ordinary.next readFrame cursor, resident.live.staged.preserved readFrame (by decide),
        resident.live.trailReady.preserved readFrame, resident.live.aux.preserved readFrame⟩
    exact ⟨after, steps, ∅, ran, readFrame.mono (by decide) (Finset.Subset.refl _), .idle,
      next.dispatch.termReady, extends_self rfl, next.dispatch.one,
      ⟨⟨resident.equations, resident.bindings, older, next, tail, resident.history⟩, by simp [agendaDemand],
        by simp [trailDemand], ⟨resumes⟩⟩⟩
  | decompose pairs =>
    obtain ⟨after, steps, ran, outcome⟩ := NativeDecompose.fetched_expansion other extra vector point controls
      code.dispatch code.expand (decomposition_space space) resident.equations resident.root left right ordinary
      resident.live.aux.pool resident.live.aux.agendaLimit pending history pairs resident.pending examined
    rw [if_pos (show resident.equations.size + pairs.length ≤ ac from bounds.agenda)] at outcome
    obtain ⟨updated, nextRoot, writes, _, framed, confined, size, remapped, spec, next, atEntry⟩ := outcome
    obtain rfl := Option.some.inj (spec.symm.trans advanced)
    exact ⟨after, steps, _, ran, framed.mono (by decide) (Finset.Subset.refl _),
      .union (.pending confined) .header, next.termReady, extends_self rfl, next.one,
      ⟨⟨updated, resident.bindings, nextRoot, Live.after_expand space resident.live next confined framed,
        remapped, resident.history⟩, size, by simp [trailDemand], atEntry⟩⟩
  | refuse reason =>
    have same : PackedWorklist.State.inconsistent reason = result := by
      apply Option.some.inj
      simpa [PackedWorklist.advance, examined] using advanced
    subst result
    cases reason with
    | heads =>
      obtain ⟨after, steps, _, ran, readFrame, _, _, ⟨atConflict⟩⟩ :=
        fetched_pop other extra vector code point controls terms resident.equations resident.root left right pending ordinary resident.pending
      have clash : At image after base exits.heads := by
        simpa only [show NativeTermDispatch.choose terms left right = .clash from actual, NativeTermDispatch.Targets.at,
          NativeSolverImage.targets] using atConflict
      exact ⟨after, steps, ∅, ran, readFrame.mono (by decide) (Finset.Subset.refl _), .idle,
        ordinary.termReady.preserved readFrame, extends_failure terms .heads,
        (readFrame.lookup 13 (by decide)).trans ordinary.one, ⟨clash⟩⟩
    | occurs =>
      obtain ⟨side, chosen⟩ := actual
      let desc := NativeSubstitutionFrame.scratchDescriptor frame.substitution
      have env : NativeBindEntry.Environment term terms agenda map desc before :=
        ⟨ordinary.termReady, ordinary.termBase, ordinary.agendaBase, resident.live.aux.pool,
          (NativeSubstitutionFrame.scratch_pointer frame.substitution).symm ▸ resident.live.staged.pointer,
          resident.live.staged.scratch_base, resident.live.staged.scratch_size, ordinary.zero, ordinary.one, ordinary.two⟩
      have sideCode : NativeBindEntry.EntryPlaced image side ((targets start exits).at side.exiting) (NativeSolverImage.shared start) := by
        rw [bind_target]; exact code.bind side
      obtain ⟨choice, after, steps, ran, tested⟩ :=
        NativeBindingSelection.fetched_binding other extra vector point controls side code.dispatch sideCode code.gate
          (NativeBoundSubstitution.Geometry.occurs space.substitute) space.substitute.agendaMap
          (NativeBoundSubstitution.Geometry.descriptor space.substitute) resident.equations resident.root left right pending
          ordinary env resident.pending symbols lTerm rTerm leftRead rightRead chosen
      obtain ⟨decoded, known, resolved⟩ := Option.bind_eq_some_iff.mp choice.resolved
      have within := (Array.getElem?_eq_some_iff.mp resolved).choose
      rw [PackedTerms.decode_size symbols terms known] at within
      rw [if_pos (within.trans_le (show terms.nodes.size ≤ mc from bounds.map))] at tested
      obtain ⟨bytes, _, marked, _, _, marks, retained, _, _, _, _, ⟨arrival⟩⟩ := tested
      have cyclic : choice.term.occursIn choice.name = true := by
        have same := Option.some.inj (choice.inspection.symm.trans examined)
        cases occurs : choice.term.occursIn choice.name <;> simp_all
      rw [cyclic] at arrival
      have localWrites : Includes term map frame.substitution bytes := by
        intro byte modified
        obtain ⟨slot, _, _, member⟩ := marks byte modified
        exact Or.inr (Or.inr (Or.inl ⟨slot, member⟩))
      exact ⟨after, steps, bytes, ran, marked.mono (by decide) (Finset.Subset.refl _), .graph localWrites,
        retained.termReady, extends_failure terms .occurs, retained.one, ⟨arrival⟩⟩
  | bindVar name value => exact (noBind name value rfl).elim

/-- One installed iteration refines a nonempty packed
work-list transition. The bounds refer to the actual packed
result sizes and the new records of this transition. -/
theorem fetched_nonempty (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {before : Native} (code : Placed image start exits) (point : At image before base start) (controls : Controls before)
    (space : Geometry term map frame agenda trail image base)
    (terms : PackedTerms.Arena) (left right : Word) (pending history : Words)
    (resident : Resident term map frame agenda trail ⟨terms, (left, right) :: pending, history⟩ before)
    (symbols : UnifierHeaders.Symbols σ) (lTerm rTerm : Term σ)
    (leftRead : PackedTerms.lookup symbols terms left = some lTerm) (rightRead : PackedTerms.lookup symbols terms right = some rTerm)
    (action : Encoded) (examined : PackedUnifierAction.inspect terms left right = some action) (result : Outcome)
    (advanced : PackedWorklist.advance ⟨terms, (left, right) :: pending, history⟩ = some result)
    (bounds : Room nc ec mc ac tc terms resident.equations.size resident.bindings.size pending action result) :
    Transition other extra vector term map frame agenda trail image base start exits before terms
      (resident.equations.size + agendaDemand pending action) (resident.bindings.size + trailDemand action) result := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  by_cases bound : ∃ name value, action = .bindVar name value
  · obtain ⟨name, replacement, rfl⟩ := bound
    have actual := route terms left right (.bindVar name replacement) examined
    obtain ⟨side, chosen⟩ := actual
    have bindingAdvance := advanced
    simp only [PackedWorklist.advance, examined, bind, Option.bind_some] at bindingAdvance
    obtain ⟨translated, computed, continued⟩ := Option.bind_eq_some_iff.mp bindingAdvance
    obtain ⟨moved, remapped, returned⟩ := Option.bind_eq_some_iff.mp continued
    obtain rfl := Option.some.inj returned
    have sideCode : NativeBindEntry.EntryPlaced image side ((targets start exits).at side.exiting) (NativeSolverImage.shared start) := by
      rw [bind_target]; exact code.bind side
    have traceFit : resident.bindings.size < tc := by
      have allowed := bounds.trail
      change resident.bindings.size + 1 ≤ tc at allowed
      omega
    obtain ⟨after, steps, updated, nextRoot, graphBytes, trailBytes, agendaBytes, ran, framed, graph, trace, pendingBytes,
        next, size, future, binding, _, extended, atEntry⟩ :=
      NativeBindingStep.fetched other extra vector point controls side code.dispatch sideCode code.gate code.binding space
        terms resident.equations resident.bindings resident.root left right pending history resident.live resident.pending resident.history
        symbols lTerm rTerm leftRead rightRead chosen name replacement examined translated computed moved remapped
        bounds.map bounds.nodes bounds.edges bounds.agenda traceFit
    exact ⟨after, steps, _, ran, framed.mono (by decide) (Finset.Subset.refl _),
      .union (.union (.union (.graph graph) (.binding trace)) (.pending pendingBytes)) .headers,
      NativeRemapSnapshot.ready_restrict extended next.dispatch.termReady,
      (fun _ present => Option.some.inj present ▸ extended),
      next.dispatch.one,
      ⟨⟨updated, _, nextRoot, next, future, binding⟩, size, by simp [trailDemand], atEntry⟩⟩
  · exact fetched_other other extra vector code.toCorePlaced point controls space terms left right pending history
      resident symbols lTerm rTerm leftRead rightRead action examined result advanced bounds
      (fun name value eq => bound ⟨name, value, eq⟩)

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverStep
