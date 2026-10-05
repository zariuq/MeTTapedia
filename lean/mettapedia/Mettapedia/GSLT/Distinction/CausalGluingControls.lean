import Mettapedia.GSLT.Distinction.CausalGluing
import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Controls for causal prefix gluing

One shared prefix writes cell `0`.  Two read extensions read it; two write
extensions write the same payload to cell `1`.  The same footprints are read
by two declared observers: `quiet` sees no read, `logged` sees both reads on one
ordered channel.

| Control | Theorem |
|---|---|
| Shared reads glue when unobserved | `quiet_reads_glue` |
| ... and not when one ordered channel sees both | `logged_reads_refused`, `logged_orders_differ` |
| Equal payloads, distinct events, conflicting | `equal_payload_writes_conflict` |
| The payload store forgets which write was last | `payload_store_fiber` |
| Equal syntax up to commutativity, different runs | `commutative_syntax_control` |
| Removing shared events by payload hides a conflict | `payload_glue_control` |
| A read and a write of one cell do not commute | `read_write_order_matters` |
| Commuting coefficients in a noncommutative monoid | `commuting_coefficients_swap`, `power_coefficients_descend` |
| Independent occurrences, noncommuting coefficients | `noncommuting_coefficients_control`, `noncommuting_coefficients_do_not_descend` |
| The tile of the two reads is one path trace and one word trace | `readPair_trace` |
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.CausalGluing.Controls

open Mettapedia.Machines.BranchLocalNeed.NeedWorlds
open Mettapedia.GSLT.Core.NonFactorization (NonTrivialFiber)
open Mettapedia.GSLT.Causality.EventConcurrency

inductive Occ where
  | shared | leftRead | rightRead | leftWrite | rightWrite
  deriving DecidableEq, Repr

/-- The prefix writes `1` to cell `0`; the reads read cell `0`; both branch
writes write `5` to cell `1`. -/
def footprint : Occ → Footprint ℕ ℕ
  | .shared => ⟨fun _ => false, fun cell => if cell = 0 then some 1 else none⟩
  | .leftRead => ⟨fun cell => decide (cell = 0), fun _ => none⟩
  | .rightRead => ⟨fun cell => decide (cell = 0), fun _ => none⟩
  | .leftWrite => ⟨fun _ => false, fun cell => if cell = 1 then some 5 else none⟩
  | .rightWrite => ⟨fun _ => false, fun cell => if cell = 1 then some 5 else none⟩

/-- The declared observer sees no occurrence. -/
def quiet : Occurrences Occ ℕ ℕ Unit := ⟨footprint, fun _ => none⟩

/-- The declared observer sees both reads on one ordered channel. -/
def logged : Occurrences Occ ℕ ℕ Unit :=
  ⟨footprint, fun
    | .leftRead => some ()
    | .rightRead => some ()
    | _ => none⟩

/-- The prefix precedes every extension; the extensions are unordered. -/
def basis : FiniteCausalBasis Occ where
  support
    | .shared => {.shared}
    | event => {.shared, event}
  self_mem := by intro event; cases event <;> simp
  hereditary := by
    intro event predecessor member
    cases event <;> cases predecessor <;> simp at member ⊢

/-- A set whose members are pairwise causally ordered is free of every causally
unordered conflict. -/
theorem ordered_conflictFree (hazard : Occ → Occ → Prop) (events : Finset Occ)
    (ordered : ∀ a ∈ events, ∀ b ∈ events, a ∈ basis.support b ∨ b ∈ basis.support a) :
    ConflictFree (basis.unorderedConflict hazard) events := by
  intro a b inA inB conflicting
  rcases ordered a inA b inB with before | after
  · exact conflicting.2.1 before
  · exact conflicting.2.2 after

def branchEvents (event : Occ) : Finset Occ := {.shared, event}

theorem branch_closed (event : Occ) : basis.Closed (branchEvents event) := by
  cases event <;> ext other <;> cases other <;>
    simp [FiniteCausalBasis.close, basis, branchEvents]

/-- The branch through the prefix to one extension, for either observer. -/
def branch (O : Occurrences Occ ℕ ℕ Unit) (event : Occ) : Configuration basis (O.conflict basis) where
  events := branchEvents event
  closed := branch_closed event
  consistent := ordered_conflictFree _ _ (by
    intro a inA b inB
    cases event <;> cases a <;> cases b <;> simp [branchEvents, basis] at inA inB ⊢)

/-- The branch run: the prefix, then the extension. -/
theorem branch_fires (O : Occurrences Occ ℕ ℕ Unit) (event : Occ) (extension : event ≠ .shared) :
    Fires basis (O.conflict basis) ∅ [.shared, event] := by
  refine ⟨⟨by simp, by simp [basis], by simp⟩, ⟨?_, ?_, ?_⟩, trivial⟩
  · simpa using extension
  · intro x member
    cases event <;> simp [basis] at member extension ⊢ <;> tauto
  · intro d member
    have : d = .shared := by simpa using member
    subst this
    constructor
    · intro conflicting
      exact conflicting.2.1 (by cases event <;> simp [basis] at extension ⊢)
    · intro conflicting
      exact conflicting.2.2 (by cases event <;> simp [basis] at extension ⊢)

theorem events_shared (O : Occurrences Occ ℕ ℕ Unit) (left right : Occ)
    (leftExtension : left ≠ .shared) (rightExtension : right ≠ .shared) (different : left ≠ right) :
    [Occ.shared].toFinset = (branch O left).events ∩ (branch O right).events ∧
      [left].toFinset = (branch O left).events \ (branch O right).events ∧
      [right].toFinset = (branch O right).events \ (branch O left).events := by
  refine ⟨?_, ?_, ?_⟩ <;> ext event <;>
    simp [branch, branchEvents] <;> aesop

/-! ## Shared reads -/

theorem quiet_reads_independent : quiet.Independent .leftRead .rightRead := by
  refine ⟨by decide, ?_, ?_⟩ <;>
    simp [Occurrences.Dependent, Occurrences.Hazard, Occurrences.SharesChannel,
      Occurrences.Writes, quiet, footprint]

theorem logged_reads_dependent : ¬ logged.Independent .leftRead .rightRead :=
  fun independent => independent.no_common_channel ⟨(), rfl, rfl⟩

/-- **Shared reads glue when the declared observer does not order them**: the
branches are compatible and the glued run fires. -/
theorem quiet_reads_glue :
    Configuration.Compatible (branch quiet .leftRead) (branch quiet .rightRead) ∧
      Fires basis (quiet.conflict basis) ∅ [.shared, .leftRead, .rightRead] := by
  have compatible : Configuration.Compatible (branch quiet .leftRead) (branch quiet .rightRead) := by
    rw [Configuration.compatible_iff_exclusive_hazards]
    intro a inA b inB
    have leftOnly : a = .leftRead := by
      cases a <;> simp [branch, branchEvents] at inA ⊢
    have rightOnly : b = .rightRead := by
      cases b <;> simp [branch, branchEvents] at inB ⊢
    subst leftOnly
    subst rightOnly
    exact ⟨quiet_reads_independent.2.1, quiet_reads_independent.2.2⟩
  obtain ⟨shared, leftOnly, rightOnly⟩ :=
    events_shared quiet .leftRead .rightRead (by decide) (by decide) (by decide)
  exact ⟨compatible, (Occurrences.glue_fires_iff (branch quiet .leftRead) (branch quiet .rightRead)
    (branch_fires quiet .leftRead (by decide)) (branch_fires quiet .rightRead (by decide))
    shared leftOnly rightOnly).mpr compatible⟩

/-- **... and are refused when one ordered channel observes both.** -/
theorem logged_reads_refused :
    ¬ Configuration.Compatible (branch logged .leftRead) (branch logged .rightRead) ∧
      ¬ Fires basis (logged.conflict basis) ∅ [.shared, .leftRead, .rightRead] := by
  have incompatible :
      ¬ Configuration.Compatible (branch logged .leftRead) (branch logged .rightRead) := by
    intro compatible
    have checked := (Configuration.compatible_iff_exclusive_hazards logged.Dependent _ _).mp
      compatible .leftRead (by simp [branch, branchEvents]) .rightRead
        (by simp [branch, branchEvents])
    exact checked.1 (.inr ⟨(), rfl, rfl⟩)
  obtain ⟨shared, leftOnly, rightOnly⟩ :=
    events_shared logged .leftRead .rightRead (by decide) (by decide) (by decide)
  exact ⟨incompatible, fun glued => incompatible ((Occurrences.glue_fires_iff (branch logged .leftRead)
    (branch logged .rightRead) (branch_fires logged .leftRead (by decide))
    (branch_fires logged .rightRead (by decide)) shared leftOnly rightOnly).mp glued)⟩

/-- The initial store: every cell holds `0`, written by no occurrence. -/
def initial : Store Occ ℕ ℕ := fun _ => (0, none)

/-- The ordered channel sees the two reads in the order they fire: the two
interleavings differ for that observer. -/
theorem logged_orders_differ :
    logged.observe [.shared, .leftRead, .rightRead] initial () ≠
      logged.observe [.shared, .rightRead, .leftRead] initial () := by
  intro same
  have ids := congrArg (List.map Prod.fst) same
  simp [Occurrences.observe, Occurrences.log, logged] at ids

/-- For the quiet observer the glued run's reading does not depend on the order
of the extensions, and each read sees the prefix's write. -/
theorem quiet_glue_reads :
    quiet.log [.shared, .leftRead, .rightRead] initial =
      quiet.log [.shared] initial ++ quiet.log [.leftRead] (quiet.final [.shared] initial) ++
        quiet.log [.rightRead] (quiet.final [.shared] initial) ∧
      quiet.seen .rightRead (quiet.final [.shared] initial) 0 = some (1, some .shared) := by
  refine ⟨Occurrences.glue_log quiet_reads_glue.1 [.shared] (l := [.leftRead]) (r := [.rightRead])
    (by simp [branch, branchEvents]) (by simp [branch, branchEvents]) initial, ?_⟩
  simp [Occurrences.seen, Occurrences.final, Occurrences.apply, quiet, footprint]

/-! ## Equal-payload writes -/

/-- **Equal payloads do not identify occurrences**: the two writes have one
footprint, are distinct events, and conflict. -/
theorem equal_payload_writes_conflict :
    footprint .leftWrite = footprint .rightWrite ∧ Occ.leftWrite ≠ .rightWrite ∧
      ¬ quiet.Independent .leftWrite .rightWrite ∧
      ¬ Configuration.Compatible (branch quiet .leftWrite) (branch quiet .rightWrite) := by
  have hazard : quiet.Dependent .leftWrite .rightWrite :=
    .inl ⟨1, by simp [Occurrences.Writes, quiet, footprint],
      .inl (by simp [Occurrences.Writes, quiet, footprint])⟩
  refine ⟨rfl, by decide, fun independent => independent.2.1 hazard, ?_⟩
  intro compatible
  have checked := (Configuration.compatible_iff_exclusive_hazards quiet.Dependent _ _).mp
    compatible .leftWrite (by simp [branch, branchEvents]) .rightWrite
      (by simp [branch, branchEvents])
  exact checked.1 hazard

/-- **The payload store forgets which write was last**: the two orders of the
equal-payload writes leave equal payloads and different writers. -/
def payload_store_fiber :
    NonTrivialFiber (fun word : List Occ => fun cell => (quiet.final word initial cell).1)
      (fun word => quiet.final word initial) where
  left := [.leftWrite, .rightWrite]
  right := [.rightWrite, .leftWrite]
  sameShadow := by
    funext cell
    by_cases written : cell = 1 <;>
      simp [Occurrences.final, Occurrences.apply, quiet, footprint, written]
  differentValue := by
    intro same
    have writer := congrArg (fun store : Store Occ ℕ ℕ => (store 1).2) same
    simp [Occurrences.final, Occurrences.apply, quiet, footprint] at writer

/-- **Commutative syntax supplies no swap**: the two words are equal as
multisets of occurrences, as two parallel compositions are equal up to
commutativity, and their runs differ. -/
theorem commutative_syntax_control :
    ((([.leftWrite, .rightWrite] : List Occ)) : Multiset Occ) = ([.rightWrite, .leftWrite] : List Occ) ∧
      quiet.final [.leftWrite, .rightWrite] initial ≠ quiet.final [.rightWrite, .leftWrite] initial :=
  ⟨Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _), payload_store_fiber.differentValue⟩

/-- What a payload-based deduplication sees: the cell and value written. -/
def written : Occ → Option (ℕ × ℕ)
  | .shared => some (0, 1)
  | .leftWrite => some (1, 5)
  | .rightWrite => some (1, 5)
  | _ => none

/-- Remove from the second branch every occurrence whose payload the first
already carries: deduplication by payload rather than by identity. -/
def glueByPayload (first second : List Occ) : List Occ :=
  first ++ second.filter fun i => decide (∀ j ∈ first, written j ≠ written i)

/-- **Removing shared events by payload hides the conflict**: it drops the
second write, and the resulting run fires, while gluing by identity keeps both
writes and is refused. -/
theorem payload_glue_control :
    glueByPayload [.shared, .leftWrite] [.shared, .rightWrite] = [.shared, .leftWrite] ∧
      Occurrences.glue ([.shared, .leftWrite] : List Occ) [.shared, .rightWrite] =
        [.shared, .leftWrite, .rightWrite] ∧
      Fires basis (quiet.conflict basis) ∅ (glueByPayload [.shared, .leftWrite] [.shared, .rightWrite]) ∧
      ¬ Fires basis (quiet.conflict basis) ∅
        (Occurrences.glue ([.shared, .leftWrite] : List Occ) [.shared, .rightWrite]) := by
  have byPayload : glueByPayload [.shared, .leftWrite] [.shared, .rightWrite] = [.shared, .leftWrite] := by
    decide
  have byIdentity : Occurrences.glue ([.shared, .leftWrite] : List Occ) [.shared, .rightWrite] =
      [.shared, .leftWrite, .rightWrite] := by
    decide
  refine ⟨byPayload, byIdentity, byPayload ▸ branch_fires quiet .leftWrite (by decide), ?_⟩
  rw [byIdentity]
  obtain ⟨shared, leftOnly, rightOnly⟩ :=
    events_shared quiet .leftWrite .rightWrite (by decide) (by decide) (by decide)
  intro glued
  exact equal_payload_writes_conflict.2.2.2 ((Occurrences.glue_fires_iff (branch quiet .leftWrite)
    (branch quiet .rightWrite) (branch_fires quiet .leftWrite (by decide))
    (branch_fires quiet .rightWrite (by decide)) shared leftOnly rightOnly).mp glued)

/-- **A read and a write of one cell do not commute**: the read sees the initial
value before the write and the prefix's write after it. -/
theorem read_write_order_matters :
    quiet.Dependent .shared .leftRead ∧
      quiet.seen .leftRead initial 0 = some (0, none) ∧
      quiet.seen .leftRead (quiet.apply .shared initial) 0 = some (1, some .shared) := by
  refine ⟨.inl ⟨0, by simp [Occurrences.Writes, quiet, footprint],
    .inr (by simp [Occurrences.Reads, quiet, footprint])⟩, ?_, ?_⟩ <;>
    simp [Occurrences.seen, Occurrences.apply, quiet, footprint, initial]

/-! ## Coefficients in a noncommutative monoid -/

/-- An upper shear. -/
def shear : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]

/-- A lower shear. -/
def lowerShear : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]

theorem shear_lowerShear_ne : shear * lowerShear ≠ lowerShear * shear := by
  intro same
  have entry := congrFun (congrFun same 0) 0
  simp [shear, lowerShear, Matrix.mul_apply, Fin.sum_univ_two] at entry

/-- Coefficients drawn from the powers of one matrix. -/
def powerCoefficient : Occ → Matrix (Fin 2) (Fin 2) ℤ
  | .leftRead => shear
  | .rightRead => shear ^ 2
  | _ => 1

/-- Two coefficients that do not commute. -/
def shearCoefficient : Occ → Matrix (Fin 2) (Fin 2) ℤ
  | .leftRead => shear
  | .rightRead => lowerShear
  | _ => 1

/-- **Positive**: in the noncommutative monoid of matrices, commuting
coefficients keep the account across the swap. -/
theorem commuting_coefficients_swap :
    Occurrences.account powerCoefficient [.leftRead, .rightRead] =
      Occurrences.account powerCoefficient [.rightRead, .leftRead] :=
  (Occurrences.account_tile_iff_commute powerCoefficient _ _).mpr ((Commute.refl shear).pow_right 2)

/-- **Negative**: independent occurrences, which keep the store and every
observation across the swap, change a noncommutative account. -/
theorem noncommuting_coefficients_control :
    quiet.Independent .leftRead .rightRead ∧
      quiet.final [.leftRead, .rightRead] initial = quiet.final [.rightRead, .leftRead] initial ∧
      Occurrences.account shearCoefficient [.leftRead, .rightRead] ≠
        Occurrences.account shearCoefficient [.rightRead, .leftRead] := by
  refine ⟨quiet_reads_independent, ?_, ?_⟩
  · simpa using quiet.final_swap quiet_reads_independent [] [] initial
  · intro same
    exact shear_lowerShear_ne ((Occurrences.account_tile_iff_commute shearCoefficient _ _).mp same)

/-- The tile of the two reads after the prefix, in the configuration machine. -/
def readPair : (quiet.concurrency basis).Pair (quiet.apply .shared initial, {.shared}) where
  first := ⟨.leftRead, _, ⟨⟨by simp, by intro x member; simp [basis] at member ⊢; tauto,
    fun d member => by
    have : d = .shared := by simpa using member
    subst this
    exact ⟨fun conflicting => conflicting.2.1 (by simp [basis]),
      fun conflicting => conflicting.2.2 (by simp [basis])⟩⟩, rfl⟩⟩
  second := ⟨.rightRead, _, ⟨⟨by simp, by intro x member; simp [basis] at member ⊢; tauto,
    fun d member => by
    have : d = .shared := by simpa using member
    subst this
    exact ⟨fun conflicting => conflicting.2.1 (by simp [basis]),
      fun conflicting => conflicting.2.2 (by simp [basis])⟩⟩, rfl⟩⟩
  independent := quiet_reads_independent

/-- **Positive**: the tile's two routes are one trace of the configuration
machine, and their site words are one word trace. -/
theorem readPair_trace :
    Trace.mk (T := (quiet.concurrency basis).tiles) (readPair.route (quiet.concurrency basis)) =
        Trace.mk (readPair.swapped (quiet.concurrency basis)) ∧
      TraceEquiv quiet.Independent [.leftRead, .rightRead] [.rightRead, .leftRead] :=
  ⟨Trace.mk_sound (.tile (T := (quiet.concurrency basis).tiles) readPair), by
    have related := Occurrences.traceEq_sites (.tile (T := (quiet.concurrency basis).tiles) readPair)
    change TraceEquiv quiet.Independent
      (Mettapedia.GSLT.Causality.OccurrenceHistory.OccurrencePath.sites
        (readPair.route (quiet.concurrency basis)))
      (Mettapedia.GSLT.Causality.OccurrenceHistory.OccurrencePath.sites
        (readPair.swapped (quiet.concurrency basis))) at related
    unfold Concurrency.Pair.swapped at related
    rw [Occurrences.sites_cast] at related
    exact related⟩

/-- **On paths, noncommuting coefficients are not a property of the trace.** -/
theorem noncommuting_coefficients_do_not_descend :
    ¬ Descends (quiet.concurrency basis).tiles
      (Occurrences.accountValuation (O := quiet) (basis := basis) shearCoefficient) := by
  intro descends
  exact shear_lowerShear_ne
    ((Occurrences.accountValuation_descends_iff shearCoefficient).mp descends _ readPair)

/-- Coefficients that are powers of one matrix commute pairwise. -/
def powerOf (occurrence : Occ) : ℕ :=
  match occurrence with
  | .shared => 0
  | .leftRead => 1
  | .rightRead => 2
  | .leftWrite => 3
  | .rightWrite => 4

/-- **On paths, coefficients drawn from one commuting family are a property of
the trace.** -/
theorem power_coefficients_descend :
    Descends (quiet.concurrency basis).tiles
      (Occurrences.accountValuation (O := quiet) (basis := basis) fun i => shear ^ powerOf i) :=
  (Occurrences.accountValuation_descends_iff (O := quiet) (basis := basis)
    (fun i => shear ^ powerOf i)).mpr fun _ pair =>
      Commute.pow_pow_self shear (powerOf pair.first.site) (powerOf pair.second.site)

end Mettapedia.GSLT.Distinction.CausalGluing.Controls
