import Mettapedia.GSLT.Parsing.GrammarReadDependencies
import Mettapedia.Machines.ReadCertifiedQueryReuse

/-!
# Grammar evolution with read-validated parse caches

An entry is populated by the actual dependency-reading scheduler. Reuse checks
the selected root, input, nesting budget and every observed category catalogue.
On a miss the same scheduler recomputes. The resulting candidates and packed
forest agree with fresh exhaustive bounded parsing after arbitrary grammar
updates. The freshness counter counts query executions, not validation work.

The parser algorithm and guard meanings are fixed by this module. Native
artifacts, changing lexer profiles, interpretation changes and imported cache
bytes require their own authority and representation contracts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GrammarCacheReuse

open CompilerCorrespondence (Category Codepoint)
open GuardCorrespondence (CompiledGrammar CompiledProduction)
open BoundedScheduler (Candidate)
open GrammarReadDependencies
open Mettapedia.Machines

structure Request where
  input : List Codepoint
  fuel : Nat
  deriving DecidableEq, Repr

/-- The root is the governing parameter of this fixed parser family. -/
def family (start : Category) (request : Request) : Query (List Candidate) :=
  root request.input request.fuel start

abbrev Entry := ReadCertifiedQueryReuse.Entry Category Request Category
  (List CompiledProduction) (List Candidate)

def capture (grammar : CompiledGrammar) (request : Request) : Entry :=
  ReadCertifiedQueryReuse.populate family grammar.start request (catalogue grammar)

theorem capture_recorded (grammar : CompiledGrammar) (request : Request) :
    ReadCertifiedQueryReuse.Recorded family (capture grammar request) :=
  ReadCertifiedQueryReuse.populate_recorded family grammar.start request (catalogue grammar)

def accepts (grammar : CompiledGrammar) (request : Request) (entry : Entry) : Bool :=
  ReadCertifiedQueryReuse.admissible grammar.start request (catalogue grammar) entry

def reuse (grammar : CompiledGrammar) (request : Request) (entry : Entry) : List Candidate × Nat :=
  ReadCertifiedQueryReuse.reuse family grammar.start request (catalogue grammar) entry

/-- The hit path validates reads and the miss path recomputes. Both give the
same ordered certificates as the pre-existing exhaustive parser. -/
theorem reuse_exact (grammar : CompiledGrammar) (request : Request) (entry : Entry)
    (recorded : ReadCertifiedQueryReuse.Recorded family entry) :
    (reuse grammar request entry).1 =
      BoundedScheduler.scheduleRoot grammar request.input request.fuel := by
  exact (ReadCertifiedQueryReuse.reuse_exact family grammar.start request
    (catalogue grammar) entry recorded).trans (root_answer grammar request.input request.fuel)

theorem reuse_capture_exact (before after : CompiledGrammar) (oldRequest request : Request) :
    (reuse after request (capture before oldRequest)).1 =
      BoundedScheduler.scheduleRoot after request.input request.fuel :=
  reuse_exact after request _ (capture_recorded before oldRequest)

theorem accepted_skips_query {grammar : CompiledGrammar} {request : Request} {entry : Entry}
    (accepted : accepts grammar request entry = true) :
    (reuse grammar request entry).2 = 0 :=
  ReadCertifiedQueryReuse.accepted_skips_query family grammar.start request
    (catalogue grammar) entry accepted

theorem rejected_recomputes {grammar : CompiledGrammar} {request : Request} {entry : Entry}
    (rejected : accepts grammar request entry = false) :
    (reuse grammar request entry).2 = 1 :=
  ReadCertifiedQueryReuse.rejected_executes_query family grammar.start request
    (catalogue grammar) entry rejected

def reuseForest (grammar : CompiledGrammar) (request : Request) (entry : Entry) : PackedForest.Forest :=
  PackedForest.packCertificates ((reuse grammar request entry).1.map Candidate.certificate)

theorem reuseForest_exact (grammar : CompiledGrammar) (request : Request) (entry : Entry)
    (recorded : ReadCertifiedQueryReuse.Recorded family entry) :
    reuseForest grammar request entry =
      BoundedScheduler.scheduleForest grammar request.input request.fuel := by
  simp only [reuseForest, reuse_exact grammar request entry recorded, BoundedScheduler.scheduleForest]

/-- The cached forest retains a replayable source witness for every parse in
the declared bound, by composition with the existing source compiler. -/
theorem reuseForest_source_complete (presentation : GuardCorrespondence.SourceDefinition)
    (request : Request) (entry : Entry)
    (recorded : ReadCertifiedQueryReuse.Recorded family entry) :
    BoundedScheduler.BoundedComplete
      (reuseForest (GuardCorrespondence.compile presentation) request entry)
      presentation request.input request.fuel := by
  rw [reuseForest_exact _ _ _ recorded]
  exact BoundedScheduler.scheduleForest_bounded_complete presentation request.input request.fuel

/-- The restored snapshot may recover an old entry without making the cache
monotone in time. Every intermediate query still revalidates at its own state. -/
theorem restored_snapshot_accepts (grammar : CompiledGrammar) (request : Request) :
    accepts grammar request (capture grammar request) = true := by
  apply (ReadCertifiedQueryReuse.admissible_iff _ _ _ _).mpr
  exact ⟨rfl, rfl, ReadOnlyQuery.run_agrees (catalogue grammar) (family grammar.start request)⟩

end Mettapedia.GSLT.Parsing.GrammarCacheReuse
