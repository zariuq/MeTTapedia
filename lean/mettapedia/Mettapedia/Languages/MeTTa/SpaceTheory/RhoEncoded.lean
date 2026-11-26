import Mettapedia.GSLT.Contracts.PaperRhoNamed
import Mettapedia.GSLT.Contracts.PaperRhoOuterBag
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSuccessorInstance
import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mettapedia.Languages.MeTTa.SpaceTheory.FirstOrderForwarding

/-!
# Storing encoded rho processes as ordinary Atoms

Bound slots, held code and parallel contexts are explicit in this
representation. The Atom grammar has not acquired a binder. The
enumeration below uses the existing scoped rho stepper, and reads back
its canonical results. Exactness is for the paper's closed-payload
profile, modulo its structural congruence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.RhoEncoded

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Contracts.PaperRho
open PatternBoundary (encodeName)
open Adequacy (canonicalForm decodeProcess_canonicalize)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSuccessorInstance (rhoSuccessors mem_rhoSuccessors)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep (CanonicalStep)

mutual
def storeName : Name → Atom
  | .bound index => .expression [.symbol "rho.bound", .grounded (.int (Int.ofNat index))]
  | .quote body => .expression [.symbol "rho.quote", storeProcess body]

def storeProcess : Process → Atom
  | .zero => .symbol "rho.zero"
  | .par first second => .expression [.symbol "rho.par", storeProcess first, storeProcess second]
  | .send name body => .expression [.symbol "rho.send", storeName name, storeProcess body]
  | .receive name body => .expression [.symbol "rho.receive", storeName name, storeProcess body]
  | .drop name => .expression [.symbol "rho.drop", storeName name]
end

mutual
def readName : Atom → Option Name
  | .expression [.symbol "rho.bound", .grounded (.int (.ofNat index))] => some (.bound index)
  | .expression [.symbol "rho.quote", body] => (readProcess body).map .quote
  | _ => none
termination_by atom => sizeOf atom

def readProcess : Atom → Option Process
  | .symbol "rho.zero" => some .zero
  | .expression [.symbol "rho.par", first, second] => do
    return .par (← readProcess first) (← readProcess second)
  | .expression [.symbol "rho.send", name, body] => do
    return .send (← readName name) (← readProcess body)
  | .expression [.symbol "rho.receive", name, body] => do
    return .receive (← readName name) (← readProcess body)
  | .expression [.symbol "rho.drop", name] => (readName name).map .drop
  | _ => none
termination_by atom => sizeOf atom
end

mutual
@[simp] theorem read_stored_name (name : Name) : readName (storeName name) = some name := by
  cases name with
  | bound index => rw [storeName, readName]
  | quote body => simp [storeName, readName, read_stored_process body]
termination_by sizeOf name

@[simp] theorem read_stored_process (process : Process) : readProcess (storeProcess process) = some process := by
  cases process with
  | zero => simp [storeProcess, readProcess]
  | par left right =>
    simp [storeProcess, readProcess, read_stored_process left, read_stored_process right]
  | send name body =>
    simp [storeProcess, readProcess, read_stored_name name, read_stored_process body]
  | receive name body =>
    simp [storeProcess, readProcess, read_stored_name name, read_stored_process body]
  | drop name => simp [storeProcess, readProcess, read_stored_name name]
termination_by sizeOf process
end

theorem store_injective : Function.Injective storeProcess := by
  intro first second equal
  have decoded := congrArg readProcess equal
  simpa only [read_stored_process, Option.some.injEq] using decoded

def nameKey (input : Atom) : Option Pattern :=
  (readName input).map fun name => canonicalize rhoReflectivePresentation (encodeName name)

theorem name_key_exact (first second : Name) :
    nameKey (storeName first) = nameKey (storeName second) ↔ NameEquivalence first second := by
  simp only [nameKey, read_stored_name, Option.map_some, Option.some.injEq]
  exact Adequacy.canonicalize_encodeName_eq_iff first second

private def readResult (result : Pattern) : Option Atom :=
  (Adequacy.decodeProcess (canonicalize rhoReflectivePresentation result)).map storeProcess

def successors (input : Atom) : List Atom :=
  match readProcess input with
  | none => []
  | some process => (rhoSuccessors (canonicalForm process)).filterMap readResult

/-- The encoded stepper preserves and reflects the independent paper
relation on closed processes; the finite list represents successor
classes, not a promise to enumerate distinct firing occurrences once. -/
theorem successors_exact (before after : Process) (closed : ScopedProcess 0 before) :
    Reduction before after ↔
      ∃ representative, storeProcess representative ∈ successors (storeProcess before) ∧
        Congruence representative after := by
  simp only [successors, read_stored_process]
  constructor
  · intro fires
    obtain ⟨result, advanced, equal⟩ := Adequacy.canonicalStep_of_reduction fires
    obtain ⟨representative, read, same⟩ := decodeProcess_canonicalize after
    have found : readResult result = some (storeProcess representative) := by
      unfold readResult
      rw [equal, read]
      rfl
    exact ⟨representative, List.mem_filterMap.mpr ⟨result, mem_rhoSuccessors.mpr advanced, found⟩, same.symm⟩
  · rintro ⟨representative, member, desired⟩
    obtain ⟨result, found, read⟩ := List.mem_filterMap.mp member
    have step : CanonicalStep (canonicalForm before) (canonicalize rhoReflectivePresentation result) :=
      ⟨result, mem_rhoSuccessors.mp found, rfl⟩
    obtain ⟨actual, advanced, sameClass⟩ := Adequacy.reduction_of_canonicalStep closed step
    obtain ⟨reached, decoded, reachedClass⟩ := decodeProcess_canonicalize actual
    unfold readResult at read
    rw [← sameClass, decoded, Option.map_some] at read
    have same := store_injective (Option.some.inj read)
    exact .equiv (.refl _) advanced (reachedClass.trans (same ▸ desired))

theorem every_emitted_atom_is_a_reduct {before : Process} {result : Atom}
    (closed : ScopedProcess 0 before) (member : result ∈ successors (storeProcess before)) :
    ∃ after, storeProcess after = result ∧ Reduction before after := by
  have printed := member
  simp only [successors, read_stored_process] at printed
  obtain ⟨raw, _, printed⟩ := List.mem_filterMap.mp printed
  obtain ⟨after, _, equal⟩ := Option.map_eq_some_iff.mp printed
  exact ⟨after, equal, (successors_exact before after closed).mpr
    ⟨after, equal.symm ▸ member, .refl _⟩⟩

theorem parallel_context_is_active {before after : Process} (frame : Process)
    (step : Reduction before after) (closed : ScopedProcess 0 before) (frameClosed : ScopedProcess 0 frame) :
    ∃ reached, storeProcess reached ∈ successors (storeProcess (.par before frame)) ∧
      Congruence reached (.par after frame) :=
  (successors_exact _ _ (.par closed frameClosed)).mp (.par frame step)

theorem suspended_context_is_inactive {channel : Name} {body : Process}
    (closedName : ScopedName 0 channel) (bodyScope : ScopedProcess 1 body) :
    successors (storeProcess (.receive channel body)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨after, _, advanced⟩ := every_emitted_atom_is_a_reduct (.receive closedName bodyScope) member
  exact OuterBag.suspended_body_cannot_fire _ _ _ advanced

def StoredStep (before after : Atom) : Prop := after ∈ successors before

theorem store_run {before after : Process} (closed : ScopedProcess 0 before)
    (path : Relation.ReflTransGen Reduction before after) :
    ∃ representative, Relation.ReflTransGen StoredStep (storeProcess before) (storeProcess representative) ∧
      Congruence representative after := by
  induction path with
  | refl => exact ⟨before, .refl, .refl _⟩
  | tail earlier last ih =>
    obtain ⟨representative, read, equivalent⟩ := ih
    have nowClosed := (equivalent.scoped_iff 0).mpr (Adequacy.closed_of_reflTransGen earlier closed)
    have lastFromRep := Reduction.equiv equivalent last (.refl _)
    obtain ⟨reached, advanced, agrees⟩ := (successors_exact _ _ nowClosed).mp lastFromRep
    exact ⟨reached, read.tail advanced, agrees⟩

theorem read_run {before : Process} (closed : ScopedProcess 0 before) {atom : Atom}
    (path : Relation.ReflTransGen StoredStep (storeProcess before) atom) :
    ∃ reached, storeProcess reached = atom ∧ Relation.ReflTransGen Reduction before reached := by
  induction path with
  | refl => exact ⟨before, rfl, .refl⟩
  | tail first last ih =>
    obtain ⟨source, encoded, steps⟩ := ih
    have advanced := last
    change _ ∈ successors _ at advanced
    rw [← encoded] at advanced
    obtain ⟨reached, result, actual⟩ :=
      every_emitted_atom_is_a_reduct (Adequacy.closed_of_reflTransGen steps closed) advanced
    exact ⟨reached, result, steps.tail actual⟩

theorem quoted_name_equality_requires_the_interpretation :
    let x : Name := .quote .zero
    storeName (.quote (.drop x)) ≠ storeName x ∧
      nameKey (storeName (.quote (.drop x))) = nameKey (storeName x) := by
  intro x
  exact ⟨by decide +kernel, (name_key_exact _ _).mpr (.quote_drop _)⟩

theorem literal_reading_stores_alpha_variants_identically :
    storeProcess (Named.literal Named.Controls.innerBinder) =
      storeProcess (Named.literal Named.Controls.renamedInnerBinder) :=
  congrArg storeProcess Named.Controls.bindingAware_not_alpha_invariant.1

theorem capturing_inside_quotation_is_not_an_alpha_encoding :
    storeProcess (Named.bindingAware Named.Controls.innerBinder) ≠
      storeProcess (Named.bindingAware Named.Controls.renamedInnerBinder) := by
  intro identical
  exact Named.Controls.bindingAware_not_alpha_invariant.2 (congrArg canonicalForm (store_injective identical))

section Controls

open FirstOrderForwarding (send wait request declaration)

private def base : Name := .quote .zero
private def aliasName : Name := .quote (.drop base)
private def payload : Process := .send base .zero
private def input : Process := .par (.send aliasName payload) (OuterBag.forwarder base)

private theorem input_closed : ScopedProcess 0 input :=
  .par (.send (.literal (.drop (.literal .zero))) (.send (.literal .zero) .zero))
    (.receive (.literal .zero) (.drop (.bound (by decide))))

/-- Testing the same stored name spellings with the first-order rule
is not the paper's communication test. The encoded machine follows
quote-drop, fires, and produces a representative of the payload. -/
theorem quote_alias_fires_only_with_the_encoded_test :
    ¬ModuleTheories.InstanceOf declaration
      (request (send (storeName aliasName) (storeProcess payload)) (wait (storeName base))) (storeProcess payload) ∧
      ∃ reached, storeProcess reached ∈ successors (storeProcess input) ∧ Congruence reached payload := by
  refine ⟨FirstOrderForwarding.different_channel_fails (by decide +kernel), ?_⟩
  apply (successors_exact input payload input_closed).mp
  exact .comm (.literal (.drop (.literal .zero))) (.literal .zero) (.send (.literal .zero) .zero)
    (.drop (.bound (by decide))) (.quote_drop _) (.drop_hit (.refl _))

/-- The very same communication is inactive as a held body. -/
theorem quoted_alias_is_not_a_license_to_enter_a_held_body :
    successors (storeProcess (.receive base input)) = [] :=
  suspended_context_is_inactive (.literal .zero) (input_closed.weaken (by decide))

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.RhoEncoded
