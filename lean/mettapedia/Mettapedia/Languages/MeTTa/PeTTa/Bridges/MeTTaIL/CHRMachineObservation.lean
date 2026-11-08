import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineStoreExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler
import Mettapedia.Languages.CHR.MachineStore
import Mettapedia.Languages.CHR.MachinePublication
import Mettapedia.Languages.MeTTa.PeTTa.ReadSourceAfterRender
import Mettapedia.Languages.CHR.Declared

/-! The observer reads the machine's result back. Its decoders invert the
machine's encodings: lists, identifiers, values, occurrences and store
slots decode to exactly what was encoded, given fuel at least the size of
the encoded atom; a coherent store decodes to its contents. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open WireKit (integer)
open Mettapedia.Languages.CHR (Value Constraint)
open Mettapedia.Languages.CHR.Machine (Key Occ Store contents Coherent lift)
open Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler (listAtoms? natural? machineValue? occurrence? slot?
  atomSize atomsSize observeResult observe program? dictionary? Dictionary declared consumed additions
  constraintJson completeJson completeObservation)
open Lean (Json toJson)

theorem listAtoms_listAtom : ∀ (items : List Atom) (fuel : Nat), items.length < fuel →
    listAtoms? fuel (listAtom items) = some items
  | [], fuel + 1, _ => by simp [listAtoms?, listAtom, nil]
  | first :: rest, fuel + 1, bounded => by
    have smaller : rest.length < fuel := by simp at bounded; omega
    simp [listAtoms?, listAtom, cons, listAtoms_listAtom rest fuel smaller]

theorem natural_natAtom (id : Nat) : natural? (natAtom id) = some id := by
  simp [natural?, natAtom, integer]

mutual
  /-- Nodes of a value. -/
  def Value.size : Value → Nat
    | .integer _ => 1
    | .atom _ => 1
    | .tuple fields => 1 + Value.listSize fields
  def Value.listSize : List Value → Nat
    | [] => 1
    | first :: rest => 1 + Value.size first + Value.listSize rest
end

theorem listSize_length : ∀ (values : List Value), values.length < Value.listSize values
  | [] => by simp [Value.listSize]
  | first :: rest => by
    have := listSize_length rest
    simp [Value.listSize]
    omega

theorem size_le_listSize : ∀ (values : List Value) (value : Value), value ∈ values →
    Value.size value < Value.listSize values
  | [], _, inside => by cases inside
  | first :: rest, value, inside => by
    rcases List.mem_cons.mp inside with rfl | later
    · simp only [Value.listSize]
      omega
    · have := size_le_listSize rest value later
      simp only [Value.listSize]
      omega

theorem machineValue_valueAtom : ∀ (value : Value) (fuel : Nat), Value.size value ≤ fuel →
    machineValue? fuel (valueAtom value) = some value
  | value, 0, bounded => by
    exfalso
    cases value <;> simp only [Value.size] at bounded <;> omega
  | .integer number, fuel + 1, _ => by simp [machineValue?, valueAtom, integer]
  | .atom name, fuel + 1, _ => by simp [machineValue?, valueAtom]
  | .tuple fields, fuel + 1, bounded => by
    have lengthBound := listSize_length fields
    have listed := listAtoms_listAtom (fields.map valueAtom) (fuel + 1)
      (by simp only [List.length_map, Value.size] at bounded ⊢; omega)
    have decoded : (fields.map valueAtom).mapM (machineValue? fuel) = some fields := by
      have each : ∀ value ∈ fields, machineValue? fuel (valueAtom value) = some value := by
        intro value inside
        have smaller := size_le_listSize fields value inside
        exact machineValue_valueAtom value fuel (by simp only [Value.size] at bounded; omega)
      clear bounded lengthBound listed
      induction fields with
      | nil => rfl
      | cons first rest ih =>
        simp only [List.map_cons, List.mapM_cons, each first List.mem_cons_self,
          ih (fun value member => each value (List.mem_cons_of_mem _ member))]
        rfl
    simp only [machineValue?, valueAtom, valuesAtom_eq, listed, Option.bind_eq_bind, Option.bind_some, decoded]
    rfl

/-- The size of an occurrence's values. -/
def Occ.size (occurrence : Occ) : Nat := 2 + Value.listSize occurrence.values

theorem occurrence_occAtom (name : String) (occurrence : Occ) (fuel : Nat) (bounded : Occ.size occurrence ≤ fuel) :
    occurrence? fuel name occurrence.values.length (occAtom occurrence) =
      some (occurrence.id, ⟨name, occurrence.values⟩) := by
  have lengthBound := listSize_length occurrence.values
  have listed := listAtoms_listAtom (occurrence.values.map valueAtom) fuel
    (by simp only [List.length_map, Occ.size] at bounded ⊢; omega)
  have decoded : (occurrence.values.map valueAtom).mapM (machineValue? fuel) = some occurrence.values := by
    have each : ∀ value ∈ occurrence.values, machineValue? fuel (valueAtom value) = some value := by
      intro value inside
      have smaller := size_le_listSize occurrence.values value inside
      exact machineValue_valueAtom value fuel (by simp only [Occ.size] at bounded; omega)
    clear bounded lengthBound listed
    generalize occurrence.values = values at each ⊢
    induction values with
    | nil => rfl
    | cons first rest ih =>
      simp only [List.map_cons, List.mapM_cons, each first List.mem_cons_self,
        ih (fun value member => each value (List.mem_cons_of_mem _ member))]
      rfl
  simp only [occurrence?, occAtom, valuesAtom_eq, listed, Option.bind_eq_bind, Option.bind_some, decoded,
    beq_self_eq_true, ↓reduceIte]
  have nonneg : ¬ ((occurrence.id : Int) < 0) := by omega
  simp [natural?, integer, nonneg]

/-! ## Sizes: the observer's fuel covers every encoded part -/

theorem listAtom_size : ∀ (items : List Atom),
    items.length + 1 ≤ atomSize (listAtom items) ∧ ∀ item ∈ items, atomSize item < atomSize (listAtom items)
  | [] => ⟨by simp [listAtom, nil, atomSize], by simp⟩
  | first :: rest => by
    obtain ⟨lengthBound, itemBound⟩ := listAtom_size rest
    simp only [listAtom, cons, atomSize, atomsSize]
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    intro item member
    rcases List.mem_cons.mp member with rfl | later
    · omega
    · have := itemBound item later
      omega

mutual
  theorem valueAtom_size : ∀ (value : Value), Value.size value ≤ atomSize (valueAtom value)
    | .integer _ => by simp [Value.size, valueAtom, integer, atomSize]
    | .atom _ => by simp [Value.size, valueAtom, atomSize]
    | .tuple fields => by
      have := valuesAtom_size fields
      simp only [Value.size, valueAtom, atomSize, atomsSize]
      omega
  theorem valuesAtom_size : ∀ (values : List Value), Value.listSize values ≤ atomSize (valuesAtom values)
    | [] => by simp [Value.listSize, valuesAtom, nil, atomSize]
    | first :: rest => by
      have one := valueAtom_size first
      have two := valuesAtom_size rest
      simp only [Value.listSize, valuesAtom, cons, atomSize, atomsSize]
      omega
end

theorem occAtom_size (occurrence : Occ) : Occ.size occurrence ≤ atomSize (occAtom occurrence) := by
  have := valuesAtom_size occurrence.values
  simp only [Occ.size, occAtom, atomSize, atomsSize, integer]
  omega

theorem slot_slotAtom (key : Key) (occurrences : List Occ) (fuel : Nat)
    (arity : ∀ occurrence ∈ occurrences, occurrence.values.length = key.2)
    (bounded : atomSize (occsAtom occurrences) < fuel) :
    slot? fuel (slotAtom (key, occurrences)) =
      some (occurrences.map fun occurrence => (occurrence.id, ⟨key.1, occurrence.values⟩)) := by
  obtain ⟨lengthBound, itemBound⟩ := listAtom_size (occurrences.map occAtom)
  have listed := listAtoms_listAtom (occurrences.map occAtom) fuel
    (by simp only [occsAtom] at bounded; simp only [List.length_map] at lengthBound ⊢; omega)
  have each : ∀ occurrence ∈ occurrences, occurrence? fuel key.1 key.2 (occAtom occurrence) =
      some (occurrence.id, ⟨key.1, occurrence.values⟩) := by
    intro occurrence member
    rw [← arity occurrence member]
    apply occurrence_occAtom
    have small := itemBound (occAtom occurrence) (List.mem_map_of_mem member)
    have := occAtom_size occurrence
    simp only [occsAtom] at bounded
    omega
  have mapped : (occurrences.map occAtom).mapM (occurrence? fuel key.1 key.2) =
      some (occurrences.map fun occurrence => (occurrence.id, ⟨key.1, occurrence.values⟩)) := by
    clear listed itemBound lengthBound bounded arity
    induction occurrences with
    | nil => rfl
    | cons first rest ih =>
      simp only [List.map_cons, List.mapM_cons, each first List.mem_cons_self,
        ih (fun occurrence member => each occurrence (List.mem_cons_of_mem _ member))]
      rfl
  rw [List.mapM_map] at mapped
  simp only [slot?, slotAtom, keyAtom, natural?, integer, Int.natCast_nonneg, not_lt.mpr, Int.toNat_natCast]
  simp [listed, mapped, occsAtom]

/-- A `mapM` whose function agrees with a total one returns its map. -/
theorem mapM_pointwise {α β : Type} (decode : α → Option β) (total : α → β) :
    ∀ (items : List α), (∀ item ∈ items, decode item = some (total item)) →
      items.mapM decode = some (items.map total)
  | [], _ => rfl
  | first :: rest, agree => by
    simp only [List.mapM_cons, agree first List.mem_cons_self, List.map_cons,
      mapM_pointwise decode total rest (fun item member => agree item (List.mem_cons_of_mem _ member))]
    rfl

/-- What the observer reads from a store: each slot's occurrences, with the
slot's name, in store order. -/
def decodedStore (store : Store) : List (List (Nat × Constraint)) :=
  store.map fun entry => entry.2.map fun occurrence => (occurrence.id, ⟨entry.1.1, occurrence.values⟩)

theorem store_decode (store : Store) (coherent : Coherent store) (fuel : Nat)
    (bounded : atomSize (storeAtom store) < fuel) :
    listAtoms? fuel (storeAtom store) = some (store.map slotAtom) ∧
      (store.map slotAtom).mapM (slot? fuel) = some (decodedStore store) := by
  obtain ⟨lengthBound, itemBound⟩ := listAtom_size (store.map slotAtom)
  have listed := listAtoms_listAtom (store.map slotAtom) fuel
    (by simp only [storeAtom] at bounded; simp only [List.length_map] at lengthBound ⊢; omega)
  have each : ∀ entry ∈ store, slot? fuel (slotAtom entry) =
      some (entry.2.map fun occurrence => (occurrence.id, ⟨entry.1.1, occurrence.values⟩)) := by
    intro entry member
    obtain ⟨key, occurrences⟩ := entry
    apply slot_slotAtom key occurrences fuel (fun occurrence inside => coherent.arity _ member occurrence inside)
    have small := itemBound (slotAtom (key, occurrences)) (List.mem_map_of_mem member)
    simp only [storeAtom] at bounded
    simp only [slotAtom, atomSize, atomsSize] at small
    omega
  have mapped : (store.map slotAtom).mapM (slot? fuel) = some (decodedStore store) := by
    rw [List.mapM_map]
    exact mapM_pointwise _ _ store each
  exact ⟨listed, mapped⟩

theorem decodedStore_flatten (store : Store) :
    (decodedStore store).flatten = (contents store).map fun occurrence => (occurrence.id, occurrence.constraint) := by
  simp [decodedStore, contents, List.flatMap, List.map_flatten, List.map_map, Function.comp_def]

/-! ## The observation of a completed run -/

/-- The final store as the observer reports it: identifiers and constraints,
ordered by identifier. -/
def orderedContents (store : Store) : List (Nat × Constraint) :=
  ((contents store).map fun occurrence => (occurrence.id, occurrence.constraint)).mergeSort
    fun first second => first.1 ≤ second.1

theorem orderedContents_perm (store : Store) :
    (orderedContents store).Perm ((contents store).map fun occurrence => (occurrence.id, occurrence.constraint)) :=
  List.mergeSort_perm _ _

theorem completeObservation_ok (lowered : Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLowering.Program)
    (dictionary : Dictionary) (stored : List (Nat × Constraint)) (seedIds : List Nat)
    (posted : seedIds.length = dictionary.captured.length + dictionary.queries)
    (distinct : ((stored.mergeSort fun first second => first.1 ≤ second.1).map Prod.fst).Nodup)
    (allDeclared : (stored.mergeSort fun first second => first.1 ≤ second.1).all
      (fun entry => declared lowered.program entry.2.name entry.2.arguments.length) = true) :
    completeObservation lowered dictionary stored seedIds =
      .ok (completeJson dictionary seedIds (stored.mergeSort fun first second => first.1 ≤ second.1)) := by
  simp only [completeObservation]
  -- Splitting the first check settles the other two from `distinct` and `allDeclared`.
  split
  · next different => exact absurd posted different
  rfl

theorem observe_complete (lowered : Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLowering.Program)
    (dictionary : Dictionary) (machine : MachineState) (coherent : Coherent machine.store)
    (postedAll : machine.seeds.length = dictionary.captured.length + dictionary.queries)
    (declaredAll : ∀ occurrence ∈ contents machine.store,
      declared lowered.program occurrence.constraint.name occurrence.constraint.arguments.length = true) :
    observeResult lowered dictionary (.expression [.symbol "ChrMachineResult", .symbol "ChrComplete",
        storeAtom machine.store, idsAtom machine.seeds.reverse]) =
      .ok (completeJson dictionary machine.seeds.reverse (orderedContents machine.store)) := by
  have storeSize := listAtom_size (machine.store.map slotAtom)
  have seedSize := listAtom_size (machine.seeds.reverse.map natAtom)
  obtain ⟨storeListed, storeMapped⟩ := store_decode machine.store coherent
    (atomSize (storeAtom machine.store) + atomSize (idsAtom machine.seeds.reverse) + 1) (by omega)
  have seedsListed : listAtoms? (atomSize (storeAtom machine.store) + atomSize (idsAtom machine.seeds.reverse) + 1)
      (idsAtom machine.seeds.reverse) = some (machine.seeds.reverse.map natAtom) :=
    listAtoms_listAtom (machine.seeds.reverse.map natAtom) _ (by simp only [idsAtom] at seedSize ⊢; omega)
  have seedsDecoded : (machine.seeds.reverse.map natAtom).mapM natural? = some machine.seeds.reverse := by
    rw [List.mapM_map]
    have each := mapM_pointwise (natural? ∘ natAtom) id machine.seeds.reverse
      (fun id _ => by simp [Function.comp, natural_natAtom])
    simpa using each
  have distinct : ((orderedContents machine.store).map Prod.fst).Nodup := by
    have permuted := (orderedContents_perm machine.store).map Prod.fst
    simp only [List.map_map, Function.comp_def] at permuted
    exact permuted.nodup_iff.mpr coherent.ids
  have allDeclared : (orderedContents machine.store).all (fun entry =>
      declared lowered.program entry.2.name entry.2.arguments.length) = true := by
    apply List.all_eq_true.mpr
    intro entry member
    have inContents := (orderedContents_perm machine.store).subset member
    obtain ⟨occurrence, inside, rfl⟩ := List.mem_map.mp inContents
    exact declaredAll occurrence inside
  have postedLength : machine.seeds.reverse.length = dictionary.captured.length + dictionary.queries := by
    simpa using postedAll
  simp only [observeResult]
  rw [storeListed]
  dsimp only
  rw [storeMapped]
  dsimp only
  rw [seedsListed]
  dsimp only
  rw [seedsDecoded]
  dsimp only
  rw [decodedStore_flatten]
  exact completeObservation_ok lowered dictionary _ _ postedLength distinct allDeclared

/-! ## Observation at the text boundary -/

/-- The result a completed run reports to the observer. -/
def completeResult (machine : MachineState) : Atom :=
  .expression [.symbol "ChrMachineResult", .symbol "ChrComplete", storeAtom machine.store,
    idsAtom machine.seeds.reverse]

/-- **Observation at the text boundary.** The observer reads a printed result
back as exactly that result, so observing its text is observing the result. -/
theorem observe_text (wire dictionaryText data separator : String) (result : Atom)
    (printed : ReadAfterRender.render? result = some data) (expression : ∃ items, result = .expression items) :
    observe wire dictionaryText data separator =
      (do
        let lowered ← program? wire
        let dictionary ← dictionary? dictionaryText
        observeResult lowered dictionary result) := by
  simp only [observe, ReadAfterRender.readSource_render printed expression]

/-- A completed run, observed through its printed text. -/
theorem observe_complete_text (wire dictionaryText data separator : String)
    (lowered : Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLowering.Program) (dictionary : Dictionary)
    (machine : MachineState) (read : program? wire = .ok lowered)
    (dictionaryRead : dictionary? dictionaryText = .ok dictionary)
    (printed : ReadAfterRender.render? (completeResult machine) = some data) (coherent : Coherent machine.store)
    (postedAll : machine.seeds.length = dictionary.captured.length + dictionary.queries)
    (declaredAll : ∀ occurrence ∈ contents machine.store,
      declared lowered.program occurrence.constraint.name occurrence.constraint.arguments.length = true) :
    observe wire dictionaryText data separator =
      .ok (completeJson dictionary machine.seeds.reverse (orderedContents machine.store)) := by
  rw [observe_text wire dictionaryText data separator _ printed ⟨_, rfl⟩]
  simp only [read, dictionaryRead, bind, Except.bind]
  exact observe_complete lowered dictionary machine coherent postedAll declaredAll

/-- **The observed values are a refined CHR final store.** When a bounded run
of the machine has completed, the constraints the observer reports are, as a
multiset, the final store of a completed run of the refined CHR relation from
the same constraints; the run's store is coherent and it posted every seed. -/
theorem ordered_refines (program : Mettapedia.Languages.CHR.Program) (constraints : List Constraint)
    (budget : Nat) (final : MachineState)
    (reached : Mettapedia.Languages.CHR.Machine.advance (Mettapedia.Languages.CHR.Machine.table program) budget
      (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead)) = final)
    (running : final.status = .running) (finished : final.tasks = []) :
    Coherent final.store ∧ final.seeds.length = constraints.length ∧
      ∃ abstract store, Relation.ReflTransGen (Mettapedia.Languages.CHR.Step program)
          (Mettapedia.Languages.CHR.initial constraints) abstract ∧
        Mettapedia.Languages.CHR.observe abstract = .completed store ∧
        ((orderedContents final.store).map Prod.snd).Perm store := by
  have posting := Mettapedia.Languages.CHR.Machine.run_posting program constraints budget
  obtain ⟨abstract, run, simulates, related⟩ :=
    Mettapedia.Languages.CHR.Machine.advance_refines program constraints budget
  subst reached
  refine ⟨simulates.coherent, Mettapedia.Languages.CHR.Machine.completed_posted constraints _ posting finished, ?_⟩
  have completed : Mettapedia.Languages.CHR.Machine.outcome
      (Mettapedia.Languages.CHR.Machine.advance (Mettapedia.Languages.CHR.Machine.table program) budget
        (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead))) =
      .completed ((contents (Mettapedia.Languages.CHR.Machine.advance (Mettapedia.Languages.CHR.Machine.table program)
        budget (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead))).store).map
          Mettapedia.Languages.CHR.Occurrence.constraint) := by
    simp [Mettapedia.Languages.CHR.Machine.outcome, running, finished]
  rw [completed] at related
  generalize observed : Mettapedia.Languages.CHR.observe abstract = result at related
  cases related with
  | completed machineStore abstractStore permuted =>
    have ordered := (orderedContents_perm (Mettapedia.Languages.CHR.Machine.advance
      (Mettapedia.Languages.CHR.Machine.table program) budget
      (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead))).store).map Prod.snd
    simp only [List.map_map, Function.comp_def] at ordered
    exact ⟨abstract, abstractStore, run, observed, ordered.trans permuted.symm⟩

/-! ## Declared stores and the whole observation -/

theorem declared_bool (program : Mettapedia.Languages.CHR.Program) (name : String) (arity : Nat)
    (holds : Mettapedia.Languages.CHR.Declared program name arity) : declared program name arity = true := by
  obtain ⟨declaration, member, named, sized⟩ := holds
  simp only [declared, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨declaration, member, named, sized⟩

/-- A bounded machine run of an admitted program from declared constraints
stores only declared constraints. -/
theorem machine_declared (program : Mettapedia.Languages.CHR.Program)
    (admitted : Mettapedia.Languages.CHR.Admission.diagnose program = none) (constraints : List Constraint)
    (seeds : ∀ constraint ∈ constraints,
      Mettapedia.Languages.CHR.Declared program constraint.name constraint.arguments.length)
    (budget : Nat) :
    ∀ occurrence ∈ contents (Mettapedia.Languages.CHR.Machine.advance (Mettapedia.Languages.CHR.Machine.table program)
        budget (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead))).store,
      Mettapedia.Languages.CHR.Declared program occurrence.constraint.name occurrence.constraint.arguments.length := by
  obtain ⟨abstract, run, simulates, _⟩ := Mettapedia.Languages.CHR.Machine.advance_refines program constraints budget
  intro occurrence member
  exact Mettapedia.Languages.CHR.admitted_store_declared program admitted constraints seeds run occurrence
    (simulates.store.symm.subset member)

/-- **C0 observation, end to end.** Let an admitted program run from declared
constraints, as many as the dictionary's captured occurrences and queries,
until the machine completes. The observer, given the printed result, reports
the ordered final constraints and their publication, and those constraints
are, as a multiset, the final store of a completed run of the refined CHR
relation from the same constraints. -/
theorem observed_refines (wire dictionaryText data separator : String)
    (lowered : Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLowering.Program) (dictionary : Dictionary)
    (constraints : List Constraint) (budget : Nat) (final : MachineState)
    (read : program? wire = .ok lowered) (dictionaryRead : dictionary? dictionaryText = .ok dictionary)
    (admitted : Mettapedia.Languages.CHR.Admission.diagnose lowered.program = none)
    (seeds : ∀ constraint ∈ constraints,
      Mettapedia.Languages.CHR.Declared lowered.program constraint.name constraint.arguments.length)
    (counted : constraints.length = dictionary.captured.length + dictionary.queries)
    (reached : Mettapedia.Languages.CHR.Machine.advance (Mettapedia.Languages.CHR.Machine.table lowered.program)
      budget (Mettapedia.Languages.CHR.Machine.start (constraints.map Constraint.asHead)) = final)
    (running : final.status = .running) (finished : final.tasks = [])
    (printed : ReadAfterRender.render? (completeResult final) = some data) :
    observe wire dictionaryText data separator =
        .ok (completeJson dictionary final.seeds.reverse (orderedContents final.store)) ∧
      ∃ abstract store, Relation.ReflTransGen (Mettapedia.Languages.CHR.Step lowered.program)
          (Mettapedia.Languages.CHR.initial constraints) abstract ∧
        Mettapedia.Languages.CHR.observe abstract = .completed store ∧
        ((orderedContents final.store).map Prod.snd).Perm store := by
  have declaredAll := machine_declared lowered.program admitted constraints seeds budget
  rw [reached] at declaredAll
  obtain ⟨coherent, posted, refined⟩ :=
    ordered_refines lowered.program constraints budget final reached running finished
  exact ⟨observe_complete_text wire dictionaryText data separator lowered dictionary final read dictionaryRead printed
    coherent (posted.trans counted)
    (fun occurrence member => declared_bool _ _ _ (declaredAll occurrence member)), refined⟩

#print axioms listAtoms_listAtom
#print axioms observe_complete
#print axioms observe_complete_text
#print axioms ordered_refines
#print axioms observed_refines
#print axioms slot_slotAtom
#print axioms machineValue_valueAtom
#print axioms occurrence_occAtom

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
