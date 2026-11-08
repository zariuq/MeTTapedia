import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeEndToEnd
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompilerLaws
import Mettapedia.Languages.CHR.MachineSeedIds

/-! The publication is exact. For a bounded run from captured occurrences and
query constraints, the transform the observer reports (consume the captured
ordinals whose identifiers left the store, add the occurrences that are new)
turns the captured occurrences into exactly the final store, as a multiset;
for a completed run that is the final store of a completed refined CHR run. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler

open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution (orderedContents orderedContents_perm
  ordered_refines)

theorem mapM_ok_forall₂ {α β ε : Type} (f : α → Except ε β) :
    ∀ (inputs : List α) (outputs : List β), inputs.mapM f = .ok outputs →
      List.Forall₂ (fun input output => f input = .ok output) inputs outputs
  | [], outputs, mapped => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at mapped
    subst mapped
    exact .nil
  | first :: rest, outputs, mapped => by
    rw [List.mapM_cons] at mapped
    cases one : f first with
    | error message => simp [one, bind, Except.bind] at mapped
    | ok value =>
      cases others : rest.mapM f with
      | error message => simp [one, others, bind, Except.bind] at mapped
      | ok values =>
        simp only [one, others, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at mapped
        subst mapped
        exact .cons one (mapM_ok_forall₂ f rest values others)

theorem reduceOption_ordinals {α γ : Type} {indexed : List (α × Nat)} {results : List (Option (Nat × γ))}
    (related : List.Forall₂ (fun pair result => result = none ∨ ∃ value, result = some (pair.2, value))
      indexed results) :
    (results.reduceOption.map Prod.fst).Sublist (indexed.map Prod.snd) := by
  induction related with
  | nil => simp
  | cons head _ ih =>
    rcases head with rfl | ⟨value, rfl⟩
    · simp only [List.reduceOption_cons_of_none, List.map_cons]
      exact ih.cons _
    · simp only [List.reduceOption_cons_of_some, List.map_cons]
      exact ih.cons_cons _

/-- Captured occurrences carry distinct selection ordinals. -/
theorem capture_ordinals (program : CHR.Program) (rows : List HostShape) (captured : List (Nat × CHR.Constraint))
    (taken : capture program rows = .ok captured) : (captured.map Prod.fst).Nodup := by
  unfold capture at taken
  simp only [bind, Except.bind] at taken
  split at taken
  · cases taken
  · rename_i results mapped
    simp only [pure, Except.pure, Except.ok.injEq] at taken
    subst taken
    have related := mapM_ok_forall₂ _ _ _ mapped
    have shaped : List.Forall₂ (fun (pair : HostShape × Nat) result =>
        result = none ∨ ∃ value, result = some (pair.2, value)) rows.zipIdx results := by
      refine related.imp ?_
      intro pair result produced
      obtain ⟨row, ordinal⟩ := pair
      simp only at produced
      cases row' : captureRow program row with
      | error message => simp [row'] at produced
      | ok option =>
        cases option with
        | none =>
          simp [row', pure, Except.pure] at produced
          subst produced
          exact .inl rfl
        | some constraint =>
          simp [row', pure, Except.pure] at produced
          subst produced
          exact .inr ⟨constraint, rfl⟩
    have sub := reduceOption_ordinals shaped
    rw [List.zipIdx_map_snd] at sub
    exact sub.nodup (List.nodup_range' (s := 0) (n := rows.length))

theorem zip_fst_sublist {α β : Type} : ∀ (first : List α) (second : List β),
    ((first.zip second).map Prod.fst).Sublist first
  | [], _ => by simp
  | _ :: _, [] => by simp
  | head :: tail, _ :: others => by simpa using (zip_fst_sublist tail others).cons_cons head

theorem zip_snd_sublist {α β : Type} : ∀ (first : List α) (second : List β),
    ((first.zip second).map Prod.snd).Sublist second
  | _, [] => by simp
  | [], _ :: _ => by simp
  | _ :: tail, head :: others => by simpa using (zip_snd_sublist tail others).cons_cons head

/-- Captured occurrences with the identifiers they were posted under:
ordinal, identifier, constraint. -/
def capturedRows (captured : List (Nat × CHR.Constraint)) (posted : List Nat) : List (Nat × Nat × CHR.Constraint) :=
  (captured.zip (posted.take captured.length)).map fun pair => (pair.1.1, pair.2, pair.1.2)

/-- The rows' ordinals and identifiers are the pairs the observer's
publication uses. -/
theorem capturedRows_pairs (captured : List (Nat × CHR.Constraint)) (posted : List Nat) :
    (capturedRows captured posted).map (fun row => (row.1, row.2.1)) =
      (captured.map Prod.fst).zip (posted.take captured.length) := by
  rw [List.zip_map_left, capturedRows, List.map_map]
  rfl

/-- **The publication is exact.** The captured occurrences the publication
does not consume, with its additions, are the final store's constraints, as
a multiset. -/
theorem publication_exact (program : CHR.Program) (captured : List (Nat × CHR.Constraint))
    (inputs : List CHR.Constraint) (ordinals : (captured.map Prod.fst).Nodup) (budget : Nat)
    (final : CHR.Machine.State)
    (reached : CHR.Machine.advance (CHR.Machine.table program) budget
      (CHR.Machine.start ((captured.map Prod.snd ++ inputs).map CHR.Constraint.asHead)) = final) :
    (((capturedRows captured final.seeds.reverse).filter fun row =>
        row.1 ∉ consumed ((capturedRows captured final.seeds.reverse).map fun row => (row.1, row.2.1))
          (orderedContents final.store)).map (·.2.2) ++
      (additions ((capturedRows captured final.seeds.reverse).map fun row => (row.1, row.2.1))
        (orderedContents final.store)).map Prod.snd).Perm
      ((orderedContents final.store).map Prod.snd) := by
  have posting := CHR.Machine.run_posting program (captured.map Prod.snd ++ inputs) budget
  have distinct := CHR.Machine.run_seeds_nodup program (captured.map Prod.snd ++ inputs) budget
  obtain ⟨abstract, _, simulates, _⟩ :=
    CHR.Machine.advance_refines program (captured.map Prod.snd ++ inputs) budget
  rw [reached] at posting distinct simulates
  apply publication_perm
  · -- distinct ordinals
    have sub := (zip_fst_sublist captured (final.seeds.reverse.take captured.length)).map Prod.fst
    simp only [List.map_map, Function.comp_def] at sub
    simp only [capturedRows, List.map_map, Function.comp_def]
    exact sub.nodup ordinals
  · -- distinct identifiers
    have sub := zip_snd_sublist captured (final.seeds.reverse.take captured.length)
    simp only [capturedRows, List.map_map, Function.comp_def]
    exact (sub.trans (List.take_sublist _ _)).nodup (List.nodup_reverse.mpr distinct)
  · -- distinct final identifiers
    have permuted := (orderedContents_perm final.store).map Prod.fst
    simp only [List.map_map, Function.comp_def] at permuted
    exact permuted.nodup_iff.mpr simulates.coherent.ids
  · -- a captured identifier names its captured constraint
    intro row rowMember entry entryMember sameId
    obtain ⟨⟨⟨ordinal, constraint⟩, id⟩, zipped, rfl⟩ := List.mem_map.mp rowMember
    obtain ⟨index, atIndex⟩ := List.mem_iff_getElem?.mp zipped
    rw [List.getElem?_zip_eq_some] at atIndex
    obtain ⟨capturedAt, postedAt⟩ := atIndex
    change captured[index]? = some (ordinal, constraint) at capturedAt
    change (final.seeds.reverse.take captured.length)[index]? = some id at postedAt
    have short : index < captured.length := (List.getElem?_eq_some_iff.mp capturedAt).1
    rw [List.getElem?_take_of_lt short] at postedAt
    have seedAt : (captured.map Prod.snd ++ inputs)[index]? = some constraint := by
      have shortMapped : index < (captured.map Prod.snd).length := by simpa using short
      simp [List.getElem?_append_left shortMapped, capturedAt]
    have inContents := (orderedContents_perm final.store).subset entryMember
    obtain ⟨occurrence, inside, rfl⟩ := List.mem_map.mp inContents
    exact (posting.stored index id constraint postedAt seedAt occurrence inside sameId.symm).symm

/-- **The published Space is a refined CHR final store.** For a completed run,
the captured occurrences left after the consumption, with the additions, are
as a multiset the final store of a completed refined CHR run from the
captured constraints followed by the query. -/
theorem publication_refines (program : CHR.Program) (captured : List (Nat × CHR.Constraint))
    (inputs : List CHR.Constraint) (ordinals : (captured.map Prod.fst).Nodup) (budget : Nat)
    (final : CHR.Machine.State)
    (reached : CHR.Machine.advance (CHR.Machine.table program) budget
      (CHR.Machine.start ((captured.map Prod.snd ++ inputs).map CHR.Constraint.asHead)) = final)
    (running : final.status = .running) (finished : final.tasks = []) :
    ∃ abstract store, Relation.ReflTransGen (CHR.Step program) (CHR.initial (captured.map Prod.snd ++ inputs))
        abstract ∧ CHR.observe abstract = .completed store ∧
      (((capturedRows captured final.seeds.reverse).filter fun row =>
          row.1 ∉ consumed ((capturedRows captured final.seeds.reverse).map fun row => (row.1, row.2.1))
            (orderedContents final.store)).map (·.2.2) ++
        (additions ((capturedRows captured final.seeds.reverse).map fun row => (row.1, row.2.1))
          (orderedContents final.store)).map Prod.snd).Perm store := by
  obtain ⟨_, _, abstract, store, run, observed, refined⟩ :=
    ordered_refines program (captured.map Prod.snd ++ inputs) budget final reached running finished
  exact ⟨abstract, store, run, observed,
    (publication_exact program captured inputs ordinals budget final reached).trans refined⟩

/-- **C0 publication, from preparation.** For a ready preparation and a
completed bounded run of its port, the captured occurrences that the
observer's transform keeps, with its additions, are as a multiset the final
store of a completed refined CHR run from the posted seeds. The pairs are the
ones the observer's publication uses for the dictionary of this preparation. -/
theorem prepared_publication (wire rows : String) (lowered : CHRPrologLowering.Program)
    (captured : List (Nat × CHR.Constraint)) (definitions : String)
    (ready : prepareRun wire rows "lang:compiled" = .ok (.ready lowered captured definitions))
    (budget : Nat) (final : CHR.Machine.State)
    (reached : CHR.Machine.advance (CHR.Machine.table lowered.program) budget
      (CHR.Machine.start ((seedsOf lowered captured).map CHR.Constraint.asHead)) = final)
    (running : final.status = .running) (finished : final.tasks = []) :
    ∃ abstract store, Relation.ReflTransGen (CHR.Step lowered.program) (CHR.initial (seedsOf lowered captured))
        abstract ∧ CHR.observe abstract = .completed store ∧
      (((capturedRows captured final.seeds.reverse).filter fun row =>
          row.1 ∉ consumed ((captured.map Prod.fst).zip (final.seeds.reverse.take captured.length))
            (orderedContents final.store)).map (·.2.2) ++
        (additions ((captured.map Prod.fst).zip (final.seeds.reverse.take captured.length))
          (orderedContents final.store)).map Prod.snd).Perm store := by
  obtain ⟨_, _, _, _, shapes, _, taken⟩ :=
    prepareRun_ready wire rows "lang:compiled" lowered captured definitions ready
  have refined := publication_refines lowered.program captured lowered.inputs (capture_ordinals _ _ _ taken)
    budget final reached running finished
  rw [capturedRows_pairs] at refined
  exact refined

#print axioms publication_exact
#print axioms publication_refines
#print axioms prepared_publication

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler
