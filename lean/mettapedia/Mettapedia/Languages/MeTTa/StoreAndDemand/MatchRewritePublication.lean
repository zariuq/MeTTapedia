import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection
import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.OrderedStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces

/-!
# Ordered publication of an occurrence census

For each occurrence, a complete read supplies a finite fibre of output values.
A singleton fibre determines the output, and an empty fibre leaves the old
occurrence alone. An incomplete or ambiguous read refuses preparation. The
ordered Transform step consumes the selected identities and appends the
materialized outputs with independently scoped variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StoreAndDemand.MatchRewritePublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)
open Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection (atomFrames)
open Interface
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

universe u

/-- A complete list of possible materialized replacements for a single
occurrence. Missing coverage is represented separately from a complete miss. -/
abbrev Replacement := Nat → Atom → Option (List Atom)

/-- An injective row-local renaming outside the complete supplied scope. -/
def freshRow (avoid : List String) (use : Nat) (row : Atom) : Atom :=
  rename (HE.instanceName avoid (atomFreeVars row).eraseDups use) row

theorem freshRow_avoids (avoid : List String) (use : Nat) (row : Atom) :
    ∀ x ∈ atomFreeVars (freshRow avoid use row), x ∉ avoid := by
  intro x visible
  rw [freshRow, freeVars_rename] at visible
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp visible
  exact HE.instanceName_not_mem _ _ _ name

theorem freshRow_variant (avoid : List String) (use : Nat) (row : Atom) :
    Variant row (freshRow avoid use row) := by
  let forward := HE.instanceName avoid (atomFreeVars row).eraseDups use
  have injection : Function.Injective forward := HE.instanceName_injective _ _ _
  refine ⟨forward, Function.invFun forward, rfl, ?_⟩
  change rename (Function.invFun forward) (rename forward row) = row
  rw [composition]
  exact ((equal_iff_on_variables _ id row).mpr fun name _ =>
    Function.leftInverse_invFun injection name).trans (identity row)

inductive PreparedError where
  | incomplete
  | ambiguous
  deriving DecidableEq, Repr

variable {O : Type u} (label : O → Atom) (replace : Replacement)

/-- Compute once from the entry population. The output atoms are never
passed through the matcher or evaluated. -/
def prepare : Nat → List O → Except PreparedError (List (O × Atom))
  | _, [] => .ok []
  | use, o :: rest =>
    match replace use (label o) with
    | none => .error .incomplete
    | some [] => prepare (use + 1) rest
    | some [replacement] =>
      match prepare (use + 1) rest with
      | .ok later => .ok ((o, replacement) :: later)
      | .error reason => .error reason
    | some (_ :: _ :: _) => .error .ambiguous

/-- Declarative completeness of the entry census. A successful scan with
no hits still visited every entry and certified each one as a miss. -/
inductive Census : Nat → List O → List (O × Atom) → Prop
  | nil (use) : Census use [] []
  | miss {use o rest remaining} (refuted : replace use (label o) = some [])
      (later : Census (use + 1) rest remaining) : Census use (o :: rest) remaining
  | hit {use o rest remaining value} (output : replace use (label o) = some [value])
      (later : Census (use + 1) rest remaining) : Census use (o :: rest) ((o, value) :: remaining)

theorem prepare_iff (use : Nat) (rows : List O) (items : List (O × Atom)) :
    prepare label replace use rows = .ok items ↔ Census label replace use rows items := by
  constructor
  · induction rows generalizing use items with
    | nil =>
      intro ready
      cases ready
      exact .nil use
    | cons o rest ih =>
      intro ready
      cases outcome : replace use (label o) with
      | none => simp [prepare, outcome] at ready
      | some values =>
        cases values with
        | nil =>
          exact .miss outcome (ih _ _ (by simpa [prepare, outcome] using ready))
        | cons value tail =>
          cases tail with
          | nil =>
            cases suffix : prepare label replace (use + 1) rest with
            | error reason => simp [prepare, outcome, suffix] at ready
            | ok later =>
              have shape : (o, value) :: later = items := by simpa [prepare, outcome, suffix] using ready
              subst items
              exact .hit outcome (ih _ _ suffix)
          | cons second extra => simp [prepare, outcome] at ready
  · intro census
    induction census with
    | nil => rfl
    | miss decision _ ih => simp [prepare, decision, ih]
    | hit decision _ ih => simp [prepare, decision, ih]

theorem Census.selected_sublist {use rows items} (census : Census label replace use rows items) :
    (items.map Prod.fst).Sublist rows := by
  induction census with
  | nil => exact List.Sublist.slnil
  | miss _ _ ih => exact ih.cons _
  | hit _ _ ih => exact ih.cons_cons _

/-- Every entry with a decided unique replacement was selected at that
position, and every selected entry comes from such an input. -/
theorem Census.member_iff {use rows items} (census : Census label replace use rows items)
    (item : O × Atom) :
    item ∈ items ↔ ∃ (i : Nat) (h : i < rows.length),
      rows[i] = item.1 ∧ replace (use + i) (label rows[i]) = some [item.2] := by
  induction census with
  | nil => simp
  | @miss use o rest remaining refuted later ih =>
    rw [ih]
    constructor
    · rintro ⟨i, within, row, output⟩
      exact ⟨i + 1, by simp [within], row,
        by simpa only [List.getElem_cons_succ, show use + (i + 1) = use + 1 + i by omega] using output⟩
    · rintro ⟨i, within, row, output⟩
      cases i with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero, refuted] at output
        cases output
      | succ i =>
        exact ⟨i, by simpa using within, row,
          by simpa only [List.getElem_cons_succ, show use + i.succ = use + 1 + i by omega] using output⟩
  | @hit use o rest remaining value output later ih =>
    rw [List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, within, row, answer⟩)
      · exact ⟨0, by simp, rfl, by simpa using output⟩
      · exact ⟨i + 1, by simp [within], row,
          by simpa only [List.getElem_cons_succ, show use + (i + 1) = use + 1 + i by omega] using answer⟩
    · rintro ⟨i, within, row, answer⟩
      cases i with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero, output, Option.some.injEq,
          List.singleton_inj] at answer
        exact .inl (Prod.ext row.symm answer.symm)
      | succ i =>
        exact .inr ⟨i, by simpa using within, row,
          by simpa only [List.getElem_cons_succ, show use + i.succ = use + 1 + i by omega] using answer⟩

variable [DecidableEq O]

/-- Choose a representative of each new row's private schema. The scope
for the next row includes every variable allocated in this one. -/
def closeOutputs (avoid : List String) : List Atom → List Atom
  | [] => []
  | atom :: rest =>
    let closedRow := freshRow avoid 0 atom
    closedRow :: closeOutputs (atomFreeVars closedRow ++ avoid) rest

theorem closeOutputs_length (avoid : List String) (values : List Atom) :
    (closeOutputs avoid values).length = values.length := by
  induction values generalizing avoid with
  | nil => rfl
  | cons atom rest ih => simp [closeOutputs, ih]

/-- Renaming preserves the template tree and every repeated variable within
one row, including output-only variables. -/
theorem closeOutputs_variants (avoid : List String) (values : List Atom) :
    List.Forall₂ Variant values (closeOutputs avoid values) := by
  induction values generalizing avoid with
  | nil => exact .nil
  | cons atom rest ih => exact .cons (freshRow_variant avoid 0 atom) (ih _)

/-- Each new schema uses no variable spelling in the supplied context;
the generated schemas also have independent variable names. -/
theorem closeOutputs_apart (avoid : List String) (values : List Atom) :
    (∀ atom ∈ closeOutputs avoid values, ∀ x ∈ atomFreeVars atom, x ∉ avoid) ∧
      (closeOutputs avoid values).Pairwise (fun first later =>
        ∀ x ∈ atomFreeVars first, x ∉ atomFreeVars later) := by
  induction values generalizing avoid with
  | nil => simp [closeOutputs]
  | cons atom rest ih =>
    let first := freshRow avoid 0 atom
    obtain ⟨laterAvoid, laterApart⟩ := ih (atomFreeVars first ++ avoid)
    change (∀ a ∈ first :: closeOutputs (atomFreeVars first ++ avoid) rest,
      ∀ x ∈ atomFreeVars a, x ∉ avoid) ∧ _
    refine ⟨?_, List.pairwise_cons.mpr ⟨fun later member x name clash => ?_, laterApart⟩⟩
    · intro a member x name
      rcases List.mem_cons.mp member with rfl | later
      · exact freshRow_avoids avoid 0 atom x name
      · exact fun inAvoid => laterAvoid a later x name (List.mem_append_right _ inAvoid)
    · exact laterAvoid later member x clash (List.mem_append_left _ name)

/-- The writer protects the entire entry view and any additional caller
names supplied by the enclosing declaration or command. -/
def outputValues (avoid : List String) (rows : List O) (items : List (O × Atom)) : List Atom :=
  closeOutputs ((rows.map label).flatMap atomFreeVars ++ avoid) (items.map Prod.snd)

/-- The publication is a mixed physical effect. Occurrence order is stable
for survivors, with newly made occurrences in the prepared order. -/
def request (items : List (O × Atom)) (fresh : List O) : OrderedStore.Publication Atom O :=
  ⟨⟨items.map Prod.fst, [], fresh⟩, []⟩

/-- Restrict the actual ordered occurrence step to complete, nonempty
entry plans. An empty command returns zero without a store firing. -/
def step (avoid : List String) (use : Nat) : Interface.Step atomFrames O (EquationStore Atom × List O)
    (fun _ => OrderedStore.Publication Atom O) :=
  Spaces.restrict (OrderedStore.step atomFrames PUnit.unit label)
    fun {s} out => ∃ items, Census label replace use s.2 items ∧ items ≠ [] ∧
      out = request items out.selection.made ∧
      out.selection.made.map label = outputValues label avoid s.2 items

theorem prepare_publication (avoid : List String) {use : Nat} {items : List (O × Atom)} {rows fresh : List O}
    {knowledge : EquationStore Atom} (prepared : prepare label replace use rows = .ok items)
    (nonempty : items ≠ []) (distinct : rows.Nodup) (different : fresh.Nodup)
    (unused : Disjoint fresh.toFinset rows.toFinset)
    (allocated : fresh.map label = outputValues label avoid rows items)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ admitted : (step label replace avoid use).Admits (s := (knowledge, rows)) (request items fresh),
      let after := (step label replace avoid use).result (request items fresh) admitted
      after.1 = knowledge ∧
      after.2 = OrderedStore.survivors rows (items.map Prod.fst) ++ fresh ∧
      after.2.map label = (OrderedStore.survivors rows (items.map Prod.fst)).map label ++
        outputValues label avoid rows items ∧
      (request items fresh).selection.taken.length = items.length := by
  have census := (prepare_iff label replace use rows items).mp prepared
  have sub := census.selected_sublist label replace
  have permits : (step label replace avoid use).Admits (s := (knowledge, rows)) (request items fresh) := by
    refine ⟨⟨⟨distinct, sub.nodup distinct, different⟩, ?_, consistent⟩,
      items, census, nonempty, rfl, allocated⟩
    refine ⟨fun o member => ?_, by simp [request, OrderedStore.Publication.commit, Selection.commit],
      by simp [request, OrderedStore.Publication.commit, Selection.commit], unused, ?_⟩
    · exact List.mem_toFinset.mpr (sub.subset (List.mem_toFinset.mp member))
    · intro observed member
      simp [request, OrderedStore.Publication.commit] at member
  refine ⟨permits, rfl, rfl, ?_, ?_⟩
  · simp [step, Spaces.restrict, OrderedStore.step, OrderedStore.effect,
      OrderedStore.publish, request, allocated]
  · exact List.length_map Prod.fst

#print axioms prepare_iff
#print axioms Census.member_iff
#print axioms closeOutputs_variants
#print axioms closeOutputs_apart
#print axioms prepare_publication

end Mettapedia.Languages.MeTTa.StoreAndDemand.MatchRewritePublication

