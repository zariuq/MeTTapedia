import Mettapedia.Languages.MeTTa.PeTTa.RunsChained
import Mettapedia.Languages.MeTTa.PeTTa.LibTransformAdmission
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintRefusal

/-!
# What a read tells, in the step's own frames

`RunsChained.scan_sound` states what a read tells its alternative in the machine's terms:
the unifier makes the pattern equal to the occurrence's renamed atom. This module states it
in the terms of the step: the alternative's bindings, read as a substitution of the
step's frames (`LibTransformStep.solution`), solve the knowledge of the alternative that
read together with the told equation. So a read firing whose tell is that equation, at the
reader's knowledge, has solvable information, with the machine's own unifier as the
witness.

* `knowledgeOf`: an alternative's bindings as an equation store: each bound variable equal
  to what the bindings resolve it to.
* `knowledge_solved`: idempotent bindings solve their own knowledge.
* `knowledge_kept`: bindings that refine an alternative's bindings solve that
  alternative's knowledge. Knowledge only grows along one alternative.
* `read_tells`: each occurrence a `match` reads gives bindings that solve the reader's
  knowledge and the equation between the pattern and the occurrence's renamed atom; hence
  `read_information_solvable`: that information is solvable in the step's frames.
* `call_keeps_knowledge`: each equation a call selects goes on under bindings that refine
  the caller's and solve the caller's knowledge.
* Negative: `Controls.told_differently` (the two answers of `addEach` do not solve one
  another's knowledge: no substitution of one alternative is a solution for the other).

* `clash_unsolvable`: when the machine's unifier clashes, the reader's knowledge and the
  told equation have no solution in the step's frames. It carries the tree's refusal
  theorem for destination-equation models (`unifyTerms_refutes_model`) over by `envOf`,
  which reads a substitution of the frames as such a model (`read_envOf`).
* `row_read_iff_solvable`: where the unifier decides (it does not run out of fuel), a
  `match` reads an occurrence exactly when the information of that read (the reader's
  knowledge and the told equation) is solvable in the step's frames. Solvable information
  is what the step asks of a firing; so the machine's reads are the admitted ones.

* `match_reads_exactly_the_admissible`: for a scan the machine completed over distinct
  occurrences, with no condition on fuel: the occurrence at a position is read exactly
  when its read is admissible (`scan_row`: a completed scan decided every row).
* `removal_takes_exactly_the_admissible`: the same for a completed `remove-atom`: it takes
  an occurrence exactly when its pattern and the renamed atom have a common instance.
* `row_taken_iff_solvable`: the per-row form for `remove-atom`, which unifies under no bindings: it
  takes an occurrence exactly when the pattern and the renamed atom have a common instance.

That the fuel always decides is proved in `UnifyingDecides` and `UnifyingPatternDecides`;
`RunsDecide` restates the two theorems above without the completed scan as a hypothesis.
Not proved: the segments built as runs of a step with tells; for calls, whose argument
patterns have list views, the equivalence with solvability (their selection completing
is in `RunsDecide`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
open Mettapedia.Languages.MeTTa.ContextualTransform
open PeTTaStoreSelection (atomFrames)
open PeTTaQueryInterpretation (scan)
open LibTransformStep (solution applySubst_eq_subst)
open Unifying (resolve)
open UnifyingConstraintPresentation (presentation read_expression unifyTerms_refutes_model)

/-- An alternative's bindings as knowledge: each bound variable equal to what the bindings
resolve it to. -/
def knowledgeOf (bindings : Subst) : EquationStore Atom :=
  bindings.map fun binding => (Atom.var binding.1, resolve bindings (.var binding.1))

/-- Two atoms equal under bindings are a solved equation of the step's frames. -/
theorem solves_of_resolve {bindings : Subst} {left right : Atom}
    (same : resolve bindings left = resolve bindings right) :
    atomAction.Solves (solution bindings) (left, right) := by
  show Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst (solution bindings) left =
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst (solution bindings) right
  rw [← applySubst_eq_subst, ← applySubst_eq_subst]
  exact same

/-- Idempotent bindings solve their own knowledge. -/
theorem knowledge_solved {bindings : Subst} (idempotent : Unifying.Idempotent bindings) :
    atomAction.Models (solution bindings) (knowledgeOf bindings) := by
  intro equation member
  obtain ⟨binding, _, rfl⟩ := List.mem_map.mp member
  exact solves_of_resolve (Unifying.resolve_idem idempotent _).symm

/-- **Knowledge only grows along one alternative**: bindings that refine an alternative's
bindings solve that alternative's knowledge. -/
theorem knowledge_kept {earlier later : Subst} (refined : Unifying.Refines earlier later) :
    atomAction.Models (solution later) (knowledgeOf earlier) := by
  intro equation member
  obtain ⟨binding, _, rfl⟩ := List.mem_map.mp member
  exact solves_of_resolve (refined (.var binding.1)).symm

/-- **What a read tells, in the step's frames.** Each occurrence a `match` reads gives
bindings that solve the reader's knowledge together with the equation between the pattern
and the occurrence's atom renamed for its own use. -/
theorem read_tells {O : Type} (label : O → Atom) (bindings : Subst) (pattern : Atom)
    (idempotent : Unifying.Idempotent bindings) (use : Nat) (rows : List O)
    (packets : List (O × Subst))
    (scanned : scan label bindings pattern use rows = some packets) :
    ∀ packet ∈ packets, ∃ index, rows[index]? = some packet.1 ∧
      atomAction.Models (solution packet.2)
        (knowledgeOf bindings ++
          [(pattern, Unifying.rename (use + index) (label packet.1))]) := by
  intro packet member
  obtain ⟨index, at_, _, refined, solved⟩ :=
    scan_sound label bindings pattern idempotent use rows packets scanned packet member
  refine ⟨index, at_, ?_⟩
  intro equation inside
  rcases List.mem_append.mp inside with old | told
  · exact knowledge_kept refined equation old
  · rw [List.mem_singleton.mp told]
    exact solves_of_resolve solved

/-- So the information of such a read (the reader's knowledge and the told equation) is
solvable in the frames of the step: the machine's own unifier is a solution. -/
theorem read_information_solvable {O : Type} (label : O → Atom) (bindings : Subst)
    (pattern : Atom) (idempotent : Unifying.Idempotent bindings) (use : Nat) (rows : List O)
    (packets : List (O × Subst))
    (scanned : scan label bindings pattern use rows = some packets) :
    ∀ packet ∈ packets, ∃ index, rows[index]? = some packet.1 ∧
      atomFrames.Solvable (a := PUnit.unit)
        (knowledgeOf bindings ++
          [(pattern, Unifying.rename (use + index) (label packet.1))]) := by
  intro packet member
  obtain ⟨index, at_, solved⟩ :=
    read_tells label bindings pattern idempotent use rows packets scanned packet member
  exact ⟨index, at_, PUnit.unit, solution packet.2, solved⟩

/-- **A call's alternatives keep the caller's knowledge.** Each equation occurrence a call
selects goes on under bindings that are idempotent, refine the caller's, and so solve the
caller's knowledge in the step's frames. -/
theorem call_keeps_knowledge {O : Type} (label : O → Atom) (bindings : Subst) (head : String)
    (values : List Atom) (idempotent : Unifying.Idempotent bindings) :
    ∀ (use : Nat) (rows : List O) (packets : List (O × Unifying.Control)),
      scanCall label bindings head values use rows = some packets →
      ∀ packet ∈ packets, ∃ bound body, packet.2 = Unifying.Control.evaluate bound body ∧
        Unifying.BindingRefines bindings bound ∧
        atomAction.Models (solution bound) (knowledgeOf bindings)
  | _, [], packets, scanned, packet, member => by
      simp only [scanCall, Option.some.injEq] at scanned
      subst scanned
      cases member
  | use, occurrence :: rest, packets, scanned, packet, member => by
      unfold scanCall at scanned
      split at scanned
      · split_ifs at scanned with fits
        · cases later : scanCall label bindings head values (use + 1) rest with
          | none => simp [later] at scanned
          | some remaining =>
              have inherited := call_keeps_knowledge label bindings head values idempotent
                (use + 1) rest remaining later
              simp only [later, bind, Option.bind_some] at scanned
              split at scanned
              · rename_i bound unified
                cases scanned
                rcases List.mem_cons.mp member with here | found
                · subst here
                  have good : Unifying.BindingRefines bindings bound :=
                    Unifying.BindingRefines.arguments
                      ⟨idempotent, Unifying.Refines.refl idempotent⟩ _ _ unified
                  exact ⟨bound, _, rfl, good, knowledge_kept good.2⟩
                · exact inherited packet found
              · cases scanned
                exact inherited packet member
              · cases scanned
        · exact call_keeps_knowledge label bindings head values idempotent use rest packets
            scanned packet member
      · exact call_keeps_knowledge label bindings head values idempotent use rest packets
          scanned packet member

/-! ## The converse: a clash has no solution -/

/-- A substitution of the step's frames read as a model of destination equations. -/
def envOf (σ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) : EagerDFS.Destination.Environment :=
  fun name =>
    match σ name with
    | none => .var name
    | some value => EagerDFS.Destination.encode value

/-- Reading an atom in that model is substituting. -/
theorem read_envOf (σ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) :
    ∀ atom : Atom, EagerDFS.Destination.read (envOf σ) atom =
      Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst σ atom
  | .var name => by
      cases found : σ name with
      | none =>
          simp [EagerDFS.Destination.read, EagerDFS.Destination.encode, EagerDFS.Destination.decode, envOf,
            Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst, found]
      | some value =>
          simp [EagerDFS.Destination.read, EagerDFS.Destination.encode, envOf,
            Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst, found]
  | .symbol name => by
      simp [EagerDFS.Destination.read, EagerDFS.Destination.encode, EagerDFS.Destination.decode,
        Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst]
  | .grounded value => by
      simp [EagerDFS.Destination.read, EagerDFS.Destination.encode, EagerDFS.Destination.decode,
        Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst]
  | .expression items => by
      rw [read_expression]
      simp only [Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst, Atom.expression.injEq]
      exact list items
where
  list : ∀ items : List Atom, items.map (EagerDFS.Destination.read (envOf σ)) =
      Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst.substList σ items
    | [] => rfl
    | first :: rest => by
        simp only [List.map_cons, Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst.substList]
        rw [read_envOf σ first, list rest]

/-- A solution of an alternative's knowledge is a model of its bindings' presentation. -/
theorem models_presentation {σ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst}
    {bindings : Subst} (solved : atomAction.Models σ (knowledgeOf bindings)) :
    EagerDFS.Destination.Solves (envOf σ) (presentation bindings) := by
  intro pair member
  have here : atomAction.Solves σ pair := solved pair member
  rw [read_envOf, read_envOf]
  exact here

/-- **A clash has no solution.** When the machine's unifier clashes on two atoms under
idempotent bindings, no substitution of the step's frames solves the bindings' knowledge
together with the equation between the two atoms. -/
theorem clash_unsolvable {bindings : Subst} {left right : Atom}
    (idempotent : Unifying.Idempotent bindings)
    (clashed : Unifying.unify bindings left right = .clash) :
    ¬ atomFrames.Solvable (a := PUnit.unit) (knowledgeOf bindings ++ [(left, right)]) := by
  rintro ⟨_, σ, solved⟩
  have old : atomAction.Models σ (knowledgeOf bindings) :=
    fun equation member => solved equation (List.mem_append_left _ member)
  have told : atomAction.Solves σ (left, right) :=
    solved (left, right) (List.mem_append_right _ (List.mem_singleton_self _))
  apply unifyTerms_refutes_model _ bindings left right idempotent clashed (envOf σ)
    (models_presentation old)
  rw [read_envOf, read_envOf]
  exact told

/-- **A `match` reads an occurrence exactly when the information of that read is
solvable.** Where the unifier decides the row, it unifies the pattern with the
occurrence's renamed atom exactly when the reader's knowledge and the told equation have a
solution in the step's frames. -/
theorem row_read_iff_solvable {O : Type} (label : O → Atom) (bindings : Subst)
    (pattern : Atom) (idempotent : Unifying.Idempotent bindings) (use : Nat) (occurrence : O)
    (decided : Unifying.unify bindings pattern (Unifying.rename use (label occurrence)) ≠
      .exhausted) :
    (∃ bound, Unifying.unify bindings pattern (Unifying.rename use (label occurrence)) =
        .ok bound) ↔
      atomFrames.Solvable (a := PUnit.unit)
        (knowledgeOf bindings ++ [(pattern, Unifying.rename use (label occurrence))]) := by
  constructor
  · rintro ⟨bound, unified⟩
    obtain ⟨_, refined, solved⟩ := Unifying.unifyTerms_sound _ bindings bound pattern
      (Unifying.rename use (label occurrence)) idempotent unified
    refine ⟨PUnit.unit, solution bound, ?_⟩
    intro equation inside
    rcases List.mem_append.mp inside with old | told
    · exact knowledge_kept refined equation old
    · rw [List.mem_singleton.mp told]
      exact solves_of_resolve solved
  · intro solvable
    cases outcome : Unifying.unify bindings pattern (Unifying.rename use (label occurrence)) with
    | ok bound => exact ⟨bound, rfl⟩
    | clash => exact absurd solvable (clash_unsolvable idempotent outcome)
    | exhausted => exact absurd outcome decided

/-- A scan that completed decided every row: at each position the unifier either
succeeded, and that occurrence with its unifier is among the packets, or clashed. -/
theorem scan_row {O : Type} (label : O → Atom) (bindings : Subst) (pattern : Atom) :
    ∀ (use : Nat) (rows : List O) (packets : List (O × Subst)),
      scan label bindings pattern use rows = some packets →
      ∀ (index : Nat) (occurrence : O), rows[index]? = some occurrence →
        (∃ bound, Unifying.unify bindings pattern
            (Unifying.rename (use + index) (label occurrence)) = .ok bound ∧
          (occurrence, bound) ∈ packets) ∨
        Unifying.unify bindings pattern
          (Unifying.rename (use + index) (label occurrence)) = .clash
  | _, [], _, _, index, occurrence, at_ => by simp at at_
  | use, row :: rest, packets, scanned, index, occurrence, at_ => by
      cases later : scan label bindings pattern (use + 1) rest with
      | none => simp [scan, later] at scanned
      | some remaining =>
          have inherited := scan_row label bindings pattern (use + 1) rest remaining later
          cases matched : Unifying.unify bindings pattern
              (Unifying.rename use (label row)) with
          | exhausted => simp [scan, later, matched] at scanned
          | ok bound =>
              simp [scan, later, matched] at scanned
              subst scanned
              cases index with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at at_
                  subst at_
                  exact Or.inl ⟨bound, by simpa using matched, List.mem_cons_self ..⟩
              | succ next =>
                  simp only [List.getElem?_cons_succ] at at_
                  have shifted : use + (next + 1) = use + 1 + next := by omega
                  rw [shifted]
                  rcases inherited next occurrence at_ with ⟨found, unified, member⟩ | clashed
                  · exact Or.inl ⟨found, unified, List.mem_cons_of_mem _ member⟩
                  · exact Or.inr clashed
          | clash =>
              simp [scan, later, matched] at scanned
              subst scanned
              cases index with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at at_
                  subst at_
                  exact Or.inr (by simpa using matched)
              | succ next =>
                  simp only [List.getElem?_cons_succ] at at_
                  have shifted : use + (next + 1) = use + 1 + next := by omega
                  rw [shifted]
                  exact inherited next occurrence at_

/-- **A `match` reads exactly the admissible occurrences.** For a scan the machine
completed over distinct occurrences: the occurrence at a position is among those read
exactly when the reader's knowledge together with the equation between the pattern and
that occurrence's renamed atom is solvable in the step's frames. No condition on fuel: a
completed scan decided every row. -/
theorem match_reads_exactly_the_admissible {O : Type} (label : O → Atom) (bindings : Subst)
    (pattern : Atom) (idempotent : Unifying.Idempotent bindings) (use : Nat) (rows : List O)
    (packets : List (O × Subst)) (unique : rows.Nodup)
    (scanned : scan label bindings pattern use rows = some packets)
    (index : Nat) (occurrence : O) (at_ : rows[index]? = some occurrence) :
    occurrence ∈ packets.map Prod.fst ↔
      atomFrames.Solvable (a := PUnit.unit)
        (knowledgeOf bindings ++
          [(pattern, Unifying.rename (use + index) (label occurrence))]) := by
  have here := scan_row label bindings pattern use rows packets scanned index occurrence at_
  constructor
  · intro read
    rcases here with ⟨bound, unified, _⟩ | clashed
    · exact (row_read_iff_solvable label bindings pattern idempotent (use + index) occurrence
        (by rw [unified]; exact fun impossible => by cases impossible)).mp ⟨bound, unified⟩
    · exfalso
      obtain ⟨packet, member, same⟩ := List.mem_map.mp read
      obtain ⟨other, there, _, refined, solved⟩ :=
        scan_sound label bindings pattern idempotent use rows packets scanned packet member
      rw [same] at there solved
      have within : index < rows.length := (List.getElem?_eq_some_iff.mp at_).1
      have sameIndex : index = other :=
        (List.getElem?_inj within unique).mp (at_.trans there.symm)
      subst sameIndex
      refine clash_unsolvable idempotent clashed ⟨PUnit.unit, solution packet.2, ?_⟩
      intro equation inside
      rcases List.mem_append.mp inside with old | told
      · exact knowledge_kept refined equation old
      · rw [List.mem_singleton.mp told]
        exact solves_of_resolve solved
  · intro solvable
    rcases here with ⟨bound, _, member⟩ | clashed
    · exact List.mem_map.mpr ⟨(occurrence, bound), member, rfl⟩
    · exact absurd solvable (clash_unsolvable idempotent clashed)

/-- **A `remove-atom` takes an occurrence exactly when its pattern and the occurrence's
renamed atom have a common instance.** A removal unifies under no bindings, so the
information of the take is the one equation. -/
theorem row_taken_iff_solvable {O : Type} (label : O → Atom) (pattern : Atom) (use : Nat)
    (occurrence : O)
    (decided : Unifying.unify [] pattern (Unifying.rename use (label occurrence)) ≠
      .exhausted) :
    (∃ bound, Unifying.unify [] pattern (Unifying.rename use (label occurrence)) =
        .ok bound) ↔
      atomFrames.Solvable (a := PUnit.unit)
        [(pattern, Unifying.rename use (label occurrence))] := by
  have empty : Unifying.Idempotent [] := by simp [Unifying.Idempotent, Subst.lookup]
  simpa [knowledgeOf] using
    row_read_iff_solvable label [] pattern empty use occurrence decided

/-- A removal's selection that completed decided every row: at each position the unifier
either succeeded, and that occurrence is among the taken, or clashed. -/
theorem selected_row {O : Type} (label : O → Atom) (pattern : Atom) :
    ∀ (use : Nat) (rows taken : List O),
      PeTTaStoreSelection.selectedRows label pattern use rows = some taken →
      ∀ (index : Nat) (occurrence : O), rows[index]? = some occurrence →
        ((∃ bound, Unifying.unify [] pattern
            (Unifying.rename (use + index) (label occurrence)) = .ok bound) ∧
          occurrence ∈ taken) ∨
        Unifying.unify [] pattern
          (Unifying.rename (use + index) (label occurrence)) = .clash
  | _, [], _, _, index, occurrence, at_ => by simp at at_
  | use, row :: rest, taken, selected, index, occurrence, at_ => by
      cases later : PeTTaStoreSelection.selectedRows label pattern (use + 1) rest with
      | none => simp [PeTTaStoreSelection.selectedRows, later] at selected
      | some remaining =>
          have inherited := selected_row label pattern (use + 1) rest remaining later
          cases matched : Unifying.unify [] pattern (Unifying.rename use (label row)) with
          | exhausted => simp [PeTTaStoreSelection.selectedRows, later, matched] at selected
          | ok bound =>
              simp [PeTTaStoreSelection.selectedRows, later, matched] at selected
              subst selected
              cases index with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at at_
                  subst at_
                  exact Or.inl ⟨⟨bound, by simpa using matched⟩, List.mem_cons_self ..⟩
              | succ next =>
                  simp only [List.getElem?_cons_succ] at at_
                  have shifted : use + (next + 1) = use + 1 + next := by omega
                  rw [shifted]
                  rcases inherited next occurrence at_ with ⟨unified, member⟩ | clashed
                  · exact Or.inl ⟨unified, List.mem_cons_of_mem _ member⟩
                  · exact Or.inr clashed
          | clash =>
              simp [PeTTaStoreSelection.selectedRows, later, matched] at selected
              subst selected
              cases index with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at at_
                  subst at_
                  exact Or.inr (by simpa using matched)
              | succ next =>
                  simp only [List.getElem?_cons_succ] at at_
                  have shifted : use + (next + 1) = use + 1 + next := by omega
                  rw [shifted]
                  exact inherited next occurrence at_

/-- Every taken occurrence is at a position where the unifier succeeded. -/
theorem selected_sound {O : Type} (label : O → Atom) (pattern : Atom) :
    ∀ (use : Nat) (rows taken : List O),
      PeTTaStoreSelection.selectedRows label pattern use rows = some taken →
      ∀ occurrence ∈ taken, ∃ index bound, rows[index]? = some occurrence ∧
        Unifying.unify [] pattern (Unifying.rename (use + index) (label occurrence)) =
          .ok bound
  | _, [], taken, selected, occurrence, member => by
      simp only [PeTTaStoreSelection.selectedRows, Option.some.injEq] at selected
      subst selected
      cases member
  | use, row :: rest, taken, selected, occurrence, member => by
      cases later : PeTTaStoreSelection.selectedRows label pattern (use + 1) rest with
      | none => simp [PeTTaStoreSelection.selectedRows, later] at selected
      | some remaining =>
          have inherited := selected_sound label pattern (use + 1) rest remaining later
          have fromRest : occurrence ∈ remaining → ∃ index bound,
              (row :: rest)[index]? = some occurrence ∧
              Unifying.unify [] pattern
                (Unifying.rename (use + index) (label occurrence)) = .ok bound := by
            intro found
            obtain ⟨index, bound, at_, unified⟩ := inherited occurrence found
            refine ⟨index + 1, bound, by simpa using at_, ?_⟩
            have shifted : use + (index + 1) = use + 1 + index := by omega
            rw [shifted]
            exact unified
          cases matched : Unifying.unify [] pattern (Unifying.rename use (label row)) with
          | exhausted => simp [PeTTaStoreSelection.selectedRows, later, matched] at selected
          | ok bound =>
              simp [PeTTaStoreSelection.selectedRows, later, matched] at selected
              subst selected
              rcases List.mem_cons.mp member with here | found
              · subst here
                exact ⟨0, bound, rfl, by simpa using matched⟩
              · exact fromRest found
          | clash =>
              simp [PeTTaStoreSelection.selectedRows, later, matched] at selected
              subst selected
              exact fromRest member

/-- **A `remove-atom` takes exactly the admissible occurrences.** For a selection the
machine completed over distinct occurrences: the occurrence at a position is taken exactly
when the equation between the pattern and that occurrence's renamed atom is solvable in
the step's frames. -/
theorem removal_takes_exactly_the_admissible {O : Type} (label : O → Atom) (pattern : Atom)
    (use : Nat) (rows taken : List O) (unique : rows.Nodup)
    (selected : PeTTaStoreSelection.selectedRows label pattern use rows = some taken)
    (index : Nat) (occurrence : O) (at_ : rows[index]? = some occurrence) :
    occurrence ∈ taken ↔
      atomFrames.Solvable (a := PUnit.unit)
        [(pattern, Unifying.rename (use + index) (label occurrence))] := by
  have here := selected_row label pattern use rows taken selected index occurrence at_
  have decides : ∀ bound, Unifying.unify [] pattern
      (Unifying.rename (use + index) (label occurrence)) = .ok bound →
      Unifying.unify [] pattern (Unifying.rename (use + index) (label occurrence)) ≠
        .exhausted := by
    intro bound unified impossible
    rw [unified] at impossible
    cases impossible
  constructor
  · intro member
    rcases here with ⟨⟨bound, unified⟩, _⟩ | clashed
    · exact (row_taken_iff_solvable label pattern (use + index) occurrence
        (decides bound unified)).mp ⟨bound, unified⟩
    · exfalso
      obtain ⟨other, bound, there, unified⟩ :=
        selected_sound label pattern use rows taken selected occurrence member
      have within : index < rows.length := (List.getElem?_eq_some_iff.mp at_).1
      have sameIndex : index = other :=
        (List.getElem?_inj within unique).mp (at_.trans there.symm)
      subst sameIndex
      rw [unified] at clashed
      cases clashed
  · intro solvable
    rcases here with ⟨_, member⟩ | clashed
    · exact member
    · have empty : Unifying.Idempotent [] := by simp [Unifying.Idempotent, Subst.lookup]
      exact absurd (by simpa [knowledgeOf] using solvable) (clash_unsolvable empty clashed)

namespace Controls

/-- Negative: knowledge is not shared between alternatives. The bindings of the first
answer of `addEach` do not solve the knowledge of the second. -/
theorem told_differently (first second : Unifying.Answer)
    (answers : (Streaming.advance registry 60
      (Streaming.enter { state := store } addEach)).answers = [first, second]) :
    ¬ atomAction.Models (solution first.bindings)
      [(Atom.var "x#0", resolve second.bindings (.var "x#0"))] := by
  have resolved := addEach_answers
  rw [answers] at resolved
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at resolved
  intro solved
  have here := solved _ (List.mem_singleton_self _)
  have same : resolve first.bindings (.var "x#0") =
      resolve first.bindings (resolve second.bindings (.var "x#0")) := by
    have := here
    simp only [SubstitutionAction.Solves] at this
    show applySubst first.bindings _ = applySubst first.bindings _
    rw [applySubst_eq_subst, applySubst_eq_subst]
    exact this
  rw [resolved.1, resolved.2] at same
  have symbol : resolve first.bindings b = b := rfl
  rw [symbol] at same
  exact absurd same (by decide)

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
