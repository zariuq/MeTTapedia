import Mettapedia.Languages.MeTTa.PeTTa.RunsTells
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingGround

/-!
# On a ground space every read and take is decided

`RunsTells` shows that a `match` reads, and a `remove-atom` takes, exactly the occurrences
whose firing the step admits, for every scan the machine completed. A scan fails to complete
only when the fuelled unifier runs out of fuel on a row. This module shows that it never
does on a row without variables, whatever the reader already knows.

* `unifyLists_decides`, `unifyTerms_ground_decides`: against a ground term the unifier's
  descent follows that term, so fuel above the term's size is enough, for any bindings. The
  tree's `unifyTerms_ground` needs every bound value to be ground and says more (the result
  is one-way matching); this needs nothing of the bindings and says only that the unifier
  decides.
* `unify_ground_decides`: the fuel `unify` gives is enough.
* `scan_ground_completes`, `selectedRows_ground_completes`: on rows without variables a
  `match` scan and a `remove-atom` selection complete.
* `ground_match_reads_exactly_the_admissible`, `ground_removal_takes_exactly_the_admissible`:
  the theorems of `RunsTells` on a ground space, with no hypothesis that the scan completed.

Positive example: `Controls.open_knowledge_ground_row` (a reader whose bindings hold a
variable, so the earlier ground-range theorem does not apply, reads a ground row).
Negative example: `Controls.fuel_is_needed` (with fuel 1 the unifier does not decide two
equal one-element expressions: the bound on fuel is used).

Rows that hold variables are in `RunsDecide`, from `UnifyingDecides` (the unifier never runs
out of fuel on an idempotent substitution). The ground case here stays as the statement
that asks nothing of the reader's bindings: `unifyTerms_ground_decides` holds for bindings
that are not idempotent too.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst isGroundAtom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.MeTTa.ContextualTransform
open PeTTaStoreSelection (atomFrames)
open PeTTaQueryInterpretation (scan)
open Unifying (resolve Unified unifyTerms unifyLists unify atomSize fuelFor)

/-! ## The unifier against a ground term -/

/-- A list unification decides when the element unification decides against every element of
the second list. -/
theorem unifyLists_decides (unifier : Subst → Atom → Atom → Unified) :
    ∀ (items others : List Atom) (bindings : Subst),
      (∀ (bound : Subst) (item other : Atom), other ∈ others →
        unifier bound item other ≠ .exhausted) →
      unifyLists unifier bindings items others ≠ .exhausted
  | [], [], _, _ => by simp [unifyLists]
  | [], _ :: _, _, _ => by simp [unifyLists]
  | _ :: _, [], _, _ => by simp [unifyLists]
  | first :: rest, other :: remaining, bindings, decides => by
      simp only [unifyLists]
      cases outcome : unifier bindings first other with
      | ok bound =>
          simp only [Unified.ok_andThen]
          exact unifyLists_decides unifier rest remaining bound
            (fun later item value member =>
              decides later item value (List.mem_cons_of_mem _ member))
      | clash => simp
      | exhausted => exact absurd outcome (decides bindings first other List.mem_cons_self)

/-- **Against a ground term the unifier decides**, for any bindings: its descent follows the
ground term, so fuel above that term's size is enough. -/
theorem unifyTerms_ground_decides : ∀ (fuel : Nat) (bindings : Subst) (left right : Atom),
    isGroundAtom right = true → atomSize right < fuel →
      unifyTerms fuel bindings left right ≠ .exhausted
  | 0, _, _, _, _, small => absurd small (Nat.not_lt_zero _)
  | fuel + 1, bindings, left, right, ground, small => by
      unfold unifyTerms
      rw [show resolve bindings right = right from Unifying.applySubst_ground _ _ ground]
      generalize resolve bindings left = resolved
      cases right with
      | var _ => simp [isGroundAtom] at ground
      | symbol other =>
          cases resolved with
          | var name => simp only []; split <;> simp
          | symbol name => simp only []; split <;> simp
          | grounded _ => simp
          | expression _ => simp
      | grounded other =>
          cases resolved with
          | var name => simp only []; split <;> simp
          | symbol _ => simp
          | grounded value => simp only []; split <;> simp
          | expression _ => simp
      | expression others =>
          cases resolved with
          | var name => simp only []; split <;> simp
          | symbol _ => simp
          | grounded _ => simp
          | expression items =>
              simp only []
              exact unifyLists_decides (unifyTerms fuel) items others bindings
                (fun bound item other member =>
                  unifyTerms_ground_decides fuel bound item other
                    (Unifying.isGround_of_mem member ground)
                    (by
                      have smaller := Unifying.atomSize_lt_of_mem member
                      omega))

/-- The fuel `unify` gives is enough against a ground term. -/
theorem unify_ground_decides (bindings : Subst) (pattern : Atom) {value : Atom}
    (ground : isGroundAtom value = true) : unify bindings pattern value ≠ .exhausted := by
  unfold unify
  exact unifyTerms_ground_decides _ bindings pattern value ground (by unfold fuelFor; omega)

/-! ## Scans and selections on rows without variables -/

/-- **On rows without variables a `match` scan completes**, whatever the reader knows. -/
theorem scan_ground_completes {O : Type} (label : O → Atom) (bindings : Subst)
    (pattern : Atom) :
    ∀ (use : Nat) (rows : List O), (∀ row ∈ rows, isGroundAtom (label row) = true) →
      ∃ packets, scan label bindings pattern use rows = some packets
  | _, [], _ => ⟨[], rfl⟩
  | use, row :: rest, ground => by
      obtain ⟨later, scanned⟩ := scan_ground_completes label bindings pattern (use + 1) rest
        (fun item member => ground item (List.mem_cons_of_mem _ member))
      have rowGround := ground row List.mem_cons_self
      have decides : unify bindings pattern (Unifying.rename use (label row)) ≠ .exhausted :=
        unify_ground_decides bindings pattern
          (by rw [Unifying.rename_ground use (label row) rowGround]; exact rowGround)
      simp only [scan, scanned, Option.bind_eq_bind, Option.bind_some]
      cases outcome : unify bindings pattern (Unifying.rename use (label row)) with
      | ok bound => exact ⟨_, rfl⟩
      | clash => exact ⟨_, rfl⟩
      | exhausted => exact absurd outcome decides

/-- **On rows without variables a `remove-atom` selection completes.** -/
theorem selectedRows_ground_completes {O : Type} (label : O → Atom) (pattern : Atom) :
    ∀ (use : Nat) (rows : List O), (∀ row ∈ rows, isGroundAtom (label row) = true) →
      ∃ taken, PeTTaStoreSelection.selectedRows label pattern use rows = some taken
  | _, [], _ => ⟨[], rfl⟩
  | use, row :: rest, ground => by
      obtain ⟨later, selected⟩ := selectedRows_ground_completes label pattern (use + 1) rest
        (fun item member => ground item (List.mem_cons_of_mem _ member))
      have rowGround := ground row List.mem_cons_self
      have decides : unify [] pattern (Unifying.rename use (label row)) ≠ .exhausted :=
        unify_ground_decides [] pattern
          (by rw [Unifying.rename_ground use (label row) rowGround]; exact rowGround)
      simp only [PeTTaStoreSelection.selectedRows, selected, Option.bind_eq_bind,
        Option.bind_some]
      cases outcome : unify [] pattern (Unifying.rename use (label row)) with
      | ok bound => exact ⟨_, rfl⟩
      | clash => exact ⟨_, rfl⟩
      | exhausted => exact absurd outcome decides

/-! ## Reads and takes on a ground space -/

/-- **On a ground space a `match` reads exactly the admissible occurrences.** Its scan
completes, and the occurrence at a position is among those read exactly when the reader's
knowledge together with the equation between the pattern and that occurrence's atom is
solvable in the step's frames. Nothing is assumed of the scan or of the reader's bindings
beyond idempotence. -/
theorem ground_match_reads_exactly_the_admissible {O : Type} (label : O → Atom)
    (bindings : Subst) (pattern : Atom) (idempotent : Unifying.Idempotent bindings) (use : Nat)
    (rows : List O) (unique : rows.Nodup)
    (ground : ∀ row ∈ rows, isGroundAtom (label row) = true) :
    ∃ packets, scan label bindings pattern use rows = some packets ∧
      ∀ (index : Nat) (occurrence : O), rows[index]? = some occurrence →
        (occurrence ∈ packets.map Prod.fst ↔
          atomFrames.Solvable (a := PUnit.unit)
            (knowledgeOf bindings ++ [(pattern, label occurrence)])) := by
  obtain ⟨packets, scanned⟩ := scan_ground_completes label bindings pattern use rows ground
  refine ⟨packets, scanned, fun index occurrence at_ => ?_⟩
  have exact := match_reads_exactly_the_admissible label bindings pattern idempotent use rows
    packets unique scanned index occurrence at_
  rwa [Unifying.rename_ground (use + index) (label occurrence)
    (ground occurrence (List.mem_of_getElem? at_))] at exact

/-- **On a ground space a `remove-atom` takes exactly the admissible occurrences.** Its
selection completes, and the occurrence at a position is taken exactly when the equation
between the pattern and that occurrence's atom is solvable in the step's frames. -/
theorem ground_removal_takes_exactly_the_admissible {O : Type} (label : O → Atom)
    (pattern : Atom) (use : Nat) (rows : List O) (unique : rows.Nodup)
    (ground : ∀ row ∈ rows, isGroundAtom (label row) = true) :
    ∃ taken, PeTTaStoreSelection.selectedRows label pattern use rows = some taken ∧
      ∀ (index : Nat) (occurrence : O), rows[index]? = some occurrence →
        (occurrence ∈ taken ↔
          atomFrames.Solvable (a := PUnit.unit) [(pattern, label occurrence)]) := by
  obtain ⟨taken, selected⟩ := selectedRows_ground_completes label pattern use rows ground
  refine ⟨taken, selected, fun index occurrence at_ => ?_⟩
  have exact := removal_takes_exactly_the_admissible label pattern use rows taken unique
    selected index occurrence at_
  rwa [Unifying.rename_ground (use + index) (label occurrence)
    (ground occurrence (List.mem_of_getElem? at_))] at exact

namespace Controls

/-- Positive: the reader's bindings hold a variable (`x` is bound to `$y`), so they are not of
ground range; the scan of the ground row `(p a)` still completes and reads it. -/
theorem open_knowledge_ground_row :
    ¬ Unifying.GroundRange [("x", Atom.var "y")] ∧
      (scan (fun _ : Nat => Atom.expression [.symbol "p", .symbol "a"])
        [("x", Atom.var "y")] (.expression [.symbol "p", .var "x"]) 0 [0]).isSome = true := by
  refine ⟨?_, by decide⟩
  intro range
  have ground := range ("x", Atom.var "y") List.mem_cons_self
  simp [isGroundAtom] at ground

/-- Negative: with fuel 1 the unifier does not decide two equal one-element expressions, so
the bound on fuel is used. -/
theorem fuel_is_needed :
    unifyTerms 1 [] (.expression [.symbol "a"]) (.expression [.symbol "a"]) = .exhausted := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
