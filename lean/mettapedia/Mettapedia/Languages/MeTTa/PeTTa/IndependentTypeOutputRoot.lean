import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutputStructural

/-!
# Root publication of independent intrinsic type answers

The root comparison uses joint caller observations and preserves the ordered
answer vector. Private allocation coordinates are unobservable; source and
caller names are fixed. Fuel approximates completion rather than language
failure, and the two traversals need not consume equal approximation depth.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Root

open Mettapedia.Logic.LP
open IntrinsicTypeFacts (signature TypeTerm Declaration undefinedType)
open Admission Structural

private theorem equivalent_refl (path : Path) (output : Nat) (answer : TypeTerm) :
    AnswerEquivalent path output answer answer := fun _ _ => rfl

private theorem paired_refl (path : Path) (output : Nat) (answers : List TypeTerm) :
    List.Forall₂ (AnswerEquivalent path output) answers answers := by
  induction answers with
  | nil => exact .nil
  | cons answer rest ih => exact .cons (equivalent_refl path output answer) ih

/-- Matching an independent output to a fresh scheme changes only its
private alias direction. Proper types retain their original representation. -/
theorem matched_independent_pairing (path : Path) (output : Nat) (candidates : List TypeTerm)
    (outputApart : AllocationApart path (.var output))
    (supported : ∀ candidate ∈ candidates, ∀ name ∈ candidate.freeVars,
      ∃ stem slot, name = freshSupply (stem ++ path) slot) :
    List.Forall₂ (AnswerEquivalent path output)
      (matched (.var output) candidates) candidates := by
  have one (candidate : TypeTerm) (present : candidate ∈ candidates) :
      List.Forall₂ (AnswerEquivalent path output) (matched (.var output) [candidate]) [candidate] := by
    have absent : output ∉ candidate.freeVars := by
      intro occurs
      obtain ⟨stem, slot, same⟩ := supported candidate present output occurs
      exact outputApart stem slot (by simpa only [Term.freeVars, Finset.mem_singleton] using same.symm)
    cases candidate with
    | var name =>
        have different : name ≠ output := by
          simpa only [Term.freeVars, Finset.mem_singleton, ne_eq, eq_comm] using absent
        simp only [matched, List.flatMap_cons, List.flatMap_nil,
          IndependentOutputUnification.variable_output_match (σ := signature) name output different,
          Option.toList_some, List.map_cons, List.map_nil, List.append_nil, Subst.applyTerm_var]
        rw [Subst.single_ne (σ := signature) (.var output) different.symm]
        refine .cons ?_ .nil
        intro observations apart
        obtain ⟨stem, slot, rfl⟩ := supported (.var name) present name (by simp [Term.freeVars])
        have same := IndependentOutputUnification.solved_private_output_publication _ output different
          (.var (freshSupply (stem ++ path) slot)) (Or.inl rfl) absent observations
          (fun term member => apart term member stem slot)
        simpa only [UnificationRenaming.rename_var, Equiv.swap_apply_left] using same
    | const value =>
        have same : matched (.var output) [.const value] = [.const value] := by
          simp [matched, IndependentOutputUnification.nonvariable_output_match output
            (.const value) (by simp) absent, Subst.single]
        rw [same]
        exact .cons (equivalent_refl path output _) .nil
    | app arity terms =>
        have same : matched (.var output) [.app arity terms] = [.app arity terms] := by
          simp [matched, IndependentOutputUnification.nonvariable_output_match output
            (.app arity terms) (by simp) absent, Subst.single]
        rw [same]
        exact .cons (equivalent_refl path output _) .nil
  induction candidates with
  | nil => exact .nil
  | cons candidate rest ih =>
      have head := one candidate List.mem_cons_self
      have tail := ih (fun value member => supported value (List.mem_cons_of_mem _ member))
        (fun value member => one value (List.mem_cons_of_mem _ member))
      simpa only [matched, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append] using List.rel_append head tail

private theorem finish_pairing (path : Path) (output : Nat) (bound fresh : List TypeTerm)
    (paired : List.Forall₂ (AnswerEquivalent path output) bound fresh) :
    List.Forall₂ (AnswerEquivalent path output)
      (finish (some (.var output)) bound) (finish none fresh) := by
  cases paired with
  | nil =>
      simp only [finish, List.isEmpty_nil, ↓reduceIte]
      simp only [matched, undefinedType, IntrinsicTypeFacts.named, List.flatMap_cons,
        List.flatMap_nil, unifyTotal, Subst.applyEqs, List.map_nil, Option.toList_some,
        List.map_cons, List.append_nil, Subst.comp, Subst.applyTerm, Subst.single_eq]
      exact .cons (equivalent_refl path output _) .nil
  | cons first rest =>
      simpa only [finish, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] using
        List.Forall₂.cons first rest

/-- The already checked function service has the same completion and a
position-by-position scheme correspondence in both root modes. -/
theorem functions_pairing (library : List Declaration) (fuel : Nat) (path : Path)
    (items : List TypeTerm) (output : Nat)
    (outputApart : AllocationApart path (.var output))
    (independent : ∀ item ∈ items, output ∉ item.freeVars) :
    ∀ fresh, functions library freshSupply (run library freshSupply fuel) path items none = some fresh →
      ∃ bound, functions library freshSupply (run library freshSupply fuel) path items
        (some (.var output)) = some bound ∧
        List.Forall₂ (AnswerEquivalent path output) bound fresh := by
  have notAllocated : ∀ stem slot, freshSupply (stem ++ path) slot ≠ output := by
    intro stem slot
    simpa only [Term.freeVars, Finset.mem_singleton] using outputApart stem slot
  intro fresh freshRun
  have compared (observations : List TypeTerm)
      (apart : ∀ term ∈ observations, AllocationApart path term) :=
    functions_variable_publication library fuel path items output notAllocated independent observations
      (fun occurrence slot term member => apart term member [1, occurrence] slot)
  have completion := compared [] (by simp)
  rw [freshRun] at completion
  cases boundRun : functions library freshSupply (run library freshSupply fuel) path items
      (some (.var output)) with
  | none => simp [boundRun] at completion
  | some bound =>
      refine ⟨bound, rfl, ?_⟩
      apply IndependentOutputUnification.ordered_publication_pairing bound fresh output
        (fun observations => ∀ term ∈ observations, AllocationApart path term) (by simp)
      intro observations apart
      have same := compared observations apart
      simpa only [boundRun, freshRun, Option.map_some, Option.some.injEq] using same

/-- The reverse completion direction for whole function dispatch is exact
at the same child fuel. The structural branch needs a separate fuel shift. -/
theorem functions_pairing_reverse (library : List Declaration) (fuel : Nat) (path : Path)
    (items : List TypeTerm) (output : Nat)
    (outputApart : AllocationApart path (.var output))
    (independent : ∀ item ∈ items, output ∉ item.freeVars) :
    ∀ bound, functions library freshSupply (run library freshSupply fuel) path items
        (some (.var output)) = some bound →
      ∃ fresh, functions library freshSupply (run library freshSupply fuel) path items none = some fresh ∧
        List.Forall₂ (AnswerEquivalent path output) bound fresh := by
  intro bound boundRun
  have notAllocated : ∀ stem slot, freshSupply (stem ++ path) slot ≠ output := by
    intro stem slot
    simpa only [Term.freeVars, Finset.mem_singleton] using outputApart stem slot
  have completion := functions_variable_publication library fuel path items output notAllocated
    independent [] (by simp)
  rw [boundRun] at completion
  cases freshRun : functions library freshSupply (run library freshSupply fuel) path items none with
  | none => simp [freshRun] at completion
  | some fresh =>
      obtain ⟨other, otherRun, paired⟩ := functions_pairing library fuel path items output
        outputApart independent fresh freshRun
      have same : other = bound := Option.some.inj (otherRun.symm.trans boundRun)
      exact ⟨fresh, rfl, same ▸ paired⟩

private theorem declarations_supported (library : List Declaration) (path : Path) (subject : TypeTerm) :
    ∀ candidate ∈ declarations library freshSupply path subject, ∀ name ∈ candidate.freeVars,
      ∃ stem slot, name = freshSupply (stem ++ path) slot := by
  intro candidate present name occurs
  by_contra missing
  apply declarations_exclude library freshSupply path subject name _ candidate present occurs
  intro occurrence slot same
  exact missing ⟨[1, occurrence], slot, same.symm⟩

private theorem leaf_pairing (library : List Declaration) (query : Query) (path : Path)
    (subject : TypeTerm) (output : Nat) (outputApart : AllocationApart path (.var output))
    (leaf : elements subject = none) :
    ∃ bound fresh, step library freshSupply query path subject (some (.var output)) = some bound ∧
      step library freshSupply query path subject none = some fresh ∧
      List.Forall₂ (AnswerEquivalent path output) bound fresh := by
  unfold step
  by_cases sourceVariable : isVariable subject = true
  · simp only [sourceVariable, ↓reduceIte, Option.getD_some, Option.getD_none]
    refine ⟨_, _, rfl, rfl, .cons ?_ .nil⟩
    apply fresh_variable_equivalent
    simpa only [Term.freeVars, Finset.mem_singleton, List.singleton_append] using outputApart [5] 0
  · simp only [sourceVariable]
    cases primitiveRun : literal subject with
    | none =>
        simp only [leaf, select]
        refine ⟨_, _, rfl, rfl, ?_⟩
        exact finish_pairing path output _ _
          (matched_independent_pairing path output _ outputApart
            (declarations_supported library path subject))
    | some primitive =>
        have paired := matched_independent_pairing path output [primitive] outputApart
          (by intro candidate member name occurs
              simp only [List.mem_singleton] at member
              subst candidate
              exact False.elim (literal_excludes subject primitive name primitiveRun occurs))
        cases matchedRun : matched (.var output) [primitive] with
        | nil => simp [matchedRun] at paired
        | cons first rest =>
            have paired' : List.Forall₂ (AnswerEquivalent path output) (first :: rest) [primitive] := by
              simpa only [matchedRun] using paired
            cases paired' with
            | cons head tail =>
                cases tail
                exact ⟨[first], [primitive], by simp [select, matchedRun], rfl, .cons head .nil⟩

private theorem expression_fresh_normalize (library : List Declaration) (fuel : Nat)
    (path : Path) (items : List TypeTerm) :
    expression library freshSupply (run library freshSupply fuel) path items none =
      ((functions library freshSupply (run library freshSupply fuel) path items none).bind fun answers =>
        if answers.isEmpty then
          (structural freshSupply (run library freshSupply fuel) path items none).map (finish none)
        else some answers) := by
  unfold expression
  cases functions library freshSupply (run library freshSupply fuel) path items none with
  | none => rfl
  | some answers =>
      cases answers with
      | nil =>
          cases structural freshSupply (run library freshSupply fuel) path items none <;> rfl
      | cons first rest => simp [allowsRow, finish]

private theorem expression_variable_normalize (library : List Declaration) (fuel : Nat)
    (path : Path) (items : List TypeTerm) (output : Nat)
    (outputApart : AllocationApart path (.var output))
    (independent : ∀ item ∈ items, output ∉ item.freeVars) :
    expression library freshSupply (run library freshSupply fuel) path items (some (.var output)) =
      ((functions library freshSupply (run library freshSupply fuel) path items (some (.var output))).bind
        fun answers => if answers.isEmpty then
          (structural freshSupply (run library freshSupply fuel) path items (some (.var output))).map
            (finish (some (.var output))) else some answers) := by
  cases functionRun : functions library freshSupply (run library freshSupply fuel) path items
      (some (.var output)) with
  | none => simp only [expression, functionRun, bind, Option.bind]
  | some answers =>
      cases answers with
      | nil =>
          obtain ⟨fresh, freshRun, paired⟩ := functions_pairing_reverse library fuel path items output
            outputApart independent [] functionRun
          cases paired
          simp only [expression, functionRun, freshRun, allowsRow, List.isEmpty_nil,
            Bool.true_and, ↓reduceIte, bind, Option.bind, List.nil_append]
          cases structural freshSupply (run library freshSupply fuel) path items (some (.var output)) <;> rfl
      | cons first rest => simp [expression, functionRun, allowsRow, finish]

private theorem expression_fresh_to_bound (library : List Declaration) (fuel : Nat)
    (path : Path) (items : List TypeTerm) (output : Nat)
    (outputApart : AllocationApart path (.var output))
    (independent : ∀ item ∈ items, output ∉ item.freeVars)
    (rowsTransfer : ∀ fresh,
      structural freshSupply (run library freshSupply fuel) path items none = some fresh →
      ∃ bound, structural freshSupply (run library freshSupply fuel) path items
        (some (.var output)) = some bound ∧ List.Forall₂ (AnswerEquivalent path output) bound fresh)
    (fresh : List TypeTerm)
    (returned : expression library freshSupply (run library freshSupply fuel) path items none = some fresh) :
    ∃ bound, expression library freshSupply (run library freshSupply fuel) path items
      (some (.var output)) = some bound ∧ List.Forall₂ (AnswerEquivalent path output) bound fresh := by
  rw [expression_fresh_normalize] at returned
  obtain ⟨freshFunctions, freshRun, remaining⟩ := Option.bind_eq_some_iff.mp returned
  obtain ⟨boundFunctions, boundRun, paired⟩ := functions_pairing library fuel path items output
    outputApart independent freshFunctions freshRun
  rw [expression_variable_normalize library fuel path items output outputApart independent, boundRun]
  cases freshFunctions with
  | nil =>
      have boundEmpty := List.forall₂_nil_right_iff.mp paired
      subst boundFunctions
      simp only [List.isEmpty_nil, ↓reduceIte] at remaining
      cases rowsRun : structural freshSupply (run library freshSupply fuel) path items none with
      | none => simp [rowsRun] at remaining
      | some freshRows =>
          have same : finish none freshRows = fresh := by simpa [rowsRun] using remaining
          subst fresh
          obtain ⟨boundRows, boundRowsRun, rowPairing⟩ := rowsTransfer freshRows rowsRun
          exact ⟨_, by simp [boundRowsRun], finish_pairing path output _ _ rowPairing⟩
  | cons first rest =>
      cases boundFunctions with
      | nil => cases paired
      | cons head tail =>
          have same : first :: rest = fresh := by simpa using remaining
          subst fresh
          exact ⟨head :: tail, rfl, paired⟩

private theorem expression_bound_to_fresh (library : List Declaration) (fuel : Nat)
    (path : Path) (items : List TypeTerm) (output : Nat)
    (outputApart : AllocationApart path (.var output))
    (independent : ∀ item ∈ items, output ∉ item.freeVars)
    (rowsTransfer : ∀ bound,
      structural freshSupply (run library freshSupply fuel) path items (some (.var output)) = some bound →
      ∃ fresh, structural freshSupply (run library freshSupply (fuel + 1)) path items none = some fresh ∧
        List.Forall₂ (AnswerEquivalent path output) bound fresh)
    (bound : List TypeTerm)
    (returned : expression library freshSupply (run library freshSupply fuel) path items
      (some (.var output)) = some bound) :
    ∃ fresh, expression library freshSupply (run library freshSupply (fuel + 1)) path items none = some fresh ∧
      List.Forall₂ (AnswerEquivalent path output) bound fresh := by
  rw [expression_variable_normalize library fuel path items output outputApart independent] at returned
  obtain ⟨boundFunctions, boundRun, remaining⟩ := Option.bind_eq_some_iff.mp returned
  obtain ⟨freshFunctions, freshRun, paired⟩ := functions_pairing_reverse library fuel path items output
    outputApart independent boundFunctions boundRun
  have larger := Completion.functions_extends library freshSupply _ _
    (Completion.run_succ_extends library freshSupply fuel) path items none freshFunctions freshRun
  rw [expression_fresh_normalize, larger]
  cases boundFunctions with
  | nil =>
      have freshEmpty := List.forall₂_nil_left_iff.mp paired
      subst freshFunctions
      simp only [List.isEmpty_nil, ↓reduceIte] at remaining
      cases rowsRun : structural freshSupply (run library freshSupply fuel) path items (some (.var output)) with
      | none => simp [rowsRun] at remaining
      | some boundRows =>
          have same : finish (some (.var output)) boundRows = bound := by simpa [rowsRun] using remaining
          subst bound
          obtain ⟨freshRows, freshRowsRun, rowPairing⟩ := rowsTransfer boundRows rowsRun
          exact ⟨_, by simp [freshRowsRun], finish_pairing path output _ _ rowPairing⟩
  | cons first rest =>
      cases freshFunctions with
      | nil => cases paired
      | cons head tail =>
          have same : first :: rest = bound := by simpa using remaining
          subst bound
          exact ⟨head :: tail, rfl, paired⟩

private theorem child_field_apart (path : Path) (position : Nat) :
    AllocationApart (0 :: position :: 4 :: path) (.var (freshSupply (3 :: path) position)) := by
  intro stem slot occurs
  have same := (Term.mem_freeVars_var (σ := signature)).mp occurs
  exact field_name_ne_child_allocation path stem position position slot same.symm

/-- Completed intrinsic root queries permit independent output publication
in both directions. Fresh inference at depth `fuel` is simulated at the
same bound depth. Bound inference at depth `fuel` is simulated by fresh
inference at depth `fuel + 1`, accounting for skipped variable fields.

Each original answer occurrence is paired at its original position and has
identical joint refinements on every caller observation. The admission
excludes allocator capture of source names and of the independent output;
it makes no groundness assumption about either the subject or observations. -/
theorem completed_independent_output (library : List Declaration) (fuel : Nat) :
    (∀ path subject output,
      AllocationApart path subject → AllocationApart path (.var output) →
      output ∉ subject.freeVars → ∀ fresh,
      run library freshSupply fuel path subject none = some fresh →
      ∃ bound, run library freshSupply fuel path subject (some (.var output)) = some bound ∧
        List.Forall₂ (AnswerEquivalent path output) bound fresh) ∧
    (∀ path subject output,
      AllocationApart path subject → AllocationApart path (.var output) →
      output ∉ subject.freeVars → ∀ bound,
      run library freshSupply fuel path subject (some (.var output)) = some bound →
      ∃ fresh, run library freshSupply (fuel + 1) path subject none = some fresh ∧
        List.Forall₂ (AnswerEquivalent path output) bound fresh) := by
  induction fuel with
  | zero =>
      constructor
      · intro path subject output sourceApart outputApart independent fresh returned
        simp [run] at returned
      · intro path subject output sourceApart outputApart independent bound returned
        simp [run] at returned
  | succ fuel ih =>
      constructor
      · intro path subject output sourceApart outputApart independent fresh returned
        change step library freshSupply (run library freshSupply fuel) path subject none = some fresh at returned
        by_cases leaf : elements subject = none
        · obtain ⟨bound, expected, boundRun, freshRun, paired⟩ :=
            leaf_pairing library (run library freshSupply fuel) path subject output outputApart leaf
          have same : expected = fresh := Option.some.inj (freshRun.symm.trans returned)
          exact ⟨bound, boundRun, same ▸ paired⟩
        · cases subject with
          | var _ => simp [elements] at leaf
          | const _ => simp [elements] at leaf
          | app arity terms =>
              let items := List.ofFn terms
              have sourceItems : ∀ item ∈ items, AllocationApart path item := by
                intro item member stem slot occurs
                obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
                exact sourceApart stem slot ((Term.mem_freeVars_app (σ := signature)).mpr ⟨index, occurs⟩)
              have independentItems : ∀ item ∈ items, output ∉ item.freeVars := by
                intro item member occurs
                obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
                exact independent ((Term.mem_freeVars_app (σ := signature)).mpr ⟨index, occurs⟩)
              change expression library freshSupply (run library freshSupply fuel) path items none = some fresh at returned
              apply expression_fresh_to_bound library fuel path items output outputApart independentItems _ fresh returned
              intro freshRowAnswers rowsRun
              cases vectorsRun : freshRows (run library freshSupply fuel) (4 :: path) 0 items with
              | none => simp [structural, vectorsRun] at rowsRun
              | some freshVectors =>
                  obtain ⟨boundVectors, boundVectorsRun, vectorsPaired⟩ :=
                    completed_fresh_rows_to_field library fuel fuel path 0 items freshVectors vectorsRun
                      (by
                        intro position _ item member freshChild freshChildRun
                        have fieldIndependent : freshSupply (3 :: path) position ∉ item.freeVars :=
                          sourceItems item member [3] position
                        obtain ⟨boundChild, boundChildRun, childrenPaired⟩ :=
                          ih.1 (0 :: position :: 4 :: path) item (freshSupply (3 :: path) position)
                            ((sourceItems item member).descendant [0, position, 4])
                            (child_field_apart path position) fieldIndependent freshChild freshChildRun
                        by_cases sourceVariable : isVariable item = true
                        · have singleton : boundChild = [.var (freshSupply (3 :: path) position)] := by
                            cases fuel with
                            | zero => simp [run] at boundChildRun
                            | succ depth => simpa only [run, step, sourceVariable, ↓reduceIte,
                                Option.getD_some, Option.some.injEq] using boundChildRun.symm
                          subst boundChild
                          exact ⟨_, by simp [fieldAnswers, sourceVariable], childrenPaired⟩
                        · exact ⟨boundChild, by simpa only [fieldAnswers, sourceVariable, Bool.false_eq_true, ↓reduceIte]
                            using boundChildRun, childrenPaired⟩)
                  obtain ⟨boundRowAnswers, expected, boundRowsRun, freshRowsRun, rowsPaired⟩ :=
                    structural_completed_pairing library fuel fuel path items output sourceItems outputApart
                      independentItems boundVectors freshVectors boundVectorsRun vectorsRun vectorsPaired
                  have same : expected = freshRowAnswers := Option.some.inj (freshRowsRun.symm.trans rowsRun)
                  exact ⟨boundRowAnswers, boundRowsRun, same ▸ rowsPaired⟩
      · intro path subject output sourceApart outputApart independent bound returned
        change step library freshSupply (run library freshSupply fuel) path subject (some (.var output)) = some bound at returned
        by_cases leaf : elements subject = none
        · obtain ⟨expected, fresh, boundRun, freshRun, paired⟩ :=
            leaf_pairing library (run library freshSupply fuel) path subject output outputApart leaf
          have same : expected = bound := Option.some.inj (boundRun.symm.trans returned)
          exact ⟨fresh, Completion.run_succ_extends library freshSupply (fuel + 1) path subject none fresh freshRun,
            same ▸ paired⟩
        · cases subject with
          | var _ => simp [elements] at leaf
          | const _ => simp [elements] at leaf
          | app arity terms =>
              let items := List.ofFn terms
              have sourceItems : ∀ item ∈ items, AllocationApart path item := by
                intro item member stem slot occurs
                obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
                exact sourceApart stem slot ((Term.mem_freeVars_app (σ := signature)).mpr ⟨index, occurs⟩)
              have independentItems : ∀ item ∈ items, output ∉ item.freeVars := by
                intro item member occurs
                obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
                exact independent ((Term.mem_freeVars_app (σ := signature)).mpr ⟨index, occurs⟩)
              change expression library freshSupply (run library freshSupply fuel) path items (some (.var output)) = some bound at returned
              apply expression_bound_to_fresh library fuel path items output outputApart independentItems _ bound returned
              intro boundRowAnswers rowsRun
              have projection := structural_independent_product library fuel path items output [] independentItems
                (fun item present => (sourceItems item present).fieldsApart 0)
                (outputApart.fieldsApart 0) (by simp)
              rw [rowsRun, Option.map_some] at projection
              cases vectorsRun : fieldRows library fuel path 0 items with
              | none => simp [vectorsRun] at projection
              | some boundVectors =>
                  obtain ⟨freshVectors, freshVectorsRun, vectorsPaired⟩ :=
                    completed_field_rows_to_fresh library fuel (fuel + 1) path 0 items boundVectors vectorsRun
                      (by
                        intro position _ item member boundChild boundChildRun
                        by_cases sourceVariable : isVariable item = true
                        · have singleton : boundChild = [.var (freshSupply (3 :: path) position)] := by
                            simpa only [fieldAnswers, sourceVariable, ↓reduceIte, Option.some.injEq]
                              using boundChildRun.symm
                          subst boundChild
                          refine ⟨[.var (freshSupply (5 :: 0 :: position :: 4 :: path) 0)], ?_, .cons ?_ .nil⟩
                          · simp only [run, step, sourceVariable, ↓reduceIte, Option.getD_none]
                          · exact fresh_variable_equivalent (0 :: position :: 4 :: path)
                              (freshSupply (3 :: path) position)
                              (Ne.symm (field_name_ne_child_allocation path [5] position position 0))
                        · have actualRun : run library freshSupply fuel (0 :: position :: 4 :: path)
                              item (some (.var (freshSupply (3 :: path) position))) = some boundChild := by
                            simpa only [fieldAnswers, sourceVariable, Bool.false_eq_true, ↓reduceIte] using boundChildRun
                          exact ih.2 (0 :: position :: 4 :: path) item (freshSupply (3 :: path) position)
                            ((sourceItems item member).descendant [0, position, 4])
                            (child_field_apart path position) (sourceItems item member [3] position)
                            boundChild actualRun)
                  obtain ⟨expected, freshRowAnswers, boundRowsRun, freshRowsRun, rowsPaired⟩ :=
                    structural_completed_pairing library fuel (fuel + 1) path items output sourceItems outputApart
                      independentItems boundVectors freshVectors vectorsRun freshVectorsRun vectorsPaired
                  have same : expected = boundRowAnswers := Option.some.inj (boundRowsRun.symm.trans rowsRun)
                  exact ⟨freshRowAnswers, freshRowsRun, same ▸ rowsPaired⟩

/-- Any two completed approximations agree on the ordered answer schemes,
even when fresh and bound traversal complete at different depths. -/
theorem completed_answer_vectors_equivalent (library : List Declaration)
    (boundFuel freshFuel : Nat) (path : Path) (subject : TypeTerm) (output : Nat)
    (sourceApart : AllocationApart path subject)
    (outputApart : AllocationApart path (.var output)) (independent : output ∉ subject.freeVars)
    (bound fresh : List TypeTerm)
    (boundRun : run library freshSupply boundFuel path subject (some (.var output)) = some bound)
    (freshRun : run library freshSupply freshFuel path subject none = some fresh) :
    List.Forall₂ (AnswerEquivalent path output) bound fresh := by
  obtain ⟨other, otherRun, paired⟩ := (completed_independent_output library freshFuel).1
    path subject output sourceApart outputApart independent fresh freshRun
  have same := Completion.completed_answers_unique library freshSupply freshFuel boundFuel
    path subject (some (.var output)) other bound otherRun boundRun
  exact same ▸ paired

/-- Completion itself is equivalent. This statement includes completed
empty vectors; unfinished approximation is never interpreted as exhaustion. -/
theorem independent_completion_iff (library : List Declaration)
    (path : Path) (subject : TypeTerm) (output : Nat)
    (sourceApart : AllocationApart path subject)
    (outputApart : AllocationApart path (.var output)) (independent : output ∉ subject.freeVars) :
    (∃ fuel answers, run library freshSupply fuel path subject (some (.var output)) = some answers) ↔
      ∃ fuel answers, run library freshSupply fuel path subject none = some answers := by
  constructor
  · rintro ⟨fuel, bound, returned⟩
    obtain ⟨fresh, freshRun, _⟩ := (completed_independent_output library fuel).2
      path subject output sourceApart outputApart independent bound returned
    exact ⟨fuel + 1, fresh, freshRun⟩
  · rintro ⟨fuel, fresh, returned⟩
    obtain ⟨bound, boundRun, _⟩ := (completed_independent_output library fuel).1
      path subject output sourceApart outputApart independent fresh returned
    exact ⟨fuel, bound, boundRun⟩

/-- The completed vectors have equal joint refinement families for every
caller observation, including repeated variables and shared subterms. -/
theorem completed_publication_exact (library : List Declaration)
    (boundFuel freshFuel : Nat) (path : Path) (subject : TypeTerm) (output : Nat)
    (sourceApart : AllocationApart path subject)
    (outputApart : AllocationApart path (.var output)) (independent : output ∉ subject.freeVars)
    (bound fresh : List TypeTerm)
    (boundRun : run library freshSupply boundFuel path subject (some (.var output)) = some bound)
    (freshRun : run library freshSupply freshFuel path subject none = some fresh)
    (observations : List TypeTerm)
    (observationsApart : ∀ term ∈ observations, AllocationApart path term) :
    bound.map (fun answer => IndependentOutputUnification.solutions [(answer, .var output)] observations) =
      fresh.map (fun answer => IndependentOutputUnification.solutions [(answer, .var output)] observations) := by
  have paired := completed_answer_vectors_equivalent library boundFuel freshFuel path subject output
    sourceApart outputApart independent bound fresh boundRun freshRun
  clear boundRun freshRun
  induction paired with
  | nil => rfl
  | cons same _ ih =>
      exact congrArg₂ List.cons (same observations observationsApart) ih

/-- The model's caller namespace supplies a concrete, nonvacuous admission
for source terms and observations. It is disjoint from every activation,
structural field and recursively allocated private name. -/
theorem caller_term_allocation_apart (path : Path) (term : TypeTerm)
    (sourceNames : ∀ name ∈ term.freeVars, ∃ index, name = callerName index) :
    AllocationApart path term := by
  intro stem slot occurs
  obtain ⟨index, same⟩ := sourceNames _ occurs
  exact fresh_supply_separate (stem ++ path) slot index same

/-- A caller-named independent output and arbitrary caller-named subject
satisfy the full recursive theorem's allocation admission. -/
theorem caller_output_publication_exact (library : List Declaration)
    (boundFuel freshFuel : Nat) (path : Path) (subject : TypeTerm) (output : Nat)
    (sourceNames : ∀ name ∈ subject.freeVars, ∃ index, name = callerName index)
    (independent : callerName output ∉ subject.freeVars)
    (bound fresh : List TypeTerm)
    (boundRun : run library freshSupply boundFuel path subject (some (.var (callerName output))) = some bound)
    (freshRun : run library freshSupply freshFuel path subject none = some fresh)
    (observations : List TypeTerm)
    (observationNames : ∀ term ∈ observations, ∀ name ∈ term.freeVars, ∃ index, name = callerName index) :
    bound.map (fun answer => IndependentOutputUnification.solutions
      [(answer, .var (callerName output))] observations) =
    fresh.map (fun answer => IndependentOutputUnification.solutions
      [(answer, .var (callerName output))] observations) := by
  apply completed_publication_exact library boundFuel freshFuel path subject (callerName output)
    (caller_term_allocation_apart path subject sourceNames) _ independent bound fresh boundRun freshRun
    observations (fun term member => caller_term_allocation_apart path term (observationNames term member))
  apply caller_term_allocation_apart
  intro name present
  exact ⟨output, (Term.mem_freeVars_var (σ := signature)).mp present⟩

end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Root
