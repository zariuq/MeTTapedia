import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutputSpine

/-!
# Recursive incremental intrinsic typing

A known proper row already supplies each child's requirement before that
child runs. Matching the entire row after querying fresh child types would
change these checks. This module relates the actual eager matcher of private
fields to those already-known requirements, keeping refinement between
successive children. It then proves full recursive equivalence under source
and type-name separation, derives that admission for each recursive child,
and proves completion at a sufficient finite source-size bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.SpineRecursive

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.UnificationRenaming
open IntrinsicTypeFacts (signature TypeTerm Declaration)
open Structural Admission Spine

/-- Bind only the freshly allocated row fields. Existing requirement
variables retain their names and sharing. -/
def bindFields (path : Path) (position : Nat) : List TypeTerm → Subst signature
  | [] => Subst.id signature
  | target :: later => bindFields path (position + 1) later ∘ₛ
      Subst.single (freshSupply (3 :: path) position) target

private theorem single_fixes (name : Nat) (value term : TypeTerm)
    (absent : name ∉ term.freeVars) :
    (Subst.single name value).applyTerm term = term := by
  apply Subst.applyTerm_eq_self
  intro other present
  exact Subst.single_ne value (fun equal => absent (equal ▸ present))

/-- An actual fresh-variable unification step, with its continuation. -/
private theorem match_fresh_head (name : Nat) (target : TypeTerm)
    (rest : List (TypeTerm × TypeTerm)) (absent : name ∉ target.freeVars) :
    unifyTotal ((.var name, target) :: rest) =
      (unifyTotal ((Subst.single name target).applyEqs rest)).map
        (fun later => later ∘ₛ Subst.single name target) := by
  cases target with
  | var other =>
      have different : name ≠ other := by simpa only [Term.freeVars, Finset.mem_singleton] using absent
      simp only [unifyTotal, different, ↓reduceIte]
      cases unifyTotal ((Subst.single name (.var other)).applyEqs rest) <;> rfl
  | const value =>
      simp only [unifyTotal, Term.occursIn, Bool.false_eq_true, ↓reduceIte]
      cases unifyTotal ((Subst.single name (.const value)).applyEqs rest) <;> rfl
  | app arity arguments =>
      have noOccurs : ¬ (Term.app arity arguments : TypeTerm).occursIn name = true :=
        fun occurs => absent ((Term.occursIn_iff_mem_freeVars (σ := signature) name _).mp occurs)
      simp only [unifyTotal, noOccurs]
      cases unifyTotal ((Subst.single name (.app arity arguments)).applyEqs rest) <;> rfl

/-- The earlier field binding leaves all later private fields and all
existing requirement terms untouched. -/
private theorem single_fixes_later_equations (path : Path) (position later : Nat)
    (before : position < later) (value : TypeTerm) (targets : List TypeTerm)
    (apart : ∀ target ∈ targets, FieldsApart path position target) :
    (Subst.single (freshSupply (3 :: path) position) value).applyEqs
      ((fieldVariables path later targets.length).zip targets) =
      (fieldVariables path later targets.length).zip targets := by
  induction targets generalizing later with
  | nil => rfl
  | cons target rest ih =>
      have headFixed := single_fixes (freshSupply (3 :: path) position) value target
        (fun occurs => apart target List.mem_cons_self position (Nat.le_refl _) _ occurs (Or.inl rfl))
      have different : freshSupply (3 :: path) later ≠ freshSupply (3 :: path) position := by
        intro equal
        have same := ((fresh_supply_injective _ _ _ _).mp equal).2
        omega
      simp only [List.length_cons, fieldVariables, List.zip_cons_cons, Subst.applyEqs, List.map_cons]
      rw [headFixed, show (Subst.single (freshSupply (3 :: path) position) value).applyTerm
        (.var (freshSupply (3 :: path) later)) = .var (freshSupply (3 :: path) later)
        from Subst.single_ne value different]
      congr 1
      exact ih (later + 1) (by omega)
        (fun item member => apart item (List.mem_cons_of_mem _ member))

/-- Unifying private fields with a pre-existing vector produces only the
expected field bindings. This evaluates the actual total unifier. -/
theorem match_field_vector (path : Path) (position : Nat) (targets : List TypeTerm)
    (apart : ∀ target ∈ targets, FieldsApart path position target) :
    unifyTotal ((fieldVariables path position targets.length).zip targets) =
      some (bindFields path position targets) := by
  induction targets generalizing position with
  | nil => simp [fieldVariables, bindFields, unifyTotal]
  | cons target rest ih =>
      simp only [List.length_cons, fieldVariables, List.zip_cons_cons]
      rw [match_fresh_head _ target _
        (fun occurs => apart target List.mem_cons_self position (Nat.le_refl _) _ occurs (Or.inl rfl)),
        single_fixes_later_equations path position (position + 1) (by omega) target rest
          (fun item member => apart item (List.mem_cons_of_mem _ member)),
        ih (position + 1) (fun item member =>
          (apart item (List.mem_cons_of_mem _ member)).later (by omega))]
      rfl

/-- Field initialization does not mutate any existing type or source term
whose names are outside this invocation's field namespace. -/
theorem bindFields_fixes (path : Path) (position : Nat) (targets : List TypeTerm)
    (term : TypeTerm) (apart : FieldsApart path position term) :
    (bindFields path position targets).applyTerm term = term := by
  induction targets generalizing position with
  | nil => exact Subst.applyTerm_id _
  | cons target rest ih =>
      simp only [bindFields, Subst.applyTerm_comp]
      rw [single_fixes _ target term
        (fun occurs => apart position (Nat.le_refl _) _ occurs (Or.inl rfl))]
      exact ih (position + 1) (apart.later (by omega))

private theorem single_fixes_later_fields (path : Path) (position later count : Nat)
    (before : position < later) (value : TypeTerm) :
    (fieldVariables path later count).map
      (Subst.single (freshSupply (3 :: path) position) value).applyTerm =
      fieldVariables path later count := by
  induction count generalizing later with
  | zero => rfl
  | succ count ih =>
      simp only [fieldVariables, List.map_cons]
      rw [show (Subst.single (freshSupply (3 :: path) position) value).applyTerm
        (.var (freshSupply (3 :: path) later)) = .var (freshSupply (3 :: path) later)
        from Subst.single_ne value (fun equal => by
          have same := ((fresh_supply_injective _ _ _ _).mp equal).2; omega), ih (later + 1) (by omega)]

/-- Applying the actual initial matcher returns the original ordered type
vector, even when its fields share type variables. -/
theorem bindFields_vector (path : Path) (position : Nat) (targets : List TypeTerm)
    (apart : ∀ target ∈ targets, FieldsApart path position target) :
    (fieldVariables path position targets.length).map (bindFields path position targets).applyTerm = targets := by
  induction targets generalizing position with
  | nil => rfl
  | cons target rest ih =>
      simp only [List.length_cons, fieldVariables, List.map_cons, bindFields, Subst.applyTerm_comp]
      rw [show (Subst.single (freshSupply (3 :: path) position) target).applyTerm
        (.var (freshSupply (3 :: path) position)) = target from Subst.single_eq _ _,
        bindFields_fixes path (position + 1) rest target
          ((apart target List.mem_cons_self).later (by omega))]
      congr 1
      have fieldsFixed := single_fixes_later_fields path position (position + 1) rest.length
        (by omega) target
      rw [show (bindFields path (position + 1) rest ∘ₛ
          Subst.single (freshSupply (3 :: path) position) target).applyTerm =
          (bindFields path (position + 1) rest).applyTerm ∘
            (Subst.single (freshSupply (3 :: path) position) target).applyTerm
        from funext (fun term => Subst.applyTerm_comp _ _ term), ← List.map_map, fieldsFixed]
      exact ih (position + 1) (fun item member =>
        (apart item (List.mem_cons_of_mem _ member)).later (by omega))

private theorem fields_length (path : Path) (position count : Nat) :
    (fieldVariables path position count).length = count := by
  induction count generalizing position with
  | zero => rfl
  | succ count ih => simp only [fieldVariables, List.length_cons, ih]

private theorem cast_fin_apply {first second : Nat} (same : first = second)
    (values : Fin first → TypeTerm) (index : Fin second) :
    (same ▸ values) index = values ⟨index.val, by omega⟩ := by
  cases same
  rfl

private theorem match_rows (first second : List TypeTerm) (sameLength : first.length = second.length) :
    unifyTotal [(row first, row second)] = unifyTotal (first.zip second) := by
  simp only [row, unifyTotal]
  split
  · rename_i same
    congr 1
    apply List.ext_getElem
    · simp [finPairsToList, sameLength]
    · intro index firstBound secondBound
      simp [finPairsToList]
      exact cast_fin_apply _ _ _
  · contradiction

/-- A known proper row initializes the exact requirements which the
incremental spine exposes one at a time. -/
theorem match_proper_row (path : Path) (position : Nat) (targets : List TypeTerm)
    (apart : ∀ target ∈ targets, FieldsApart path position target) :
    unifyTotal [(row (fieldVariables path position targets.length), row targets)] =
      some (bindFields path position targets) := by
  rw [match_rows _ _ (fields_length path position targets.length)]
  exact match_field_vector path position targets apart

private theorem row_substitute (store : Subst signature) (items : List TypeTerm) :
    store.applyTerm (row items) = row (items.map store.applyTerm) := by
  simp only [row, Subst.applyTerm, Term.app.injEq, List.length_map, true_and]
  apply (Fin.heq_fun_iff (List.length_map store.applyTerm).symm).mpr
  intro index
  simp

/-- With equal row lengths, the initial eager match and the direct known
requirements enter exactly the same resolved argument traversal. All later
queries still receive the current refined requirement, before they run. -/
theorem proper_row_arguments (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (items targets : List TypeTerm)
    (sameLength : items.length = targets.length)
    (sourceApart : ∀ item ∈ items, FieldsApart path position item)
    (targetApart : ∀ target ∈ targets, FieldsApart path position target) :
    arguments (run library freshSupply fuel) (4 :: path) position
      (items.zip (fieldVariables path position items.length))
      (row (fieldVariables path position items.length)) (bindFields path position targets) =
    Resolution.argumentsResolved (run library freshSupply fuel) (4 :: path) position
      (items.zip targets) (row targets) := by
  rw [sameLength, Resolution.arguments_eq_resolved, row_substitute,
    bindFields_vector path position targets targetApart]
  congr 1
  have sourceFixed : items.map (bindFields path position targets).applyTerm = items := by
    conv_rhs => rw [← List.map_id items]
    apply List.map_congr_left
    intro item present
    exact bindFields_fixes path position targets item (sourceApart item present)
  change ((items.zip (fieldVariables path position targets.length)).map
    (Prod.map (bindFields path position targets).applyTerm (bindFields path position targets).applyTerm)) = _
  rw [← List.zip_map]
  rw [sourceFixed, bindFields_vector path position targets targetApart]

/-- Consume a pre-existing proper row in source order. The end-of-list
check occurs when the traversal reaches it, after earlier child queries.
Unlike `zip`, this does not silently discard an unmatched suffix. -/
def knownRow (query : Query) (path : Path) (position : Nat) :
    List TypeTerm → List TypeTerm → TypeTerm → Result
  | [], [], result => some [result]
  | subject :: rest, formal :: later, result =>
      if isVariable subject then knownRow query path (position + 1) rest later result
      else do
        let candidates ← query (0 :: position :: path) subject (some formal)
        collect candidates fun candidate =>
          match unifyTotal [(candidate, formal)] with
          | none => some []
          | some refinement => knownRow query path (position + 1)
              (rest.map refinement.applyTerm) (later.map refinement.applyTerm)
              (refinement.applyTerm result)
  | _, _, _ => some []
termination_by subjects => subjects.length
decreasing_by all_goals simp_wf

/-- On a known row of the right length, incremental consumption is exactly
the existing sequential argument service, including all current type checks. -/
theorem knownRow_eq_arguments (query : Query) (path : Path) (position : Nat)
    (items targets : List TypeTerm) (result : TypeTerm)
    (sameLength : items.length = targets.length) :
    knownRow query path position items targets result =
      Resolution.argumentsResolved query path position (items.zip targets) result := by
  induction items using (measure List.length).wf.induction generalizing position targets result with
  | h items ih =>
      cases items with
      | nil =>
          have empty : targets = [] := List.eq_nil_of_length_eq_zero sameLength.symm
          subst targets
          simp only [knownRow, List.zip_nil_left, Resolution.argumentsResolved]
      | cons subject rest =>
          cases targets with
          | nil => simp at sameLength
          | cons formal later =>
              have lengths : rest.length = later.length := Nat.succ.inj sameLength
              simp only [knownRow, List.zip_cons_cons, Resolution.argumentsResolved]
              split
              · exact ih rest (Nat.lt_succ_self rest.length) (position + 1) later result lengths
              · cases query (0 :: position :: path) subject (some formal) with
                | none => rfl
                | some candidates =>
                    simp only [bind, Option.bind]
                    apply Coordinates.collect_congr
                    intro candidate _
                    cases accepted : unifyTotal [(candidate, formal)] with
                    | none => rfl
                    | some refinement =>
                        simp only
                        rw [ih (rest.map refinement.applyTerm) (by change (rest.map refinement.applyTerm).length < (subject :: rest).length; simpa only [List.length_map, List.length_cons] using Nat.lt_succ_self rest.length)
                          (position + 1) (later.map refinement.applyTerm)
                          (refinement.applyTerm result) (by simpa using lengths)]
                        congr 1
                        exact List.zip_map

/-- A completed traversal of a row with the wrong length is answerless.
An incomplete earlier query remains incomplete; this theorem does not
turn it into exhaustion or claim an equal approximation depth. -/
theorem knownRow_mismatch_completed (query : Query) (path : Path) (position : Nat)
    (items targets : List TypeTerm) (result : TypeTerm)
    (different : items.length ≠ targets.length) (answers : List TypeTerm)
    (returned : knownRow query path position items targets result = some answers) :
    answers = [] := by
  induction items using (measure List.length).wf.induction generalizing position targets result answers with
  | h items ih =>
      cases items with
      | nil =>
          cases targets with
          | nil => exact False.elim (different rfl)
          | cons _ _ => simpa only [knownRow, Option.some.injEq] using returned.symm
      | cons subject rest =>
          cases targets with
          | nil => simpa only [knownRow, Option.some.injEq] using returned.symm
          | cons formal later =>
              have lengths : rest.length ≠ later.length := fun equal => different (by simpa using equal)
              simp only [knownRow] at returned
              split at returned
              · exact ih rest (Nat.lt_succ_self rest.length) (position + 1) later result lengths answers returned
              · cases queried : query (0 :: position :: path) subject (some formal) with
                | none => simp only [queried, bind, Option.bind] at returned; cases returned
                | some candidates =>
                    simp only [queried, bind, Option.bind] at returned
                    have emptyBranch : ∀ candidate ∈ candidates, ∀ branch,
                        (match unifyTotal [(candidate, formal)] with
                        | none => some []
                        | some refinement => knownRow query path (position + 1)
                            (rest.map refinement.applyTerm) (later.map refinement.applyTerm)
                            (refinement.applyTerm result)) = some branch → branch = [] := by
                      intro candidate _ branch run
                      split at run
                      · exact Option.some.inj run.symm
                      · rename_i refinement accepted
                        exact ih (rest.map refinement.applyTerm) (by change (rest.map refinement.applyTerm).length < (subject :: rest).length; simpa only [List.length_map, List.length_cons] using Nat.lt_succ_self rest.length) (position + 1)
                          (later.map refinement.applyTerm) (refinement.applyTerm result)
                          (by simpa using lengths) branch run
                    apply List.eq_nil_iff_forall_not_mem.mpr
                    intro answer member
                    obtain ⟨candidate, present, branch, run, inBranch⟩ :=
                      collect_member _ _ _ returned member
                    rw [emptyBranch candidate present branch run] at inBranch
                    exact List.not_mem_nil inBranch

/-- Combined proper-row entry theorem: the eager fresh-field matcher and
the incremental known-row traversal make precisely the same child calls
and return precisely the same ordered answers at equal child fuel. -/
theorem proper_row_entry (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (items targets : List TypeTerm)
    (sameLength : items.length = targets.length)
    (sourceApart : ∀ item ∈ items, FieldsApart path position item)
    (targetApart : ∀ target ∈ targets, FieldsApart path position target) :
    ((unifyTotal [(row (fieldVariables path position items.length), row targets)]).bind fun initial =>
      arguments (run library freshSupply fuel) (4 :: path) position
        (items.zip (fieldVariables path position items.length))
        (row (fieldVariables path position items.length)) initial) =
      knownRow (run library freshSupply fuel) (4 :: path) position items targets (row targets) := by
  rw [sameLength, match_proper_row path position targets targetApart, Option.bind_some]
  rw [← sameLength, proper_row_arguments library fuel path position items targets sameLength sourceApart targetApart]
  exact (knownRow_eq_arguments _ _ _ _ _ _ sameLength).symm

private theorem collect_complete {α β : Type} (items : List α)
    (visit : α → Option (List β))
    (complete : ∀ item ∈ items, (visit item).isSome) :
    (collect items visit).isSome := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      have first := complete item List.mem_cons_self
      have later := ih (fun other member => complete other (List.mem_cons_of_mem _ member))
      cases headRun : visit item with
      | none => simp only [headRun] at first; cases first
      | some answers =>
          cases tailRun : collect rest visit with
          | none => simp only [tailRun] at later; cases later
          | some more => simp only [collect, headRun, tailRun, bind, Option.bind, Option.pure_def, Option.isSome_some]

/-- Complete smaller child queries remain complete throughout a function's
argument traversal. Non-ground subjects are retained exactly: actual child
refinements cannot introduce protected source names into later formals or
change a source variable. This is the induction step needed for a source-
size completion bound, rather than assuming that variable-free inputs are
the only safe inputs. -/
theorem arguments_complete_separated (library : List Declaration) (fuel : Nat)
    (path : Path) (sourceFrame : TypeTerm) (sources : List TypeTerm)
    (sourceApart : AllocationApart path sourceFrame)
    (sourceNames : ∀ subject ∈ sources, subject.freeVars ⊆ sourceFrame.freeVars)
    (complete : ∀ subject ∈ sources, ∀ position required,
      Disjoint sourceFrame.freeVars required.freeVars →
      (run library freshSupply fuel (0 :: position :: path) subject (some required)).isSome)
    (position : Nat) (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm)
    (pendingSources : ∀ pair ∈ pending, pair.1 ∈ sources)
    (pendingApart : ∀ pair ∈ pending, Disjoint sourceFrame.freeVars pair.2.freeVars) :
    (Resolution.argumentsResolved (run library freshSupply fuel) path position pending result).isSome := by
  induction pending using (measure List.length).wf.induction generalizing position result with
  | h pending ih =>
      cases pending with
      | nil => simp only [Resolution.argumentsResolved, Option.isSome_some]
      | cons pair rest =>
          rcases pair with ⟨subject, formal⟩
          simp only [Resolution.argumentsResolved]
          split
          · exact ih rest (Nat.lt_succ_self rest.length) (position + 1) result
              (fun pair member => pendingSources pair (List.mem_cons_of_mem _ member))
              (fun pair member => pendingApart pair (List.mem_cons_of_mem _ member))
          · have available := complete subject (pendingSources _ List.mem_cons_self)
              position formal (pendingApart _ List.mem_cons_self)
            cases queried : run library freshSupply fuel (0 :: position :: path) subject (some formal) with
            | none => simp only [queried] at available; cases available
            | some answers =>
                simp only [bind, Option.bind]
                apply collect_complete
                intro candidate present
                cases accepted : unifyTotal [(candidate, formal)] with
                | none => rfl
                | some refinement =>
                    have protectedFixed := query_match_preserves_separate_source library fuel
                      (0 :: position :: path) subject formal sourceFrame answers
                      (sourceApart.descendant [0, position]) (pendingApart _ List.mem_cons_self)
                      queried candidate present refinement accepted
                    have sourceFixed : ∀ item ∈ sources, refinement.applyTerm item = item := by
                      intro item member
                      apply Subst.applyTerm_eq_self
                      intro name occurs
                      exact Subst.var_fixed_of_applyTerm_eq_self protectedFixed name
                        (sourceNames item member occurs)
                    apply ih (rest.map fun pair => (refinement.applyTerm pair.1, refinement.applyTerm pair.2))
                      (by change (rest.map _).length < ((subject, formal) :: rest).length
                          simpa only [List.length_map, List.length_cons] using Nat.lt_succ_self rest.length)
                      (position + 1) (refinement.applyTerm result)
                    · intro changed member
                      obtain ⟨old, oldPresent, rfl⟩ := List.mem_map.mp member
                      have inSources := pendingSources old (List.mem_cons_of_mem _ oldPresent)
                      simpa only [sourceFixed old.1 inSources] using inSources
                    · intro changed member
                      obtain ⟨old, oldPresent, rfl⟩ := List.mem_map.mp member
                      exact query_match_preserves_source_separation library fuel (0 :: position :: path)
                        subject formal sourceFrame old.2 answers (sourceApart.descendant [0, position])
                        (pendingApart _ List.mem_cons_self)
                        (pendingApart old (List.mem_cons_of_mem _ oldPresent))
                        queried candidate present refinement accepted

/-- An existing type requirement can be shared among several formals.
That sharing is preserved, while the source frame stays untouched. -/
theorem bound_child_frame (library : List Declaration) (fuel : Nat) (path : Path)
    (subject formal sourceFrame : TypeTerm) (answers : List TypeTerm)
    (sourceApart : AllocationApart path sourceFrame)
    (formalApart : Disjoint sourceFrame.freeVars formal.freeVars)
    (returned : run library freshSupply fuel path subject (some formal) = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, formal)] = some refinement)
    (pending : List (TypeTerm × TypeTerm))
    (sourceNames : ∀ pair ∈ pending, pair.1.freeVars ⊆ sourceFrame.freeVars)
    (pendingApart : ∀ pair ∈ pending, Disjoint sourceFrame.freeVars pair.2.freeVars) :
    ∀ pair ∈ pending,
      refinement.applyTerm pair.1 = pair.1 ∧
      Disjoint sourceFrame.freeVars (refinement.applyTerm pair.2).freeVars := by
  have protectedFixed := query_match_preserves_separate_source library fuel path subject formal
    sourceFrame answers sourceApart formalApart returned candidate present refinement accepted
  intro pair member
  constructor
  · apply Subst.applyTerm_eq_self
    intro name occurs
    exact Subst.var_fixed_of_applyTerm_eq_self protectedFixed name (sourceNames pair member occurs)
  · exact query_match_preserves_source_separation library fuel path subject formal sourceFrame pair.2
      answers sourceApart formalApart (pendingApart pair member) returned candidate present refinement accepted

/-- Equal-fuel eager/incremental completion is false even with a closed
source. The eager wrong-arity match rejects immediately; the incremental
row reaches its first child, whose depth-zero approximation is unfinished. -/
theorem wrong_length_depth_separator :
    structural freshSupply (run [] freshSupply 0) [] [IntrinsicTypeFacts.named "item"]
      (some (row [IntrinsicTypeFacts.undefinedType, IntrinsicTypeFacts.undefinedType])) = some [] ∧
    knownRow (run [] freshSupply 0) [4] 0 [IntrinsicTypeFacts.named "item"]
      [IntrinsicTypeFacts.undefinedType, IntrinsicTypeFacts.undefinedType]
      (row [IntrinsicTypeFacts.undefinedType, IntrinsicTypeFacts.undefinedType]) = none := by
  constructor
  · simp [structural, row, unifyTotal]
  · simp [knownRow, IntrinsicTypeFacts.named, isVariable, run]

private theorem match_fixes_separate (source first second : TypeTerm) (refinement : Subst signature)
    (firstApart : Disjoint source.freeVars first.freeVars)
    (secondApart : Disjoint source.freeVars second.freeVars)
    (accepted : unifyTotal [(first, second)] = some refinement) :
    refinement.applyTerm source = source := by
  apply Subst.applyTerm_eq_self
  intro name occurs
  apply (unifyTotal_relevantIdempotent _ _ accepted).fixes
  simp only [eqVars, Finset.union_empty, Finset.mem_union, not_or]
  exact ⟨fun present => Finset.disjoint_left.mp firstApart occurs present,
    fun present => Finset.disjoint_left.mp secondApart occurs present⟩

private theorem match_keeps_separate (source first second term : TypeTerm) (refinement : Subst signature)
    (firstApart : Disjoint source.freeVars first.freeVars)
    (secondApart : Disjoint source.freeVars second.freeVars)
    (termApart : Disjoint source.freeVars term.freeVars)
    (accepted : unifyTotal [(first, second)] = some refinement) :
    Disjoint source.freeVars (refinement.applyTerm term).freeVars := by
  apply Finset.disjoint_left.mpr
  intro name occurs after
  exact match_excludes_name first second name refinement accepted
    (fun present => Finset.disjoint_left.mp firstApart occurs present)
    (fun present => Finset.disjoint_left.mp secondApart occurs present)
    term (fun present => Finset.disjoint_left.mp termApart occurs present) after

private theorem functions_complete_separated (library : List Declaration) (fuel : Nat)
    (path : Path) (sourceFrame : TypeTerm) (sources : List TypeTerm)
    (sourceApart : AllocationApart path sourceFrame)
    (sourceNames : ∀ subject ∈ sources, subject.freeVars ⊆ sourceFrame.freeVars)
    (complete : ∀ subject ∈ sources, ∀ position required,
      Disjoint sourceFrame.freeVars required.freeVars →
      (run library freshSupply fuel (0 :: position :: path) subject (some required)).isSome)
    (items : List TypeTerm) (required : Option TypeTerm)
    (inSources : ∀ item ∈ items, item ∈ sources)
    (requiredApart : ∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars) :
    (functions library freshSupply (run library freshSupply fuel) path items required).isSome := by
  cases items with
  | nil => rfl
  | cons head actuals =>
      simp only [functions]
      apply collect_complete
      intro scheme member
      have schemeApart : Disjoint sourceFrame.freeVars scheme.freeVars := by
        apply Finset.disjoint_left.mpr
        intro name occurs
        exact declarations_exclude library freshSupply path head name
          (fun occurrence slot equal => sourceApart [1, occurrence] slot (equal.symm ▸ occurs))
          scheme member
      cases parsed : callParts actuals.length scheme with
      | none => rfl
      | some pair =>
          rcases pair with ⟨domains, result⟩
          have domainApart : ∀ domain ∈ domains, Disjoint sourceFrame.freeVars domain.freeVars := by
            intro domain member
            apply Finset.disjoint_left.mpr
            intro name occurs
            exact (callParts_exclude scheme actuals.length domains result name
              (fun present => Finset.disjoint_left.mp schemeApart occurs present) parsed).1 domain member
          have resultApart : Disjoint sourceFrame.freeVars result.freeVars := by
            apply Finset.disjoint_left.mpr
            intro name occurs
            exact (callParts_exclude scheme actuals.length domains result name
              (fun present => Finset.disjoint_left.mp schemeApart occurs present) parsed).2
          have pendingSources : ∀ pair ∈ actuals.zip domains, pair.1 ∈ sources := by
            intro pair present
            exact inSources pair.1 (List.mem_cons_of_mem _ (List.of_mem_zip present).1)
          have pendingApart : ∀ pair ∈ actuals.zip domains, Disjoint sourceFrame.freeVars pair.2.freeVars :=
            fun pair present => domainApart pair.2 (List.of_mem_zip present).2
          cases required with
          | none =>
              simp only [Resolution.arguments_id]
              exact arguments_complete_separated library fuel path sourceFrame sources sourceApart
                sourceNames complete 0 (actuals.zip domains) result pendingSources pendingApart
          | some target =>
              have targetApart : Disjoint sourceFrame.freeVars target.freeVars := requiredApart target (by simp)
              simp only
              cases accepted : unifyTotal [(result, target)] with
              | none => rfl
              | some initial =>
                  simp only [Resolution.arguments_eq_resolved]
                  have frameFixed := match_fixes_separate sourceFrame result target initial resultApart targetApart accepted
                  have subjectsFixed : ∀ item ∈ sources, initial.applyTerm item = item := by
                    intro item member
                    apply Subst.applyTerm_eq_self
                    intro name occurs
                    exact Subst.var_fixed_of_applyTerm_eq_self frameFixed name (sourceNames item member occurs)
                  apply arguments_complete_separated library fuel path sourceFrame sources sourceApart
                    sourceNames complete 0 _ (initial.applyTerm result)
                  · intro changed present
                    obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
                    have source := pendingSources old member
                    simpa only [subjectsFixed old.1 source] using source
                  · intro changed present
                    obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
                    exact match_keeps_separate sourceFrame result target old.2 initial
                      resultApart targetApart (pendingApart old member) accepted

private theorem freshRows_complete (query : Query) (path : Path) (position : Nat)
    (items : List TypeTerm)
    (complete : ∀ item ∈ items, ∀ position, (query (0 :: position :: path) item none).isSome) :
    (freshRows query path position items).isSome := by
  induction items generalizing position with
  | nil => rfl
  | cons item rest ih =>
      have first := complete item List.mem_cons_self position
      have later := ih (position + 1)
        (fun other member => complete other (List.mem_cons_of_mem _ member))
      cases here : query (0 :: position :: path) item none with
      | none => simp only [here] at first; cases first
      | some answers =>
          cases tail : freshRows query path (position + 1) rest with
          | none => simp only [tail] at later; cases later
          | some rows => simp only [freshRows, here, tail, bind, Option.bind, Option.pure_def, Option.isSome_some]

private theorem structural_complete_separated (library : List Declaration) (fuel : Nat)
    (path : Path) (sourceFrame : TypeTerm) (items : List TypeTerm)
    (sourceApart : AllocationApart path sourceFrame)
    (sourceNames : ∀ subject ∈ items, subject.freeVars ⊆ sourceFrame.freeVars)
    (complete : ∀ subject ∈ items, ∀ position required,
      (∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars) →
      (run library freshSupply fuel (0 :: position :: 4 :: path) subject required).isSome)
    (required : Option TypeTerm)
    (requiredApart : ∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars) :
    (structural freshSupply (run library freshSupply fuel) path items required).isSome := by
  cases required with
  | none =>
      simpa only [structural, Option.isSome_map] using
        freshRows_complete (run library freshSupply fuel) (4 :: path) 0 items
          (fun subject member position => complete subject member position none (by simp))
  | some target =>
      let fields := (List.range items.length).map fun index =>
        (Term.var (freshSupply (3 :: path) index) : TypeTerm)
      have fieldsApart : ∀ field ∈ fields, Disjoint sourceFrame.freeVars field.freeVars := by
        intro field member
        obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
        apply Finset.disjoint_left.mpr
        intro name occurs inField
        simp only [Term.freeVars, Finset.mem_singleton] at inField
        exact sourceApart [3] index (inField ▸ occurs)
      have resultApart : Disjoint sourceFrame.freeVars (row fields).freeVars := by
        apply Finset.disjoint_left.mpr
        intro name occurs inRow
        obtain ⟨index, inField⟩ := (Term.mem_freeVars_app (σ := signature)).mp inRow
        exact Finset.disjoint_left.mp (fieldsApart fields[index] (List.getElem_mem _)) occurs inField
      have targetApart := requiredApart target (by simp)
      change (match unifyTotal [(row fields, target)] with
        | none => some []
        | some initial => arguments (run library freshSupply fuel) (4 :: path) 0
            (items.zip fields) (row fields) initial).isSome
      cases accepted : unifyTotal [(row fields, target)] with
      | none => rfl
      | some initial =>
          simp only [Resolution.arguments_eq_resolved]
          have frameFixed := match_fixes_separate sourceFrame (row fields) target initial
            resultApart targetApart accepted
          have subjectsFixed : ∀ item ∈ items, initial.applyTerm item = item := by
            intro item member
            apply Subst.applyTerm_eq_self
            intro name occurs
            exact Subst.var_fixed_of_applyTerm_eq_self frameFixed name (sourceNames item member occurs)
          apply arguments_complete_separated library fuel (4 :: path) sourceFrame items
            (sourceApart.descendant [4]) sourceNames
            (fun subject member position formal apart =>
              complete subject member position (some formal) (by simpa using apart))
            0 _ (initial.applyTerm (row fields))
          · intro changed member
            obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
            have source := (List.of_mem_zip present).1
            simpa only [subjectsFixed old.1 source] using source
          · intro changed member
            obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
            exact match_keeps_separate sourceFrame (row fields) target old.2 initial
              resultApart targetApart (fieldsApart old.2 (List.of_mem_zip present).2) accepted

private theorem bind_complete {α β : Type} (value : Option α) (next : α → Option β)
    (complete : value.isSome) (nextComplete : ∀ item, (next item).isSome) :
    (value.bind next).isSome := by
  cases value with
  | none => cases complete
  | some item => exact nextComplete item

private theorem expression_complete_separated (library : List Declaration) (fuel : Nat)
    (path : Path) (sourceFrame : TypeTerm) (items : List TypeTerm)
    (sourceApart : AllocationApart path sourceFrame)
    (sourceNames : ∀ subject ∈ items, subject.freeVars ⊆ sourceFrame.freeVars)
    (complete : ∀ subject ∈ items, ∀ stem required,
      (∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars) →
      (run library freshSupply fuel (stem ++ path) subject required).isSome)
    (required : Option TypeTerm)
    (requiredApart : ∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars) :
    (expression library freshSupply (run library freshSupply fuel) path items required).isSome := by
  have functionsDone (target : Option TypeTerm)
      (apart : ∀ term ∈ target.toList, Disjoint sourceFrame.freeVars term.freeVars) :=
    functions_complete_separated library fuel path sourceFrame items sourceApart sourceNames
      (fun subject member position formal separated => complete subject member [0, position]
        (some formal) (by simpa using separated)) items target (fun _ member => member) apart
  have rows := structural_complete_separated library fuel path sourceFrame items sourceApart sourceNames
    (fun subject member position target separated => complete subject member [0, position, 4] target separated)
    required requiredApart
  unfold expression
  apply bind_complete _ _ (functionsDone required requiredApart)
  intro answers
  apply bind_complete
  · cases required with
    | none => rfl
    | some target => dsimp only; split
                     · exact functionsDone none (by simp)
                     · rfl
  · intro allAnswers
    apply bind_complete
    · split
      · exact rows
      · rfl
    · intro rowAnswers
      rfl

/-- Finite source size bounds complete intrinsic evaluation even for
non-ground subjects. Incoming type variables may share with one another,
but not with the source; fresh signature allocation is disjoint from the
source. Every recursive source therefore remains a strict source subterm.
This is a completion theorem, not an identification of algorithm budgets. -/
theorem separated_subject_complete (library : List Declaration) (fuel : Nat)
    (path : Path) (subject : TypeTerm) (required : Option TypeTerm)
    (sourceApart : AllocationApart path subject)
    (requiredApart : ∀ term ∈ required.toList, Disjoint subject.freeVars term.freeVars)
    (enough : subject.size < fuel) :
    (run library freshSupply fuel path subject required).isSome := by
  induction fuel generalizing path subject required with
  | zero => omega
  | succ fuel ih =>
      cases subject with
      | var name => simp only [run, step, isVariable, ↓reduceIte, Option.isSome_some]
      | const value =>
          simp only [run, step, isVariable, Bool.false_eq_true, ↓reduceIte, literal]
          cases IntrinsicTypeFacts.primitiveType value <;> simp only
          · rfl
          · split <;> rfl
      | app arity children =>
          simp only [run, step, isVariable, Bool.false_eq_true, ↓reduceIte, literal, elements]
          have childNames : ∀ item ∈ List.ofFn children,
              item.freeVars ⊆ (Term.app arity children : TypeTerm).freeVars := by
            intro item member name occurs
            obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
            exact (Term.mem_freeVars_app (σ := signature)).mpr ⟨index, occurs⟩
          apply expression_complete_separated library fuel path (.app arity children)
            (List.ofFn children) sourceApart childNames
          · intro item member stem target separated
            apply ih (stem ++ path) item target
            · intro more slot occurs
              exact (sourceApart.descendant stem) more slot (childNames item member occurs)
            · intro formal inTarget
              apply Finset.disjoint_left.mpr
              intro name occurs inFormal
              exact Finset.disjoint_left.mp (separated formal inTarget) (childNames item member occurs) inFormal
            · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
              have smaller := Term.size_subterm (ts := children) index
              omega
          · exact requiredApart

/-- Allocation inside one argument invocation cannot name a variable
allocated inside a different sibling, at any recursive depth. -/
theorem sibling_allocations_distinct (path leftStem rightStem : Path)
    (left right leftSlot rightSlot : Nat) (different : left ≠ right) :
    freshSupply (leftStem ++ 0 :: left :: path) leftSlot ≠
      freshSupply (rightStem ++ 0 :: right :: path) rightSlot := by
  intro equal
  have paths := ((fresh_supply_injective _ _ _ _).mp equal).1
  have reversed := congrArg List.reverse paths
  simp only [List.reverse_append, List.reverse_cons] at reversed
  have tails : [left, 0] ++ leftStem.reverse = [right, 0] ++ rightStem.reverse := by
    apply List.append_cancel_left (as := path.reverse)
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using reversed
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at tails
  exact different tails.1

/-- Pending type terms cannot capture the allocator of any unvisited
argument. They may retain names from earlier completed children. -/
def FutureApart (path : Path) (position : Nat) (term : TypeTerm) : Prop :=
  ∀ later, position ≤ later → AllocationApart (0 :: later :: path) term

theorem FutureApart.later {path : Path} {position : Nat} {term : TypeTerm}
    (apart : FutureApart path position term) {later : Nat} (after : position ≤ later) :
    FutureApart path later term := fun index bound => apart index (by omega)

theorem allocation_future {path : Path} {term : TypeTerm} (apart : AllocationApart path term)
    (position : Nat) : FutureApart path position term :=
  fun later _ => apart.descendant [0, later]

/-- An actual child query and MGU keep the unvisited sibling namespace
absent. The proof uses the query's output-support theorem and does not
assume a correspondence with the incremental evaluator. -/
theorem child_match_future (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (subject formal term : TypeTerm)
    (formalApart : FutureApart path position formal)
    (termApart : FutureApart path position term)
    (answers : List TypeTerm)
    (returned : run library freshSupply fuel (0 :: position :: path) subject (some formal) = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, formal)] = some refinement) :
    FutureApart path (position + 1) (refinement.applyTerm term) := by
  intro later after stem slot
  have formalAbsent := formalApart later (by omega) stem slot
  have termAbsent := termApart later (by omega) stem slot
  have candidateAbsent := run_output_excludes_name library fuel (0 :: position :: path)
    subject (some formal) answers (freshSupply (stem ++ 0 :: later :: path) slot)
    (fun other otherSlot => sibling_allocations_distinct path other stem position later otherSlot slot (by omega))
    (by simpa using formalAbsent) returned candidate present
  exact match_excludes_name candidate formal _ refinement accepted candidateAbsent formalAbsent term termAbsent

/-- Replace the recursive service throughout an argument traversal.
The replacement need agree only on admitted calls: original source
subterms, separated type requirements, and fresh future allocation.
All three premises are preserved by the actual intervening MGUs. -/
theorem arguments_congr_separated (library : List Declaration) (fuel : Nat) (other : Query)
    (path : Path) (sourceFrame : TypeTerm) (sources : List TypeTerm)
    (sourceApart : AllocationApart path sourceFrame)
    (sourceNames : ∀ subject ∈ sources, subject.freeVars ⊆ sourceFrame.freeVars)
    (same : ∀ subject ∈ sources, ∀ position formal,
      Disjoint sourceFrame.freeVars formal.freeVars →
      AllocationApart (0 :: position :: path) formal →
      run library freshSupply fuel (0 :: position :: path) subject (some formal) =
        other (0 :: position :: path) subject (some formal))
    (position : Nat) (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm)
    (pendingSources : ∀ pair ∈ pending, pair.1 ∈ sources)
    (pendingApart : ∀ pair ∈ pending, Disjoint sourceFrame.freeVars pair.2.freeVars)
    (pendingFuture : ∀ pair ∈ pending, FutureApart path position pair.2) :
    Resolution.argumentsResolved (run library freshSupply fuel) path position pending result =
      Resolution.argumentsResolved other path position pending result := by
  induction pending using (measure List.length).wf.induction generalizing position result with
  | h pending ih =>
      cases pending with
      | nil => simp only [Resolution.argumentsResolved]
      | cons pair rest =>
          rcases pair with ⟨subject, formal⟩
          simp only [Resolution.argumentsResolved]
          split
          · exact ih rest (Nat.lt_succ_self rest.length) (position + 1) result
              (fun pair member => pendingSources pair (List.mem_cons_of_mem _ member))
              (fun pair member => pendingApart pair (List.mem_cons_of_mem _ member))
              (fun pair member => (pendingFuture pair (List.mem_cons_of_mem _ member)).later (by omega))
          · have querySame := same subject (pendingSources _ List.mem_cons_self) position formal
              (pendingApart _ List.mem_cons_self) (pendingFuture _ List.mem_cons_self position (Nat.le_refl _))
            rw [← querySame]
            cases queried : run library freshSupply fuel (0 :: position :: path) subject (some formal) with
            | none => rfl
            | some answers =>
                simp only [bind, Option.bind]
                apply Coordinates.collect_congr
                intro candidate present
                cases accepted : unifyTotal [(candidate, formal)] with
                | none => rfl
                | some refinement =>
                    have frame := bound_child_frame library fuel (0 :: position :: path) subject formal
                      sourceFrame answers (sourceApart.descendant [0, position])
                      (pendingApart _ List.mem_cons_self) queried candidate present refinement accepted rest
                      (fun pair member => sourceNames pair.1 (pendingSources pair (List.mem_cons_of_mem _ member)))
                      (fun pair member => pendingApart pair (List.mem_cons_of_mem _ member))
                    apply ih (rest.map fun pair => (refinement.applyTerm pair.1, refinement.applyTerm pair.2))
                      (by change (rest.map _).length < ((subject, formal) :: rest).length
                          simpa only [List.length_map, List.length_cons] using Nat.lt_succ_self rest.length)
                      (position + 1) (refinement.applyTerm result)
                    · intro changed member
                      obtain ⟨old, oldPresent, rfl⟩ := List.mem_map.mp member
                      simpa only [(frame old oldPresent).1] using pendingSources old (List.mem_cons_of_mem _ oldPresent)
                    · intro changed member
                      obtain ⟨old, oldPresent, rfl⟩ := List.mem_map.mp member
                      exact (frame old oldPresent).2
                    · intro changed member
                      obtain ⟨old, oldPresent, rfl⟩ := List.mem_map.mp member
                      exact child_match_future library fuel path position subject formal old.2
                        (pendingFuture _ List.mem_cons_self) (pendingFuture old (List.mem_cons_of_mem _ oldPresent))
                        answers queried candidate present refinement accepted

private theorem signature_child_distinct (path stem : Path) (occurrence position slot other : Nat) :
    freshSupply (1 :: occurrence :: path) slot ≠ freshSupply (stem ++ 0 :: position :: path) other := by
  intro equal
  have reversed := congrArg List.reverse ((fresh_supply_injective _ _ _ _).mp equal).1
  simp only [List.reverse_append, List.reverse_cons] at reversed
  have tails : [occurrence, 1] = [position, 0] ++ stem.reverse := by
    apply List.append_cancel_left (as := path.reverse)
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using reversed
  simp at tails

private theorem match_keeps_future (path : Path) (position : Nat)
    (first second term : TypeTerm) (refinement : Subst signature)
    (firstApart : FutureApart path position first)
    (secondApart : FutureApart path position second)
    (termApart : FutureApart path position term)
    (accepted : unifyTotal [(first, second)] = some refinement) :
    FutureApart path position (refinement.applyTerm term) := by
  intro later after stem slot
  exact match_excludes_name first second _ refinement accepted
    (firstApart later after stem slot) (secondApart later after stem slot)
    term (termApart later after stem slot)

private theorem functions_congr_separated (library : List Declaration) (fuel : Nat) (other : Query)
    (path : Path) (sourceFrame : TypeTerm) (sources : List TypeTerm)
    (sourceApart : AllocationApart path sourceFrame)
    (sourceNames : ∀ subject ∈ sources, subject.freeVars ⊆ sourceFrame.freeVars)
    (same : ∀ subject ∈ sources, ∀ position formal,
      Disjoint sourceFrame.freeVars formal.freeVars →
      AllocationApart (0 :: position :: path) formal →
      run library freshSupply fuel (0 :: position :: path) subject (some formal) =
        other (0 :: position :: path) subject (some formal))
    (items : List TypeTerm) (required : Option TypeTerm)
    (inSources : ∀ item ∈ items, item ∈ sources)
    (requiredApart : ∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars)
    (requiredFresh : ∀ term ∈ required.toList, AllocationApart path term) :
    functions library freshSupply (run library freshSupply fuel) path items required =
      functions library freshSupply other path items required := by
  cases items with
  | nil => rfl
  | cons head actuals =>
      simp only [functions]
      apply Coordinates.collect_congr
      intro scheme member
      have schemeApart : Disjoint sourceFrame.freeVars scheme.freeVars := by
        apply Finset.disjoint_left.mpr
        intro name occurs
        exact declarations_exclude library freshSupply path head name
          (fun occurrence slot equal => sourceApart [1, occurrence] slot (equal.symm ▸ occurs))
          scheme member
      have schemeFuture : FutureApart path 0 scheme := by
        intro later _ stem slot
        exact declarations_exclude library freshSupply path head _
          (fun occurrence other => signature_child_distinct path stem occurrence later other slot) scheme member
      cases parsed : callParts actuals.length scheme with
      | none => rfl
      | some pair =>
          rcases pair with ⟨domains, result⟩
          have domainApart : ∀ domain ∈ domains, Disjoint sourceFrame.freeVars domain.freeVars := by
            intro domain member
            apply Finset.disjoint_left.mpr
            intro name occurs
            exact (callParts_exclude scheme actuals.length domains result name
              (fun present => Finset.disjoint_left.mp schemeApart occurs present) parsed).1 domain member
          have resultApart : Disjoint sourceFrame.freeVars result.freeVars := by
            apply Finset.disjoint_left.mpr
            intro name occurs
            exact (callParts_exclude scheme actuals.length domains result name
              (fun present => Finset.disjoint_left.mp schemeApart occurs present) parsed).2
          have domainFuture : ∀ domain ∈ domains, FutureApart path 0 domain := by
            intro domain member later after stem slot
            exact (callParts_exclude scheme actuals.length domains result _
              (schemeFuture later after stem slot) parsed).1 domain member
          have resultFuture : FutureApart path 0 result := by
            intro later after stem slot
            exact (callParts_exclude scheme actuals.length domains result _
              (schemeFuture later after stem slot) parsed).2
          have pendingSources : ∀ pair ∈ actuals.zip domains, pair.1 ∈ sources := by
            intro pair present
            exact inSources pair.1 (List.mem_cons_of_mem _ (List.of_mem_zip present).1)
          have pendingApart : ∀ pair ∈ actuals.zip domains, Disjoint sourceFrame.freeVars pair.2.freeVars :=
            fun pair present => domainApart pair.2 (List.of_mem_zip present).2
          have pendingFuture : ∀ pair ∈ actuals.zip domains, FutureApart path 0 pair.2 :=
            fun pair present => domainFuture pair.2 (List.of_mem_zip present).2
          cases required with
          | none =>
              simp only [Resolution.arguments_id]
              exact arguments_congr_separated library fuel other path sourceFrame sources sourceApart
                sourceNames same 0 (actuals.zip domains) result pendingSources pendingApart pendingFuture
          | some target =>
              have targetApart : Disjoint sourceFrame.freeVars target.freeVars := requiredApart target (by simp)
              have targetFuture := allocation_future (requiredFresh target (by simp)) 0
              simp only
              cases accepted : unifyTotal [(result, target)] with
              | none => rfl
              | some initial =>
                  simp only [Resolution.arguments_eq_resolved]
                  have frameFixed := match_fixes_separate sourceFrame result target initial resultApart targetApart accepted
                  have subjectsFixed : ∀ item ∈ sources, initial.applyTerm item = item := by
                    intro item member
                    apply Subst.applyTerm_eq_self
                    intro name occurs
                    exact Subst.var_fixed_of_applyTerm_eq_self frameFixed name (sourceNames item member occurs)
                  apply arguments_congr_separated library fuel other path sourceFrame sources sourceApart
                    sourceNames same 0 _ (initial.applyTerm result)
                  · intro changed present
                    obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
                    have source := pendingSources old member
                    simpa only [subjectsFixed old.1 source] using source
                  · intro changed present
                    obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
                    exact match_keeps_separate sourceFrame result target old.2 initial
                      resultApart targetApart (pendingApart old member) accepted
                  · intro changed present
                    obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
                    exact match_keeps_future path 0 result target old.2 initial
                      resultFuture targetFuture (pendingFuture old member) accepted

/-- Complete admitted child services can be replaced inside a proper row,
including rows whose length ultimately fails. The mismatch is checked at
the end, so all prefix queries retain their actual early requirements. -/
theorem knownRow_transfer (library : List Declaration) (fuel : Nat) (other : Query)
    (path : Path) (sourceFrame : TypeTerm) (sources : List TypeTerm)
    (sourceApart : AllocationApart path sourceFrame)
    (sourceNames : ∀ subject ∈ sources, subject.freeVars ⊆ sourceFrame.freeVars)
    (complete : ∀ subject ∈ sources, ∀ position formal,
      Disjoint sourceFrame.freeVars formal.freeVars →
      (run library freshSupply fuel (0 :: position :: path) subject (some formal)).isSome)
    (same : ∀ subject ∈ sources, ∀ position formal,
      Disjoint sourceFrame.freeVars formal.freeVars →
      AllocationApart (0 :: position :: path) formal →
      run library freshSupply fuel (0 :: position :: path) subject (some formal) =
        other (0 :: position :: path) subject (some formal))
    (position : Nat) (items targets : List TypeTerm) (result : TypeTerm)
    (inSources : ∀ item ∈ items, item ∈ sources)
    (targetApart : ∀ target ∈ targets, Disjoint sourceFrame.freeVars target.freeVars)
    (targetFuture : ∀ target ∈ targets, FutureApart path position target) :
    knownRow (run library freshSupply fuel) path position items targets result =
        knownRow other path position items targets result ∧
      (knownRow (run library freshSupply fuel) path position items targets result).isSome := by
  induction items using (measure List.length).wf.induction generalizing position targets result with
  | h items ih =>
      cases items with
      | nil => cases targets <;> simp only [knownRow, Option.isSome_some, and_self]
      | cons subject rest =>
          cases targets with
          | nil => simp only [knownRow, Option.isSome_some, and_self]
          | cons formal later =>
              simp only [knownRow]
              split
              · exact ih rest (Nat.lt_succ_self rest.length) (position + 1) later result
                  (fun item member => inSources item (List.mem_cons_of_mem _ member))
                  (fun target member => targetApart target (List.mem_cons_of_mem _ member))
                  (fun target member => (targetFuture target (List.mem_cons_of_mem _ member)).later (by omega))
              · have firstDone := complete subject (inSources _ List.mem_cons_self) position formal
                  (targetApart _ List.mem_cons_self)
                have firstSame := same subject (inSources _ List.mem_cons_self) position formal
                  (targetApart _ List.mem_cons_self) (targetFuture _ List.mem_cons_self position (Nat.le_refl _))
                rw [← firstSame]
                cases queried : run library freshSupply fuel (0 :: position :: path) subject (some formal) with
                | none => simp only [queried] at firstDone; cases firstDone
                | some answers =>
                    simp only [bind, Option.bind]
                    have branch (candidate : TypeTerm) (present : candidate ∈ answers) :
                        (match unifyTotal [(candidate, formal)] with
                        | none => some []
                        | some refinement => knownRow (run library freshSupply fuel) path (position + 1)
                            (rest.map refinement.applyTerm) (later.map refinement.applyTerm)
                            (refinement.applyTerm result)) =
                        (match unifyTotal [(candidate, formal)] with
                        | none => some []
                        | some refinement => knownRow other path (position + 1)
                            (rest.map refinement.applyTerm) (later.map refinement.applyTerm)
                            (refinement.applyTerm result)) ∧
                        (match unifyTotal [(candidate, formal)] with
                        | none => some []
                        | some refinement => knownRow (run library freshSupply fuel) path (position + 1)
                            (rest.map refinement.applyTerm) (later.map refinement.applyTerm)
                            (refinement.applyTerm result)).isSome := by
                      cases accepted : unifyTotal [(candidate, formal)] with
                      | none => exact ⟨rfl, rfl⟩
                      | some refinement =>
                          have frameFixed := query_match_preserves_separate_source library fuel
                            (0 :: position :: path) subject formal sourceFrame answers
                            (sourceApart.descendant [0, position]) (targetApart _ List.mem_cons_self)
                            queried candidate present refinement accepted
                          have sourceFixed : ∀ item ∈ sources, refinement.applyTerm item = item := by
                            intro item member
                            apply Subst.applyTerm_eq_self
                            intro name occurs
                            exact Subst.var_fixed_of_applyTerm_eq_self frameFixed name (sourceNames item member occurs)
                          apply ih (rest.map refinement.applyTerm)
                            (by change (rest.map _).length < (subject :: rest).length
                                simpa only [List.length_map, List.length_cons] using Nat.lt_succ_self rest.length)
                            (position + 1) (later.map refinement.applyTerm) (refinement.applyTerm result)
                          · intro changed member
                            obtain ⟨item, present, rfl⟩ := List.mem_map.mp member
                            have original := inSources item (List.mem_cons_of_mem _ present)
                            simpa only [sourceFixed item original] using original
                          · intro changed member
                            obtain ⟨target, inLater, rfl⟩ := List.mem_map.mp member
                            exact query_match_preserves_source_separation library fuel (0 :: position :: path)
                              subject formal sourceFrame target answers (sourceApart.descendant [0, position])
                              (targetApart _ List.mem_cons_self) (targetApart target (List.mem_cons_of_mem _ inLater))
                              queried candidate present refinement accepted
                          · intro changed member
                            obtain ⟨target, inLater, rfl⟩ := List.mem_map.mp member
                            exact child_match_future library fuel path position subject formal target
                              (targetFuture _ List.mem_cons_self) (targetFuture target (List.mem_cons_of_mem _ inLater))
                              answers queried candidate present refinement accepted
                    exact ⟨Coordinates.collect_congr _ _ _ (fun candidate present => (branch candidate present).1),
                      collect_complete _ _ (fun candidate present => (branch candidate present).2)⟩

/-- Incremental structural traversal, with a proper tuple representing the
completed public spine. The private cons-cell schedule for a fresh output
is justified by `Spine.FieldActions.incremental_eq_eager`; existing proper
rows are consumed directly, with each requirement visible before its child.
This representation is admitted only when source and output are separate. -/
def structuralSpine (query : Query) (path : Path) (items : List TypeTerm) : Option TypeTerm → Result
  | none => (freshRows query (4 :: path) 0 items).map (List.map row)
  | some (.var _) =>
      let fields := (List.range items.length).map fun index =>
        (Term.var (freshSupply (3 :: path) index) : TypeTerm)
      arguments query (4 :: path) 0 (items.zip fields) (row fields) (Subst.id signature)
  | some (.const _) => some []
  | some (.app arity targets) => knownRow query (4 :: path) 0 items (List.ofFn targets) (.app arity targets)

def expressionSpine (library : List Declaration) (query : Query) (path : Path)
    (items : List TypeTerm) (required : Option TypeTerm) : Result := do
  let functionAnswers ← functions library freshSupply query path items required
  let allFunctions ← (match required with
    | none => some functionAnswers
    | some _ => if allowsRow required && functionAnswers.isEmpty then
        functions library freshSupply query path items none else some functionAnswers)
  let rowAnswers ← (if allowsRow required && allFunctions.isEmpty then
      structuralSpine query path items required else some [])
  pure (finish required (functionAnswers ++ rowAnswers))

def stepSpine (library : List Declaration) (query : Query)
    (path : Path) (subject : TypeTerm) (required : Option TypeTerm) : Result :=
  if isVariable subject then some [required.getD (.var (freshSupply (5 :: path) 0))]
  else match literal subject with
  | some primitive =>
      let primitiveAnswers := select required [primitive]
      if !primitiveAnswers.isEmpty then some primitiveAnswers else some (finish required [])
  | none => match elements subject with
    | none => some (finish required (select required (declarations library freshSupply path subject)))
    | some items => expressionSpine library query path items required

/-- Approximation depth is explicit. This is not the shared-output
interpreter: its separated-source admission is proved below. -/
def runSpine (library : List Declaration) : Nat → Query
  | 0 => fun _ _ _ => none
  | fuel + 1 => stepSpine library (runSpine library fuel)

private theorem freshRows_congr (first second : Query) (path : Path) (position : Nat)
    (items : List TypeTerm)
    (same : ∀ item ∈ items, ∀ position,
      first (0 :: position :: path) item none = second (0 :: position :: path) item none) :
    freshRows first path position items = freshRows second path position items := by
  induction items generalizing position with
  | nil => rfl
  | cons item rest ih =>
      simp only [freshRows, same item List.mem_cons_self position,
        ih (position + 1) (fun other member => same other (List.mem_cons_of_mem _ member))]

private theorem row_ofFn (arity : Nat) (children : Fin arity → TypeTerm) :
    row (List.ofFn children) = .app arity children := by
  simp only [row, Term.app.injEq, List.length_ofFn, true_and]
  apply (Fin.heq_fun_iff (List.length_ofFn (f := children))).mpr
  intro index
  simp

private theorem fieldVariables_range (path : Path) (position count : Nat) :
    fieldVariables path position count =
      (List.range' position count).map (fun index => .var (freshSupply (3 :: path) index)) := by
  induction count generalizing position with
  | zero => rfl
  | succ count ih => simp only [fieldVariables, List.range'_succ, List.map_cons, ih]

/-- Replace both the structural strategy and its recursive service. Every
call made by the replacement is admitted by derived source/future-name
invariants. Wrong-length rows may use more approximation depth, but their
completed ordered result is exactly the original empty vector. -/
theorem structural_transfer (library : List Declaration) (fuel : Nat) (other : Query)
    (path : Path) (sourceFrame : TypeTerm) (items : List TypeTerm)
    (sourceApart : AllocationApart path sourceFrame)
    (sourceNames : ∀ subject ∈ items, subject.freeVars ⊆ sourceFrame.freeVars)
    (complete : ∀ subject ∈ items, ∀ position required,
      (∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars) →
      (run library freshSupply fuel (0 :: position :: 4 :: path) subject required).isSome)
    (same : ∀ subject ∈ items, ∀ position required,
      (∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars) →
      (∀ term ∈ required.toList, AllocationApart (0 :: position :: 4 :: path) term) →
      run library freshSupply fuel (0 :: position :: 4 :: path) subject required =
        other (0 :: position :: 4 :: path) subject required)
    (required : Option TypeTerm)
    (requiredApart : ∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars)
    (requiredFresh : ∀ term ∈ required.toList, AllocationApart path term) :
    structural freshSupply (run library freshSupply fuel) path items required =
      structuralSpine other path items required := by
  cases required with
  | none =>
      simp only [structural, structuralSpine]
      rw [freshRows_congr _ _ (4 :: path) 0 items
        (fun subject member position => same subject member position none (by simp) (by simp))]
  | some target =>
      let fields := (List.range items.length).map fun index =>
        (Term.var (freshSupply (3 :: path) index) : TypeTerm)
      have fieldsApart : ∀ field ∈ fields, Disjoint sourceFrame.freeVars field.freeVars := by
        intro field member
        obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
        apply Finset.disjoint_left.mpr
        intro name occurs inField
        simp only [Term.freeVars, Finset.mem_singleton] at inField
        exact sourceApart [3] index (inField ▸ occurs)
      have fieldsFuture : ∀ field ∈ fields, FutureApart (4 :: path) 0 field := by
        intro field member later _ stem slot occurs
        obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
        simp only [Term.freeVars, Finset.mem_singleton] at occurs
        exact field_name_ne_child_allocation path stem index later slot occurs.symm
      have targetApart := requiredApart target (by simp)
      have targetFresh := requiredFresh target (by simp)
      cases target with
      | const value => simp only [structural, structuralSpine, row, unifyTotal]
      | var output =>
          have outputAbsent : ∀ item ∈ items, output ∉ item.freeVars := by
            intro item member occurs
            exact Finset.disjoint_left.mp targetApart (sourceNames item member occurs) (by simp [Term.freeVars])
          have fieldAbsent : ∀ field ∈ fields, output ∉ field.freeVars := by
            intro field member occurs
            obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
            simp only [Term.freeVars, Finset.mem_singleton] at occurs
            exact targetFresh [3] index (by simpa [Term.freeVars] using occurs.symm)
          have resultAbsent : output ∉ (row fields).freeVars := by
            intro occurs
            obtain ⟨index, inField⟩ := (Term.mem_freeVars_app (σ := signature)).mp occurs
            exact fieldAbsent fields[index] (List.getElem_mem _) inField
          have removeInitial := nonvariable_codomain_arguments (run library freshSupply fuel)
            (4 :: path) 0 (items.zip fields) (row fields) output (by intro name equal; cases equal)
            (fun pair member => ⟨outputAbsent pair.1 (List.of_mem_zip member).1,
              fieldAbsent pair.2 (List.of_mem_zip member).2⟩) resultAbsent
          have initialMatch := IndependentOutputUnification.nonvariable_output_match output (row fields)
            (by intro name equal; cases equal) resultAbsent
          rw [initialMatch, Option.bind_some] at removeInitial
          change (match unifyTotal [(row fields, .var output)] with
            | none => some []
            | some initial => arguments (run library freshSupply fuel) (4 :: path) 0 (items.zip fields)
                (row fields) initial) = arguments other (4 :: path) 0 (items.zip fields) (row fields) (Subst.id signature)
          simp only [initialMatch]
          rw [removeInitial, Resolution.arguments_id, Resolution.arguments_id]
          exact arguments_congr_separated library fuel other (4 :: path) sourceFrame items
            (sourceApart.descendant [4]) sourceNames
            (fun subject member position formal apart fresh =>
              same subject member position (some formal) (by simpa using apart) (by simpa using fresh))
            0 (items.zip fields) (row fields)
            (fun pair member => (List.of_mem_zip member).1)
            (fun pair member => fieldsApart pair.2 (List.of_mem_zip member).2)
            (fun pair member => fieldsFuture pair.2 (List.of_mem_zip member).2)
      | app arity targets =>
          let targetList := List.ofFn targets
          have targetNames : ∀ term ∈ targetList, term.freeVars ⊆ (Term.app arity targets : TypeTerm).freeVars := by
            intro term member name occurs
            obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
            exact (Term.mem_freeVars_app (σ := signature)).mpr ⟨index, occurs⟩
          have componentApart : ∀ term ∈ targetList, Disjoint sourceFrame.freeVars term.freeVars := by
            intro term member
            exact Finset.disjoint_left.mpr (fun name occurs inTerm =>
              Finset.disjoint_left.mp targetApart occurs (targetNames term member inTerm))
          have componentFresh : ∀ term ∈ targetList, AllocationApart path term :=
            fun term member stem slot occurs => targetFresh stem slot (targetNames term member occurs)
          have transferred := knownRow_transfer library fuel other (4 :: path) sourceFrame items
            (sourceApart.descendant [4]) sourceNames
            (fun subject member position formal apart => complete subject member position (some formal) (by simpa using apart))
            (fun subject member position formal apart fresh => same subject member position (some formal)
              (by simpa using apart) (by simpa using fresh))
            0 items targetList (.app arity targets) (fun _ member => member) componentApart
            (fun term member => allocation_future ((componentFresh term member).descendant [4]) 0)
          simp only [structuralSpine]
          rw [← transferred.1]
          by_cases lengths : items.length = targetList.length
          · have actualFields : fields = fieldVariables path 0 items.length := by
              simpa only [List.range'_eq_map_range, List.map_map, Function.comp_def, Nat.zero_add, fields] using
                (fieldVariables_range path 0 items.length).symm
            have rowTargets : row targetList = .app arity targets := row_ofFn arity targets
            have proper := proper_row_entry library fuel path 0 items targetList lengths
              (fun item member => (fun later after name occurs allocated =>
                sourceApart.fieldsApart 0 later after name (sourceNames item member occurs) allocated))
              (fun term member => (componentFresh term member).fieldsApart 0)
            rw [rowTargets] at proper
            have accepted : ∃ initial, unifyTotal [(row fields, .app arity targets)] = some initial := by
              rw [actualFields, lengths, ← rowTargets, match_proper_row path 0 targetList
                (fun term member => (componentFresh term member).fieldsApart 0)]
              exact ⟨_, rfl⟩
            obtain ⟨initial, accepted⟩ := accepted
            change (match unifyTotal [(row fields, .app arity targets)] with
              | none => some []
              | some initial => arguments (run library freshSupply fuel) (4 :: path) 0
                  (items.zip fields) (row fields) initial) = _
            rw [← actualFields, accepted, Option.bind_some] at proper
            rw [accepted]
            exact proper
          · have wrong : fields.length ≠ arity := by simpa [fields, targetList] using lengths
            have failed : unifyTotal [(row fields, .app arity targets)] = none := by
              simp [row, unifyTotal, wrong]
            change (match unifyTotal [(row fields, .app arity targets)] with
              | none => some []
              | some initial => arguments (run library freshSupply fuel) (4 :: path) 0
                  (items.zip fields) (row fields) initial) = _
            rw [failed]
            cases returned : knownRow (run library freshSupply fuel) (4 :: path) 0 items targetList (.app arity targets) with
            | none => simp only [returned] at transferred; cases transferred.2
            | some answers =>
                have empty := knownRow_mismatch_completed (run library freshSupply fuel) (4 :: path) 0
                  items targetList (.app arity targets) lengths answers returned
                rw [empty]

private theorem expression_transfer (library : List Declaration) (fuel : Nat) (other : Query)
    (path : Path) (sourceFrame : TypeTerm) (items : List TypeTerm)
    (sourceApart : AllocationApart path sourceFrame)
    (sourceNames : ∀ subject ∈ items, subject.freeVars ⊆ sourceFrame.freeVars)
    (complete : ∀ subject ∈ items, ∀ stem required,
      (∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars) →
      (run library freshSupply fuel (stem ++ path) subject required).isSome)
    (same : ∀ subject ∈ items, ∀ stem required,
      (∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars) →
      (∀ term ∈ required.toList, AllocationApart (stem ++ path) term) →
      run library freshSupply fuel (stem ++ path) subject required =
        other (stem ++ path) subject required)
    (required : Option TypeTerm)
    (requiredApart : ∀ term ∈ required.toList, Disjoint sourceFrame.freeVars term.freeVars)
    (requiredFresh : ∀ term ∈ required.toList, AllocationApart path term) :
    expression library freshSupply (run library freshSupply fuel) path items required =
      expressionSpine library other path items required := by
  have functionsSame (target : Option TypeTerm)
      (apart : ∀ term ∈ target.toList, Disjoint sourceFrame.freeVars term.freeVars)
      (fresh : ∀ term ∈ target.toList, AllocationApart path term) :=
    functions_congr_separated library fuel other path sourceFrame items sourceApart sourceNames
      (fun subject member position formal separated allocated => same subject member [0, position]
        (some formal) (by simpa using separated) (by simpa using allocated))
      items target (fun _ member => member) apart fresh
  have rowsSame := structural_transfer library fuel other path sourceFrame items sourceApart sourceNames
    (fun subject member position target apart => complete subject member [0, position, 4] target apart)
    (fun subject member position target apart fresh => same subject member [0, position, 4] target apart fresh)
    required requiredApart requiredFresh
  unfold expression expressionSpine
  rw [functionsSame required requiredApart requiredFresh, functionsSame none (by simp) (by simp), rowsSame]
  rfl

/-- The recursively incremental evaluator agrees with the original bound
query on admitted source/type separation. This is an equality of completed
ordered answer vectors, including duplicates, correlations, and ordinary
answerless exhaustion. Source size supplies sufficient approximation depth;
there is deliberately no equality claim for arbitrary smaller depths. -/
theorem recursive_spine_equivalence (library : List Declaration) (fuel : Nat)
    (path : Path) (subject : TypeTerm) (required : Option TypeTerm)
    (sourceApart : AllocationApart path subject)
    (requiredApart : ∀ term ∈ required.toList, Disjoint subject.freeVars term.freeVars)
    (requiredFresh : ∀ term ∈ required.toList, AllocationApart path term)
    (enough : subject.size < fuel) :
    run library freshSupply fuel path subject required =
      runSpine library fuel path subject required := by
  induction fuel generalizing path subject required with
  | zero => omega
  | succ fuel ih =>
      cases subject with
      | var name => rfl
      | const value =>
          simp only [run, runSpine, step, stepSpine, isVariable, Bool.false_eq_true, ↓reduceIte, literal]
          cases IntrinsicTypeFacts.primitiveType value <;> rfl
      | app arity children =>
          simp only [run, runSpine, step, stepSpine, isVariable, Bool.false_eq_true, ↓reduceIte, literal, elements]
          have childNames : ∀ item ∈ List.ofFn children,
              item.freeVars ⊆ (Term.app arity children : TypeTerm).freeVars := by
            intro item member name occurs
            obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
            exact (Term.mem_freeVars_app (σ := signature)).mpr ⟨index, occurs⟩
          have childApart (item : TypeTerm) (member : item ∈ List.ofFn children) (stem : Path) :
              AllocationApart (stem ++ path) item :=
            fun more slot occurs => (sourceApart.descendant stem) more slot (childNames item member occurs)
          have childSeparate (item : TypeTerm) (member : item ∈ List.ofFn children) (target : Option TypeTerm)
              (separated : ∀ term ∈ target.toList,
                Disjoint (Term.app arity children : TypeTerm).freeVars term.freeVars) :
              ∀ term ∈ target.toList, Disjoint item.freeVars term.freeVars := by
            intro term present
            exact Finset.disjoint_left.mpr (fun name occurs inFormal =>
              Finset.disjoint_left.mp (separated term present) (childNames item member occurs) inFormal)
          have childSize (item : TypeTerm) (member : item ∈ List.ofFn children) : item.size < fuel := by
            obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
            have smaller := Term.size_subterm (ts := children) index
            omega
          exact expression_transfer library fuel (runSpine library fuel) path (.app arity children)
            (List.ofFn children) sourceApart childNames
            (fun item member stem target separated => separated_subject_complete library fuel (stem ++ path)
              item target (childApart item member stem) (childSeparate item member target separated) (childSize item member))
            (fun item member stem target separated fresh => ih (stem ++ path) item target
              (childApart item member stem) (childSeparate item member target separated) fresh (childSize item member))
            required requiredApart requiredFresh

/-- The incremental implementation completes under the same sufficient
source-size bound. This does not equate the two algorithms' minimum budgets. -/
theorem recursive_spine_complete (library : List Declaration) (fuel : Nat)
    (path : Path) (subject : TypeTerm) (required : Option TypeTerm)
    (sourceApart : AllocationApart path subject)
    (requiredApart : ∀ term ∈ required.toList, Disjoint subject.freeVars term.freeVars)
    (requiredFresh : ∀ term ∈ required.toList, AllocationApart path term)
    (enough : subject.size < fuel) :
    (runSpine library fuel path subject required).isSome := by
  rw [← recursive_spine_equivalence library fuel path subject required sourceApart requiredApart requiredFresh enough]
  exact separated_subject_complete library fuel path subject required sourceApart requiredApart enough

/-- Sufficiently deep runs may use different resource budgets and still
publish the identical completed ordered vector. -/
theorem completed_spine_budget_independent (library : List Declaration) (leftFuel rightFuel : Nat)
    (path : Path) (subject : TypeTerm) (required : Option TypeTerm)
    (sourceApart : AllocationApart path subject)
    (requiredApart : ∀ term ∈ required.toList, Disjoint subject.freeVars term.freeVars)
    (requiredFresh : ∀ term ∈ required.toList, AllocationApart path term)
    (leftEnough : subject.size < leftFuel) (rightEnough : subject.size < rightFuel) :
    runSpine library leftFuel path subject required = runSpine library rightFuel path subject required := by
  rw [← recursive_spine_equivalence library leftFuel path subject required sourceApart requiredApart requiredFresh leftEnough,
    ← recursive_spine_equivalence library rightFuel path subject required sourceApart requiredApart requiredFresh rightEnough]
  have leftDone := separated_subject_complete library leftFuel path subject required sourceApart requiredApart leftEnough
  have rightDone := separated_subject_complete library rightFuel path subject required sourceApart requiredApart rightEnough
  cases leftRun : run library freshSupply leftFuel path subject required with
  | none => simp only [leftRun] at leftDone; cases leftDone
  | some leftAnswers =>
      cases rightRun : run library freshSupply rightFuel path subject required with
      | none => simp only [rightRun] at rightDone; cases rightDone
      | some rightAnswers =>
          congr 1
          exact Completion.completed_answers_unique library freshSupply leftFuel rightFuel path subject required
            leftAnswers rightAnswers leftRun rightRun

/-- The actual cons-cell protocol parameterized by its recursive query.
Private cell construction precedes the current child's check; closure is
the empty-source rule. This is separate from the normalized tuple relation. -/
inductive ExecutesWith (query : Query) (path : Path) :
    (position : Nat) → List TypeTerm → Subst spineSignature → FieldTrace path position → Prop where
  | done {position : Nat} {store : Subst spineSignature}
      (closed : unifyTotal [(nil, store (tailName path position))] = some (closeTail path position)) :
      ExecutesWith query path position [] store (.done position)
  | step {position : Nat} {subject : TypeTerm} {rest : List TypeTerm}
      {store : Subst spineSignature} {candidate : TypeTerm} {action : FieldAction path position}
      {later : FieldTrace path (position + 1)} {answers : List TypeTerm}
      (cellMatched : unifyTotal [(cons (.var (freshSupply (3 :: path) position)) (.var (tailName path (position + 1))),
        store (tailName path position))] = some (cell path position))
      (sourceResolved : (cell path position ∘ₛ store).applyTerm (embed subject) = embed subject)
      (fieldResolved : (cell path position ∘ₛ store) (freshSupply (3 :: path) position) =
        .var (freshSupply (3 :: path) position))
      (returned : (if isVariable subject then some [.var (freshSupply (3 :: path) position)]
        else query (0 :: position :: 4 :: path) subject (some (.var (freshSupply (3 :: path) position)))) = some answers)
      (present : candidate ∈ answers)
      (accepted : unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] = some action.substitution)
      (tail : ExecutesWith query path (position + 1) rest
        (extend action.substitution ∘ₛ cell path position ∘ₛ store) later) :
      ExecutesWith query path position (subject :: rest) store (.step candidate action later)

/-- The checked cons-cell trace can use the recursively incremental service
at every child. The child's fresh output, source frame, and sufficient fuel
are all discharged here; the old child service is not assumed equivalent. -/
theorem cons_execution_recursive (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (items : List TypeTerm) (store : Subst spineSignature)
    (trace : FieldTrace path position)
    (executed : Executes library fuel path position items store trace)
    (sourceApart : ∀ item ∈ items, AllocationApart path item)
    (enough : ∀ item ∈ items, item.size < fuel) :
    ExecutesWith (runSpine library fuel) path position items store trace := by
  induction executed with
  | done closed => exact .done closed
  | @step position subject rest store candidate action later answers cellMatched sourceResolved fieldResolved
      returned present accepted tail ih =>
      have independent : freshSupply (3 :: path) position ∉ subject.freeVars :=
        sourceApart subject List.mem_cons_self [3] position
      have requiredApart : Disjoint subject.freeVars (Term.var (freshSupply (3 :: path) position) : TypeTerm).freeVars := by
        apply Finset.disjoint_left.mpr
        intro name inSubject inField
        exact independent ((Term.mem_freeVars_var (σ := signature)).mp inField ▸ inSubject)
      have fieldFresh : AllocationApart (0 :: position :: 4 :: path) (.var (freshSupply (3 :: path) position)) := by
        intro stem slot occurs
        simp only [Term.freeVars, Finset.mem_singleton] at occurs
        exact field_name_ne_child_allocation path stem position position slot occurs.symm
      have service := recursive_spine_equivalence library fuel (0 :: position :: 4 :: path) subject
        (some (.var (freshSupply (3 :: path) position)))
        ((sourceApart subject List.mem_cons_self).descendant [0, position, 4])
        (by simpa using requiredApart) (by simpa using fieldFresh) (enough subject List.mem_cons_self)
      apply ExecutesWith.step cellMatched sourceResolved fieldResolved _ present accepted
        (ih (fun item member => sourceApart item (List.mem_cons_of_mem _ member))
          (fun item member => enough item (List.mem_cons_of_mem _ member)))
      simpa only [fieldAnswers, service] using returned

/-- Every ordered generated trace is an actual cons-cell execution with
recursive incremental children, and its completed spine reads back to the
same tuple with the same payload variables and aliases. -/
theorem recursive_cons_execution_readback (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (items : List TypeTerm) (rows : List (FieldTrace path position))
    (returned : traces library fuel path position items = some rows)
    (sourceApart : ∀ item ∈ items, AllocationApart path item)
    (enough : ∀ item ∈ items, item.size < fuel) :
    ∀ trace ∈ rows,
      ExecutesWith (runSpine library fuel) path position items (Subst.id spineSignature) trace ∧
      RepresentsTuple (trace.actions.incremental (tailName path position)) (traceTuple trace) := by
  intro trace present
  exact ⟨cons_execution_recursive library fuel path position items (Subst.id spineSignature) trace
      (traces_execute library fuel path position items rows returned sourceApart trace present) sourceApart enough,
    incremental_represents_tuple trace⟩

/-- The normalized fresh-output structural branch and its actual cons-cell
executions have exactly the same ordered joint caller refinements. Combined
with `recursive_cons_execution_readback`, this supplies the operational
normalization link used by the full recursive publication theorem. -/
theorem recursive_cons_publication (library : List Declaration) (fuel : Nat)
    (path : Path) (items : List TypeTerm) (output : Nat) (observations : List TypeTerm)
    (independent : ∀ item ∈ items, output ∉ item.freeVars)
    (sourceApart : ∀ item ∈ items, AllocationApart path item)
    (outputApart : AllocationApart path (.var output))
    (observationsApart : ∀ term ∈ observations, AllocationApart path term)
    (enough : ∀ item ∈ items, item.size < fuel) :
    (traces library fuel path 0 items).map (List.map fun trace =>
      IndependentOutputUnification.solutions [(traceTuple trace, .var output)] observations) =
    (structuralSpine (runSpine library fuel) path items (some (.var output))).map
      (List.map fun answer => IndependentOutputUnification.solutions [(answer, .var output)] observations) := by
  rw [structural_incremental_publication library fuel path items output observations independent sourceApart
    outputApart observationsApart]
  have names : ∀ item ∈ items, item.freeVars ⊆ (row items).freeVars := by
    intro item member name occurs
    obtain ⟨index, bounded, rfl⟩ := List.getElem_of_mem member
    exact (Term.mem_freeVars_app (σ := signature)).mpr ⟨⟨index, bounded⟩, occurs⟩
  have frameApart : AllocationApart path (row items) := by
    intro stem slot occurs
    obtain ⟨index, occurs⟩ := (Term.mem_freeVars_app (σ := signature)).mp occurs
    exact sourceApart items[index] (List.getElem_mem _) stem slot occurs
  have outputSeparate : Disjoint (row items).freeVars (Term.var output : TypeTerm).freeVars := by
    apply Finset.disjoint_left.mpr
    intro name inSource inOutput
    have equal := (Term.mem_freeVars_var (σ := signature)).mp inOutput
    subst name
    obtain ⟨index, occurs⟩ := (Term.mem_freeVars_app (σ := signature)).mp inSource
    exact independent items[index] (List.getElem_mem _) occurs
  have separate (item : TypeTerm) (member : item ∈ items) (target : Option TypeTerm)
      (apart : ∀ term ∈ target.toList, Disjoint (row items).freeVars term.freeVars) :
      ∀ term ∈ target.toList, Disjoint item.freeVars term.freeVars := by
    intro term present
    exact Finset.disjoint_left.mpr (fun name occurs inTarget =>
      Finset.disjoint_left.mp (apart term present) (names item member occurs) inTarget)
  have normalized := structural_transfer library fuel (runSpine library fuel) path (row items) items
    frameApart names
    (fun item member position target apart => separated_subject_complete library fuel
      (0 :: position :: 4 :: path) item target ((sourceApart item member).descendant [0, position, 4])
      (separate item member target apart) (enough item member))
    (fun item member position target apart fresh => recursive_spine_equivalence library fuel
      (0 :: position :: 4 :: path) item target ((sourceApart item member).descendant [0, position, 4])
      (separate item member target apart) fresh (enough item member))
    (some (.var output)) (by simpa using outputSeparate) (by simpa using outputApart)
  rw [normalized]

/-- Both children refine the same requirement; the first Number check remains visible to the second. -/
theorem recursive_shared_requirement_accepts_same_types :
    knownRow (runSpine [] 1) [] 0 [.const (.number "1"), .const (.number "2")]
      [.var 99, .var 99] (row [.var 99, .var 99]) =
      some [row [IntrinsicTypeFacts.named "Number", IntrinsicTypeFacts.named "Number"]] := by
  simp [knownRow, runSpine, stepSpine, isVariable, literal, IntrinsicTypeFacts.primitiveType,
    select, matched, finish, unifyTotal, collect, Subst.applyTerm, Subst.applyEqs, Subst.comp, Subst.single, IntrinsicTypeFacts.named, row, IntrinsicTypeFacts.undefinedType, Option.toList]
  funext index
  fin_cases index <;> simp [Subst.single]

/-- The second child cannot satisfy the shared variable after the first child fixed it to Number. -/
theorem recursive_shared_requirement_rejects_mixed_types :
    knownRow (runSpine [] 1) [] 0 [.const (.number "1"), .const (.string "two")]
      [.var 99, .var 99] (row [.var 99, .var 99]) =
      some [] := by
  simp [knownRow, runSpine, stepSpine, isVariable, literal, IntrinsicTypeFacts.primitiveType,
    select, matched, finish, unifyTotal, collect, Subst.applyTerm, Subst.applyEqs, Subst.comp, Subst.single, IntrinsicTypeFacts.named, row, IntrinsicTypeFacts.undefinedType, Option.toList]

end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.SpineRecursive
