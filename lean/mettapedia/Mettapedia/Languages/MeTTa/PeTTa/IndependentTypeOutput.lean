import Mettapedia.Logic.LP.IndependentOutputUnification
import Mettapedia.Languages.MeTTa.PeTTa.IntrinsicTypeFacts

/-!
# Ordered intrinsic type queries and independent output variables

This model follows the intrinsic service's primitive, function, structural
and declaration branches. A query carries its actual incoming requirement;
fresh inference has a separate branch and does not filter freshly inferred
types to implement checking. Matching uses total LP unification.

Names for each declaration activation, row field and variable occurrence are
provided explicitly. They are shared within an activation and separate from
other occurrences under the allocation admission proved by the caller.
Depth is an operational approximation: `none` means unfinished computation,
whereas `some []` means normal answerless completion. It is never treated as
language failure or as permission to enter fallback.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.UnificationRenaming
open Mettapedia.Logic.LP.IndependentOutputUnification
open IntrinsicTypeFacts (Scalar signature TypeTerm Declaration named primitiveType undefinedType)

abbrev Path := List Nat
abbrev Supply := Path → Nat → Nat
abbrev Result := Option (List TypeTerm)
abbrev Query := Path → TypeTerm → Option TypeTerm → Result

/-- Ordered branching propagates incompleteness rather than mistaking it for
an empty successful list. Duplicate alternatives remain distinct. -/
def collect {α β : Type} (items : List α) (visit : α → Option (List β)) :
    Option (List β) :=
  match items with
  | [] => some []
  | item :: rest => do
      let first ← visit item
      let later ← collect rest visit
      pure (first ++ later)

theorem collect_member {α β : Type} (items : List α)
    (visit : α → Option (List β)) (answers : List β)
    (returned : collect items visit = some answers) {answer : β}
    (present : answer ∈ answers) :
    ∃ item ∈ items, ∃ branch, visit item = some branch ∧ answer ∈ branch := by
  induction items generalizing answers with
  | nil => simp [collect] at returned; subst answers; simp at present
  | cons item rest ih =>
      simp only [collect] at returned
      cases first : visit item with
      | none => simp [first] at returned
      | some branch =>
          cases later : collect rest visit with
          | none => simp [first, later] at returned
          | some branches =>
              simp only [first, later, bind, Option.bind, Option.pure_def,
                Option.some.injEq] at returned
              subst answers
              rcases List.mem_append.mp present with here | there
              · exact ⟨item, List.mem_cons_self, branch, first, here⟩
              · obtain ⟨other, member, values, got, occurs⟩ := ih branches later there
                exact ⟨other, List.mem_cons_of_mem _ member, values, got, occurs⟩

def row (items : List TypeTerm) : TypeTerm :=
  .app items.length (fun i => items[i])

def elements : TypeTerm → Option (List TypeTerm)
  | .app _ children => some (List.ofFn children)
  | _ => none

def literal : TypeTerm → Option TypeTerm
  | .const value => primitiveType value
  | _ => none

def isVariable : TypeTerm → Bool
  | .var _ => true
  | _ => false

/-- Source declaration order, with a whole-scheme activation per occurrence. -/
def declarations (library : List Declaration) (supply : Supply)
    (path : Path) (subject : TypeTerm) : List TypeTerm :=
  match subject with
  | .const (.symbol name) => library.flatMap fun declaration =>
      if declaration.subject = .symbol name then
        [rename (supply (1 :: declaration.occurrence :: path)) declaration.scheme]
      else []
  | _ => []

def isArrow : TypeTerm → Bool
  | .const (.symbol name) => name == "->"
  | _ => false

def parts (arity : Nat) : List TypeTerm → Option (List TypeTerm × TypeTerm)
  | [] => none
  | head :: fields =>
      if isArrow head then
        match fields.reverse with
        | result :: reverseDomains =>
            if reverseDomains.length = arity then some (reverseDomains.reverse, result) else none
        | [] => none
      else none

/-- Recognize a proper arrow scheme at exactly this arity. -/
def callParts (arity : Nat) (scheme : TypeTerm) : Option (List TypeTerm × TypeTerm) :=
  (elements scheme).bind (parts arity)

/-- Publish the actual refined requirement of each successful match. -/
def matched (required : TypeTerm) (candidates : List TypeTerm) : List TypeTerm :=
  candidates.flatMap fun candidate =>
    (unifyTotal [(candidate, required)]).toList.map fun theta => theta.applyTerm required

def select (required : Option TypeTerm) (candidates : List TypeTerm) : List TypeTerm :=
  match required with
  | none => candidates
  | some target => matched target candidates

def finish (required : Option TypeTerm) (candidates : List TypeTerm) : List TypeTerm :=
  if candidates.isEmpty then
    match required with
    | none => [undefinedType]
    | some term => matched term [undefinedType]
  else candidates

/-- Argument/row traversal threads the actual refinements through all later
subjects and requirements. Variable subjects commit without a requirement
refinement; every other subject enters the recursive bound query. -/
def arguments (query : Query) (path : Path) (position : Nat) :
    List (TypeTerm × TypeTerm) → TypeTerm → Subst signature → Result
  | [], result, store => some [store.applyTerm result]
  | (subject, formal) :: rest, result, store =>
      if isVariable (store.applyTerm subject) then
        arguments query path (position + 1) rest result store
      else do
        let candidates ← query (0 :: position :: path)
          (store.applyTerm subject) (some (store.applyTerm formal))
        collect candidates fun candidate =>
          match unifyTotal [(candidate, store.applyTerm formal)] with
          | none => some []
          | some refinement => arguments query path (position + 1) rest result
              (refinement ∘ₛ store)

/-- Function alternatives use the source declaration order. In bound mode
the codomain match precedes every argument query. -/
def functions (library : List Declaration) (supply : Supply) (query : Query)
    (path : Path) (items : List TypeTerm) (required : Option TypeTerm) : Result :=
  match items with
  | [] => some []
  | head :: actuals =>
      collect (declarations library supply path head) fun scheme =>
        match callParts actuals.length scheme with
        | none => some []
        | some (domains, result) =>
            match required with
            | none => arguments query path 0 (actuals.zip domains) result (Subst.id signature)
            | some target =>
                match unifyTotal [(result, target)] with
                | none => some []
                | some initial => arguments query path 0 (actuals.zip domains) result initial

/-- Fresh structural inference enumerates the ordered Cartesian product;
the last child's answer varies fastest. -/
def freshRows (query : Query) (path : Path) (position : Nat) :
    List TypeTerm → Option (List (List TypeTerm))
  | [] => some [[]]
  | subject :: rest => do
      let first ← query (0 :: position :: path) subject none
      let later ← freshRows query path (position + 1) rest
      pure (first.flatMap fun answer => later.map (answer :: ·))

def structural (supply : Supply) (query : Query) (path : Path)
    (items : List TypeTerm) (required : Option TypeTerm) : Result :=
  match required with
  | none => (freshRows query (4 :: path) 0 items).map (List.map row)
  | some target =>
      let fields := (List.range items.length).map fun index =>
        (Term.var (supply (3 :: path) index) : TypeTerm)
      let result := row fields
      match unifyTotal [(result, target)] with
      | none => some []
      | some initial => arguments query (4 :: path) 0 (items.zip fields) result initial

def allowsRow : Option TypeTerm → Bool
  | some (.const _) => false
  | _ => true

def expression (library : List Declaration) (supply : Supply) (query : Query)
    (path : Path) (items : List TypeTerm) (required : Option TypeTerm) : Result := do
  let functionAnswers ← functions library supply query path items required
  let allFunctions ← (match required with
    | none => some functionAnswers
    | some _ => if allowsRow required && functionAnswers.isEmpty then
        functions library supply query path items none else some functionAnswers)
  let rowAnswers ← (if allowsRow required && allFunctions.isEmpty then
      structural supply query path items required else some [])
  pure (finish required (functionAnswers ++ rowAnswers))

/-- One layer of the source intrinsic query. Function trials precede rows;
rows require absence of any function answer, not merely absence of a
function answer matching the incoming requirement. Expression declarations
are absent under this module's symbol-subject admission. -/
def step (library : List Declaration) (supply : Supply) (query : Query)
    (path : Path) (subject : TypeTerm) (required : Option TypeTerm) : Result :=
  if isVariable subject then
    some [required.getD (.var (supply (5 :: path) 0))]
  else
    match literal subject with
    | some primitive =>
        let primitiveAnswers := select required [primitive]
        if !primitiveAnswers.isEmpty then some primitiveAnswers
        else some (finish required [])
    | none =>
        match elements subject with
        | none =>
            let declared := declarations library supply path subject
            let declaredAnswers := select required declared
            some (finish required declaredAnswers)
        | some items => expression library supply query path items required

def run (library : List Declaration) (supply : Supply) : Nat → Query
  | 0 => fun _ _ _ => none
  | fuel + 1 => step library supply (run library supply fuel)

namespace Completion

/-- A larger approximation preserves every completed answer vector. In
particular, normal answerless exhaustion is a completed vector, whereas
`none` carries no assertion about exhaustion. -/
def Extends {α : Type} (before after : Option α) : Prop :=
  ∀ answer, before = some answer → after = some answer

theorem extends_refl {α : Type} (result : Option α) : Extends result result :=
  fun _ returned => returned

theorem extends_trans {α : Type} {first second third : Option α}
    (left : Extends first second) (right : Extends second third) :
    Extends first third := fun answer returned => right answer (left answer returned)

private theorem bind_extends {α β : Type} {before after : Option α}
    {left right : α → Option β} (input : Extends before after)
    (body : ∀ item, Extends (left item) (right item)) :
    Extends (before.bind left) (after.bind right) := by
  intro answer returned
  cases original : before with
  | none => simp [original] at returned
  | some item =>
      rw [input item original]
      exact body item answer (by simpa [original] using returned)

private theorem map_extends {α β : Type} {before after : Option α}
    (same : Extends before after) (f : α → β) :
    Extends (before.map f) (after.map f) := by
  intro answer returned
  cases original : before with
  | none => simp [original] at returned
  | some item => simpa [original, same item original] using returned

theorem collect_extends {α β : Type} (items : List α)
    (left right : α → Option (List β))
    (same : ∀ item, Extends (left item) (right item)) :
    Extends (collect items left) (collect items right) := by
  induction items with
  | nil => exact extends_refl _
  | cons item rest ih =>
      apply bind_extends (same item)
      intro first
      apply bind_extends ih
      intro later
      exact extends_refl _

def QueryExtends (left right : Query) : Prop :=
  ∀ path subject required, Extends (left path subject required) (right path subject required)

theorem arguments_extends (left right : Query) (same : QueryExtends left right)
    (path : Path) (position : Nat) (pending : List (TypeTerm × TypeTerm))
    (result : TypeTerm) (store : Subst signature) :
    Extends (arguments left path position pending result store)
      (arguments right path position pending result store) := by
  induction pending generalizing position store with
  | nil => exact extends_refl _
  | cons pair rest ih =>
      rcases pair with ⟨subject, formal⟩
      simp only [arguments]
      split
      · exact ih (position + 1) store
      · apply bind_extends (same _ _ _)
        intro candidates
        apply collect_extends
        intro candidate
        cases unifyTotal [(candidate, store.applyTerm formal)] with
        | none => exact extends_refl _
        | some refinement => exact ih (position + 1) (refinement ∘ₛ store)

theorem functions_extends (library : List Declaration) (supply : Supply)
    (left right : Query) (same : QueryExtends left right)
    (path : Path) (items : List TypeTerm) (required : Option TypeTerm) :
    Extends (functions library supply left path items required)
      (functions library supply right path items required) := by
  cases items with
  | nil => exact extends_refl _
  | cons head actuals =>
      apply collect_extends
      intro scheme
      cases callParts actuals.length scheme with
      | none => exact extends_refl _
      | some pair =>
          rcases pair with ⟨domains, result⟩
          cases required with
          | none => exact arguments_extends left right same path 0 _ result _
          | some target =>
              dsimp only
              cases unifyTotal [(result, target)] with
              | none => exact extends_refl _
              | some initial => exact arguments_extends left right same path 0 _ result initial

theorem freshRows_extends (left right : Query) (same : QueryExtends left right)
    (path : Path) (position : Nat) (items : List TypeTerm) :
    Extends (freshRows left path position items) (freshRows right path position items) := by
  induction items generalizing position with
  | nil => exact extends_refl _
  | cons item rest ih =>
      apply bind_extends (same _ _ _)
      intro first
      apply bind_extends (ih (position + 1))
      intro later
      exact extends_refl _

theorem structural_extends (supply : Supply) (left right : Query)
    (same : QueryExtends left right) (path : Path)
    (items : List TypeTerm) (required : Option TypeTerm) :
    Extends (structural supply left path items required)
      (structural supply right path items required) := by
  cases required with
  | none => exact map_extends (freshRows_extends left right same _ _ _) _
  | some target =>
      simp only [structural]
      split
      · exact extends_refl _
      · exact arguments_extends left right same _ _ _ _ _

theorem expression_extends (library : List Declaration) (supply : Supply)
    (left right : Query) (same : QueryExtends left right)
    (path : Path) (items : List TypeTerm) (required : Option TypeTerm) :
    Extends (expression library supply left path items required)
      (expression library supply right path items required) := by
  apply bind_extends (functions_extends library supply left right same _ _ _)
  intro functionAnswers
  apply bind_extends
  · cases required with
    | none => exact extends_refl _
    | some target =>
        dsimp only
        split
        · exact functions_extends library supply left right same _ _ _
        · exact extends_refl _
  · intro allFunctions
    apply bind_extends
    · split
      · exact structural_extends supply left right same _ _ _
      · exact extends_refl _
    · intro rowAnswers
      exact extends_refl _

theorem step_extends (library : List Declaration) (supply : Supply)
    (left right : Query) (same : QueryExtends left right) :
    QueryExtends (step library supply left) (step library supply right) := by
  intro path subject required
  simp only [step]
  split
  · exact extends_refl _
  · split
    · exact extends_refl _
    · split
      · exact extends_refl _
      · exact expression_extends library supply left right same _ _ _

/-- Increasing fuel never changes any completed observation, including its
answer order, duplicate multiplicity or normal empty result. -/
theorem run_succ_extends (library : List Declaration) (supply : Supply) (fuel : Nat) :
    QueryExtends (run library supply fuel) (run library supply (fuel + 1)) := by
  induction fuel with
  | zero => intro path subject required answer returned; simp [run] at returned
  | succ fuel ih => exact step_extends library supply _ _ ih

theorem run_add_extends (library : List Declaration) (supply : Supply)
    (fuel extra : Nat) :
    QueryExtends (run library supply fuel) (run library supply (fuel + extra)) := by
  induction extra with
  | zero => intro path subject required; exact extends_refl _
  | succ extra ih =>
      intro path subject required
      exact extends_trans (ih path subject required)
        (run_succ_extends library supply (fuel + extra) path subject required)

theorem completed_answers_unique (library : List Declaration) (supply : Supply)
    (firstFuel secondFuel : Nat) (path : Path) (subject : TypeTerm)
    (required : Option TypeTerm) (first second : List TypeTerm)
    (firstRun : run library supply firstFuel path subject required = some first)
    (secondRun : run library supply secondFuel path subject required = some second) :
    first = second := by
  have left := run_add_extends library supply firstFuel secondFuel
    path subject required first firstRun
  have right := run_add_extends library supply secondFuel firstFuel
    path subject required second secondRun
  rw [Nat.add_comm secondFuel firstFuel, left] at right
  exact Option.some.inj right

end Completion

namespace Coordinates

abbrev R (names : Nat ≃ Nat) := rename (σ := signature) names
abbrev S (names : Nat ≃ Nat) (supply : Supply) : Supply :=
  fun path slot => names (supply path slot)
abbrev T (names : Nat ≃ Nat) :=
  Mettapedia.Logic.LP.IndependentOutputUnification.Coordinates.transport (σ := signature) names

def QueryAgrees (names : Nat ≃ Nat) (query renamed : Query) : Prop :=
  ∀ path subject required,
    renamed path (R names subject) (required.map (R names)) =
      (query path subject required).map (List.map (R names))

theorem collect_inputs {α β γ : Type} (items : List α) (names : α → β)
    (visit : β → Option (List γ)) :
    collect (items.map names) visit = collect items (fun item => visit (names item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.map_cons, collect, ih]

theorem collect_results {α β γ : Type} (items : List α) (names : β → γ)
    (visit : α → Option (List β)) :
    collect items (fun item => (visit item).map (List.map names)) =
      (collect items visit).map (List.map names) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [collect, ih]
      cases visit item <;> cases collect rest visit <;> simp [List.map_append]

theorem row_rename (names : Nat ≃ Nat) (items : List TypeTerm) :
    R names (row items) = row (items.map (R names)) := by
  simp only [R, row, rename, Subst.applyTerm, Term.app.injEq, List.length_map, true_and]
  apply (Fin.heq_fun_iff (List.length_map (R names)).symm).mpr
  intro index
  simp [rename]

theorem elements_rename (names : Nat ≃ Nat) (term : TypeTerm) :
    elements (R names term) = (elements term).map (List.map (R names)) := by
  cases term <;> simp [elements, R, List.map_ofFn, Function.comp_def]

theorem isVariable_rename (names : Nat ≃ Nat) (term : TypeTerm) :
    isVariable (R names term) = isVariable term := by
  cases term <;> rfl

theorem literal_rename (names : Nat ≃ Nat) (term : TypeTerm) :
    literal (R names term) = (literal term).map (R names) := by
  cases term with
  | var _ => rfl
  | app _ _ => rfl
  | const scalar => cases scalar <;> rfl

theorem isArrow_rename (names : Nat ≃ Nat) (term : TypeTerm) :
    isArrow (R names term) = isArrow term := by
  cases term with
  | var _ => rfl
  | app _ _ => rfl
  | const scalar => cases scalar <;> rfl

theorem parts_rename (names : Nat ≃ Nat) (arity : Nat) (items : List TypeTerm) :
    parts arity (items.map (R names)) =
      (parts arity items).map (fun pair => (pair.1.map (R names), R names pair.2)) := by
  cases items with
  | nil => rfl
  | cons head fields =>
      simp only [List.map_cons, parts, isArrow_rename]
      by_cases arrow : isArrow head = true
      · simp only [arrow, ↓reduceIte, ← List.map_reverse]
        cases fields.reverse with
        | nil => rfl
        | cons result reverseDomains =>
            simp only [List.map_cons, List.length_map]
            split <;> simp only [Option.map_some, Option.map_none, ← List.map_reverse]
      · simp only [arrow, Bool.false_eq_true, ↓reduceIte, Option.map_none]

theorem callParts_rename (names : Nat ≃ Nat) (arity : Nat) (term : TypeTerm) :
    callParts arity (R names term) =
      (callParts arity term).map (fun pair => (pair.1.map (R names), R names pair.2)) := by
  simp only [callParts, elements_rename]
  cases elements term with
  | none => rfl
  | some fields => exact parts_rename names arity fields

theorem declarations_rename (names : Nat ≃ Nat) (library : List Declaration)
    (supply : Supply) (path : Path) (subject : TypeTerm) :
    declarations library (S names supply) path (R names subject) =
      (declarations library supply path subject).map (R names) := by
  cases subject with
  | var _ => rfl
  | app _ _ => rfl
  | const scalar =>
      cases scalar with
      | number _ => rfl
      | string _ => rfl
      | boolean _ => rfl
      | symbol name =>
          simp only [R, rename_const, declarations, List.map_flatMap]
          apply List.flatMap_congr
          intro declaration _
          split <;> simp only [List.map_cons, List.map_nil, rename_comp]
          rfl

theorem transported_apply (names : Nat ≃ Nat) (store : Subst signature) (term : TypeTerm) :
    (T names store).applyTerm (R names term) = R names (store.applyTerm term) :=
  push_apply (σ := signature) names names.symm names.symm_apply_apply store term

theorem matching_rename (names : Nat ≃ Nat) (left right : TypeTerm) :
    unifyTotal [(R names left, R names right)] =
      (unifyTotal [(left, right)]).map (T names) :=
  Mettapedia.Logic.LP.IndependentOutputUnification.Coordinates.total_equivariant (σ := signature) names [(left, right)]

theorem matched_rename (names : Nat ≃ Nat) (required : TypeTerm)
    (candidates : List TypeTerm) :
    matched (R names required) (candidates.map (R names)) =
      (matched required candidates).map (R names) := by
  simp only [matched, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro candidate _
  simp only [matching_rename]
  cases unifyTotal [(candidate, required)] <;>
    simp only [Option.map_none, Option.map_some, Option.toList_none,
      Option.toList_some, List.map_nil, List.map_cons, transported_apply]

theorem finish_rename (names : Nat ≃ Nat) (required : Option TypeTerm)
    (candidates : List TypeTerm) :
    finish (required.map (R names)) (candidates.map (R names)) =
      (finish required candidates).map (R names) := by
  simp only [finish, List.isEmpty_map]
  by_cases empty : candidates.isEmpty = true
  · simp only [empty, ↓reduceIte]
    cases required with
    | none => rfl
    | some term =>
        simpa only [Option.map_some, R, undefinedType, named, rename_const,
          List.map_cons, List.map_nil] using matched_rename names term [undefinedType]
  · simp only [empty, Bool.false_eq_true, ↓reduceIte]

theorem collect_congr {α β : Type} (items : List α)
    (first second : α → Option (List β))
    (same : ∀ item ∈ items, first item = second item) :
    collect items first = collect items second := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [collect, same item List.mem_cons_self,
        ih (fun other member => same other (List.mem_cons_of_mem _ member))]

theorem arguments_rename (names : Nat ≃ Nat) (query renamed : Query)
    (agrees : QueryAgrees names query renamed) (path : Path) (position : Nat)
    (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm) (store : Subst signature) :
    arguments renamed path position
        (pending.map (fun pair => (R names pair.1, R names pair.2)))
        (R names result) (T names store) =
      (arguments query path position pending result store).map (List.map (R names)) := by
  induction pending generalizing position store with
  | nil => simp only [List.map_nil, arguments, transported_apply, Option.map_some,
      List.map_cons, List.map_nil]
  | cons pair rest ih =>
      rcases pair with ⟨subject, formal⟩
      simp only [List.map_cons, arguments, transported_apply, isVariable_rename]
      by_cases variableSubject : isVariable (store.applyTerm subject) = true
      · simp only [variableSubject, ↓reduceIte]
        exact ih (position + 1) store
      · simp only [variableSubject, Bool.false_eq_true, ↓reduceIte]
        have child := agrees (0 :: position :: path) (store.applyTerm subject)
          (some (store.applyTerm formal))
        simp only [Option.map_some] at child
        rw [child]
        cases answered : query (0 :: position :: path) (store.applyTerm subject)
            (some (store.applyTerm formal)) with
        | none => rfl
        | some candidates =>
            dsimp only [Option.map_some, bind, Option.bind]
            rw [collect_inputs]
            rw [← collect_results]
            apply collect_congr
            intro candidate _
            rw [matching_rename]
            cases accepted : unifyTotal [(candidate, store.applyTerm formal)] with
            | none => rfl
            | some refinement =>
                simp only [Option.map_some]
                rw [← Mettapedia.Logic.LP.IndependentOutputUnification.Coordinates.transport_comp]
                exact ih (position + 1) (refinement ∘ₛ store)

theorem zip_rename (names : Nat ≃ Nat) (left right : List TypeTerm) :
    (left.map (R names)).zip (right.map (R names)) =
      (left.zip right).map (fun pair => (R names pair.1, R names pair.2)) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons first rest ih =>
      cases right with
      | nil => rfl
      | cons second later => simp only [List.map_cons, List.zip_cons_cons, ih]

theorem functions_rename (names : Nat ≃ Nat) (library : List Declaration)
    (supply : Supply) (query renamed : Query) (agrees : QueryAgrees names query renamed)
    (path : Path) (items : List TypeTerm) (required : Option TypeTerm) :
    functions library (S names supply) renamed path (items.map (R names))
        (required.map (R names)) =
      (functions library supply query path items required).map (List.map (R names)) := by
  cases items with
  | nil => rfl
  | cons head actuals =>
      simp only [List.map_cons, functions, declarations_rename, collect_inputs,
        List.length_map]
      rw [← collect_results]
      apply collect_congr
      intro scheme _
      rw [callParts_rename]
      cases partsResult : callParts actuals.length scheme with
      | none => rfl
      | some pair =>
          rcases pair with ⟨domains, result⟩
          simp only [Option.map_some, zip_rename]
          cases required with
          | none =>
              have child := arguments_rename names query renamed agrees path 0
                (actuals.zip domains) result (Subst.id signature)
              simpa only [Option.map_none, Mettapedia.Logic.LP.IndependentOutputUnification.Coordinates.transport_id]
                using child
          | some target =>
              simp only [Option.map_some, matching_rename]
              cases unifyTotal [(result, target)] with
              | none => rfl
              | some initial =>
                  simpa only [Option.map_some] using
                    arguments_rename names query renamed agrees path 0
                      (actuals.zip domains) result initial

theorem freshRows_rename (names : Nat ≃ Nat) (query renamed : Query)
    (agrees : QueryAgrees names query renamed) (path : Path) (position : Nat)
    (items : List TypeTerm) :
    freshRows renamed path position (items.map (R names)) =
      (freshRows query path position items).map (List.map (List.map (R names))) := by
  induction items generalizing position with
  | nil => rfl
  | cons subject rest ih =>
      simp only [List.map_cons, freshRows]
      have child := agrees (0 :: position :: path) subject none
      simp only [Option.map_none] at child
      rw [child, ih]
      cases query (0 :: position :: path) subject none <;>
        cases freshRows query path (position + 1) rest <;>
          simp [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

theorem structural_rename (names : Nat ≃ Nat) (supply : Supply)
    (query renamed : Query) (agrees : QueryAgrees names query renamed)
    (path : Path) (items : List TypeTerm) (required : Option TypeTerm) :
    structural (S names supply) renamed path (items.map (R names))
        (required.map (R names)) =
      (structural supply query path items required).map (List.map (R names)) := by
  cases required with
  | none =>
      simp only [Option.map_none, structural, freshRows_rename names query renamed agrees]
      cases freshRows query (4 :: path) 0 items with
      | none => rfl
      | some rows =>
          simp only [Option.map_some, List.map_map]
          congr 1
          apply List.map_congr_left
          intro fields _
          exact (row_rename names fields).symm
  | some target =>
      let fields : List TypeTerm := (List.range items.length).map fun index =>
        .var (supply (3 :: path) index)
      have renamedFields :
          ((List.range (items.map (R names)).length).map fun index =>
            (Term.var (S names supply (3 :: path) index) : TypeTerm)) =
          fields.map (R names) := by
        simp only [List.length_map, fields, List.map_map]
        rfl
      simp only [Option.map_some, structural, renamedFields, ← row_rename, matching_rename]
      change (match (unifyTotal [(row fields, target)]).map (T names) with
        | none => some []
        | some initial => arguments renamed (4 :: path) 0
            ((items.map (R names)).zip (fields.map (R names)))
            (R names (row fields)) initial) = _
      cases unifyTotal [(row fields, target)] with
      | none => rfl
      | some initial =>
          simp only [Option.map_some, zip_rename]
          exact arguments_rename names query renamed agrees (4 :: path) 0
            (items.zip fields) (row fields) initial

theorem allowsRow_rename (names : Nat ≃ Nat) (required : Option TypeTerm) :
    allowsRow (required.map (R names)) = allowsRow required := by
  cases required with
  | none => rfl
  | some term => cases term <;> rfl

theorem expression_rename (names : Nat ≃ Nat) (library : List Declaration)
    (supply : Supply) (query renamed : Query) (agrees : QueryAgrees names query renamed)
    (path : Path) (items : List TypeTerm) (required : Option TypeTerm) :
    expression library (S names supply) renamed path (items.map (R names))
        (required.map (R names)) =
      (expression library supply query path items required).map (List.map (R names)) := by
  simp only [expression, functions_rename names library supply query renamed agrees,
    allowsRow_rename]
  cases answered : functions library supply query path items required with
  | none => rfl
  | some answers =>
      dsimp only [Option.map_some, bind, Option.bind]
      simp only [List.isEmpty_map]
      cases required with
      | none =>
          simp only [Option.map_none, allowsRow, Bool.true_and]
          try dsimp only [bind, Option.bind]
          simp only [List.isEmpty_map]
          by_cases empty : answers.isEmpty = true
          · simp only [empty, ↓reduceIte]
            have structuralEq := structural_rename names supply query renamed agrees path items none
            simp only [Option.map_none] at structuralEq
            rw [structuralEq]
            cases structural supply query path items none <;>
              simp [← finish_rename names none]
          · simp only [empty, Bool.false_eq_true, ↓reduceIte]
            simp [← finish_rename names none]
      | some target =>
          simp only [Option.map_some]
          by_cases probe : (allowsRow (some target) && answers.isEmpty) = true
          · simp only [probe, ↓reduceIte]
            have all := functions_rename names library supply query renamed agrees path items none
            simp only [Option.map_none] at all
            rw [all]
            cases functions library supply query path items none with
            | none => rfl
            | some allAnswers =>
                dsimp only [Option.map_some, bind, Option.bind]
                simp only [List.isEmpty_map]
                by_cases rows : (allowsRow (some target) && allAnswers.isEmpty) = true
                · simp only [rows, ↓reduceIte]
                  have structuralEq := structural_rename names supply query renamed agrees path items (some target)
                  simp only [Option.map_some] at structuralEq
                  rw [structuralEq]
                  cases structural supply query path items (some target) <;>
                    simp [← finish_rename names (some target)]
                · simp only [rows, Bool.false_eq_true, ↓reduceIte]
                  simp [← finish_rename names (some target)]
          · simp only [probe, Bool.false_eq_true, ↓reduceIte]
            try dsimp only [bind, Option.bind]
            simp only [List.isEmpty_map, probe, Bool.false_eq_true, ↓reduceIte]
            simp [← finish_rename names (some target)]

theorem select_rename (names : Nat ≃ Nat) (required : Option TypeTerm)
    (candidates : List TypeTerm) :
    select (required.map (R names)) (candidates.map (R names)) =
      (select required candidates).map (R names) := by
  cases required with
  | none => rfl
  | some target => exact matched_rename names target candidates

theorem step_rename (names : Nat ≃ Nat) (library : List Declaration)
    (supply : Supply) (query renamed : Query) (agrees : QueryAgrees names query renamed)
    (path : Path) (subject : TypeTerm) (required : Option TypeTerm) :
    step library (S names supply) renamed path (R names subject) (required.map (R names)) =
      (step library supply query path subject required).map (List.map (R names)) := by
  simp only [step, isVariable_rename, literal_rename]
  by_cases variableSubject : isVariable subject = true
  · simp only [variableSubject, ↓reduceIte]
    cases required <;> rfl
  · simp only [variableSubject, Bool.false_eq_true, ↓reduceIte]
    cases primitive : literal subject with
    | some intrinsic =>
        simp only [Option.map_some]
        have selected := select_rename names required [intrinsic]
        simp only [List.map_cons, List.map_nil] at selected
        rw [selected]
        simp only [List.isEmpty_map]
        by_cases empty : (!(select required [intrinsic]).isEmpty) = true
        · simp only [empty, ↓reduceIte, Option.map_some]
        · simp only [empty, Bool.false_eq_true, ↓reduceIte, Option.map_some]
          exact congrArg some (finish_rename names required [])
    | none =>
        simp only [Option.map_none, elements_rename]
        cases shape : elements subject with
        | none =>
            simp only [Option.map_none, declarations_rename, select_rename, Option.map_some]
            exact congrArg some (finish_rename names required _)
        | some items => exact expression_rename names library supply query renamed agrees path items required

/-- The full ordered recursive query respects lossless variable coordinates.
This includes primitive commitment, negative function probes, structural
products, every signature alternative and shared polymorphic fields. -/
theorem run_equivariant (names : Nat ≃ Nat) (library : List Declaration)
    (supply : Supply) (fuel : Nat) :
    QueryAgrees names (run library supply fuel) (run library (S names supply) fuel) := by
  induction fuel with
  | zero => intro path subject required; rfl
  | succ fuel ih =>
      intro path subject required
      exact step_rename names library supply (run library supply fuel)
        (run library (S names supply) fuel) ih path subject required

end Coordinates

namespace Resolution

/-- A separate presentation applies each accepted refinement immediately to
all pending fields. It has the same child calls as the store-based loop. -/
def argumentsResolved (query : Query) (path : Path) (position : Nat) :
    List (TypeTerm × TypeTerm) → TypeTerm → Result
  | [], result => some [result]
  | (subject, formal) :: rest, result =>
      if isVariable subject then
        argumentsResolved query path (position + 1) rest result
      else do
        let candidates ← query (0 :: position :: path) subject (some formal)
        collect candidates fun candidate =>
          match unifyTotal [(candidate, formal)] with
          | none => some []
          | some refinement => argumentsResolved query path (position + 1)
              (rest.map fun pair =>
                (refinement.applyTerm pair.1, refinement.applyTerm pair.2))
              (refinement.applyTerm result)
termination_by pending => pending.length
decreasing_by all_goals simp_wf

theorem arguments_eq_resolved (query : Query) (path : Path) (position : Nat)
    (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm) (store : Subst signature) :
    arguments query path position pending result store =
      argumentsResolved query path position
        (pending.map fun pair => (store.applyTerm pair.1, store.applyTerm pair.2))
        (store.applyTerm result) := by
  induction pending generalizing position result store with
  | nil => simp [arguments, argumentsResolved]
  | cons pair rest ih =>
      rcases pair with ⟨subject, formal⟩
      simp only [arguments, List.map_cons, argumentsResolved]
      by_cases variableSubject : isVariable (store.applyTerm subject) = true
      · simp only [variableSubject, ↓reduceIte]
        exact ih (position + 1) result store
      · simp only [variableSubject, Bool.false_eq_true, ↓reduceIte]
        cases query (0 :: position :: path) (store.applyTerm subject)
            (some (store.applyTerm formal)) with
        | none => rfl
        | some candidates =>
            dsimp only [bind, Option.bind]
            apply Coordinates.collect_congr
            intro candidate _
            cases unifyTotal [(candidate, store.applyTerm formal)] with
            | none => rfl
            | some refinement =>
                dsimp only
                rw [ih]
                simp only [List.map_map, Function.comp_def, Subst.applyTerm_comp]

theorem arguments_id (query : Query) (path : Path) (position : Nat)
    (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm) :
    arguments query path position pending result (Subst.id signature) =
      argumentsResolved query path position pending result := by
  rw [arguments_eq_resolved]
  simp only [Subst.applyTerm_id, List.map_id']

theorem argumentsResolved_rename (names : Nat ≃ Nat) (query renamed : Query)
    (agrees : Coordinates.QueryAgrees names query renamed)
    (path : Path) (position : Nat) (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm) :
    argumentsResolved renamed path position
        (pending.map fun pair => (Coordinates.R names pair.1, Coordinates.R names pair.2))
        (Coordinates.R names result) =
      (argumentsResolved query path position pending result).map
        (List.map (Coordinates.R names)) := by
  have comparison := Coordinates.arguments_rename names query renamed agrees
    path position pending result (Subst.id signature)
  simpa only [Mettapedia.Logic.LP.IndependentOutputUnification.Coordinates.transport_id,
    arguments_id] using comparison

/-- A variable codomain's initial alias is an invertible coordinate change
on the actual pending fields when the caller output is absent there. The
child service's coordinate law is discharged by `Coordinates.run_equivariant`
for the recursive service, with allocation locality selecting unchanged
child scopes. -/
theorem private_alias_arguments (privateName output : Nat) (query renamed : Query)
    (agrees : Coordinates.QueryAgrees (Equiv.swap privateName output) query renamed)
    (path : Path) (position : Nat) (pending : List (TypeTerm × TypeTerm))
    (result : TypeTerm)
    (independent : ∀ pair ∈ pending, output ∉ pair.1.freeVars ∧ output ∉ pair.2.freeVars)
    (resultIndependent : output ∉ result.freeVars) :
    arguments renamed path position pending result (Subst.single privateName (.var output)) =
      (arguments query path position pending result (Subst.id signature)).map
        (List.map (Coordinates.R (Equiv.swap privateName output))) := by
  rw [arguments_eq_resolved, arguments_id]
  have pendingChange :
      pending.map (fun pair =>
        ((Subst.single (σ := signature) privateName (.var output)).applyTerm pair.1,
         (Subst.single (σ := signature) privateName (.var output)).applyTerm pair.2)) =
      pending.map (fun pair =>
        (Coordinates.R (Equiv.swap privateName output) pair.1,
         Coordinates.R (Equiv.swap privateName output) pair.2)) := by
    apply List.map_congr_left
    intro pair member
    rw [private_alias_is_swap privateName output pair.1 (independent pair member).1,
      private_alias_is_swap privateName output pair.2 (independent pair member).2]
  rw [pendingChange, private_alias_is_swap privateName output result resultIndependent]
  exact argumentsResolved_rename (Equiv.swap privateName output) query renamed agrees
    path position pending result

end Resolution

/-- A concrete disjoint namespace for the model's generated variables. -/
def freshSupply (path : Path) (slot : Nat) : Nat :=
  Nat.pair 1 (Nat.pair (Encodable.encode path) slot)

def callerName (slot : Nat) : Nat := Nat.pair 0 slot

theorem fresh_supply_injective (first second : Path) (left right : Nat) :
    freshSupply first left = freshSupply second right ↔ first = second ∧ left = right := by
  simp only [freshSupply, Nat.pair_eq_pair, true_and]
  exact and_congr Encodable.encode_inj Iff.rfl

theorem fresh_supply_separate (path : Path) (slot caller : Nat) :
    freshSupply path slot ≠ callerName caller := by
  simp [freshSupply, callerName, Nat.pair_eq_pair]

namespace Controls

def number : TypeTerm := named "Number"
def function : TypeTerm := named "f"
def untypedVariable : TypeTerm := .var (callerName 0)
def monoDeclaration : Declaration :=
  ⟨0, .symbol "f", row [named "->", number, number]⟩
def openApplication : TypeTerm := row [function, untypedVariable]

theorem fresh_open_function :
    run [monoDeclaration] freshSupply 3 [] openApplication none = some [number] := by
  simp [run, step, expression, functions, arguments, structural, freshRows,
    collect, declarations, callParts, parts, isArrow, elements, literal,
    isVariable, select, finish, allowsRow, monoDeclaration,
    openApplication, function, untypedVariable, number, row, named,
    rename, Subst.applyTerm, Subst.id, callerName, freshSupply, primitiveType]

theorem independent_output_open_function :
    run [monoDeclaration] freshSupply 3 [] openApplication
      (some (.var (callerName 1))) = some [number] := by
  simp [run, step, expression, functions, arguments, structural,
    collect, declarations, callParts, parts, isArrow, elements, literal,
    isVariable, finish, allowsRow, matched, monoDeclaration,
    openApplication, function, untypedVariable, number, row, named,
    rename, Subst.applyTerm, Subst.id, callerName, freshSupply,
    unifyTotal, Subst.applyEqs, Subst.single, Subst.comp, Term.occursIn]

theorem shared_output_changes_the_query :
    run [monoDeclaration] freshSupply 3 [] openApplication
      (some (.var (callerName 0))) = some [undefinedType] := by
  simp [run, step, expression, functions, arguments, structural,
    collect, declarations, callParts, parts, isArrow, elements, literal,
    isVariable, select, finish, allowsRow, matched, monoDeclaration,
    openApplication, function, untypedVariable, number, row, named, undefinedType,
    rename, Subst.applyTerm, Subst.id, callerName, freshSupply, primitiveType,
    unifyTotal, Subst.applyEqs, Subst.single, Subst.comp, Term.occursIn]

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput
