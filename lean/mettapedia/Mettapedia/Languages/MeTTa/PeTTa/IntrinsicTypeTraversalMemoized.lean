import Mettapedia.Languages.MeTTa.PeTTa.IntrinsicTypeTraversal
import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutputNativeAdmission

/-!
# Memoized intrinsic traversal and retained-frontier work

A closed subject has a complete ordered intrinsic service. Its canonical
answer scheme rebases to each invocation without adding that invocation's
path to the fact key. The explicit query script below erases to the existing
intrinsic evaluator, preserving ordered function trials, negative probes,
refinement branches and structural products.

Retained-boundary traversal is proved equal to that source evaluator.
A separate ideal traversal determines the finite residual frontier before
consulting any bounded cache. Covering those concrete boundaries gives a
warm work bound: residual operations, lookup and activation, and materialized
answer nodes. Eviction and refusal remain cold paths; capacity alone cannot
establish a hit. Local operation and activation weights remain operand-
dependent, including the cost of variable inventories and unification.

The finite evaluator uses conservative completion fuel, not a native runtime
fuel check. Root-variable requirements enter through the separately proved
independent-output normalization. Native pointer identity, revision/owner
stamps, payload eligibility and actual residency must instantiate this
interface; equal term syntax does not establish a native cache hit. Native
allocation failure and cold store/replacement remain implementation
correspondence obligations beyond these laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Memoized

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.UnificationRenaming
open IntrinsicTypeFacts (signature TypeTerm Declaration)

private theorem apply_ground (store : Subst signature) (term : TypeTerm)
    (closed : term.isGround) : store.applyTerm term = term := by
  apply Subst.applyTerm_eq_self
  intro name present
  have empty : term.freeVars = ∅ := (Term.isGround_iff_freeVars_empty term).mp closed
  rw [empty] at present
  exact False.elim (Finset.notMem_empty name present)

private theorem collect_complete {α β : Type} (items : List α)
    (visit : α → Option (List β))
    (complete : ∀ item ∈ items, (visit item).isSome) :
    (collect items visit).isSome := by
  induction items with
  | nil => rfl
  | cons item later ih =>
      have first := complete item List.mem_cons_self
      have rest := ih (fun other member => complete other (List.mem_cons_of_mem _ member))
      cases here : visit item with
      | none => simp [here] at first
      | some answers =>
          cases tail : collect later visit with
          | none => simp [tail] at rest
          | some more => simp [collect, here, tail]

private theorem arguments_complete (query : Query) (path : Path) (position : Nat)
    (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm) (store : Subst signature)
    (closed : ∀ pair ∈ pending, pair.1.isGround)
    (complete : ∀ pair ∈ pending, ∀ childPath required,
      (query childPath pair.1 required).isSome) :
    (arguments query path position pending result store).isSome := by
  induction pending generalizing position store with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨subject, formal⟩
      have fixed := apply_ground store subject (closed _ List.mem_cons_self)
      simp only [arguments, fixed]
      split
      · exact ih (position + 1) store
          (fun pair member => closed pair (List.mem_cons_of_mem _ member))
          (fun pair member => complete pair (List.mem_cons_of_mem _ member))
      · have available := complete (subject, formal) List.mem_cons_self
          (0 :: position :: path) (some (store.applyTerm formal))
        cases got : query (0 :: position :: path) subject (some (store.applyTerm formal)) with
        | none => simp [got] at available
        | some candidates =>
            apply collect_complete
            intro candidate _
            cases unifyTotal [(candidate, store.applyTerm formal)] with
            | none => rfl
            | some refinement =>
                exact ih (position + 1) (refinement ∘ₛ store)
                  (fun pair member => closed pair (List.mem_cons_of_mem _ member))
                  (fun pair member => complete pair (List.mem_cons_of_mem _ member))

private theorem functions_complete (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (items : List TypeTerm) (required : Option TypeTerm)
    (closed : ∀ item ∈ items, item.isGround)
    (complete : ∀ item ∈ items, ∀ childPath required, (query childPath item required).isSome) :
    (functions library supply query path items required).isSome := by
  cases items with
  | nil => rfl
  | cons head actuals =>
      unfold functions
      apply collect_complete
      intro scheme _
      cases callParts actuals.length scheme with
      | none => rfl
      | some pair =>
          rcases pair with ⟨domains, result⟩
          have done (store : Subst signature) := arguments_complete query path 0
            (actuals.zip domains) result store
            (fun pair present => closed pair.1 (List.mem_cons_of_mem _ (List.of_mem_zip present).1))
            (fun pair present => complete pair.1 (List.mem_cons_of_mem _ (List.of_mem_zip present).1))
          cases required with
          | none => exact done (Subst.id signature)
          | some target =>
              dsimp only
              cases unifyTotal [(result, target)] with
              | none => rfl
              | some initial => exact done initial

private theorem rows_complete (query : Query) (path : Path) (position : Nat)
    (items : List TypeTerm)
    (complete : ∀ item ∈ items, ∀ childPath required, (query childPath item required).isSome) :
    (freshRows query path position items).isSome := by
  induction items generalizing position with
  | nil => rfl
  | cons item rest ih =>
      have first := complete item List.mem_cons_self (0 :: position :: path) none
      have later := ih (position + 1)
        (fun other member => complete other (List.mem_cons_of_mem _ member))
      cases here : query (0 :: position :: path) item none with
      | none => simp [here] at first
      | some answers =>
          cases tail : freshRows query path (position + 1) rest with
          | none => simp [tail] at later
          | some rows => simp [freshRows, here, tail]

private theorem structural_complete (supply : Supply) (query : Query) (path : Path)
    (items : List TypeTerm) (required : Option TypeTerm)
    (closed : ∀ item ∈ items, item.isGround)
    (complete : ∀ item ∈ items, ∀ childPath required, (query childPath item required).isSome) :
    (structural supply query path items required).isSome := by
  cases required with
  | none => simpa only [structural, Option.isSome_map] using rows_complete query (4 :: path) 0 items complete
  | some target =>
      simp only [structural]
      split
      · rfl
      · apply arguments_complete
        · intro pair present
          exact closed pair.1 (List.of_mem_zip present).1
        · intro pair present
          exact complete pair.1 (List.of_mem_zip present).1

private theorem bind_complete {α β : Type} (value : Option α) (next : α → Option β)
    (complete : value.isSome) (nextComplete : ∀ item, (next item).isSome) :
    (value.bind next).isSome := by
  cases value with
  | none => cases complete
  | some item => exact nextComplete item

private theorem expression_complete (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (items : List TypeTerm) (required : Option TypeTerm)
    (closed : ∀ item ∈ items, item.isGround)
    (complete : ∀ item ∈ items, ∀ childPath required, (query childPath item required).isSome) :
    (expression library supply query path items required).isSome := by
  have bound := functions_complete library supply query path items required closed complete
  have fresh := functions_complete library supply query path items none closed complete
  have rows := structural_complete supply query path items required closed complete
  unfold expression
  apply bind_complete _ _ bound
  intro answers
  apply bind_complete
  · cases required with
    | none => rfl
    | some target => dsimp only; split
                     · exact fresh
                     · rfl
  · intro allAnswers
    apply bind_complete
    · split
      · exact rows
      · rfl
    · intro rowAnswers
      rfl

/-- A closed subject cannot be enlarged by argument refinements. Every
recursive subject is a proper subterm, so its size bounds the approximation
needed for complete ordered intrinsic evaluation, in every requirement mode. -/
theorem closed_subject_complete (library : List Declaration) (supply : Supply)
    (fuel : Nat) (path : Path) (subject : TypeTerm) (required : Option TypeTerm)
    (closed : subject.isGround) (enough : subject.size < fuel) :
    (run library supply fuel path subject required).isSome := by
  induction fuel generalizing path subject required with
  | zero => omega
  | succ fuel ih =>
      cases subject with
      | var _ => cases closed
      | const value =>
          simp only [run, step, isVariable, Bool.false_eq_true, ↓reduceIte, literal]
          cases IntrinsicTypeFacts.primitiveType value <;> simp only
          · rfl
          · split <;> rfl
      | app arity children =>
          simp only [run, step, isVariable, Bool.false_eq_true, ↓reduceIte, literal,
            elements]
          apply expression_complete library supply (run library supply fuel)
          · intro item present
            obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
            exact closed index
          · intro item present childPath target
            obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
            apply ih childPath (children index) target (closed index)
            have smaller := Term.size_subterm (ts := children) index
            omega


/-- Relocate a complete invocation subtree; allocation keys remain relative
inside a retained fact scheme, rather than entering the native cache key. -/
def shiftSupply (supply : Supply) (base : Path) : Supply :=
  fun path slot => supply (path ++ base) slot

def shiftQuery (query : Query) (base : Path) : Query :=
  fun path subject required => query (path ++ base) subject required

private theorem declarations_shift (library : List Declaration) (supply : Supply)
    (base path : Path) (subject : TypeTerm) :
    declarations library (shiftSupply supply base) path subject =
      declarations library supply (path ++ base) subject := by
  cases subject with
  | var _ => rfl
  | app _ _ => rfl
  | const value => cases value <;> rfl

private theorem arguments_shift (query : Query) (base path : Path) (position : Nat)
    (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm) (store : Subst signature) :
    arguments (shiftQuery query base) path position pending result store =
      arguments query (path ++ base) position pending result store := by
  induction pending generalizing position store with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨subject, formal⟩
      simp only [arguments]
      split
      · exact ih (position + 1) store
      · simp only [shiftQuery, List.cons_append]
        cases query (0 :: position :: (path ++ base)) (store.applyTerm subject)
            (some (store.applyTerm formal)) with
        | none => rfl
        | some answers =>
            apply Coordinates.collect_congr
            intro candidate _
            split
            · rfl
            · exact ih (position + 1) _

private theorem functions_shift (library : List Declaration) (supply : Supply)
    (query : Query) (base path : Path) (items : List TypeTerm) (required : Option TypeTerm) :
    functions library (shiftSupply supply base) (shiftQuery query base) path items required =
      functions library supply query (path ++ base) items required := by
  cases items with
  | nil => rfl
  | cons head actuals =>
      simp only [functions, declarations_shift]
      apply Coordinates.collect_congr
      intro scheme _
      cases callParts actuals.length scheme with
      | none => rfl
      | some pair =>
          rcases pair with ⟨domains, result⟩
          cases required with
          | none => exact arguments_shift query base path 0 _ _ _
          | some target =>
              dsimp only
              split
              · rfl
              · exact arguments_shift query base path 0 _ _ _

private theorem rows_shift (query : Query) (base path : Path) (position : Nat)
    (items : List TypeTerm) :
    freshRows (shiftQuery query base) path position items =
      freshRows query (path ++ base) position items := by
  induction items generalizing position with
  | nil => rfl
  | cons item rest ih => simp only [freshRows, shiftQuery, List.cons_append, ih]

private theorem structural_shift (supply : Supply) (query : Query) (base path : Path)
    (items : List TypeTerm) (required : Option TypeTerm) :
    structural (shiftSupply supply base) (shiftQuery query base) path items required =
      structural supply query (path ++ base) items required := by
  cases required with
  | none => simp only [structural, rows_shift, List.cons_append]
  | some target =>
      simp only [structural, shiftSupply, List.cons_append]
      split <;> simp_all only [arguments_shift, List.cons_append]

private theorem expression_shift (library : List Declaration) (supply : Supply)
    (query : Query) (base path : Path) (items : List TypeTerm) (required : Option TypeTerm) :
    expression library (shiftSupply supply base) (shiftQuery query base) path items required =
      expression library supply query (path ++ base) items required := by
  simp only [expression, functions_shift, structural_shift]

private theorem step_shift (library : List Declaration) (supply : Supply)
    (query : Query) (base path : Path) (subject : TypeTerm) (required : Option TypeTerm) :
    step library (shiftSupply supply base) (shiftQuery query base) path subject required =
      step library supply query (path ++ base) subject required := by
  simp only [step, shiftSupply, List.cons_append, declarations_shift, expression_shift]

/-- The complete ordered service can move to any invocation path while its
private allocation coordinates move with it. No invocation path is a fact key. -/
theorem run_shift (library : List Declaration) (supply : Supply) (fuel : Nat)
    (base path : Path) (subject : TypeTerm) (required : Option TypeTerm) :
    run library (shiftSupply supply base) fuel path subject required =
      run library supply fuel (path ++ base) subject required := by
  induction fuel generalizing path subject required with
  | zero => rfl
  | succ fuel ih =>
      change step library (shiftSupply supply base)
        (run library (shiftSupply supply base) fuel) path subject required = _
      have agree : SupplyLocality.QueriesAgreeAt path
          (run library (shiftSupply supply base) fuel)
          (shiftQuery (run library supply fuel) base) := by
        intro stem child target
        exact ih (stem ++ path) child target
      rw [SupplyLocality.step_eq library _ _ _ _ path
        (fun _ _ => rfl) agree]
      exact step_shift library supply (run library supply fuel) base path subject required


private noncomputable def exchange {α : Type} (left right : α → Nat) (name : Nat) : Nat := by
  classical
  exact if found : ∃ index, left index = name then right found.choose
  else if found : ∃ index, right index = name then left found.choose
  else name

private theorem exchange_left {α : Type} (left right : α → Nat)
    (injective : Function.Injective left) (index : α) :
    exchange left right (left index) = right index := by
  classical
  unfold exchange
  split
  · rename_i found
    rw [injective found.choose_spec]
  · rename_i absent
    exact False.elim (absent ⟨index, rfl⟩)

private theorem exchange_right {α : Type} (left right : α → Nat)
    (injective : Function.Injective right)
    (separate : ∀ i j, left i ≠ right j) (index : α) :
    exchange left right (right index) = left index := by
  classical
  unfold exchange
  split
  · rename_i found
    exact False.elim (separate found.choose index found.choose_spec)
  · split
    · rename_i found
      rw [injective found.choose_spec]
    · rename_i absent
      exact False.elim (absent ⟨index, rfl⟩)

private noncomputable def exchangeEquiv {α : Type} (left right : α → Nat)
    (leftInjective : Function.Injective left) (rightInjective : Function.Injective right)
    (separate : ∀ i j, left i ≠ right j) : Nat ≃ Nat :=
  by
  have involutive : Function.Involutive (exchange left right) := by
    classical
    intro name
    by_cases first : ∃ index, left index = name
    · obtain ⟨index, rfl⟩ := first
      rw [exchange_left left right leftInjective,
        exchange_right left right rightInjective separate]
    · by_cases second : ∃ index, right index = name
      · obtain ⟨index, rfl⟩ := second
        rw [exchange_right left right rightInjective separate,
          exchange_left left right leftInjective]
      · simp only [exchange, dif_neg first, dif_neg second]
  exact ⟨exchange left right, exchange left right, involutive, involutive⟩

/-- Coordinates inside a retained fact live in a namespace distinct from
both caller names and every runtime invocation's private allocations. -/
def schemeSupply (path : Path) (slot : Nat) : Nat :=
  Nat.pair 2 (Nat.pair (Encodable.encode path) slot)

private theorem scheme_injective :
    Function.Injective (fun index : Path × Nat => schemeSupply index.1 index.2) := by
  intro left right same
  rcases left with ⟨leftPath, leftSlot⟩
  rcases right with ⟨rightPath, rightSlot⟩
  simp only [schemeSupply, Nat.pair_eq_pair] at same
  exact Prod.ext (Encodable.encode_injective same.2.1) same.2.2

private theorem runtime_injective (base : Path) :
    Function.Injective (fun index : Path × Nat => freshSupply (index.1 ++ base) index.2) := by
  intro left right same
  have parts := (fresh_supply_injective _ _ _ _).mp same
  exact Prod.ext ((List.append_left_inj _).mp parts.1) parts.2

private theorem scheme_runtime_separate (base : Path) (left right : Path × Nat) :
    schemeSupply left.1 left.2 ≠ freshSupply (right.1 ++ base) right.2 := by
  simp [schemeSupply, freshSupply, Nat.pair_eq_pair]

/-- Rebase a retained scheme without including the invocation path in its
key. This coordinate permutation fixes every caller name. -/
noncomputable def rebase (base : Path) : Nat ≃ Nat :=
  exchangeEquiv (fun index : Path × Nat => schemeSupply index.1 index.2)
    (fun index => freshSupply (index.1 ++ base) index.2)
    scheme_injective (runtime_injective base) (scheme_runtime_separate base)

theorem rebase_scheme (base path : Path) (slot : Nat) :
    rebase base (schemeSupply path slot) = freshSupply (path ++ base) slot :=
  exchange_left _ _ scheme_injective (path, slot)

theorem rebase_caller (base : Path) (slot : Nat) :
    rebase base (callerName slot) = callerName slot := by
  classical
  change exchange _ _ _ = _
  have first : ¬ ∃ index : Path × Nat, schemeSupply index.1 index.2 = callerName slot := by
    rintro ⟨index, same⟩
    simp [schemeSupply, callerName, Nat.pair_eq_pair] at same
  have second : ¬ ∃ index : Path × Nat,
      freshSupply (index.1 ++ base) index.2 = callerName slot := by
    rintro ⟨index, same⟩
    exact fresh_supply_separate _ _ _ same
  simp only [exchange, dif_neg first, dif_neg second]

private theorem rename_ground (names : Nat → Nat) (term : TypeTerm)
    (closed : term.isGround) : rename names term = term := by
  induction term with
  | var _ => cases closed
  | const _ => rfl
  | app arity children ih =>
      simp only [rename, Subst.applyTerm]
      congr 1
      funext index
      exact ih index (closed index)

/-- Canonical closed facts materialize to the exact ordered local answers.
Both multiplicities and sharing within the complete answer vector survive. -/
theorem rebase_run (library : List Declaration) (fuel : Nat) (base : Path)
    (subject : TypeTerm) (required : Option TypeTerm) (closed : subject.isGround)
    (closedRequired : ∀ target ∈ required, target.isGround) :
    run library freshSupply fuel base subject required =
      (run library schemeSupply fuel [] subject required).map
        (List.map (rename (rebase base))) := by
  have subjectFixed := rename_ground (rebase base) subject closed
  have requiredFixed : required.map (rename (rebase base)) = required := by
    cases required with
    | none => rfl
    | some target => simp only [Option.map_some, rename_ground _ _ (closedRequired target rfl)]
  have names : Coordinates.S (rebase base) schemeSupply = shiftSupply freshSupply base := by
    funext path slot
    exact rebase_scheme base path slot
  have transported := Coordinates.run_equivariant (rebase base) library schemeSupply
    fuel [] subject required
  dsimp only [Coordinates.R] at transported
  rw [names, subjectFixed, requiredFixed, run_shift] at transported
  exact transported


/-- Fresh and rigid-required modes admitted by the intrinsic cache. A root
variable is normalized by the separate independent-output theorem before
this interface. Open compound requirements are deliberately absent. -/
structure ClosedKey where
  subject : IntrinsicTypeFacts.ClosedType
  required : Option IntrinsicTypeFacts.ClosedType

noncomputable instance : DecidableEq ClosedKey := Classical.decEq _

def ClosedKey.target (key : ClosedKey) : Option TypeTerm :=
  key.required.map GroundTerm.toTerm

def closedFacts (library : List Declaration) (key : ClosedKey) : List TypeTerm :=
  (run library schemeSupply (key.subject.toTerm.size + 1) []
    key.subject.toTerm key.target).get
      (closed_subject_complete library schemeSupply _ [] _ _
        key.subject.toTerm_isGround (Nat.lt_succ_self _))

theorem closed_facts_return (library : List Declaration) (key : ClosedKey) :
    run library schemeSupply (key.subject.toTerm.size + 1) []
      key.subject.toTerm key.target = some (closedFacts library key) := by
  exact (Option.some_get _).symm

noncomputable def instantiate (base : Path) (facts : List TypeTerm) : List TypeTerm :=
  facts.map (rename (rebase base))

/-- The retained canonical computation supplies the actual service at any
sufficient approximation, including normal exhaustion with no answers. -/
theorem closed_facts_exact (library : List Declaration) (key : ClosedKey)
    (base : Path) (fuel : Nat) (enough : key.subject.toTerm.size < fuel) :
    run library freshSupply fuel base key.subject.toTerm key.target =
      some (instantiate base (closedFacts library key)) := by
  rw [rebase_run library fuel base _ _ key.subject.toTerm_isGround]
  · have complete := closed_subject_complete library schemeSupply fuel []
      key.subject.toTerm key.target key.subject.toTerm_isGround enough
    obtain ⟨answers, returned⟩ := Option.isSome_iff_exists.mp complete
    have same := Completion.completed_answers_unique library schemeSupply
      fuel (key.subject.toTerm.size + 1) [] _ _ answers (closedFacts library key)
      returned (closed_facts_return library key)
    rw [returned, same]
    rfl
  · intro target present
    cases h : key.required with
    | none => simp [ClosedKey.target, h] at present
    | some closed =>
        simp only [ClosedKey.target, h, Option.map_some, Option.mem_some_iff] at present
        subst target
        exact closed.toTerm_isGround

/-- The stamp selects the entire immutable declaration inventory. Native
revision and ownership coordinates must select that same inventory. -/
abbrev FactCache := Mettapedia.Machines.RevisionedQueryFacts.Cache Nat ClosedKey TypeTerm

open Mettapedia.Machines.RevisionedQueryFacts (Valid lookup)

/-- A successful lookup is rebased as one answer vector, with no change to
its order, duplicates, or shared private variables. -/
theorem retained_boundary_exact (history : Nat → List Declaration) (stamp : Nat)
    (key : ClosedKey) (base : Path) (fuel : Nat)
    (cache : FactCache) (valid : Valid (fun revision => closedFacts (history revision)) cache)
    (facts : List TypeTerm) (found : lookup stamp key cache = some facts)
    (enough : key.subject.toTerm.size < fuel) :
    run (history stamp) freshSupply fuel base key.subject.toTerm key.target =
      some (instantiate base facts) := by
  have same := Mettapedia.Machines.RevisionedQueryFacts.lookup_sound
    (fun revision => closedFacts (history revision)) cache valid stamp key found
  rw [same]
  exact closed_facts_exact (history stamp) key base fuel enough


/-- A recursive demand keeps the resolved operands and its allocation path.
Only `ClosedKey` is used for retained lookup; the path is for materialization. -/
structure Demand where
  path : Path
  subject : TypeTerm
  required : Option TypeTerm

/-- Local service operations. Their weights may depend on complete operands:
the work theorem does not pretend unification or copying is constant-time. -/
inductive Operation where
  | inspect (subject : TypeTerm) (required : Option TypeTerm)
  | declarations (subject : TypeTerm)
  | trial (scheme : TypeTerm)
  | resolve (subject formal : TypeTerm)
  | unify (left right : TypeTerm)
  | product (rows : List (List TypeTerm))

/-- A control-preserving intrinsic layer. Continuations are selected by the
actual ordered child answers, including unsuccessful probes and duplicates. -/
inductive Script (α : Type) where
  | done (value : α)
  | exhausted
  | query (demand : Demand) (next : List TypeTerm → Script α)
  | work (operation : Operation) (next : Script α)

namespace Script

def bind {α β : Type} : Script α → (α → Script β) → Script β
  | .done value, next => next value
  | .exhausted, _ => .exhausted
  | .query demand next, after => .query demand (fun answers => bind (next answers) after)
  | .work operation next, after => .work operation (bind next after)

instance : Monad Script where
  pure := .done
  bind := bind

def ask (path : Path) (subject : TypeTerm) (required : Option TypeTerm) : Script (List TypeTerm) :=
  .query ⟨path, subject, required⟩ .done

def charge (operation : Operation) : Script Unit := .work operation (.done ())

def evaluate {α : Type} (query : Query) : Script α → Option α
  | .done value => some value
  | .exhausted => none
  | .query demand next => (query demand.path demand.subject demand.required).bind
      (fun answers => evaluate query (next answers))
  | .work _ next => evaluate query next

@[simp] theorem evaluate_bind {α β : Type} (query : Query)
    (script : Script α) (next : α → Script β) :
    evaluate query (bind script next) = (evaluate query script).bind
      (fun answer => evaluate query (next answer)) := by
  induction script with
  | done _ => rfl
  | exhausted => rfl
  | query demand later ih =>
      simp only [bind, evaluate]
      cases query demand.path demand.subject demand.required with
      | none => rfl
      | some answers => exact ih answers
  | work operation later ih => exact ih

@[simp] theorem evaluate_ask (query : Query) (path : Path)
    (subject : TypeTerm) (required : Option TypeTerm) :
    evaluate query (ask path subject required) = query path subject required := by
  simp only [ask, evaluate]
  cases query path subject required <;> rfl

@[simp] theorem evaluate_charge (query : Query) (operation : Operation) :
    evaluate query (charge operation) = some () := rfl

@[simp] theorem evaluate_pure {α : Type} (query : Query) (value : α) :
    evaluate query (pure value : Script α) = some value := rfl

def gather {α β : Type} (items : List α) (visit : α → Script (List β)) : Script (List β) :=
  match items with
  | [] => pure []
  | item :: later => do
      let first ← visit item
      let rest ← gather later visit
      pure (first ++ rest)

@[simp] theorem evaluate_gather {α β : Type} (query : Query)
    (items : List α) (visit : α → Script (List β)) :
    evaluate query (gather items visit) = collect items (fun item => evaluate query (visit item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [gather, Bind.bind, evaluate_bind, evaluate_pure, ih, collect, Option.pure_def]

def arguments (path : Path) (position : Nat) :
    List (TypeTerm × TypeTerm) → TypeTerm → Subst signature → Script (List TypeTerm)
  | [], result, store => pure [store.applyTerm result]
  | (subject, formal) :: rest, result, store => do
      charge (.resolve (store.applyTerm subject) (store.applyTerm formal))
      if isVariable (store.applyTerm subject) then
        arguments path (position + 1) rest result store
      else do
        let candidates ← ask (0 :: position :: path)
          (store.applyTerm subject) (some (store.applyTerm formal))
        gather candidates fun candidate => do
          charge (.unify candidate (store.applyTerm formal))
          match unifyTotal [(candidate, store.applyTerm formal)] with
          | none => pure []
          | some refinement => arguments path (position + 1) rest result (refinement ∘ₛ store)

@[simp] theorem evaluate_arguments (query : Query) (path : Path) (position : Nat)
    (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm) (store : Subst signature) :
    evaluate query (arguments path position pending result store) =
      IndependentTypeOutput.arguments query path position pending result store := by
  induction pending generalizing position store with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨subject, formal⟩
      simp only [arguments, Bind.bind, evaluate_bind, evaluate_charge, Option.bind_some,
        IndependentTypeOutput.arguments]
      split
      · exact ih (position + 1) store
      · simp only [evaluate_bind, evaluate_ask]
        cases query (0 :: position :: path) (store.applyTerm subject) (some (store.applyTerm formal)) with
        | none => rfl
        | some candidates =>
            dsimp only [Option.bind]
            rw [evaluate_gather]
            apply Coordinates.collect_congr
            intro candidate _
            simp only [evaluate_bind, evaluate_charge, Option.bind_some]
            cases unifyTotal [(candidate, store.applyTerm formal)] with
            | none => rfl
            | some refinement => exact ih (position + 1) (refinement ∘ₛ store)

def functions (library : List Declaration) (supply : Supply) (path : Path)
    (items : List TypeTerm) (required : Option TypeTerm) : Script (List TypeTerm) :=
  match items with
  | [] => pure []
  | head :: actuals => do
      charge (.declarations head)
      gather (IndependentTypeOutput.declarations library supply path head) fun scheme => do
        charge (.trial scheme)
        match callParts actuals.length scheme with
        | none => pure []
        | some (domains, result) =>
            match required with
            | none => arguments path 0 (actuals.zip domains) result (Subst.id signature)
            | some target => do
                charge (.unify result target)
                match unifyTotal [(result, target)] with
                | none => pure []
                | some initial => arguments path 0 (actuals.zip domains) result initial

@[simp] theorem evaluate_functions (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (items : List TypeTerm) (required : Option TypeTerm) :
    evaluate query (functions library supply path items required) =
      IndependentTypeOutput.functions library supply query path items required := by
  cases items with
  | nil => rfl
  | cons head actuals =>
      simp only [functions, Bind.bind, evaluate_bind, evaluate_charge, Option.bind_some,
        evaluate_gather, IndependentTypeOutput.functions]
      apply Coordinates.collect_congr
      intro scheme _
      cases callParts actuals.length scheme with
      | none => rfl
      | some pair =>
          rcases pair with ⟨domains, result⟩
          cases required with
          | none => exact evaluate_arguments query path 0 _ _ _
          | some target =>
              simp only [evaluate_bind, evaluate_charge, Option.bind_some]
              cases unifyTotal [(result, target)] with
              | none => rfl
              | some initial => exact evaluate_arguments query path 0 _ _ _

def rows (path : Path) (position : Nat) : List TypeTerm → Script (List (List TypeTerm))
  | [] => pure [[]]
  | subject :: rest => do
      let first ← ask (0 :: position :: path) subject none
      let later ← rows path (position + 1) rest
      let product := first.flatMap fun answer => later.map (answer :: ·)
      charge (.product product)
      pure product

@[simp] theorem evaluate_rows (query : Query) (path : Path) (position : Nat)
    (items : List TypeTerm) :
    evaluate query (rows path position items) = freshRows query path position items := by
  induction items generalizing position with
  | nil => rfl
  | cons item rest ih =>
      simp only [rows, Bind.bind, evaluate_bind, evaluate_ask, evaluate_charge,
        evaluate_pure, Option.bind_some, ih, freshRows, Option.pure_def]

def structural (supply : Supply) (path : Path) (items : List TypeTerm)
    (required : Option TypeTerm) : Script (List TypeTerm) :=
  match required with
  | none => do
      let choices ← rows (4 :: path) 0 items
      pure (choices.map row)
  | some target => do
      let fields := (List.range items.length).map fun index =>
        (Term.var (supply (3 :: path) index) : TypeTerm)
      let result := row fields
      charge (.unify result target)
      match unifyTotal [(result, target)] with
      | none => pure []
      | some initial => arguments (4 :: path) 0 (items.zip fields) result initial

@[simp] theorem evaluate_structural (supply : Supply) (query : Query) (path : Path)
    (items : List TypeTerm) (required : Option TypeTerm) :
    evaluate query (structural supply path items required) =
      IndependentTypeOutput.structural supply query path items required := by
  cases required with
  | none =>
      simp only [structural, Bind.bind, evaluate_bind, evaluate_rows, evaluate_pure,
        IndependentTypeOutput.structural]
      cases freshRows query (4 :: path) 0 items <;> rfl
  | some target =>
      simp only [structural, Bind.bind, evaluate_bind, evaluate_charge, Option.bind_some,
        IndependentTypeOutput.structural]
      split <;> simp_all only [evaluate_arguments, evaluate_pure]

def expression (library : List Declaration) (supply : Supply) (path : Path)
    (items : List TypeTerm) (required : Option TypeTerm) : Script (List TypeTerm) := do
  let functionAnswers ← functions library supply path items required
  let allFunctions ← (match required with
    | none => pure functionAnswers
    | some _ => if allowsRow required && functionAnswers.isEmpty then
        functions library supply path items none else pure functionAnswers)
  let rowAnswers ← (if allowsRow required && allFunctions.isEmpty then
      structural supply path items required else pure [])
  pure (finish required (functionAnswers ++ rowAnswers))

@[simp] theorem evaluate_expression (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (items : List TypeTerm) (required : Option TypeTerm) :
    evaluate query (expression library supply path items required) =
      IndependentTypeOutput.expression library supply query path items required := by
  simp only [expression, Bind.bind, evaluate_bind, evaluate_functions,
    IndependentTypeOutput.expression]
  congr 1
  funext answers
  have probe : evaluate query (match required with
      | none => pure answers
      | some _ => if allowsRow required && answers.isEmpty then
          functions library supply path items none else pure answers) =
      (match required with
      | none => some answers
      | some _ => if allowsRow required && answers.isEmpty then
          IndependentTypeOutput.functions library supply query path items none else some answers) := by
    cases required with
    | none => rfl
    | some _ =>
        dsimp only
        split
        · exact evaluate_functions library supply query path items none
        · rfl
  rw [probe]
  congr 1
  funext allAnswers
  split <;> simp_all only [evaluate_structural, evaluate_pure, Option.bind_some, Option.pure_def]

/-- This script uses the same rule order and same unifier as the independent
source service; only explicit query demands and local work events are added. -/
def layer (library : List Declaration) (supply : Supply) (path : Path)
    (subject : TypeTerm) (required : Option TypeTerm) : Script (List TypeTerm) := do
  charge (.inspect subject required)
  if isVariable subject then pure [required.getD (.var (supply (5 :: path) 0))]
  else match literal subject with
    | some primitive =>
        let candidates := select required [primitive]
        if !candidates.isEmpty then pure candidates else pure (finish required [])
    | none => match elements subject with
      | none => do
          charge (.declarations subject)
          pure (finish required (select required (IndependentTypeOutput.declarations library supply path subject)))
      | some items => expression library supply path items required

@[simp] theorem evaluate_layer (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (subject : TypeTerm) (required : Option TypeTerm) :
    evaluate query (layer library supply path subject required) =
      step library supply query path subject required := by
  simp only [layer, Bind.bind, evaluate_bind, evaluate_charge, Option.bind_some, step]
  split
  · rfl
  · cases literal subject with
    | some primitive =>
        dsimp only
        split <;> simp_all only [evaluate_pure]
    | none =>
        dsimp only
        cases elements subject with
        | none => simp only [evaluate_bind, evaluate_charge, Option.bind_some, evaluate_pure]
        | some items => exact evaluate_expression library supply query path items required

end Script


def asGround (term : TypeTerm) (closed : term.isGround) : IntrinsicTypeFacts.ClosedType :=
  match term with
  | .var _ => False.elim closed
  | .const value => .const value
  | .app arity children => .app arity (fun index => asGround (children index) (closed index))

theorem asGround_exact (term : TypeTerm) (closed : term.isGround) :
    (asGround term closed).toTerm = term := by
  induction term with
  | var _ => cases closed
  | const _ => rfl
  | app arity children ih =>
      simp only [asGround, GroundTerm.toTerm]
      congr 1
      funext index
      exact ih index (closed index)

/-- Operand admission precedes ownership and payload admission. Arbitrary
open requirements cannot enter a retained fact key. -/
noncomputable def demandKey (demand : Demand) : Option ClosedKey := by
  classical
  exact if closed : demand.subject.isGround then
    match demand.required with
    | none => some ⟨asGround demand.subject closed, none⟩
    | some target => if targetClosed : target.isGround then
        some ⟨asGround demand.subject closed, some (asGround target targetClosed)⟩ else none
  else none

theorem demand_key_exact (demand : Demand) (key : ClosedKey)
    (selected : demandKey demand = some key) :
    key.subject.toTerm = demand.subject ∧ key.target = demand.required := by
  classical
  unfold demandKey at selected
  split at selected
  · rename_i closed
    cases targetEq : demand.required with
    | none =>
        simp only [targetEq, Option.some.injEq] at selected
        subst key
        exact ⟨asGround_exact _ _, rfl⟩
    | some target =>
        simp only [targetEq] at selected
        split at selected
        · simp only [Option.some.injEq] at selected
          subst key
          exact ⟨asGround_exact _ _, congrArg some (asGround_exact _ _)⟩
        · contradiction
  · contradiction

/-- A finite approximation only takes a retained boundary once its closed
computation fits. This is proof fuel, not an additional native runtime test. -/
noncomputable def boundaryKey (admit : ClosedKey → Bool) (fuel : Nat)
    (demand : Demand) : Option ClosedKey :=
  (demandKey demand).bind fun key =>
    if admit key && decide (key.subject.toTerm.size < fuel) then some key else none

theorem boundary_key_exact (admit : ClosedKey → Bool) (fuel : Nat)
    (demand : Demand) (key : ClosedKey) (selected : boundaryKey admit fuel demand = some key) :
    key.subject.toTerm = demand.subject ∧ key.target = demand.required ∧
      key.subject.toTerm.size < fuel ∧ admit key = true := by
  unfold boundaryKey at selected
  cases original : demandKey demand with
  | none => simp [original] at selected
  | some found =>
      simp only [original, Option.bind_some] at selected
      split at selected
      · rename_i allowed
        simp only [Option.some.injEq] at selected
        subst key
        have exactKey := demand_key_exact demand found original
        simp only [Bool.and_eq_true, decide_eq_true_eq] at allowed
        exact ⟨exactKey.1, exactKey.2, allowed.2, allowed.1⟩
      · contradiction

/-- Events describe service work, rather than a count of unique syntax nodes.
Every signature/refinement occurrence has its own event. -/
inductive Event where
  | enter (demand : Demand)
  | local (fuel : Nat) (demand : Demand) (operation : Operation)
  | retained (key : ClosedKey) (facts : List TypeTerm)
  | miss (key : ClosedKey)

structure Observed (α : Type) where
  answer : Option α
  events : List Event

namespace Script

def observe {α : Type} (query : Demand → Observed (List TypeTerm))
    (tag : Operation → Event) : Script α → Observed α
  | .done value => ⟨some value, []⟩
  | .exhausted => ⟨none, []⟩
  | .work operation next =>
      let later := observe query tag next
      ⟨later.answer, tag operation :: later.events⟩
  | .query demand next =>
      let child := query demand
      match child.answer with
      | none => ⟨none, child.events⟩
      | some values =>
          let later := observe query tag (next values)
          ⟨later.answer, child.events ++ later.events⟩

/-- Erasing work events recovers the separately defined source evaluation. -/
theorem observe_answer {α : Type} (query : Demand → Observed (List TypeTerm))
    (tag : Operation → Event) (script : Script α) :
    (observe query tag script).answer =
      evaluate (fun path subject required => (query ⟨path, subject, required⟩).answer) script := by
  induction script with
  | done _ => rfl
  | exhausted => rfl
  | work operation next ih => exact ih
  | query demand next ih =>
      simp only [observe, evaluate]
      cases (query demand).answer with
      | none => rfl
      | some values => exact ih values

end Script

/-- A read-only retained boundary provider. It is the existing cache's
lookup function during a warm traversal; a miss executes the full layer. -/
noncomputable def walk (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm)) : Nat → Demand → Observed (List TypeTerm)
  | 0, _ => ⟨none, []⟩
  | fuel + 1, demand =>
      match boundaryKey admit (fuel + 1) demand with
      | none =>
          let expand := Script.observe (walk library admit retained fuel)
            (.local (fuel + 1) demand)
            (Script.layer library freshSupply demand.path demand.subject demand.required)
          ⟨expand.answer, .enter demand :: expand.events⟩
      | some key => match retained key with
        | none =>
            let expand := Script.observe (walk library admit retained fuel)
              (.local (fuel + 1) demand)
              (Script.layer library freshSupply demand.path demand.subject demand.required)
            ⟨expand.answer, .enter demand :: .miss key :: expand.events⟩
        | some facts => ⟨some (instantiate demand.path facts), [.enter demand, .retained key facts]⟩

/-- Arbitrary refusal or a cache snapshot after eviction affects work, not
the complete ordered answers. The only cache invariant is validity of stored facts. -/
theorem walk_exact (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm))
    (sound : ∀ key facts, retained key = some facts → facts = closedFacts library key)
    (fuel : Nat) (demand : Demand) :
    (walk library admit retained fuel demand).answer =
      run library freshSupply fuel demand.path demand.subject demand.required := by
  induction fuel generalizing demand with
  | zero => rfl
  | succ fuel ih =>
      have expanded :
          (Script.observe (walk library admit retained fuel) (.local (fuel + 1) demand)
            (Script.layer library freshSupply demand.path demand.subject demand.required)).answer =
          run library freshSupply (fuel + 1) demand.path demand.subject demand.required := by
        rw [Script.observe_answer]
        have child : (fun path subject required =>
            (walk library admit retained fuel ⟨path, subject, required⟩).answer) =
            run library freshSupply fuel := by
          funext path subject required
          exact ih ⟨path, subject, required⟩
        rw [child, Script.evaluate_layer]
        rfl
      simp only [walk]
      cases selection : boundaryKey admit (fuel + 1) demand with
      | none => exact expanded
      | some key =>
          cases found : retained key with
          | none => simpa only [found] using expanded
          | some facts =>
              obtain ⟨subjectEq, targetEq, enough, _⟩ := boundary_key_exact admit _ demand key selection
              have exactFacts := closed_facts_exact library key demand.path (fuel + 1) enough
              rw [subjectEq, targetEq, ← sound key facts found] at exactFacts
              simpa only [found] using exactFacts.symm

/-- The ideal retained traversal determines the finite boundary set and
open work before consulting any bounded cache. It is a cost specification,
not an assumption that a finite cache can retain every possible query. -/
noncomputable def frontier (library : List Declaration) (admit : ClosedKey → Bool)
    (fuel : Nat) (demand : Demand) : Observed (List TypeTerm) :=
  walk library admit (fun key => some (closedFacts library key)) fuel demand

def Covers (retained : ClosedKey → Option (List TypeTerm)) (events : List Event) : Prop :=
  ∀ key facts, Event.retained key facts ∈ events → retained key = some facts

private theorem covers_append (retained : ClosedKey → Option (List TypeTerm))
    (first later : List Event) (covered : Covers retained (first ++ later)) :
    Covers retained first ∧ Covers retained later := by
  constructor <;> intro key facts present
  · exact covered key facts (List.mem_append_left _ present)
  · exact covered key facts (List.mem_append_right _ present)

namespace Script

/-- Exact child answers preserve all following control decisions; boundary
coverage is needed only for the actually visited ideal execution. -/
theorem observe_simulation {α : Type}
    (actual ideal : Demand → Observed (List TypeTerm))
    (retained : ClosedKey → Option (List TypeTerm))
    (simulation : ∀ demand, Covers retained (ideal demand).events → actual demand = ideal demand)
    (tag : Operation → Event) (script : Script α)
    (covered : Covers retained (observe ideal tag script).events) :
    observe actual tag script = observe ideal tag script := by
  induction script with
  | done _ => rfl
  | exhausted => rfl
  | work operation next ih =>
      have smaller : Covers retained (observe ideal tag next).events := by
        intro key facts present
        exact covered key facts (List.mem_cons_of_mem _ present)
      simp only [observe, ih smaller]
  | query demand next ih =>
      simp only [observe] at covered ⊢
      cases result : (ideal demand).answer with
      | none =>
          have same := simulation demand (by simpa only [result] using covered)
          simp only [same, result]
      | some values =>
          have parts := covers_append retained (ideal demand).events
            (observe ideal tag (next values)).events (by simpa only [result] using covered)
          have same := simulation demand parts.1
          simp only [same, result, ih values parts.2]

end Script

/-- A bounded cache which contains this query's finite retained frontier
executes exactly its ideal warm trace, including all materialization events.
There is no assumption about queries outside that frontier. -/
theorem walk_warm (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm)) (fuel : Nat) (demand : Demand)
    (covered : Covers retained (frontier library admit fuel demand).events) :
    walk library admit retained fuel demand = frontier library admit fuel demand := by
  induction fuel generalizing demand with
  | zero => rfl
  | succ fuel ih =>
      unfold frontier at covered ⊢
      simp only [walk] at covered ⊢
      cases selection : boundaryKey admit (fuel + 1) demand with
      | none =>
          have inner : Covers retained (Script.observe
              (walk library admit (fun key => some (closedFacts library key)) fuel)
              (.local (fuel + 1) demand) (Script.layer library freshSupply demand.path demand.subject demand.required)).events := by
            intro key facts present
            exact covered key facts (by simpa only [selection] using List.mem_cons_of_mem (.enter demand) present)
          have same := Script.observe_simulation
            (walk library admit retained fuel)
            (walk library admit (fun key => some (closedFacts library key)) fuel)
            retained (fun child available => ih child available)
            (.local (fuel + 1) demand) (Script.layer library freshSupply demand.path demand.subject demand.required) inner
          simp only [same]
      | some key =>
          have found : retained key = some (closedFacts library key) :=
            covered key (closedFacts library key) (by simp only [selection, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inr trivial)
          simp only [found]


namespace Script

theorem observe_events {α : Type} (query : Demand → Observed (List TypeTerm))
    (tag : Operation → Event) (property : Event → Prop)
    (tagged : ∀ operation, property (tag operation))
    (children : ∀ demand event, event ∈ (query demand).events → property event)
    (script : Script α) : ∀ event ∈ (observe query tag script).events, property event := by
  induction script with
  | done _ => simp [observe]
  | exhausted => simp [observe]
  | work operation next ih =>
      intro event present
      rcases List.mem_cons.mp present with rfl | later
      · exact tagged operation
      · exact ih event later
  | query demand next ih =>
      intro event present
      simp only [observe] at present
      cases result : (query demand).answer with
      | none => exact children demand event (by simpa only [result] using present)
      | some values =>
          have member : event ∈ (query demand).events ++ (observe query tag (next values)).events := by
            simpa only [result] using present
          rcases List.mem_append.mp member with child | later
          · exact children demand event child
          · exact ih values event later

end Script

/-- The ideal trace has no cold misses. Every expanded operation belongs to
a genuinely residual query: open operands, refused admission, or insufficient
proof approximation. Retained events hold the canonical complete facts. -/
def FrontierEvent (library : List Declaration) (admit : ClosedKey → Bool) : Event → Prop
  | .enter _ => True
  | .local fuel demand _ => boundaryKey admit fuel demand = none
  | .retained key facts => facts = closedFacts library key
  | .miss _ => False

theorem frontier_events (library : List Declaration) (admit : ClosedKey → Bool)
    (fuel : Nat) (demand : Demand) :
    ∀ event ∈ (frontier library admit fuel demand).events, FrontierEvent library admit event := by
  induction fuel generalizing demand with
  | zero => simp [frontier, walk]
  | succ fuel ih =>
      unfold frontier
      simp only [walk]
      cases selection : boundaryKey admit (fuel + 1) demand with
      | none =>
          intro event present
          rcases List.mem_cons.mp present with rfl | later
          · trivial
          · exact Script.observe_events
              (walk library admit (fun key => some (closedFacts library key)) fuel)
              (.local (fuel + 1) demand) (FrontierEvent library admit)
              (fun _ => selection) (fun child => ih child) _ event later
      | some key =>
          intro event present
          simp only [List.mem_cons, List.not_mem_nil, or_false] at present
          rcases present with rfl | rfl
          · trivial
          · rfl

def neededKeys (events : List Event) : List ClosedKey :=
  events.filterMap fun event => match event with
    | .retained key _ => some key
    | _ => none

private theorem needed_of_retained (events : List Event) (key : ClosedKey) (facts : List TypeTerm)
    (present : Event.retained key facts ∈ events) : key ∈ neededKeys events := by
  exact List.mem_filterMap.mpr ⟨.retained key facts, present, rfl⟩

/-- Bounded retention must cover this particular frontier after eviction.
A capacity number alone gives no residency guarantee. -/
theorem bounded_cache_warm (history : Nat → List Declaration) (stamp capacity : Nat)
    (cache : FactCache) (valid : Valid (fun revision => closedFacts (history revision)) cache)
    (admit : ClosedKey → Bool) (fuel : Nat) (demand : Demand)
    (resident : ∀ key ∈ neededKeys (frontier (history stamp) admit fuel demand).events,
      (lookup stamp key (cache.take capacity)).isSome) :
    walk (history stamp) admit (fun key => lookup stamp key (cache.take capacity)) fuel demand =
      frontier (history stamp) admit fuel demand := by
  apply walk_warm
  intro key facts present
  have live := resident key (needed_of_retained _ key facts present)
  obtain ⟨stored, found⟩ := Option.isSome_iff_exists.mp live
  have storedExact := Mettapedia.Machines.RevisionedQueryFacts.lookup_sound
    (fun revision => closedFacts (history revision)) (cache.take capacity)
    (Mettapedia.Machines.RevisionedQueryFacts.valid_take _ cache valid capacity) stamp key found
  have factsExact := frontier_events (history stamp) admit fuel demand (.retained key facts) present
  change facts = closedFacts (history stamp) key at factsExact
  dsimp only
  rw [found, storedExact, factsExact]

/-- Operand-dependent local and lookup costs are kept explicit. `copyNode`
measures copying one syntactic node; variable inventory management can be
charged in `activate`, so it is not assumed constant-time. -/
structure CostModel where
  lookup : Demand → Nat
  operation : Demand → Operation → Nat
  activate : ClosedKey → List TypeTerm → Nat
  missHandling : ClosedKey → Nat
  copyNode : Nat

def outputNodes (facts : List TypeTerm) : Nat :=
  (facts.map Term.size).sum

/-- Whole-vector materialization visits each answer occurrence, including
repeated answers. Sharing does not license dropping duplicate output costs. -/
theorem instantiated_output_nodes (base : Path) (facts : List TypeTerm) :
    outputNodes (instantiate base facts) = outputNodes facts := by
  simp only [outputNodes, instantiate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro term _
  exact NativeAdmission.rename_preserves_size _ term

def eventCost (model : CostModel) : Event → Nat
  | .enter demand => model.lookup demand
  | .local _ demand operation => model.operation demand operation
  | .retained key facts => model.activate key facts + model.copyNode * outputNodes facts
  | .miss key => model.missHandling key

def executionWork (model : CostModel) (events : List Event) : Nat :=
  (events.map (eventCost model)).sum

def frontierWork (model : CostModel) (events : List Event) : Nat :=
  (events.map fun event => match event with
    | .local _ demand operation => model.operation demand operation
    | _ => 0).sum

def boundaryWork (model : CostModel) (events : List Event) : Nat :=
  (events.map fun event => match event with
    | .enter demand => model.lookup demand
    | .retained key facts => model.activate key facts
    | _ => 0).sum

def materializedWork (events : List Event) : Nat :=
  (events.map fun event => match event with
    | .retained _ facts => outputNodes facts
    | _ => 0).sum

def coldWork (model : CostModel) (events : List Event) : Nat :=
  (events.map fun event => match event with
    | .miss key => model.missHandling key
    | _ => 0).sum

private theorem frontier_cold_zero (library : List Declaration) (admit : ClosedKey → Bool)
    (fuel : Nat) (demand : Demand) (model : CostModel) :
    coldWork model (frontier library admit fuel demand).events = 0 := by
  unfold coldWork
  apply List.sum_eq_zero
  intro cost present
  obtain ⟨event, member, rfl⟩ := List.mem_map.mp present
  have invariant := frontier_events library admit fuel demand event member
  cases event with
  | miss key => exact False.elim invariant
  | enter _ => rfl
  | «local» _ _ _ => rfl
  | retained _ _ => rfl

theorem work_accounting (model : CostModel) (events : List Event) :
    executionWork model events = frontierWork model events + boundaryWork model events +
      model.copyNode * materializedWork events + coldWork model events := by
  induction events with
  | nil => simp [executionWork, frontierWork, boundaryWork, materializedWork, coldWork]
  | cons event later ih =>
      cases event <;>
        simp_all only [executionWork, frontierWork, boundaryWork, materializedWork, coldWork,
          List.map_cons, List.sum_cons, eventCost, Nat.mul_add] <;> omega

/-- Under concrete finite-frontier residency, warm work contains only the
residual source operations, boundary tests/activation and the materialized
answer nodes. It has no term proportional to the interiors of retained
closed subtrees. Function alternatives and output multiplicities are kept. -/
theorem warm_work_bound (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm)) (fuel : Nat) (demand : Demand)
    (model : CostModel)
    (covered : Covers retained (frontier library admit fuel demand).events) :
    executionWork model (walk library admit retained fuel demand).events =
      frontierWork model (frontier library admit fuel demand).events +
      boundaryWork model (frontier library admit fuel demand).events +
      model.copyNode * materializedWork (frontier library admit fuel demand).events := by
  rw [walk_warm library admit retained fuel demand covered]
  simpa only [frontier_cold_zero, Nat.add_zero] using work_accounting model
    (frontier library admit fuel demand).events

/-- When a syntactically closed query is neither refused nor below its
completion bound, it cannot contribute an operation to the warm frontier. -/
theorem warm_local_is_open (library : List Declaration) (admit : ClosedKey → Bool)
    (fuel : Nat) (demand : Demand) (localFuel : Nat) (localDemand : Demand) (operation : Operation)
    (present : Event.local localFuel localDemand operation ∈ (frontier library admit fuel demand).events)
    (accepted : ∀ key, demandKey localDemand = some key → admit key = true)
    (adequate : ∀ key, demandKey localDemand = some key → key.subject.toTerm.size < localFuel) :
    demandKey localDemand = none := by
  have residual := frontier_events library admit fuel demand _ present
  change boundaryKey admit localFuel localDemand = none at residual
  cases selected : demandKey localDemand with
  | none => rfl
  | some key =>
      have allowed := accepted key selected
      have enough := adequate key selected
      simp [boundaryKey, selected, allowed, enough] at residual

/-- The native warm correspondence requires an unchanged stamp and retained
boundaries throughout the traversal. Cold store/clear/slot replacement can
invalidate residency; it cannot be justified merely by the byte bound. -/
theorem bounded_cache_work (history : Nat → List Declaration) (stamp capacity : Nat)
    (cache : FactCache) (valid : Valid (fun revision => closedFacts (history revision)) cache)
    (admit : ClosedKey → Bool) (fuel : Nat) (demand : Demand) (model : CostModel)
    (resident : ∀ key ∈ neededKeys (frontier (history stamp) admit fuel demand).events,
      (lookup stamp key (cache.take capacity)).isSome) :
    executionWork model
        (walk (history stamp) admit (fun key => lookup stamp key (cache.take capacity)) fuel demand).events =
      frontierWork model (frontier (history stamp) admit fuel demand).events +
      boundaryWork model (frontier (history stamp) admit fuel demand).events +
      model.copyNode * materializedWork (frontier (history stamp) admit fuel demand).events := by
  rw [bounded_cache_warm history stamp capacity cache valid admit fuel demand resident]
  simpa only [frontier_cold_zero, Nat.add_zero] using work_accounting model
    (frontier (history stamp) admit fuel demand).events


private theorem asGround_roundtrip (term : IntrinsicTypeFacts.ClosedType) :
    asGround term.toTerm term.toTerm_isGround = term := by
  induction term with
  | const _ => rfl
  | app arity children ih =>
      simp only [GroundTerm.toTerm, asGround]
      congr 1
      funext index
      exact ih index

private theorem demand_key_closed (key : ClosedKey) (path : Path) :
    demandKey ⟨path, key.subject.toTerm, key.target⟩ = some key := by
  classical
  rcases key with ⟨subject, required⟩
  unfold demandKey
  simp only [subject.toTerm_isGround, ↓reduceDIte, asGround_roundtrip, ClosedKey.target]
  cases required with
  | none => rfl
  | some target =>
      simp only [Option.map_some, target.toTerm_isGround, ↓reduceDIte, asGround_roundtrip]

private theorem boundary_key_closed (admit : ClosedKey → Bool) (key : ClosedKey)
    (path : Path) (fuel : Nat) (accepted : admit key = true)
    (enough : key.subject.toTerm.size < fuel) :
    boundaryKey admit fuel ⟨path, key.subject.toTerm, key.target⟩ = some key := by
  simp only [boundaryKey, demand_key_closed, Option.bind_some, accepted,
    decide_eq_true enough, Bool.and_self, ↓reduceIte]

/-- A hit on an arbitrarily large retained closed subtree performs only its
lookup, activation and actual answer copying; it never executes its layer. -/
theorem closed_hit_trace (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm)) (key : ClosedKey) (facts : List TypeTerm)
    (path : Path) (fuel : Nat) (accepted : admit key = true)
    (enough : key.subject.toTerm.size < fuel) (found : retained key = some facts) :
    walk library admit retained fuel ⟨path, key.subject.toTerm, key.target⟩ =
      ⟨some (instantiate path facts), [.enter ⟨path, key.subject.toTerm, key.target⟩, .retained key facts]⟩ := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      simp only [walk, boundary_key_closed admit key path (fuel + 1) accepted enough, found]

theorem closed_hit_work (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm)) (key : ClosedKey) (facts : List TypeTerm)
    (path : Path) (fuel : Nat) (accepted : admit key = true)
    (enough : key.subject.toTerm.size < fuel) (found : retained key = some facts) (model : CostModel) :
    executionWork model (walk library admit retained fuel ⟨path, key.subject.toTerm, key.target⟩).events =
      model.lookup ⟨path, key.subject.toTerm, key.target⟩ +
        model.activate key facts + model.copyNode * outputNodes facts := by
  rw [closed_hit_trace library admit retained key facts path fuel accepted enough found]
  simp only [executionWork, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    eventCost, Nat.add_zero, Nat.add_assoc]

/-- Evicting even a correct fact restores a full source inspection. A byte
bound or a previous hit therefore cannot establish the warm premise. -/
theorem closed_miss_inspects (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm)) (key : ClosedKey) (path : Path) (fuel : Nat)
    (accepted : admit key = true) (enough : key.subject.toTerm.size < fuel)
    (absent : retained key = none) :
    .local fuel ⟨path, key.subject.toTerm, key.target⟩ (.inspect key.subject.toTerm key.target) ∈
      (walk library admit retained fuel ⟨path, key.subject.toTerm, key.target⟩).events := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      simp only [walk, boundary_key_closed admit key path (fuel + 1) accepted enough, absent,
        Script.layer, Bind.bind, Script.charge, Script.bind, Script.observe]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- Payload or ownership refusal remains semantically safe but does not have
the retained-subtree work bound, even if an equal fact is available. -/
theorem refused_closed_inspects (library : List Declaration)
    (retained : ClosedKey → Option (List TypeTerm)) (key : ClosedKey) (path : Path) (fuel : Nat) :
    .local (fuel + 1) ⟨path, key.subject.toTerm, key.target⟩ (.inspect key.subject.toTerm key.target) ∈
      (walk library (fun _ => false) retained (fuel + 1) ⟨path, key.subject.toTerm, key.target⟩).events := by
  simp only [walk, boundaryKey, demand_key_closed, Option.bind_some, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, Script.layer, Bind.bind, Script.charge, Script.bind, Script.observe]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The bounded-cache theorem does not silently erase collision/eviction.
With no retained slots, every admitted closed boundary is a miss. -/
theorem zero_capacity_inspects (library : List Declaration) (cache : FactCache)
    (stamp : Nat) (key : ClosedKey) (path : Path) (fuel : Nat)
    (enough : key.subject.toTerm.size < fuel) :
    .local fuel ⟨path, key.subject.toTerm, key.target⟩ (.inspect key.subject.toTerm key.target) ∈
      (walk library (fun _ => true) (fun key => lookup stamp key (cache.take 0)) fuel
        ⟨path, key.subject.toTerm, key.target⟩).events := by
  apply closed_miss_inspects library (fun _ => true) _ key path fuel rfl enough
  rfl

/-- A repeated answer occurrence still costs a copied node. -/
example : outputNodes [IntrinsicTypeFacts.named "Number", IntrinsicTypeFacts.named "Number"] = 2 := rfl

example (path : Path) :
    outputNodes (instantiate path [IntrinsicTypeFacts.named "Number", IntrinsicTypeFacts.named "Number"]) = 2 := by
  rw [instantiated_output_nodes]
  rfl

/-- Reusing the same retained scheme at two invocation paths does not alias
its private names. Caller names, by contrast, are fixed by `rebase_caller`. -/
example : rebase [0] (schemeSupply [] 7) ≠ rebase [1] (schemeSupply [] 7) := by
  rw [rebase_scheme, rebase_scheme]
  simp only [List.nil_append, ne_eq, fresh_supply_injective]
  decide

/-- An open requirement must not be silently keyed as rigid or fresh. -/
example : demandKey ⟨[], IntrinsicTypeFacts.named "x", some (.var (callerName 0))⟩ = none := by
  classical
  simp [demandKey, IntrinsicTypeFacts.named, Term.isGround]

/-- A too-small approximation remains incomplete; cached facts do not turn
resource failure into normal empty exhaustion. -/
example (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm)) (demand : Demand) :
    (walk library admit retained 0 demand).answer = none := rfl


open Mettapedia.Logic.LP.IndependentOutputUnification (solutions)

/-- Compose the root independent-output theorem, recursive memo traversal,
and whole-vector native inventory materialization. Caller observations keep
all aliases; the ordered alternative list keeps duplicate occurrences. -/
theorem memoized_independent_publication (library : List Declaration)
    (admit : ClosedKey → Bool) (retained : ClosedKey → Option (List TypeTerm))
    (sound : ∀ key facts, retained key = some facts → facts = closedFacts library key)
    (boundFuel freshFuel : Nat) (path : Path) (subject : TypeTerm) (output : Nat)
    (independent : output ∉ subject.freeVars) (identity : Nat) (inventory : List Nat)
    (bound fresh : List TypeTerm)
    (boundRun : run library freshSupply boundFuel path (NativeAdmission.callerTerm subject)
      (some (.var (callerName output))) = some bound)
    (freshRun : (walk library admit retained freshFuel
      ⟨path, NativeAdmission.callerTerm subject, none⟩).answer = some fresh)
    (observations : List TypeTerm) :
    bound.map (fun answer => solutions [(answer, .var (callerName output))]
      (observations.map NativeAdmission.callerTerm)) =
    (NativeAdmission.materialize identity inventory fresh).map (fun answer =>
      solutions [(answer, .var (callerName output))] (observations.map NativeAdmission.callerTerm)) := by
  rw [walk_exact library admit retained sound freshFuel] at freshRun
  exact NativeAdmission.completed_inventory_publication_exact library boundFuel freshFuel path
    subject output independent identity inventory bound fresh boundRun freshRun observations

end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Memoized
