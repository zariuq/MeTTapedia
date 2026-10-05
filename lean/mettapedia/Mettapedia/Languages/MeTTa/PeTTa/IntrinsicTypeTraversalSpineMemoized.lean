import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutputSpineAdmission

/-!
# Retained traversal with incremental structural-row work

The retained boundary interface, scripts, events, and operand-dependent
costs are reused from `IntrinsicTypeTraversalMemoized`. This module changes
structural traversal to visit a known row's prefix before checking its final
length. Its frontier therefore includes work that eager shape rejection
would skip. Query results and weighted work are proved for this same script.

Fresh output spines use the normalized field traversal justified by the
cons-cell execution and publication laws in `IndependentTypeOutputSpineRecursive`.
This is a model of the separated-source admitted family, not a verification
of native allocation or the general shared-output interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.SpineMemoized

open Mettapedia.Logic.LP
open IntrinsicTypeFacts (signature TypeTerm Declaration named)
open Structural SpineRecursive
open Memoized (ClosedKey Demand Operation Event Observed CostModel)

namespace IncrementalScript

open Memoized.Script (charge ask gather evaluate)

/-- Inspect the current spine before querying its head, and match the
empty tail only after the source is exhausted. The inspection weight may
include representation conversion and copying of a remaining target tail;
it is not assumed constant. Shared formals are refined between children. -/
def knownRow (path : Path) (position : Nat) :
    List TypeTerm → List TypeTerm → TypeTerm → Memoized.Script (List TypeTerm)
  | [], targets, result => do
      charge (.unify (row []) (row targets))
      match targets with
      | [] => pure [result]
      | _ :: _ => pure []
  | subject :: rest, targets, result => do
      charge (.inspect (row (subject :: rest)) (some (row targets)))
      match targets with
      | [] => pure []
      | formal :: later => do
          charge (.resolve subject formal)
          if isVariable subject then knownRow path (position + 1) rest later result
          else do
            let candidates ← ask (0 :: position :: path) subject (some formal)
            gather candidates fun candidate => do
              charge (.unify candidate formal)
              match unifyTotal [(candidate, formal)] with
              | none => pure []
              | some refinement => knownRow path (position + 1) (rest.map refinement.applyTerm) (later.map refinement.applyTerm) (refinement.applyTerm result)
termination_by subjects => subjects.length
decreasing_by all_goals simp_wf

@[simp] theorem evaluate_knownRow (query : Query) (path : Path) (position : Nat)
    (items targets : List TypeTerm) (result : TypeTerm) :
    evaluate query (knownRow path position items targets result) =
      SpineRecursive.knownRow query path position items targets result := by
  induction items using (measure List.length).wf.induction generalizing position targets result with
  | h items ih =>
      cases items with
      | nil =>
          cases targets <;> simp only [knownRow, Bind.bind, Memoized.Script.evaluate_bind,
            Memoized.Script.evaluate_charge, Option.bind_some, Memoized.Script.evaluate_pure,
            SpineRecursive.knownRow]
      | cons subject rest =>
          cases targets with
          | nil => simp only [knownRow, Bind.bind, Memoized.Script.evaluate_bind,
              Memoized.Script.evaluate_charge, Option.bind_some, Memoized.Script.evaluate_pure,
              SpineRecursive.knownRow]
          | cons formal later =>
              simp only [knownRow, Bind.bind, Memoized.Script.evaluate_bind,
                Memoized.Script.evaluate_charge, Option.bind_some, SpineRecursive.knownRow]
              split
              · exact ih rest (Nat.lt_succ_self rest.length) (position + 1) later result
              · simp only [Memoized.Script.evaluate_bind, Memoized.Script.evaluate_ask]
                cases queried : query (0 :: position :: path) subject (some formal) with
                | none => rfl
                | some candidates =>
                    simp only [Option.bind_some, Memoized.Script.evaluate_gather]
                    apply Coordinates.collect_congr
                    intro candidate _
                    simp only [Memoized.Script.evaluate_bind, Memoized.Script.evaluate_charge, Option.bind_some]
                    cases unifyTotal [(candidate, formal)] with
                    | none => rfl
                    | some refinement =>
                        exact ih (rest.map refinement.applyTerm)
                          (by change (rest.map _).length < (subject :: rest).length
                              simpa only [List.length_map, List.length_cons] using Nat.lt_succ_self rest.length)
                          (position + 1) (later.map refinement.applyTerm) (refinement.applyTerm result)

def structural (path : Path) (items : List TypeTerm) : Option TypeTerm → Memoized.Script (List TypeTerm)
  | none => do
      let choices ← Memoized.Script.rows (4 :: path) 0 items
      pure (choices.map row)
  | some (.var _) =>
      let fields := (List.range items.length).map fun index =>
        (Term.var (freshSupply (3 :: path) index) : TypeTerm)
      Memoized.Script.arguments (4 :: path) 0 (items.zip fields) (row fields) (Subst.id signature)
  | some (.const _) => pure []
  | some (.app arity targets) => knownRow (4 :: path) 0 items (List.ofFn targets) (.app arity targets)

@[simp] theorem evaluate_structural (query : Query) (path : Path)
    (items : List TypeTerm) (required : Option TypeTerm) :
    evaluate query (structural path items required) = structuralSpine query path items required := by
  cases required with
  | none =>
      simp only [structural, Bind.bind, Memoized.Script.evaluate_bind, Memoized.Script.evaluate_rows,
        Memoized.Script.evaluate_pure, structuralSpine]
      cases freshRows query (4 :: path) 0 items <;> rfl
  | some target =>
      cases target with
      | var _ => exact Memoized.Script.evaluate_arguments query (4 :: path) 0 _ _ _
      | const _ => rfl
      | app arity targets => exact evaluate_knownRow query (4 :: path) 0 items (List.ofFn targets) (.app arity targets)

def expression (library : List Declaration) (path : Path)
    (items : List TypeTerm) (required : Option TypeTerm) : Memoized.Script (List TypeTerm) := do
  let functionAnswers ← Memoized.Script.functions library freshSupply path items required
  let allFunctions ← (match required with
    | none => pure functionAnswers
    | some _ => if allowsRow required && functionAnswers.isEmpty then
        Memoized.Script.functions library freshSupply path items none else pure functionAnswers)
  let rowAnswers ← (if allowsRow required && allFunctions.isEmpty then structural path items required else pure [])
  pure (finish required (functionAnswers ++ rowAnswers))

@[simp] theorem evaluate_expression (library : List Declaration) (query : Query)
    (path : Path) (items : List TypeTerm) (required : Option TypeTerm) :
    evaluate query (expression library path items required) =
      expressionSpine library query path items required := by
  simp only [expression, Bind.bind, Memoized.Script.evaluate_bind, Memoized.Script.evaluate_functions,
    expressionSpine]
  congr 1
  funext answers
  have probe : evaluate query (match required with
      | none => pure answers
      | some _ => if allowsRow required && answers.isEmpty then
          Memoized.Script.functions library freshSupply path items none else pure answers) =
      (match required with
      | none => some answers
      | some _ => if allowsRow required && answers.isEmpty then
          functions library freshSupply query path items none else some answers) := by
    cases required with
    | none => rfl
    | some _ =>
        dsimp only
        split
        · exact Memoized.Script.evaluate_functions library freshSupply query path items none
        · rfl
  rw [probe]
  congr 1
  funext allAnswers
  split <;> simp_all only [evaluate_structural, Memoized.Script.evaluate_pure, Option.bind_some, Option.pure_def]

/-- The recursive work script follows the same declaration trials and
fallback decisions as `stepSpine`. Only explicit work and query events are
inserted; answers select the subsequent control path. -/
def layer (library : List Declaration) (path : Path)
    (subject : TypeTerm) (required : Option TypeTerm) : Memoized.Script (List TypeTerm) := do
  charge (.inspect subject required)
  if isVariable subject then pure [required.getD (.var (freshSupply (5 :: path) 0))]
  else match literal subject with
    | some primitive =>
        let candidates := select required [primitive]
        if !candidates.isEmpty then pure candidates else pure (finish required [])
    | none => match elements subject with
      | none => do
          charge (.declarations subject)
          pure (finish required (select required (declarations library freshSupply path subject)))
      | some items => expression library path items required

@[simp] theorem evaluate_layer (library : List Declaration) (query : Query)
    (path : Path) (subject : TypeTerm) (required : Option TypeTerm) :
    evaluate query (layer library path subject required) = stepSpine library query path subject required := by
  simp only [layer, Bind.bind, Memoized.Script.evaluate_bind, Memoized.Script.evaluate_charge,
    Option.bind_some, stepSpine]
  split
  · rfl
  · cases literal subject with
    | some primitive =>
        dsimp only
        split <;> simp_all only [Memoized.Script.evaluate_pure]
    | none =>
        dsimp only
        cases elements subject with
        | none => simp only [Memoized.Script.evaluate_bind, Memoized.Script.evaluate_charge,
            Option.bind_some, Memoized.Script.evaluate_pure]
        | some items => exact evaluate_expression library query path items required

end IncrementalScript

private theorem ground_allocation_apart (path : Path) (term : TypeTerm) (closed : term.isGround) :
    AllocationApart path term := by
  intro stem slot
  rw [(Term.isGround_iff_freeVars_empty term).mp closed]
  simp

/-- Existing closed facts remain correct for the recursively incremental
relation. The cache key supplies groundness; the boundary supplies enough
approximation depth. Neither is replaced by an assumed output equality. -/
theorem closed_facts_spine_exact (library : List Declaration) (key : ClosedKey)
    (base : Path) (fuel : Nat) (enough : key.subject.toTerm.size < fuel) :
    runSpine library fuel base key.subject.toTerm key.target =
      some (Memoized.instantiate base (Memoized.closedFacts library key)) := by
  have sourceEmpty : key.subject.toTerm.freeVars = ∅ :=
    (Term.isGround_iff_freeVars_empty key.subject.toTerm).mp key.subject.toTerm_isGround
  rw [← recursive_spine_equivalence library fuel base key.subject.toTerm key.target
    (ground_allocation_apart base _ key.subject.toTerm_isGround)
    (by intro term present; rw [sourceEmpty]; simp)
    (by
      intro term present
      cases original : key.required with
      | none => simp [Memoized.ClosedKey.target, original] at present
      | some target =>
          simp only [Memoized.ClosedKey.target, original, Option.map_some, Option.toList_some,
            List.mem_singleton] at present
          subst term
          exact ground_allocation_apart base target.toTerm target.toTerm_isGround)
    enough]
  exact Memoized.closed_facts_exact library key base fuel enough

/-- The existing retained-boundary driver with the incremental layer.
A miss runs that layer in full; a hit instantiates the complete ordered
fact vector. No alternate cache or persistent store is introduced. -/
noncomputable def walk (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm)) : Nat → Demand → Observed (List TypeTerm)
  | 0, _ => ⟨none, []⟩
  | fuel + 1, demand =>
      match Memoized.boundaryKey admit (fuel + 1) demand with
      | none =>
          let expand := Memoized.Script.observe (walk library admit retained fuel)
            (.local (fuel + 1) demand)
            (IncrementalScript.layer library demand.path demand.subject demand.required)
          ⟨expand.answer, .enter demand :: expand.events⟩
      | some key => match retained key with
        | none =>
            let expand := Memoized.Script.observe (walk library admit retained fuel)
              (.local (fuel + 1) demand)
              (IncrementalScript.layer library demand.path demand.subject demand.required)
            ⟨expand.answer, .enter demand :: .miss key :: expand.events⟩
        | some facts => ⟨some (Memoized.instantiate demand.path facts), [.enter demand, .retained key facts]⟩

/-- Cache refusal, misses, and removal of entries preserve all ordered
answers of the same incremental relation whose work is recorded here.
Incomplete approximation and completed empty exhaustion remain distinct. -/
theorem walk_exact (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm))
    (sound : ∀ key facts, retained key = some facts → facts = Memoized.closedFacts library key)
    (fuel : Nat) (demand : Demand) :
    (walk library admit retained fuel demand).answer =
      runSpine library fuel demand.path demand.subject demand.required := by
  induction fuel generalizing demand with
  | zero => rfl
  | succ fuel ih =>
      have expanded :
          (Memoized.Script.observe (walk library admit retained fuel) (.local (fuel + 1) demand)
            (IncrementalScript.layer library demand.path demand.subject demand.required)).answer =
          runSpine library (fuel + 1) demand.path demand.subject demand.required := by
        rw [Memoized.Script.observe_answer]
        have child : (fun path subject required =>
            (walk library admit retained fuel ⟨path, subject, required⟩).answer) = runSpine library fuel := by
          funext path subject required
          exact ih ⟨path, subject, required⟩
        rw [child, IncrementalScript.evaluate_layer]
        rfl
      simp only [walk]
      cases selection : Memoized.boundaryKey admit (fuel + 1) demand with
      | none => exact expanded
      | some key =>
          cases found : retained key with
          | none => simpa only [found] using expanded
          | some facts =>
              obtain ⟨subjectEq, targetEq, enough, _⟩ := Memoized.boundary_key_exact admit _ demand key selection
              have exactFacts := closed_facts_spine_exact library key demand.path (fuel + 1) enough
              rw [subjectEq, targetEq, ← sound key facts found] at exactFacts
              simpa only [found] using exactFacts.symm

/-- The incremental script determines its own finite frontier. In
particular, child visits before a late shape failure are retained here. -/
noncomputable def frontier (library : List Declaration) (admit : ClosedKey → Bool)
    (fuel : Nat) (demand : Demand) : Observed (List TypeTerm) :=
  walk library admit (fun key => some (Memoized.closedFacts library key)) fuel demand

/-- Reuse the general script simulation law: residency is demanded only
at the boundaries actually visited by the incremental ideal trace. -/
theorem walk_warm (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm)) (fuel : Nat) (demand : Demand)
    (covered : Memoized.Covers retained (frontier library admit fuel demand).events) :
    walk library admit retained fuel demand = frontier library admit fuel demand := by
  induction fuel generalizing demand with
  | zero => rfl
  | succ fuel ih =>
      unfold frontier at covered ⊢
      simp only [walk] at covered ⊢
      cases selection : Memoized.boundaryKey admit (fuel + 1) demand with
      | none =>
          have inner : Memoized.Covers retained (Memoized.Script.observe
              (walk library admit (fun key => some (Memoized.closedFacts library key)) fuel)
              (.local (fuel + 1) demand) (IncrementalScript.layer library demand.path demand.subject demand.required)).events := by
            intro key facts present
            exact covered key facts (by simpa only [selection] using List.mem_cons_of_mem (.enter demand) present)
          have same := Memoized.Script.observe_simulation
            (walk library admit retained fuel)
            (walk library admit (fun key => some (Memoized.closedFacts library key)) fuel)
            retained (fun child available => ih child available)
            (.local (fuel + 1) demand) (IncrementalScript.layer library demand.path demand.subject demand.required) inner
          simp only [same]
      | some key =>
          have found : retained key = some (Memoized.closedFacts library key) :=
            covered key (Memoized.closedFacts library key)
              (by simp only [selection, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inr trivial)
          simp only [found]

/-- Residual operations belong to open, refused, or depth-limited queries;
retained facts are canonical and ideal warm execution has no misses. -/
theorem frontier_events (library : List Declaration) (admit : ClosedKey → Bool)
    (fuel : Nat) (demand : Demand) :
    ∀ event ∈ (frontier library admit fuel demand).events, Memoized.FrontierEvent library admit event := by
  induction fuel generalizing demand with
  | zero => simp [frontier, walk]
  | succ fuel ih =>
      unfold frontier
      simp only [walk]
      cases selection : Memoized.boundaryKey admit (fuel + 1) demand with
      | none =>
          intro event present
          rcases List.mem_cons.mp present with rfl | later
          · trivial
          · exact Memoized.Script.observe_events
              (walk library admit (fun key => some (Memoized.closedFacts library key)) fuel)
              (.local (fuel + 1) demand) (Memoized.FrontierEvent library admit)
              (fun _ => selection) (fun child => ih child) _ event later
      | some key =>
          intro event present
          simp only [List.mem_cons, List.not_mem_nil, or_false] at present
          rcases present with rfl | rfl
          · trivial
          · rfl

/-- Accepted closed operands cannot contribute local work once their
structural approximation is adequate; their interiors are retained boundaries. -/
theorem warm_local_is_open (library : List Declaration) (admit : ClosedKey → Bool)
    (fuel : Nat) (demand : Demand) (localFuel : Nat) (localDemand : Demand) (operation : Operation)
    (present : Event.local localFuel localDemand operation ∈ (frontier library admit fuel demand).events)
    (accepted : ∀ key, Memoized.demandKey localDemand = some key → admit key = true)
    (adequate : ∀ key, Memoized.demandKey localDemand = some key → key.subject.toTerm.size < localFuel) :
    Memoized.demandKey localDemand = none := by
  have residual := frontier_events library admit fuel demand _ present
  change Memoized.boundaryKey admit localFuel localDemand = none at residual
  cases selected : Memoized.demandKey localDemand with
  | none => rfl
  | some key =>
      have allowed := accepted key selected
      have enough := adequate key selected
      simp [Memoized.boundaryKey, selected, allowed, enough] at residual

private theorem frontier_cold_zero (library : List Declaration) (admit : ClosedKey → Bool)
    (fuel : Nat) (demand : Demand) (model : CostModel) :
    Memoized.coldWork model (frontier library admit fuel demand).events = 0 := by
  unfold Memoized.coldWork
  apply List.sum_eq_zero
  intro cost present
  obtain ⟨event, member, rfl⟩ := List.mem_map.mp present
  have invariant := frontier_events library admit fuel demand event member
  cases event with
  | miss key => exact False.elim invariant
  | enter _ => rfl
  | «local» _ _ _ => rfl
  | retained _ _ => rfl

/-- Warm work is the weighted open/refused frontier, retained-boundary
lookup and activation, and every materialized answer occurrence. This
frontier comes from incremental control, including failing row prefixes.
Operand-dependent inspection weights retain any suffix conversion/copying
cost; they are not silently replaced by a unit-cost iteration count. -/
theorem warm_work_bound (library : List Declaration) (admit : ClosedKey → Bool)
    (retained : ClosedKey → Option (List TypeTerm)) (fuel : Nat) (demand : Demand)
    (model : CostModel)
    (covered : Memoized.Covers retained (frontier library admit fuel demand).events) :
    Memoized.executionWork model (walk library admit retained fuel demand).events =
      Memoized.frontierWork model (frontier library admit fuel demand).events +
      Memoized.boundaryWork model (frontier library admit fuel demand).events +
      model.copyNode * Memoized.materializedWork (frontier library admit fuel demand).events := by
  rw [walk_warm library admit retained fuel demand covered]
  simpa only [frontier_cold_zero, Nat.add_zero] using Memoized.work_accounting model
    (frontier library admit fuel demand).events

/-- Bounded retention must cover the concrete new frontier after eviction.
Its capacity alone provides no promise that any requested identity remains. -/
theorem bounded_cache_warm (history : Nat → List Declaration) (stamp capacity : Nat)
    (cache : Memoized.FactCache)
    (valid : Mettapedia.Machines.RevisionedQueryFacts.Valid (fun revision => Memoized.closedFacts (history revision)) cache)
    (admit : ClosedKey → Bool) (fuel : Nat) (demand : Demand)
    (resident : ∀ key ∈ Memoized.neededKeys (frontier (history stamp) admit fuel demand).events,
      (Mettapedia.Machines.RevisionedQueryFacts.lookup stamp key (cache.take capacity)).isSome) :
    walk (history stamp) admit
        (fun key => Mettapedia.Machines.RevisionedQueryFacts.lookup stamp key (cache.take capacity)) fuel demand =
      frontier (history stamp) admit fuel demand := by
  apply walk_warm
  intro key facts present
  have needed : key ∈ Memoized.neededKeys (frontier (history stamp) admit fuel demand).events :=
    List.mem_filterMap.mpr ⟨.retained key facts, present, rfl⟩
  obtain ⟨stored, found⟩ := Option.isSome_iff_exists.mp (resident key needed)
  have storedExact := Mettapedia.Machines.RevisionedQueryFacts.lookup_sound
    (fun revision => Memoized.closedFacts (history revision)) (cache.take capacity)
    (Mettapedia.Machines.RevisionedQueryFacts.valid_take _ cache valid capacity) stamp key found
  have factsExact := frontier_events (history stamp) admit fuel demand (.retained key facts) present
  change facts = Memoized.closedFacts (history stamp) key at factsExact
  dsimp only
  rw [found, storedExact, factsExact]

/-- The weighted incremental warm bound for the existing finite cache.
Cold insertion or eviction may destroy this residency condition; those
executions follow the miss branch with their explicitly recorded costs. -/
theorem bounded_cache_work (history : Nat → List Declaration) (stamp capacity : Nat)
    (cache : Memoized.FactCache)
    (valid : Mettapedia.Machines.RevisionedQueryFacts.Valid (fun revision => Memoized.closedFacts (history revision)) cache)
    (admit : ClosedKey → Bool) (fuel : Nat) (demand : Demand) (model : CostModel)
    (resident : ∀ key ∈ Memoized.neededKeys (frontier (history stamp) admit fuel demand).events,
      (Mettapedia.Machines.RevisionedQueryFacts.lookup stamp key (cache.take capacity)).isSome) :
    Memoized.executionWork model
        (walk (history stamp) admit
          (fun key => Mettapedia.Machines.RevisionedQueryFacts.lookup stamp key (cache.take capacity)) fuel demand).events =
      Memoized.frontierWork model (frontier (history stamp) admit fuel demand).events +
      Memoized.boundaryWork model (frontier (history stamp) admit fuel demand).events +
      model.copyNode * Memoized.materializedWork (frontier (history stamp) admit fuel demand).events := by
  rw [bounded_cache_warm history stamp capacity cache valid admit fuel demand resident]
  simpa only [frontier_cold_zero, Nat.add_zero] using Memoized.work_accounting model
    (frontier (history stamp) admit fuel demand).events

/-- The new costed traversal publishes exactly the root shortcut's joint
caller refinements after one whole-vector materialization. This composes
the answer theorem for the same script whose work was bounded above. -/
theorem retained_independent_output_publication (library : List Declaration)
    (admit : ClosedKey → Bool) (retained : ClosedKey → Option (List TypeTerm))
    (sound : ∀ key facts, retained key = some facts → facts = Memoized.closedFacts library key)
    (boundFuel freshFuel : Nat) (path : Path) (subject : TypeTerm) (output : Nat)
    (independent : output ∉ subject.freeVars) (identity : Nat) (inventory : List Nat)
    (boundEnough : (NativeAdmission.callerTerm subject).size < boundFuel)
    (freshEnough : (NativeAdmission.callerTerm subject).size < freshFuel)
    (bound fresh : List TypeTerm)
    (boundRun : runSpine library boundFuel path (NativeAdmission.callerTerm subject)
      (some (.var (callerName output))) = some bound)
    (freshRun : (walk library admit retained freshFuel
      ⟨path, NativeAdmission.callerTerm subject, none⟩).answer = some fresh)
    (observations : List TypeTerm) :
    bound.map (fun answer => IndependentOutputUnification.solutions [(answer, .var (callerName output))]
      (observations.map NativeAdmission.callerTerm)) =
    (NativeAdmission.materialize identity inventory fresh).map (fun answer =>
      IndependentOutputUnification.solutions [(answer, .var (callerName output))]
        (observations.map NativeAdmission.callerTerm)) := by
  rw [walk_exact library admit retained sound] at freshRun
  exact SpineAdmission.completed_inventory_publication_exact library boundFuel freshFuel path subject output
    independent identity inventory boundEnough freshEnough bound fresh boundRun freshRun observations

namespace Controls

private def leafObservation (demand : Memoized.Demand) : Memoized.Observed (List TypeTerm) :=
  ⟨runSpine [] 1 demand.path demand.subject demand.required, [.enter demand]⟩
private def eventTag : Memoized.Operation → Memoized.Event :=
  .local 2 ⟨[], row [], none⟩
private def childVisits (events : List Memoized.Event) : Nat :=
  (events.filter fun event => match event with | .enter _ => true | _ => false).length

private def number : TypeTerm := .const (.number "1")
private def numberType : TypeTerm := named "Number"
/-- A successful row queries its numeric child and records the final empty-tail check. -/
theorem matching_row_visits_child_and_closes :
    let seen := Memoized.Script.observe leafObservation eventTag
      (IncrementalScript.knownRow [] 0 [number] [numberType] (row [numberType]))
    seen.answer = some [row [numberType]] ∧ childVisits seen.events = 1 ∧
      eventTag (.unify (row []) (row [])) ∈ seen.events := by
  simp [Bind.bind, Pure.pure, IncrementalScript.knownRow, Memoized.Script.observe,
    Memoized.Script.bind, Memoized.Script.charge, Memoized.Script.ask,
    Memoized.Script.gather, leafObservation, eventTag, childVisits, number, numberType,
    runSpine, stepSpine, isVariable, literal, IntrinsicTypeFacts.primitiveType,
    select, matched, unifyTotal, Subst.applyTerm_id, Subst.applyTerm, named]

/-- A too-long target is rejected only after the matching prefix has been visited. -/
theorem wrong_length_visits_child_before_rejecting :
    let seen := Memoized.Script.observe leafObservation eventTag
      (IncrementalScript.knownRow [] 0 [number] [numberType, numberType] (row [numberType, numberType]))
    seen.answer = some [] ∧ childVisits seen.events = 1 ∧
      eventTag (.unify (row []) (row [numberType])) ∈ seen.events := by
  simp [Bind.bind, Pure.pure, IncrementalScript.knownRow, Memoized.Script.observe,
    Memoized.Script.bind, Memoized.Script.charge, Memoized.Script.ask,
    Memoized.Script.gather, leafObservation, eventTag, childVisits, number, numberType,
    runSpine, stepSpine, isVariable, literal, IntrinsicTypeFacts.primitiveType,
    select, matched, unifyTotal, Subst.applyTerm, named]

/-- Negative control: the old eager trace answers the same but omits that child visit. -/
theorem eager_shape_rejection_omits_prefix :
    let seen := Memoized.Script.observe leafObservation eventTag
      (Memoized.Script.structural freshSupply [] [number] (some (row [numberType, numberType])))
    seen.answer = some [] ∧ childVisits seen.events = 0 := by
  simp [Memoized.Script.structural, Bind.bind, Pure.pure, Memoized.Script.observe,
    Memoized.Script.bind, Memoized.Script.charge, eventTag, childVisits, row, unifyTotal]

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.SpineMemoized
