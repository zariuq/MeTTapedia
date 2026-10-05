import Mettapedia.GSLT.Weighting.Keys
import Mettapedia.GSLT.Core.InteractionEvent
import Mettapedia.GSLT.Dynamics.WeightedResumption
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat

/-!
# The weight construction

Every redex of a presented theory belongs to a rule (a site of the presentation)
and has a key, the refinement of the rule it satisfies. A weight map gives a
value to every key of every rule. A configuration is a term with a weight map,
and a step fires an event of the term and rewrites the map: by the update of
the event's key, then by the fold of each context around the redex, from the
redex outwards. The weighted theory steps on configurations, up to the equations
on terms. It keeps the base steps and adjoins the map to the state.

A map of keyed presentations that preserves keys reindexes weight maps by
precomposition. The weight of an event under a reindexed map is the weight of
its image. Weights that are all one and are never updated give back the base
theory, and then every redex weighs the same.

Weight maps that change are a property of configurations, not of terms. Two
updates that do not commute bring one term to two different maps, and so to two
different rates out of it (`DynamicWeights`).

On a term with finitely many redexes: the propensity of a key is the key's
weight times the sum over its redexes of their geometric factor and funding
gate. The total propensity sums all redexes. The weighted coalgebra sends a
configuration to the weights of its successors, summed over the redexes that
reach them. Unfunded redexes contribute nothing. Among the funded ones the
weights are those of the cost-free construction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent

universe uTerm uSite uEvent uKey uCtx uR

/-! ## Keyed presentations and weight maps -/

section Weights

variable {theory : GSLT.{uTerm}} (P : InteractionPresentation.{uSite, uEvent} theory)

/-- **Keys for the redexes of a presentation**: each rule (site) has its keys,
and every event has the key it satisfies. A classification is the same as a
partition of each rule's redexes (`Partition.classify_unique`). -/
structure Keyed where
  Key : P.Site → Type uKey
  classify : ∀ {rule : P.Site} {source target : theory.Term},
    P.Event rule source target → Key rule

variable {P}

/-- A weight map: a value for every key of every rule. -/
abbrev WeightMap (K : Keyed.{uTerm, uSite, uEvent, uKey} P) (R : Type uR) :=
  (Σ rule, K.Key rule) → R

/-- **Augmented rules.** Every key has an initial weight and an update of the
whole map, applied when a redex of that key fires; every redex has an address,
the contexts from the root to it, and every context has a geometric factor and
a fold of the map. -/
structure Augmented (K : Keyed.{uTerm, uSite, uEvent, uKey} P) (R : Type uR) where
  initial : WeightMap K R
  update : (Σ rule, K.Key rule) → WeightMap K R → WeightMap K R
  Context : Type uCtx
  address : ∀ {rule : P.Site} {source target : theory.Term},
    P.Event rule source target → List Context
  geometric : Context → R
  fold : Context → WeightMap K R → WeightMap K R

namespace Augmented

variable {K : Keyed.{uTerm, uSite, uEvent, uKey} P} {R : Type uR}
  (A : Augmented K R)

/-- The key of an event, as an index of weight maps. -/
def keyOf {rule : P.Site} {source target : theory.Term}
    (event : P.Event rule source target) : Σ rule, K.Key rule :=
  ⟨rule, K.classify event⟩

/-- The map after an event fires: its key's update, then the folds of its
contexts from the redex outwards. -/
def next {rule : P.Site} {source target : theory.Term}
    (event : P.Event rule source target) (map : WeightMap K R) : WeightMap K R :=
  (A.address event).foldr A.fold (A.update (keyOf event) map)

/-- The geometric factor of a redex: the product of the factors of its
contexts. -/
def geometricFactor [Monoid R] {rule : P.Site} {source target : theory.Term}
    (event : P.Event rule source target) : R :=
  ((A.address event).map A.geometric).prod

/-- When no context folds the map, the map after an event is its key's
update. -/
theorem next_of_folds_trivial (trivialFolds : ∀ context map, A.fold context map = map)
    {rule : P.Site} {source target : theory.Term} (event : P.Event rule source target)
    (map : WeightMap K R) : A.next event map = A.update (keyOf event) map := by
  unfold next
  induction A.address event with
  | nil => rfl
  | cons context rest ih => rw [List.foldr_cons, trivialFolds, ih]

/-- When every context factor is one, addressing is free. -/
theorem geometricFactor_of_trivial [Monoid R] (trivialFactors : ∀ context, A.geometric context = 1)
    {rule : P.Site} {source target : theory.Term} (event : P.Event rule source target) :
    A.geometricFactor event = 1 := by
  unfold geometricFactor
  induction A.address event with
  | nil => rfl
  | cons context rest ih => rw [List.map_cons, List.prod_cons, trivialFactors, ih, one_mul]

/-- **The weighted theory.** Configurations are terms with weight maps; a step
fires an event of a representative and rewrites the map. -/
def weightedTheory : GSLT where
  Term := theory.Term × WeightMap K R
  equations :=
    { r := fun first second => theory.Equiv first.1 second.1 ∧
        first.2 = second.2
      iseqv :=
        ⟨fun _ => ⟨theory.equations.iseqv.refl _, rfl⟩,
          fun related => ⟨theory.equations.iseqv.symm related.1, related.2.symm⟩,
          fun first second => ⟨theory.equations.iseqv.trans first.1 second.1,
            first.2.trans second.2⟩⟩ }
  rewrites source target :=
    ∃ (rule : P.Site) (from₀ to₀ : theory.Term)
      (event : P.Event rule from₀ to₀),
      theory.Equiv source.1 from₀ ∧
        theory.Equiv to₀ target.1 ∧ target.2 = A.next event source.2
  rewrites_resp_left := by
    rintro source source' target ⟨equal, sameMap⟩ ⟨rule, from₀, to₀, event, atSource, atTarget,
      updated⟩
    exact ⟨target, ⟨rule, from₀, to₀, event,
      theory.equations.iseqv.trans (theory.equations.iseqv.symm equal) atSource, atTarget,
      sameMap ▸ updated⟩, theory.equations.iseqv.refl _, rfl⟩
  rewrites_resp_right := by
    rintro source target target' ⟨rule, from₀, to₀, event, atSource, atTarget, updated⟩
      ⟨equal, sameMap⟩
    exact ⟨rule, from₀, to₀, event, atSource, theory.equations.iseqv.trans atTarget equal,
      sameMap ▸ updated⟩

/-- Every step of the weighted theory is a step of the base theory. -/
theorem base_step {source target : A.weightedTheory.Term}
    (step : A.weightedTheory.Step source target) : theory.Step source.1 target.1 := by
  obtain ⟨rule, from₀, to₀, event, atSource, atTarget, -⟩ := step
  obtain ⟨reached, stepReached, toReached⟩ :=
    theory.rewrites_resp_left (theory.equations.iseqv.symm atSource) (P.sound event)
  exact theory.rewrites_resp_right stepReached
    (theory.equations.iseqv.trans (theory.equations.iseqv.symm toReached) atTarget)

/-- Every event fires in the weighted theory, from any map. -/
theorem step_of_event {rule : P.Site} {source target : theory.Term}
    (event : P.Event rule source target) (map : WeightMap K R) :
    A.weightedTheory.Step (source, map) (target, A.next event map) :=
  ⟨rule, source, target, event, theory.equations.iseqv.refl _, theory.equations.iseqv.refl _, rfl⟩

end Augmented

/-! ## Reindexing keys -/

/-- A map of keys over the same presentation that respects classification. -/
structure KeyMap (K K' : Keyed.{uTerm, uSite, uEvent, uKey} P) where
  map : ∀ {rule : P.Site}, K.Key rule → K'.Key rule
  classify : ∀ {rule : P.Site} {source target : theory.Term}
    (event : P.Event rule source target), K'.classify event = map (K.classify event)

/-- Reindex a weight map along a map of keys: weigh a key by its image. -/
def KeyMap.reindex {K K' : Keyed.{uTerm, uSite, uEvent, uKey} P} (κ : KeyMap K K')
    {R : Type uR} (map : WeightMap K' R) : WeightMap K R :=
  fun key => map ⟨key.1, κ.map key.2⟩

/-- **Reindexing commutes with weighing**: an event weighs under a reindexed map
what it weighs under the original one. -/
theorem KeyMap.reindex_keyOf {K K' : Keyed.{uTerm, uSite, uEvent, uKey} P} (κ : KeyMap K K')
    {R : Type uR} (map : WeightMap K' R) {rule : P.Site} {source target : theory.Term}
    (event : P.Event rule source target) :
    κ.reindex map ⟨rule, K.classify event⟩ = map ⟨rule, K'.classify event⟩ := by
  rw [κ.classify event]
  rfl

end Weights

/-! ## Propensity, the funding gate and the weighted coalgebra -/

section Propensity

variable {theory : GSLT.{uTerm}} {P : InteractionPresentation.{uSite, uEvent} theory}
  {K : Keyed.{uTerm, uSite, uEvent, uKey} P} {R : Type uR} [Semiring R]
  (A : Augmented K R)

namespace Augmented

/-- The funding gate: one when the redex can be paid for, zero otherwise. -/
def gate (funded : ∀ {source : theory.Term}, P.Enabled source → Prop)
    [∀ {source : theory.Term} (redex : P.Enabled source), Decidable (funded redex)]
    {source : theory.Term} (redex : P.Enabled source) : R :=
  if funded redex then 1 else 0

variable (funded : ∀ {source : theory.Term}, P.Enabled source → Prop)
  [∀ {source : theory.Term} (redex : P.Enabled source), Decidable (funded redex)]

/-- The weight of one redex in a configuration: the weight of its key, its
geometric factor and its funding gate. -/
def redexWeight (map : WeightMap K R) {source : theory.Term} (redex : P.Enabled source) : R :=
  map (keyOf redex.evidence) * A.geometricFactor redex.evidence * gate funded redex

/-- **The propensity of a key** in a configuration: the key's weight times the
sum, over the redexes of that key (counted as distinct redexes, not up to
equations), of their geometric factor and funding gate. -/
def propensity [∀ source : theory.Term, Fintype (P.Enabled source)] [DecidableEq (Σ rule, K.Key rule)] (map : WeightMap K R) (source : theory.Term) (key : Σ rule, K.Key rule) : R :=
  map key * ∑ redex ∈ Finset.univ.filter (fun redex : P.Enabled source =>
      keyOf redex.evidence = key), A.geometricFactor redex.evidence * gate funded redex

/-- The total propensity: every redex, weighed. -/
def totalPropensity [∀ source : theory.Term, Fintype (P.Enabled source)] (map : WeightMap K R) (source : theory.Term) : R :=
  ∑ redex : P.Enabled source, A.redexWeight funded map redex

/-- The propensity of a key is the sum of the weights of its redexes. -/
theorem propensity_eq_sum [∀ source : theory.Term, Fintype (P.Enabled source)] [DecidableEq (Σ rule, K.Key rule)] (map : WeightMap K R) (source : theory.Term)
    (key : Σ rule, K.Key rule) :
    A.propensity funded map source key =
      ∑ redex ∈ Finset.univ.filter (fun redex : P.Enabled source => keyOf redex.evidence = key),
        A.redexWeight funded map redex := by
  unfold propensity redexWeight
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun redex member => ?_
  rw [(Finset.mem_filter.mp member).2, mul_assoc]

/-- **The total propensity is the sum of the propensities of the keys.** -/
theorem totalPropensity_eq_sum_propensity [∀ source : theory.Term, Fintype (P.Enabled source)] [DecidableEq (Σ rule, K.Key rule)]
    [Fintype (Σ rule, K.Key rule)] (map : WeightMap K R) (source : theory.Term) :
    A.totalPropensity funded map source =
      ∑ key : Σ rule, K.Key rule, A.propensity funded map source key := by
  simp only [propensity_eq_sum]
  unfold totalPropensity
  exact (Finset.sum_fiberwise Finset.univ (fun redex : P.Enabled source => keyOf redex.evidence)
    (A.redexWeight funded map)).symm

/-- **Unfunded redexes weigh nothing.** -/
theorem redexWeight_of_unfunded (map : WeightMap K R) {source : theory.Term}
    (redex : P.Enabled source) (unfunded : ¬ funded redex) :
    A.redexWeight funded map redex = 0 := by
  unfold redexWeight gate
  rw [if_neg unfunded, mul_zero]

/-- **Among funded redexes the weights are those without cost.** -/
theorem redexWeight_of_funded (map : WeightMap K R) {source : theory.Term}
    (redex : P.Enabled source) (isFunded : funded redex) :
    A.redexWeight funded map redex =
      map (keyOf redex.evidence) * A.geometricFactor redex.evidence := by
  unfold redexWeight gate
  rw [if_pos isFunded, mul_one]

/-- **Cost gates the support; weight distributes over it.** The total
propensity is the sum of the cost-free weights of the funded redexes. -/
theorem totalPropensity_eq_funded [∀ source : theory.Term, Fintype (P.Enabled source)] (map : WeightMap K R) (source : theory.Term) :
    A.totalPropensity funded map source =
      ∑ redex ∈ Finset.univ.filter (fun redex : P.Enabled source => funded redex),
        map (keyOf redex.evidence) * A.geometricFactor redex.evidence := by
  unfold totalPropensity
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun redex _ => ?_
  by_cases isFunded : funded redex
  · rw [if_pos isFunded, A.redexWeight_of_funded funded map redex isFunded]
  · rw [if_neg isFunded, A.redexWeight_of_unfunded funded map redex isFunded]

/-- **Exhaustion halts.** When no redex is funded, the total propensity is
zero. -/
theorem totalPropensity_of_exhausted [∀ source : theory.Term, Fintype (P.Enabled source)] (map : WeightMap K R) (source : theory.Term)
    (exhausted : ∀ redex : P.Enabled source, ¬ funded redex) :
    A.totalPropensity funded map source = 0 :=
  Finset.sum_eq_zero fun redex _ => A.redexWeight_of_unfunded funded map redex (exhausted redex)

/-- The configuration a redex leads to. -/
def successor (map : WeightMap K R) {source : theory.Term} (redex : P.Enabled source) :
    theory.Term × WeightMap K R :=
  (redex.target, A.next redex.evidence map)

/-- **The weighted coalgebra**: the weight of reaching a configuration, summed
over the redexes that reach it. -/
def coalgebra [∀ source : theory.Term, Fintype (P.Enabled source)] [DecidableEq (theory.Term × WeightMap K R)] (configuration : theory.Term × WeightMap K R)
    (successorConfiguration : theory.Term × WeightMap K R) : R :=
  ∑ redex ∈ Finset.univ.filter (fun redex : P.Enabled configuration.1 =>
      A.successor configuration.2 redex = successorConfiguration),
    A.redexWeight funded configuration.2 redex

/-- **The coalgebra distributes the total propensity over the successors.** -/
theorem coalgebra_sum [∀ source : theory.Term, Fintype (P.Enabled source)] [DecidableEq (theory.Term × WeightMap K R)]
    (configuration : theory.Term × WeightMap K R) :
    ∑ successorConfiguration ∈ Finset.univ.image
        (A.successor (source := configuration.1) configuration.2),
      A.coalgebra funded configuration successorConfiguration =
        A.totalPropensity funded configuration.2 configuration.1 := by
  unfold coalgebra totalPropensity
  exact Finset.sum_fiberwise_of_maps_to (fun redex _ => Finset.mem_image_of_mem _ (Finset.mem_univ redex))
    (A.redexWeight funded configuration.2)

end Augmented

end Propensity

/-! ## The common weighted resumption handler

A response carries the actual enabled event, including its occurrence evidence.
The continuation updates the whole configuration. This is the same free
operation and coefficient handler used by native evaluation; there is no
second sequencing or aggregation operation here. A funding gate can make a
coefficient zero without removing the event from this attachment observation.
Admission and completeness of a supplied catalogue are separate obligations.

Coefficient multiplication follows the declared context and execution order;
it need not commute. Stochastic rate interpretations impose their own order
and positivity hypotheses beyond this semiring-valued construction.
-/

section Resumptions

open Mettapedia.GSLT.Dynamics

variable {theory : GSLT.{uTerm}} {P : InteractionPresentation.{uSite, uEvent} theory}
  {K : Keyed.{uTerm, uSite, uEvent, uKey} P} {R : Type uR} [Semiring R]
  (A : Augmented K R)

namespace Augmented

variable (funded : ∀ {source : theory.Term}, P.Enabled source → Prop)
  [∀ {source : theory.Term} (redex : P.Enabled source), Decidable (funded redex)]

/-- Attach the configuration's coefficient to each supplied event occurrence. -/
def responses (catalogue : ∀ source : theory.Term, List (P.Enabled source))
    (configuration : theory.Term × WeightMap K R) :
    WeightedResumption.Contributions (P.Enabled configuration.1) R :=
  (catalogue configuration.1).map fun redex =>
    (redex, A.redexWeight funded configuration.2 redex)

/-- One presented step, followed by the actual configuration update. -/
def stepComputation (configuration : theory.Term × WeightMap K R) :
    ResumptionAlgebra.Computation (theory.Term × WeightMap K R)
      (fun current => P.Enabled current.1) (theory.Term × WeightMap K R) :=
  ResumptionAlgebra.perform configuration fun redex =>
    ResumptionAlgebra.pure (A.successor configuration.2 redex)

/-- The independently defined event update agrees with the free weighted fold. -/
theorem interpret_step (catalogue : ∀ source : theory.Term, List (P.Enabled source))
    (configuration : theory.Term × WeightMap K R) :
    WeightedResumption.interpret (A.responses funded catalogue)
        (A.stepComputation configuration) =
      (catalogue configuration.1).map fun redex =>
        (A.successor configuration.2 redex, A.redexWeight funded configuration.2 redex) := by
  rw [stepComputation, WeightedResumption.interpret_perform]
  simp only [WeightedResumption.interpret_pure]
  rw [WeightedResumption.sequence_map]
  simp only [responses, List.map_map, Function.comp_def]

/-- Every result retains a real event of the weighted theory. -/
theorem interpret_step_sound
    (catalogue : ∀ source : theory.Term, List (P.Enabled source))
    (configuration reached : theory.Term × WeightMap K R) (coefficient : R)
    (returned : (reached, coefficient) ∈
      WeightedResumption.interpret (A.responses funded catalogue)
        (A.stepComputation configuration)) :
    A.weightedTheory.Step configuration reached := by
  rw [A.interpret_step funded catalogue configuration] at returned
  obtain ⟨redex, _, same⟩ := List.mem_map.mp returned
  have target_eq : A.successor configuration.2 redex = reached := congrArg Prod.fst same
  rw [← target_eq]
  exact A.step_of_event redex.evidence configuration.2

/-- Zero coefficients remain occurrence contributions under attachment. -/
theorem unfunded_response_retained
    (catalogue : ∀ source : theory.Term, List (P.Enabled source))
    (configuration : theory.Term × WeightMap K R) (redex : P.Enabled configuration.1)
    (present : redex ∈ catalogue configuration.1) (unfunded : ¬ funded redex) :
    (redex, 0) ∈ A.responses funded catalogue configuration := by
  have zero := A.redexWeight_of_unfunded funded configuration.2 redex unfunded
  exact List.mem_map.mpr ⟨redex, present, by simp only [zero]⟩

/-- A recursive observer uses the full term and weight map at every open leaf.
The supplied return test declares the observation; it does not assert search
exhaustion. -/
def observe {Answer : Type*} (finished : theory.Term × WeightMap K R → Option Answer)
    (configuration : theory.Term × WeightMap K R) :
    ResumptionAlgebra.View (theory.Term × WeightMap K R)
      (fun current => P.Enabled current.1) Answer (theory.Term × WeightMap K R) :=
  match finished configuration with
  | some answer => .returned answer
  | none => .request configuration (A.successor configuration.2)

/-- A cut retains the configuration's changing map; continuing the cut uses
the same ordered coefficient multiplication as native weighted resumptions. -/
theorem interpret_unfold_add
    (catalogue : ∀ source : theory.Term, List (P.Enabled source))
    {Answer : Type*} (finished : theory.Term × WeightMap K R → Option Answer)
    (first second : Nat) (configuration : theory.Term × WeightMap K R) :
    WeightedResumption.interpret (A.responses funded catalogue)
        (ResumptionAlgebra.unfold (A.observe finished) (first + second) configuration) =
      WeightedResumption.sequence
        (WeightedResumption.interpret (A.responses funded catalogue)
          (ResumptionAlgebra.unfold (A.observe finished) first configuration))
        (fun leaf => WeightedResumption.interpret (A.responses funded catalogue)
          (ResumptionAlgebra.resume (A.observe finished) second leaf)) :=
  WeightedResumption.interpret_unfold_add _ _ _ _ _

variable [∀ source : theory.Term, Fintype (P.Enabled source)]

/-- One enumeration of all enabled event occurrences, each exactly once. -/
noncomputable def finiteCatalogue (source : theory.Term) : List (P.Enabled source) :=
  (Finset.univ : Finset (P.Enabled source)).val.toList

/-- The common additive readout is exactly the finite total propensity. -/
theorem total_interpret_step (configuration : theory.Term × WeightMap K R) :
    WeightedResumption.total
        (WeightedResumption.interpret (A.responses funded (finiteCatalogue (P := P)))
          (A.stepComputation configuration)) =
      A.totalPropensity funded configuration.2 configuration.1 := by
  rw [A.interpret_step funded (finiteCatalogue (P := P)) configuration]
  simp only [WeightedResumption.total, SemiringTraversal.weightSum,
    finiteCatalogue, List.map_map, Function.comp_def,
    Multiset.sum_map_toList, Finset.sum_map_val, totalPropensity]

/-- Aggregation at a successor is exactly the existing weighted coalgebra.
Equal successor values are summed after their event occurrences are retained. -/
theorem interpret_step_coalgebra [DecidableEq (theory.Term × WeightMap K R)]
    (configuration reached : theory.Term × WeightMap K R) :
    SemiringTraversal.weightSum
        (fun contribution => if contribution.1 = reached then contribution.2 else 0)
        (WeightedResumption.interpret (A.responses funded (finiteCatalogue (P := P)))
          (A.stepComputation configuration)) =
      A.coalgebra funded configuration reached := by
  rw [A.interpret_step funded (finiteCatalogue (P := P)) configuration]
  simp only [SemiringTraversal.weightSum, finiteCatalogue, List.map_map,
    Function.comp_def, Multiset.sum_map_toList, Finset.sum_map_val,
    coalgebra, Finset.sum_filter]

end Augmented

end Resumptions

/-! ## The uniform weighting -/

section Uniform

variable {theory : GSLT.{uTerm}} {P : InteractionPresentation.{uSite, uEvent} theory}
  (K : Keyed.{uTerm, uSite, uEvent, uKey} P) (R : Type uR) [Semiring R]

/-- **Uniform weights**: every key weighs one, nothing is updated or folded,
and addressing is free. -/
def uniform : Augmented K R where
  initial _ := 1
  update _ map := map
  Context := PEmpty
  address _ := []
  geometric _ := 1
  fold _ map := map

/-- In the uniformly weighted theory the map never changes. -/
theorem uniform_next {rule : P.Site} {source target : theory.Term}
    (event : P.Event rule source target) (map : WeightMap K R) :
    (uniform K R).next event map = map :=
  rfl

/-- **The uniform weighting gives back the base steps**: from the uniform map,
the weighted theory steps exactly where an event of an equal term does. -/
theorem uniform_step_iff (source target : theory.Term) :
    (uniform K R).weightedTheory.Step (source, (uniform K R).initial) (target, (uniform K R).initial) ↔
      ∃ (rule : P.Site) (from₀ to₀ : theory.Term) (_ : P.Event rule from₀ to₀),
        theory.Equiv source from₀ ∧ theory.Equiv to₀ target :=
  ⟨fun ⟨rule, from₀, to₀, event, atSource, atTarget, _⟩ => ⟨rule, from₀, to₀, event, atSource,
      atTarget⟩,
    fun ⟨rule, from₀, to₀, event, atSource, atTarget⟩ => ⟨rule, from₀, to₀, event, atSource,
      atTarget, rfl⟩⟩

variable [∀ source : theory.Term, Fintype (P.Enabled source)]

/-- **Under uniform weights every funded redex weighs one**, so the total
propensity of a term counts its funded redexes. -/
theorem uniform_totalPropensity
    (funded : ∀ {source : theory.Term}, P.Enabled source → Prop)
    [∀ {source : theory.Term} (redex : P.Enabled source), Decidable (funded redex)]
    (source : theory.Term) :
    (uniform K R).totalPropensity funded (uniform K R).initial source =
      ((Finset.univ.filter fun redex : P.Enabled source => funded redex).card : R) := by
  rw [Augmented.totalPropensity_eq_funded, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_congr rfl fun redex _ => ?_
  change (1 : R) * ((([] : List PEmpty).map fun _ => (1 : R)).prod) = 1
  simp

end Uniform

end Mettapedia.GSLT.Weighting
