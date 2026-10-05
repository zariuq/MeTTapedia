import Mettapedia.GSLT.Distinction.DemandStrategies
import Mettapedia.GSLT.Dynamics.OrderedDemand
import Mettapedia.Algebra.SharedCoefficientLedger
import Mettapedia.Algebra.OrderedProductCommutation

/-!
# Ordered sharing licences with production coefficients

`OrderedDemand` decides when eager evaluation, lazy sharing and resampling of
a bound computation agree on its ordered answer occurrences, effects and
faults.  Here every answer occurrence of the bound computation is a
**production**: a factor of `SharedCoefficientLedger` with an identity, its
value, and a semantic coefficient in a monoid (Boolean, count, tropical, PLN,
matrix or complex coefficients alike).  A use of the bound computation returns
the tuple of used values with the ledger of the productions it charges.

* **The rules** (`lazyUses`, `resampledUses`).  Sharing draws once and charges
  one production factor per shared occurrence (`answers_lazyUses`); every later
  use is a cached delivery with factor one (`deliveries_factor_one`).  A zero
  coefficient retains its occurrence: values and identities do not depend on
  coefficients (`lazyUses_recoefficient`, `resampledUses_recoefficient`).
  Equal values with different identities keep different factors: the run
  ledger of sharing is the list of all productions, one each
  (`runLedger_lazyUses`, `runLedger_lazyUses_valid_iff`).  Resampling draws
  again for every use; a draw is identified by the productions above it, so
  every resampled tuple charges `n` distinct factors (`resampled_tuple_valid`).
* **Production licences refine the ordered ones** (`forget_lazyUses`,
  `forget_eagerUses`, `forget_resampledUses`): forgetting coefficients and
  identities gives `OrderedDemand`'s traces.
* **Sharing against resampling.**  On ledgers they agree exactly with at most
  one use or no answer (`lazyUses_eq_resampledUses_iff`); a single pure answer
  used twice is licensed by the ordered law but not here.  On coefficients they
  agree exactly when, besides, a single answer's coefficient satisfies
  `c ^ n = c` (`coefficients_lazy_eq_resampled_iff`): Boolean coefficients do,
  counts and tropical costs do not.
* **Eager against lazy.**  On ledgers they agree exactly when the binding is
  used (`eagerUses_eq_lazyUses_iff`): an unused production is charged eagerly
  and never lazily.  On coefficients a single unused answer of coefficient one
  is also licensed (`coefficients_eager_eq_lazy_zero_iff`).
* **Noncommutative coefficients** (`MovesPast`).  Eager evaluation charges a
  bound production before the factors that precede its first demand; lazy
  evaluation charges it after them.  The two ledgers hold the same factors
  (`eager_lazy_ledger_perm`); their denotations agree exactly when the
  production commutes with the denotation of the preceding factors
  (`eager_eq_lazy_iff_commute_denote`, an instance of
  `Algebra.OrderedProductCommutation.prod_cons_eq_prod_concat_iff`), in
  particular when it commutes with every preceding factor
  (`eager_eq_lazy_of_movesPast`), and for one preceding factor exactly then
  (`eager_eq_lazy_single_iff`).
* **Coefficients are not observer weights** (`answers_coefficient_erasure`,
  `count_eq_unit_aggregate`).  `DemandStrategies.Weights` weigh the readings of
  an observer.  Annotating its draws with coefficients, the strategies'
  outcomes are the coefficient semantics with coefficients erased, so every
  weighted reading is read from the erasure; the bag reading is the count
  aggregate at unit coefficients.

Nothing here assumes image-finiteness or a real-valued metric: traces are finite
lists and coefficients live in an arbitrary monoid.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.ProductionLicences

open Mettapedia.GSLT.Dynamics.OrderedDemand
open Mettapedia.Algebra.SharedCoefficientLedger (Factor Ledger Valid denote identities)
open Mettapedia.GSLT.Dynamics.DemandAgreement (shareTuple)

variable {Id A B V W E F : Type}

/-! ## Traces: auxiliary laws -/

theorem Event.mapAnswer_mapAnswer (f : A → B) (g : B → W) (event : Event A E F) :
    (event.mapAnswer f).mapAnswer g = event.mapAnswer (g ∘ f) := by
  cases event <;> rfl

theorem map_mapAnswer_map (f : A → B) (g : B → W) (trace : Trace A E F) :
    (trace.map (Event.mapAnswer f)).map (Event.mapAnswer g) = trace.map (Event.mapAnswer (g ∘ f)) := by
  simp [Function.comp_def, Event.mapAnswer_mapAnswer]

theorem map_bindTrace (trace : Trace A E F) (next : A → Trace B E F) (f : B → W) :
    (bindTrace trace next).map (Event.mapAnswer f) =
      bindTrace trace fun value => (next value).map (Event.mapAnswer f) := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [Event.bind, Event.mapAnswer, ih]

theorem bindTrace_map_left (trace : Trace A E F) (f : A → B) (next : B → Trace W E F) :
    bindTrace (trace.map (Event.mapAnswer f)) next = bindTrace trace (next ∘ f) := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [Event.bind, Event.mapAnswer, ih]

theorem bindTrace_congr {trace : Trace A E F} {next next' : A → Trace B E F}
    (same : ∀ value ∈ answers trace, next value = next' value) :
    bindTrace trace next = bindTrace trace next' := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | answer value =>
          simp only [bindTrace_cons, Event.bind]
          rw [same value (by simp [answers_cons, Event.answer?]),
            ih fun later inside => same later (by simp [answers_cons, inside])]
      | effect committed =>
          simp only [bindTrace_cons, Event.bind]
          rw [ih fun later inside => same later (by simpa [answers_cons, Event.answer?] using inside)]
      | fault failure =>
          simp only [bindTrace_cons, Event.bind]
          rw [ih fun later inside => same later (by simpa [answers_cons, Event.answer?] using inside)]

/-- Without answers, composition keeps every event and only retypes it. -/
theorem bindTrace_of_answers_nil {trace : Trace A E F} (none : answers trace = [])
    (next : A → Trace B E F) (f : A → B) :
    bindTrace trace next = trace.map (Event.mapAnswer f) := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | answer value => simp [answers_cons, Event.answer?] at none
      | effect committed =>
          simp only [answers_cons, Event.answer?, Option.toList_none, List.nil_append] at none
          simp [Event.bind, Event.mapAnswer, ih none]
      | fault failure =>
          simp only [answers_cons, Event.answer?, Option.toList_none, List.nil_append] at none
          simp [Event.bind, Event.mapAnswer, ih none]

theorem answers_map_mapAnswer (trace : Trace A E F) (f : A → B) :
    answers (trace.map (Event.mapAnswer f)) = (answers trace).map f :=
  answers_map trace f

/-! ## Productions and uses -/

/-- The factor charged by a production drawn below the productions `path` (the
identities of the draws above it in one tuple). -/
def drawnAt (path : List Id) (production : Factor Id A V) : Factor (List Id × Id) A V :=
  ⟨(path, production.identity), production.dependency, production.coefficient⟩

/-- A use of the bound computation: the tuple of used values and the ledger of
the productions it charges. -/
abbrev Use (Id A V : Type) := List A × Ledger (List Id × Id) A V

/-- One draw shared by `n` uses: one production factor. -/
def sharedUse (n : ℕ) (production : Factor Id A V) : Use Id A V :=
  (List.replicate n production.dependency, [drawnAt [] production])

/-- **Eager**: the bound computation is drawn once before any use, and its
productions are charged whether or not they are used. -/
def eagerUses (n : ℕ) (bound : Trace (Factor Id A V) E F) : Trace (Use Id A V) E F :=
  bound.map (Event.mapAnswer (sharedUse n))

/-- **Lazy with sharing**: zero uses never draw; otherwise one draw, shared. -/
def lazyUses (n : ℕ) (bound : Trace (Factor Id A V) E F) : Trace (Use Id A V) E F :=
  if n = 0 then [.answer ([], [])] else eagerUses n bound

/-- Resampling below the draws `path`: every use draws again. -/
def resampledFrom : ℕ → List Id → Trace (Factor Id A V) E F → Trace (Use Id A V) E F
  | 0, _, _ => [.answer ([], [])]
  | n + 1, path, bound => bindTrace bound fun production =>
      (resampledFrom n (path ++ [production.identity]) bound).map
        (Event.mapAnswer fun use => (production.dependency :: use.1, drawnAt path production :: use.2))

/-- **Resampling**: every use draws again, charging its own productions. -/
def resampledUses (n : ℕ) (bound : Trace (Factor Id A V) E F) : Trace (Use Id A V) E F :=
  resampledFrom n [] bound

/-- The values of a production trace. -/
def values (bound : Trace (Factor Id A V) E F) : Trace A E F :=
  bound.map (Event.mapAnswer Factor.dependency)

/-- Forget the ledgers of uses. -/
def forget (trace : Trace (Use Id A V) E F) : Trace (List A) E F :=
  trace.map (Event.mapAnswer Prod.fst)

/-- The run ledger: the productions charged by every answer, in order. -/
def runLedger (trace : Trace (Use Id A V) E F) : Ledger (List Id × Id) A V :=
  (answers trace).flatMap Prod.snd

/-- The coefficient observation: each answer's values with the denotation of
its ledger. -/
def coefficients [Monoid V] (trace : Trace (Use Id A V) E F) : Trace (List A × V) E F :=
  trace.map (Event.mapAnswer fun use => (use.1, denote use.2))

/-! ## The rules -/

theorem answers_eagerUses (n : ℕ) (bound : Trace (Factor Id A V) E F) :
    answers (eagerUses n bound) = (answers bound).map (sharedUse n) :=
  answers_map bound (sharedUse n)

/-- **One production factor per shared occurrence.** -/
theorem answers_lazyUses {n : ℕ} (positive : n ≠ 0) (bound : Trace (Factor Id A V) E F) :
    answers (lazyUses n bound) = (answers bound).map (sharedUse n) := by
  rw [lazyUses, if_neg positive, answers_eagerUses]

/-- The per-use factors of a shared production: the drawing use charges its
coefficient, every later use is a cached delivery. -/
def useFactors [Monoid V] (n : ℕ) (production : Factor Id A V) : List V :=
  production.coefficient :: List.replicate (n - 1) 1

/-- **A cached delivery has factor one**: the per-use factors multiply to the
one production factor of the shared use. -/
theorem deliveries_factor_one [Monoid V] (n : ℕ) (production : Factor Id A V) :
    (useFactors n production).prod = denote (sharedUse n production).2 := by
  simp [useFactors, sharedUse, denote, drawnAt]

/-- **The run ledger of sharing holds every production once**, in order,
whatever the values: equal values with different identities keep different
factors. -/
theorem runLedger_lazyUses {n : ℕ} (positive : n ≠ 0) (bound : Trace (Factor Id A V) E F) :
    runLedger (lazyUses n bound) = (answers bound).map (drawnAt []) := by
  rw [runLedger, answers_lazyUses positive, List.flatMap_map]
  show ((answers bound).flatMap fun production => [drawnAt [] production]) = _
  induction answers bound with
  | nil => rfl
  | cons head rest ih => simp only [List.flatMap_cons, List.map_cons, ih]; rfl

theorem runLedger_lazyUses_valid_iff {n : ℕ} (positive : n ≠ 0) (bound : Trace (Factor Id A V) E F) :
    Valid (runLedger (lazyUses n bound)) ↔ (identities (answers bound)).Nodup := by
  rw [runLedger_lazyUses positive]
  have same : identities ((answers bound).map (drawnAt (A := A) (V := V) ([] : List Id))) =
      ((answers bound).map Factor.identity).map fun identity => (([] : List Id), identity) := by
    simp [identities, drawnAt, Function.comp_def]
  unfold Valid
  rw [same]
  constructor
  · exact List.Nodup.of_map _
  · exact fun distinct => distinct.map fun first second equal => (Prod.mk.inj equal).2

/-! ## Coefficients change no occurrence -/

/-- Change every coefficient. -/
def recoefficient (g : V → W) (production : Factor Id A V) : Factor Id A W :=
  ⟨production.identity, production.dependency, g production.coefficient⟩

/-- Change every coefficient of a use. -/
def recoefficientUse (g : V → W) (use : Use Id A V) : Use Id A W :=
  (use.1, use.2.map fun factor => ⟨factor.identity, factor.dependency, g factor.coefficient⟩)

theorem eagerUses_recoefficient (g : V → W) (n : ℕ) (bound : Trace (Factor Id A V) E F) :
    eagerUses n (bound.map (Event.mapAnswer (recoefficient g))) =
      (eagerUses n bound).map (Event.mapAnswer (recoefficientUse g)) := by
  simp only [eagerUses, map_mapAnswer_map]
  rfl

/-- **A zero coefficient retains its occurrence**: changing coefficients, to
zero or anything else, changes no value, identity or occurrence of sharing. -/
theorem lazyUses_recoefficient (g : V → W) (n : ℕ) (bound : Trace (Factor Id A V) E F) :
    lazyUses n (bound.map (Event.mapAnswer (recoefficient g))) =
      (lazyUses n bound).map (Event.mapAnswer (recoefficientUse g)) := by
  by_cases zero : n = 0
  · simp [lazyUses, zero, Event.mapAnswer, recoefficientUse]
  · simp only [lazyUses, if_neg zero]
    exact eagerUses_recoefficient g n bound

theorem resampledFrom_recoefficient (g : V → W) (n : ℕ) (path : List Id)
    (bound : Trace (Factor Id A V) E F) :
    resampledFrom n path (bound.map (Event.mapAnswer (recoefficient g))) =
      (resampledFrom n path bound).map (Event.mapAnswer (recoefficientUse g)) := by
  induction n generalizing path with
  | zero => simp [resampledFrom, Event.mapAnswer, recoefficientUse]
  | succ n ih =>
      simp only [resampledFrom]
      rw [bindTrace_map_left, map_bindTrace]
      apply bindTrace_congr
      intro production _
      simp only [Function.comp_apply, ih, map_mapAnswer_map]
      rfl

/-- Resampling, too, keeps every occurrence whatever the coefficients. -/
theorem resampledUses_recoefficient (g : V → W) (n : ℕ) (bound : Trace (Factor Id A V) E F) :
    resampledUses n (bound.map (Event.mapAnswer (recoefficient g))) =
      (resampledUses n bound).map (Event.mapAnswer (recoefficientUse g)) :=
  resampledFrom_recoefficient g n [] bound

/-! ## Production licences refine the ordered ones -/

theorem values_eq (bound : Trace (Factor Id A V) E F) :
    values bound = bound.map (Event.mapAnswer Factor.dependency) := rfl

theorem forget_eagerUses (n : ℕ) (bound : Trace (Factor Id A V) E F) :
    forget (eagerUses n bound) = eagerTrace n (values bound) := by
  simp only [forget, eagerUses, eagerTrace, values, map_mapAnswer_map]
  rfl

theorem forget_lazyUses (n : ℕ) (bound : Trace (Factor Id A V) E F) :
    forget (lazyUses n bound) = lazyTrace n (values bound) := by
  by_cases zero : n = 0
  · simp [forget, lazyUses, lazyTrace, zero, Event.mapAnswer]
  · simp only [lazyUses, lazyTrace, if_neg zero]
    exact forget_eagerUses n bound

theorem forget_resampledFrom (n : ℕ) (path : List Id) (bound : Trace (Factor Id A V) E F) :
    forget (resampledFrom n path bound) = resampledTrace n (values bound) := by
  induction n generalizing path with
  | zero => simp [forget, resampledFrom, resampledTrace, Event.mapAnswer]
  | succ n ih =>
      have left : forget (resampledFrom (n + 1) path bound) = bindTrace bound fun production =>
          (forget (resampledFrom n (path ++ [production.identity]) bound)).map
            (Event.mapAnswer (production.dependency :: ·)) := by
        simp only [forget, resampledFrom, map_bindTrace, map_mapAnswer_map]
        rfl
      have right : resampledTrace (n + 1) (values bound) = bindTrace bound fun production =>
          (resampledTrace n (values bound)).map (Event.mapAnswer (production.dependency :: ·)) := by
        simp only [resampledTrace, values, bindTrace_map_left]
        rfl
      rw [left, right]
      apply bindTrace_congr
      intro production _
      rw [ih]

/-- **Forgetting coefficients and identities gives the ordered traces.** -/
theorem forget_resampledUses (n : ℕ) (bound : Trace (Factor Id A V) E F) :
    forget (resampledUses n bound) = resampledTrace n (values bound) :=
  forget_resampledFrom n [] bound

theorem answers_values (bound : Trace (Factor Id A V) E F) :
    answers (values bound) = (answers bound).map Factor.dependency :=
  answers_map bound Factor.dependency

/-! ## Resampling a single production -/

/-- The ledger of a single production resampled `n` times below `path`. -/
def singleLedger (production : Factor Id A V) : ℕ → List Id → Ledger (List Id × Id) A V
  | 0, _ => []
  | n + 1, path => drawnAt path production :: singleLedger production n (path ++ [production.identity])

theorem resampledFrom_single (production : Factor Id A V) (n : ℕ) (path : List Id) :
    resampledFrom n path ([.answer production] : Trace (Factor Id A V) E F) =
      [.answer (List.replicate n production.dependency, singleLedger production n path)] := by
  induction n generalizing path with
  | zero => rfl
  | succ n ih =>
      simp only [resampledFrom, bindTrace_cons, Event.bind, bindTrace_nil, List.append_nil, ih]
      rfl

theorem singleLedger_length (production : Factor Id A V) (n : ℕ) (path : List Id) :
    (singleLedger production n path).length = n := by
  induction n generalizing path with
  | zero => rfl
  | succ n ih => simp [singleLedger, ih]

theorem denote_singleLedger [Monoid V] (production : Factor Id A V) (n : ℕ) (path : List Id) :
    denote (singleLedger production n path) = production.coefficient ^ n := by
  induction n generalizing path with
  | zero => simp [singleLedger, denote]
  | succ n ih =>
      have := ih (path ++ [production.identity])
      simp only [denote] at this
      simp [singleLedger, denote, drawnAt, this, pow_succ']

/-- Every factor of one resampled tuple is charged by a different draw. -/
theorem singleLedger_paths (production : Factor Id A V) (n : ℕ) (path : List Id) :
    (singleLedger production n path).map (fun factor => factor.identity.1.length) =
      (List.range n).map (path.length + ·) := by
  induction n generalizing path with
  | zero => rfl
  | succ n ih =>
      simp only [singleLedger, List.map_cons, ih, drawnAt, List.length_append, List.length_singleton]
      rw [List.range_succ_eq_map]
      simp [Function.comp_def, Nat.add_comm, Nat.add_left_comm]

/-- **A resampled tuple charges `n` distinct factors**: its draws sit at
different depths. -/
theorem resampled_tuple_valid (production : Factor Id A V) (n : ℕ) :
    Valid (singleLedger production n []) := by
  have depths := singleLedger_paths production n []
  simp only [List.length_nil, Nat.zero_add] at depths
  have distinct : ((singleLedger production n []).map fun factor => factor.identity.1.length).Nodup := by
    rw [depths, List.map_id']
    exact List.nodup_range
  unfold Valid identities
  exact List.Nodup.of_map (fun identity : List Id × Id => identity.1.length) (by
    simpa [List.map_map, Function.comp_def] using distinct)

/-! ## Sharing against resampling -/

private theorem single_of_discardable {bound : Trace (Factor Id A V) E F} {value : A}
    (single : values bound = [.answer value]) :
    ∃ production : Factor Id A V, bound = [.answer production] ∧ production.dependency = value := by
  match bound, single with
  | [.answer production], single =>
      simp only [values, List.map_cons, List.map_nil, Event.mapAnswer, List.cons.injEq,
        Event.answer.injEq, and_true] at single
      exact ⟨production, rfl, single⟩
  | [.effect _], single => simp [values, Event.mapAnswer] at single
  | [.fault _], single => simp [values, Event.mapAnswer] at single
  | [], single => simp [values] at single
  | _ :: _ :: _, single => simp [values] at single

theorem lazyUses_eq_resampledUses_of_none {n : ℕ} (bound : Trace (Factor Id A V) E F)
    (none : answers bound = []) :
    lazyUses n bound = resampledUses n bound := by
  cases n with
  | zero => rfl
  | succ n =>
      simp only [lazyUses, Nat.succ_ne_zero, if_false, eagerUses, resampledUses, resampledFrom]
      rw [bindTrace_of_answers_nil none _ (sharedUse (n + 1))]

theorem lazyUses_one (bound : Trace (Factor Id A V) E F) :
    lazyUses 1 bound = resampledUses 1 bound := by
  simp only [lazyUses, one_ne_zero, if_false, eagerUses, resampledUses, resampledFrom]
  rw [← bindTrace_map]
  rfl

/-- **Sharing and resampling agree on production ledgers exactly with at most
one use or no answer.**  The ordered law also licenses a single pure answer;
its ledgers still differ, one production against `n`. -/
theorem lazyUses_eq_resampledUses_iff (n : ℕ) (bound : Trace (Factor Id A V) E F) :
    lazyUses n bound = resampledUses n bound ↔ n ≤ 1 ∨ answers bound = [] := by
  constructor
  · intro same
    by_contra bad
    simp only [not_or] at bad
    obtain ⟨many, someAnswer⟩ := bad
    have ordered : lazyTrace n (values bound) = resampledTrace n (values bound) := by
      rw [← forget_lazyUses, ← forget_resampledUses, same]
    rcases (lazyTrace_eq_resampledTrace_iff n (values bound)).mp ordered with
      few | none | ⟨value, single⟩
    · exact many few
    · rw [answers_values] at none
      exact someAnswer (List.map_eq_nil_iff.mp none)
    · obtain ⟨production, rfl, _⟩ := single_of_discardable single
      have positive : n ≠ 0 := by omega
      rw [lazyUses, if_neg positive, resampledUses, resampledFrom_single] at same
      simp only [eagerUses, List.map_cons, List.map_nil, Event.mapAnswer, sharedUse, List.cons.injEq,
        Event.answer.injEq, Prod.mk.injEq, and_true] at same
      have lengths := congrArg List.length same.2
      rw [singleLedger_length] at lengths
      simp at lengths
      omega
  · rintro (few | none)
    · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · rfl
      · exact lazyUses_one bound
    · exact lazyUses_eq_resampledUses_of_none bound none

/-- **Sharing and resampling agree on coefficients** exactly with at most one
use, or no answer, or a single answer whose coefficient satisfies `c ^ n = c`. -/
theorem coefficients_lazy_eq_resampled_iff [Monoid V] (n : ℕ) (bound : Trace (Factor Id A V) E F) :
    coefficients (lazyUses n bound) = coefficients (resampledUses n bound) ↔
      n ≤ 1 ∨ answers bound = [] ∨
        ∃ production : Factor Id A V, bound = [.answer production] ∧
          production.coefficient ^ n = production.coefficient := by
  constructor
  · intro same
    by_cases few : n ≤ 1
    · exact Or.inl few
    have ordered : lazyTrace n (values bound) = resampledTrace n (values bound) := by
      have erased := congrArg (fun trace : Trace (List A × V) E F =>
        trace.map (Event.mapAnswer Prod.fst)) same
      simp only [coefficients, map_mapAnswer_map] at erased
      rw [← forget_lazyUses, ← forget_resampledUses]
      exact erased
    rcases (lazyTrace_eq_resampledTrace_iff n (values bound)).mp ordered with
      atMostOne | none | ⟨value, single⟩
    · exact absurd atMostOne few
    · rw [answers_values] at none
      exact Or.inr (Or.inl (List.map_eq_nil_iff.mp none))
    · obtain ⟨production, rfl, _⟩ := single_of_discardable single
      refine Or.inr (Or.inr ⟨production, rfl, ?_⟩)
      have positive : n ≠ 0 := by omega
      rw [lazyUses, if_neg positive, resampledUses, resampledFrom_single] at same
      simp only [coefficients, eagerUses, List.map_cons, List.map_nil, Event.mapAnswer, sharedUse,
        List.cons.injEq, Event.answer.injEq, Prod.mk.injEq, and_true, true_and] at same
      rw [denote_singleLedger] at same
      simpa [denote, drawnAt] using same.symm
  · rintro (few | none | ⟨production, rfl, power⟩)
    · rw [(lazyUses_eq_resampledUses_iff n bound).mpr (Or.inl few)]
    · rw [(lazyUses_eq_resampledUses_iff n bound).mpr (Or.inr none)]
    · by_cases zero : n = 0
      · subst zero
        rfl
      · rw [lazyUses, if_neg zero, resampledUses, resampledFrom_single]
        simp only [coefficients, eagerUses, List.map_cons, List.map_nil, Event.mapAnswer, sharedUse]
        rw [denote_singleLedger, power]
        simp [denote, drawnAt]

/-! ## Eager against lazy -/

/-- **Eager and lazy agree on production ledgers exactly when the binding is
used**: an unused production is charged eagerly and never lazily. -/
theorem eagerUses_eq_lazyUses_iff (n : ℕ) (bound : Trace (Factor Id A V) E F) :
    eagerUses n bound = lazyUses n bound ↔ 1 ≤ n := by
  constructor
  · intro same
    by_contra zero
    have zero : n = 0 := by omega
    subst zero
    simp only [lazyUses, if_true, eagerUses] at same
    match bound, same with
    | [.answer production], same =>
        simp [Event.mapAnswer, sharedUse] at same
    | [.effect _], same => simp [Event.mapAnswer] at same
    | [.fault _], same => simp [Event.mapAnswer] at same
    | [], same => simp at same
    | _ :: _ :: _, same => simp at same
  · intro positive
    rw [lazyUses, if_neg (by omega)]

/-- **With zero uses, eager and lazy agree on coefficients exactly for a
single answer of coefficient one**: discarding is licensed for a unit
production, and an unused zero production annihilates the eager account. -/
theorem coefficients_eager_eq_lazy_zero_iff [Monoid V] (bound : Trace (Factor Id A V) E F) :
    coefficients (eagerUses 0 bound) = coefficients (lazyUses 0 bound) ↔
      ∃ production : Factor Id A V, bound = [.answer production] ∧ production.coefficient = 1 := by
  simp only [lazyUses, if_true, coefficients, eagerUses, map_mapAnswer_map]
  constructor
  · intro same
    match bound, same with
    | [.answer production], same =>
        simp only [List.map_cons, List.map_nil, Event.mapAnswer, Function.comp_apply, sharedUse,
          List.replicate_zero, List.cons.injEq, Event.answer.injEq, Prod.mk.injEq, true_and,
          and_true] at same
        exact ⟨production, rfl, by simpa [denote, drawnAt] using same⟩
    | [.effect _], same => simp [Event.mapAnswer] at same
    | [.fault _], same => simp [Event.mapAnswer] at same
    | [], same => simp at same
    | _ :: _ :: _, same => simp at same
  · rintro ⟨production, rfl, unit⟩
    simp [Event.mapAnswer, sharedUse, denote, drawnAt, unit]

/-! ## Noncommutative coefficients -/

/-- Eager evaluation charges the bound production before the factors that
precede its first demand. -/
def eagerLedger (production : Factor Id A V) (preceding : Ledger (List Id × Id) A V) :
    Ledger (List Id × Id) A V :=
  drawnAt [] production :: preceding

/-- Lazy evaluation charges it at its first demand, after them. -/
def lazyLedger (production : Factor Id A V) (preceding : Ledger (List Id × Id) A V) :
    Ledger (List Id × Id) A V :=
  preceding ++ [drawnAt [] production]

/-- The two ledgers charge the same productions, once each. -/
theorem eager_lazy_ledger_perm (production : Factor Id A V) (preceding : Ledger (List Id × Id) A V) :
    (eagerLedger production preceding).Perm (lazyLedger production preceding) := by
  simpa [eagerLedger, lazyLedger] using (List.perm_append_singleton _ _).symm

/-- **The lawful condition for moving a production**: it commutes with every
factor it is moved past. -/
def MovesPast [Monoid V] (production : Factor Id A V) (preceding : Ledger (List Id × Id) A V) : Prop :=
  ∀ factor ∈ preceding, Commute production.coefficient factor.coefficient

/-- **The exact condition for moving a production**: eager and lazy charging agree
exactly when the production commutes with the denotation of the factors it is moved
past.  This is `Algebra.OrderedProductCommutation.prod_cons_eq_prod_concat_iff` on
the ledger's coefficients; `CausalGluing.Occurrences.account_tile_iff_commute` is the
same fact for a block of one occurrence. -/
theorem eager_eq_lazy_iff_commute_denote [Monoid V] (production : Factor Id A V)
    (preceding : Ledger (List Id × Id) A V) :
    denote (eagerLedger production preceding) = denote (lazyLedger production preceding) ↔
      Commute production.coefficient (denote preceding) :=
  Mettapedia.Algebra.OrderedProductCommutation.map_prod_cons_eq_concat_iff Factor.coefficient
    (drawnAt [] production) preceding

/-- `MovesPast` gives commutation with the whole denotation. -/
theorem MovesPast.commute_denote [Monoid V] {production : Factor Id A V}
    {preceding : Ledger (List Id × Id) A V} (lawful : MovesPast production preceding) :
    Commute production.coefficient (denote preceding) :=
  Commute.list_prod_right _ _ fun coefficient member => by
    obtain ⟨factor, inside, rfl⟩ := List.mem_map.mp member
    exact lawful factor inside

theorem eager_eq_lazy_of_movesPast [Monoid V] {production : Factor Id A V}
    {preceding : Ledger (List Id × Id) A V} (lawful : MovesPast production preceding) :
    denote (eagerLedger production preceding) = denote (lazyLedger production preceding) :=
  (eager_eq_lazy_iff_commute_denote production preceding).2 lawful.commute_denote

/-- For one preceding factor the condition is exact: it is the tile
`Algebra.OrderedProductCommutation.prod_pair_eq_iff_commute`. -/
theorem eager_eq_lazy_single_iff [Monoid V] (production : Factor Id A V)
    (factor : Factor (List Id × Id) A V) :
    denote (eagerLedger production [factor]) = denote (lazyLedger production [factor]) ↔
      Commute production.coefficient factor.coefficient :=
  Mettapedia.Algebra.OrderedProductCommutation.prod_pair_eq_iff_commute production.coefficient
    factor.coefficient

/-- In a commutative monoid every move is lawful. -/
theorem movesPast_of_comm {V : Type} [CommMonoid V] (production : Factor Id A V)
    (preceding : Ledger (List Id × Id) A V) : MovesPast production preceding :=
  fun factor _ => Commute.all production.coefficient factor.coefficient

/-! ## Coefficients are not observer weights -/

section Weights

open Mettapedia.GSLT.Distinction.DemandStrategies

variable {Computation : Type} [Monoid V]

/-- The draws with their coefficients erased. -/
def erasedDraw (coefficientDraw : Computation → Multiset (Option Bool × V)) :
    Computation → Multiset (Option Bool) :=
  fun computation => (coefficientDraw computation).map Prod.fst

/-- Each answer of the drawn computation is dropped, keeping its coefficient. -/
def coefficientDropped (bag : Multiset (Option Bool × V)) : Multiset (Outcome × V) :=
  bag.map fun drawn => (drawn.1.map fun _ => [], drawn.2)

/-- One draw used twice: one coefficient. -/
def coefficientShared (bag : Multiset (Option Bool × V)) : Multiset (Outcome × V) :=
  bag.map fun drawn => (drawn.1.map fun value => [value, value], drawn.2)

/-- Two independent draws: the coefficients multiply, first draw first. -/
def coefficientPairs (bag : Multiset (Option Bool × V)) : Multiset (Outcome × V) :=
  bag.bind fun first => bag.map fun second =>
    (first.1.bind fun left => second.1.map fun right => [left, right], first.2 * second.2)

/-- **The coefficient semantics of the strategies.** -/
def coefficientAnswers (coefficientDraw : Computation → Multiset (Option Bool × V)) :
    Strategy → Program Computation → Multiset (Outcome × V)
  | .eager, .discard computation => coefficientDropped (coefficientDraw computation)
  | .lazy, .discard _ => {(some [], 1)}
  | .resample, .discard _ => {(some [], 1)}
  | .eager, .copy computation => coefficientShared (coefficientDraw computation)
  | .lazy, .copy computation => coefficientShared (coefficientDraw computation)
  | .resample, .copy computation => coefficientPairs (coefficientDraw computation)
  | _, .unit => {(some [], 1)}
  | _, .forceThen computation => coefficientDropped (coefficientDraw computation)
  | _, .pairUp computation => coefficientPairs (coefficientDraw computation)
  | _, .shareUp computation => coefficientShared (coefficientDraw computation)

omit [Monoid V] in
theorem coefficientDropped_erase (bag : Multiset (Option Bool × V)) :
    (coefficientDropped bag).map Prod.fst = dropped (bag.map Prod.fst) := by
  simp [coefficientDropped, dropped, Multiset.map_map]

omit [Monoid V] in
theorem coefficientShared_erase (bag : Multiset (Option Bool × V)) :
    (coefficientShared bag).map Prod.fst = shared (bag.map Prod.fst) := by
  simp [coefficientShared, shared, Multiset.map_map]

theorem coefficientPairs_erase (bag : Multiset (Option Bool × V)) :
    (coefficientPairs bag).map Prod.fst = pairs (bag.map Prod.fst) := by
  simp [coefficientPairs, pairs, Multiset.map_bind, Multiset.bind_map, Multiset.map_map]

/-- **The named observation theorem.**  The outcomes the strategies give to the
weighted observer are the coefficient semantics with its coefficients erased.
`Weights` weigh readings of these outcomes; they are not the coefficients, and
no weighted reading sees a coefficient. -/
theorem answers_coefficient_erasure (coefficientDraw : Computation → Multiset (Option Bool × V))
    (strategy : Strategy) (program : Program Computation) :
    (coefficientAnswers coefficientDraw strategy program).map Prod.fst =
      DemandStrategies.answers (erasedDraw coefficientDraw) strategy program := by
  cases strategy <;> cases program <;>
    simp [coefficientAnswers, DemandStrategies.answers, erasedDraw, coefficientDropped_erase, coefficientShared_erase,
      coefficientPairs_erase]

omit [Monoid V] in
/-- Hence the weighted distance between two programs depends on coefficient
draws only through their erasure, for every choice of weights. -/
theorem answerDistance_of_erasure (first second : Computation → Multiset (Option Bool × V))
    (sameErasure : erasedDraw first = erasedDraw second) (weights : Weights) (strategy : Strategy)
    (left right : Program Computation) :
    answerDistance (erasedDraw first) weights strategy left right =
      answerDistance (erasedDraw second) weights strategy left right := by
  rw [sameErasure]

/-- The coefficient mass of one outcome: the sum of the coefficients of its
occurrences. -/
def aggregate {R : Type} [AddCommMonoid R] (bag : Multiset (Outcome × R)) (outcome : Outcome) : R :=
  ((bag.filter fun occurrence => occurrence.1 = outcome).map Prod.snd).sum

/-- Annotate every drawn outcome with coefficient one. -/
def unitDraw (draw : Computation → Multiset (Option Bool)) : Computation → Multiset (Option Bool × ℕ) :=
  fun computation => (draw computation).map fun outcome => (outcome, 1)

theorem coefficientAnswers_unitDraw (draw : Computation → Multiset (Option Bool))
    (strategy : Strategy) (program : Program Computation) :
    coefficientAnswers (unitDraw draw) strategy program =
      (DemandStrategies.answers draw strategy program).map fun outcome => (outcome, 1) := by
  cases strategy <;> cases program <;>
    simp [coefficientAnswers, DemandStrategies.answers, unitDraw, coefficientDropped, coefficientShared,
      coefficientPairs, dropped, shared, pairs, Multiset.map_map, Multiset.map_bind, Multiset.bind_map]

theorem aggregate_unit (bag : Multiset Outcome) (outcome : Outcome) :
    aggregate (bag.map fun occurrence => (occurrence, (1 : ℕ))) outcome = bag.count outcome := by
  unfold aggregate
  rw [Multiset.filter_map]
  simp only [Function.comp_def, Multiset.map_map, Multiset.map_const', Multiset.sum_replicate,
    smul_eq_mul, mul_one]
  rw [Multiset.count_eq_card_filter_eq]
  congr 1
  exact Multiset.filter_congr fun occurrence _ => eq_comm

/-- **The bag reading is the count aggregate at unit coefficients.** -/
theorem count_eq_unit_aggregate (draw : Computation → Multiset (Option Bool)) (strategy : Strategy)
    (program : Program Computation) (outcome : Outcome) :
    (bagReading draw strategy program).count outcome =
      aggregate (coefficientAnswers (unitDraw draw) strategy program) outcome := by
  rw [coefficientAnswers_unitDraw, aggregate_unit]
  rfl

end Weights

end Mettapedia.GSLT.Distinction.ProductionLicences
