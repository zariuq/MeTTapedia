import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeSyntax
import Mathlib.Data.String.Basic
import Mathlib.Tactic

/-!
# Canonical raw cost-rho forms

The executable matcher uses literal equality only after structural
normalization.  This module proves that the stable key sorter and the raw
normalizer are idempotent, closing the gap between nominal equivalence and
literal equality on runtime configurations.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-! ## Stable key sorting -/

def KeySorted {Alpha : Type} (key : Alpha → String) (items : List Alpha) : Prop :=
  items.Pairwise fun left right => key left ≤ key right

theorem mem_stableInsertBy {Alpha : Type} (before : Alpha → Alpha → Bool)
    (item target : Alpha) : ∀ items : List Alpha,
    target ∈ stableInsertBy before item items ↔ target = item ∨ target ∈ items
  | [] => by simp [stableInsertBy]
  | head :: tail => by
      simp only [stableInsertBy]
      split <;> simp [mem_stableInsertBy before item target tail, or_left_comm]

theorem stableInsertBy_keySorted {Alpha : Type} (key : Alpha → String)
    (item : Alpha) : ∀ items : List Alpha,
    KeySorted key items →
      KeySorted key
        (stableInsertBy (fun left right => decide (key left < key right)) item items)
  | [], _ => by simp [KeySorted, stableInsertBy]
  | head :: tail, sorted => by
      have source := (List.pairwise_cons.mp sorted)
      simp only [stableInsertBy]
      split <;> rename_i comparison
      · apply List.pairwise_cons.mpr
        refine ⟨?_, sorted⟩
        intro target member
        have item_before : key item < key head := of_decide_eq_true comparison
        rcases List.mem_cons.mp member with rfl | member
        · exact le_of_lt item_before
        · exact le_trans (le_of_lt item_before) (source.1 target member)
      · apply List.pairwise_cons.mpr
        refine ⟨?_, stableInsertBy_keySorted key item tail source.2⟩
        intro target member
        have not_before : ¬key item < key head := by simpa using comparison
        rw [mem_stableInsertBy] at member
        rcases member with rfl | member
        · exact le_of_not_gt not_before
        · exact source.1 target member

theorem foldl_stableInsertBy_keySorted {Alpha : Type} (key : Alpha → String) :
    ∀ (items accumulator : List Alpha),
      KeySorted key accumulator →
      KeySorted key
        (items.foldl (fun sorted item =>
          stableInsertBy (fun left right => decide (key left < key right))
            item sorted) accumulator)
  | [], _, sorted => sorted
  | item :: rest, accumulator, sorted =>
      foldl_stableInsertBy_keySorted key rest _
        (stableInsertBy_keySorted key item accumulator sorted)

theorem stableKeySort_keySorted {Alpha : Type} (key : Alpha → String)
    (items : List Alpha) : KeySorted key (stableKeySort key items) := by
  exact foldl_stableInsertBy_keySorted key items [] (by simp [KeySorted])

theorem stableInsertBy_eq_append_of_key_le {Alpha : Type}
    (key : Alpha → String) (item : Alpha) : ∀ items : List Alpha,
    (∀ existing ∈ items, key existing ≤ key item) →
      stableInsertBy (fun left right => decide (key left < key right)) item items =
        items ++ [item]
  | [], _ => rfl
  | head :: tail, bounded => by
      have head_le : key head ≤ key item := bounded head (by simp)
      have not_before : ¬key item < key head := not_lt_of_ge head_le
      have tail_bound : ∀ existing ∈ tail, key existing ≤ key item := by
        intro existing member
        exact bounded existing (by simp [member])
      simp only [stableInsertBy]
      split <;> rename_i comparison
      · exact (not_before (of_decide_eq_true comparison)).elim
      · simp only [List.cons_append, List.cons.injEq, true_and]
        exact stableInsertBy_eq_append_of_key_le key item tail tail_bound

theorem foldl_stableInsertBy_eq_append_of_keySorted {Alpha : Type}
    (key : Alpha → String) : ∀ (items accumulator : List Alpha),
    KeySorted key (accumulator ++ items) →
      items.foldl (fun sorted item =>
        stableInsertBy (fun left right => decide (key left < key right))
          item sorted) accumulator = accumulator ++ items
  | [], accumulator, _ => by simp
  | item :: rest, accumulator, sorted => by
      have split := List.pairwise_append.mp sorted
      have accumulator_before :
          ∀ existing ∈ accumulator, key existing ≤ key item := by
        intro existing member
        exact split.2.2 existing member item (by simp)
      have inserted :=
        stableInsertBy_eq_append_of_key_le key item accumulator accumulator_before
      have next_sorted : KeySorted key ((accumulator ++ [item]) ++ rest) := by
        simpa [List.append_assoc] using sorted
      simp only [List.foldl_cons, inserted]
      rw [foldl_stableInsertBy_eq_append_of_keySorted key rest
        (accumulator ++ [item]) next_sorted]
      simp [List.append_assoc]

theorem stableKeySort_eq_self_of_keySorted {Alpha : Type}
    (key : Alpha → String) {items : List Alpha} (sorted : KeySorted key items) :
    stableKeySort key items = items := by
  unfold stableKeySort stableSortBy
  simpa using
    foldl_stableInsertBy_eq_append_of_keySorted key items []
      (by simpa using sorted)

@[simp]
theorem stableKeySort_idempotent {Alpha : Type} (key : Alpha → String)
    (items : List Alpha) :
    stableKeySort key (stableKeySort key items) = stableKeySort key items :=
  stableKeySort_eq_self_of_keySorted key (stableKeySort_keySorted key items)

@[simp]
theorem RawCostSig.normalize_idempotent (sig : RawCostSig) :
    sig.normalize.normalize = sig.normalize := by
  exact stableKeySort_idempotent (fun atom : String => atom) sig

/-! ## Canonical parallel components -/

/-- Process components are precisely the non-unit, non-parallel constructors. -/
def RawCostProc.IsComponent : RawCostProc → Prop
  | .nil | .par _ _ => False
  | _ => True

/-- Term components are precisely the non-unit, non-parallel constructors. -/
def RawCostTerm.IsComponent : RawCostTerm → Prop
  | .nil | .par _ _ => False
  | _ => True

theorem RawCostProc.components_forall_isComponent :
    ∀ proc : RawCostProc, proc.components.Forall RawCostProc.IsComponent
  | .nil => by simp
  | .par left right => by
      simp only [RawCostProc.components, List.forall_append]
      exact ⟨RawCostProc.components_forall_isComponent left,
        RawCostProc.components_forall_isComponent right⟩
  | .send _ _ => by simp [RawCostProc.IsComponent]
  | .recv _ _ => by simp [RawCostProc.IsComponent]

theorem RawCostTerm.components_forall_isComponent :
    ∀ term : RawCostTerm, term.components.Forall RawCostTerm.IsComponent
  | .nil => by simp
  | .par left right => by
      simp only [RawCostTerm.components, List.forall_append]
      exact ⟨RawCostTerm.components_forall_isComponent left,
        RawCostTerm.components_forall_isComponent right⟩
  | .signed _ _ => by simp [RawCostTerm.IsComponent]
  | .drop _ => by simp [RawCostTerm.IsComponent]
  | .purse _ _ => by simp [RawCostTerm.IsComponent]

theorem RawCostProc.components_eq_singleton_of_isComponent
    {proc : RawCostProc} (component : proc.IsComponent) :
    proc.components = [proc] := by
  cases proc <;> simp_all [RawCostProc.IsComponent, RawCostProc.components]

theorem RawCostTerm.components_eq_singleton_of_isComponent
    {term : RawCostTerm} (component : term.IsComponent) :
    term.components = [term] := by
  cases term <;> simp_all [RawCostTerm.IsComponent, RawCostTerm.components]

theorem RawCostProc.components_fromComponents : ∀ items : List RawCostProc,
    items.Forall RawCostProc.IsComponent →
      (RawCostProc.fromComponents items).components = items
  | [], _ => rfl
  | [proc], components => by
      simpa [RawCostProc.fromComponents] using
        RawCostProc.components_eq_singleton_of_isComponent components
  | proc :: next :: rest, components => by
      obtain ⟨proc_component, tail_components⟩ :=
        (List.forall_cons RawCostProc.IsComponent proc (next :: rest)).mp components
      rw [RawCostProc.fromComponents, RawCostProc.components]
      rw [RawCostProc.components_eq_singleton_of_isComponent proc_component]
      rw [RawCostProc.components_fromComponents (next :: rest) tail_components]
      rfl

theorem RawCostTerm.components_fromComponents : ∀ items : List RawCostTerm,
    items.Forall RawCostTerm.IsComponent →
      (RawCostTerm.fromComponents items).components = items
  | [], _ => rfl
  | [term], components => by
      simpa [RawCostTerm.fromComponents] using
        RawCostTerm.components_eq_singleton_of_isComponent components
  | term :: next :: rest, components => by
      obtain ⟨term_component, tail_components⟩ :=
        (List.forall_cons RawCostTerm.IsComponent term (next :: rest)).mp components
      rw [RawCostTerm.fromComponents, RawCostTerm.components]
      rw [RawCostTerm.components_eq_singleton_of_isComponent term_component]
      rw [RawCostTerm.components_fromComponents (next :: rest) tail_components]
      rfl

theorem stableInsertBy_forall_normalization {Alpha : Type}
    (before : Alpha → Alpha → Bool) {predicate : Alpha → Prop}
    {item : Alpha} {items : List Alpha}
    (item_ok : predicate item) (items_ok : items.Forall predicate) :
    (stableInsertBy before item items).Forall predicate := by
  induction items with
  | nil => simpa [stableInsertBy] using item_ok
  | cons head tail ih =>
      obtain ⟨head_ok, tail_ok⟩ :=
        (List.forall_cons predicate head tail).mp items_ok
      simp only [stableInsertBy]
      split
      · exact (List.forall_cons predicate item (head :: tail)).mpr
          ⟨item_ok, (List.forall_cons predicate head tail).mpr ⟨head_ok, tail_ok⟩⟩
      · exact (List.forall_cons predicate head _).mpr
          ⟨head_ok, ih tail_ok⟩

theorem foldl_stableInsertBy_forall_normalization {Alpha : Type}
    (before : Alpha → Alpha → Bool) {predicate : Alpha → Prop} :
    ∀ (source accumulator : List Alpha),
      source.Forall predicate → accumulator.Forall predicate →
      (source.foldl (fun sorted item => stableInsertBy before item sorted)
        accumulator).Forall predicate
  | [], _, _, accumulator_ok => accumulator_ok
  | item :: rest, accumulator, source_ok, accumulator_ok => by
      obtain ⟨item_ok, rest_ok⟩ :=
        (List.forall_cons predicate item rest).mp source_ok
      exact foldl_stableInsertBy_forall_normalization before rest _ rest_ok
        (stableInsertBy_forall_normalization before item_ok accumulator_ok)

theorem stableKeySort_forall {Alpha : Type} (key : Alpha → String)
    {predicate : Alpha → Prop} {items : List Alpha}
    (items_ok : items.Forall predicate) :
    (stableKeySort key items).Forall predicate := by
  exact foldl_stableInsertBy_forall_normalization
    (fun left right => decide (key left < key right)) items [] items_ok (by simp)

@[simp]
theorem stableInsertBy_toMultiset {Alpha : Type}
    (before : Alpha → Alpha → Bool) (item : Alpha) : ∀ items : List Alpha,
    (stableInsertBy before item items : Multiset Alpha) =
      {item} + (items : Multiset Alpha)
  | [] => by simp [stableInsertBy]
  | head :: tail => by
      simp only [stableInsertBy]
      split
      · change ({item} + {head} + (tail : Multiset Alpha)) =
          {item} + ({head} + (tail : Multiset Alpha))
        ac_rfl
      · change ({head} +
            (stableInsertBy before item tail : Multiset Alpha)) =
          {item} + ({head} + (tail : Multiset Alpha))
        rw [stableInsertBy_toMultiset before item tail]
        ac_rfl

theorem foldl_stableInsertBy_toMultiset {Alpha : Type}
    (before : Alpha → Alpha → Bool) : ∀ source accumulator : List Alpha,
    ((source.foldl (fun sorted item => stableInsertBy before item sorted)
        accumulator : List Alpha) : Multiset Alpha) =
      (accumulator : Multiset Alpha) + (source : Multiset Alpha)
  | [], _ => by simp
  | item :: rest, accumulator => by
      rw [List.foldl_cons,
        foldl_stableInsertBy_toMultiset before rest
          (stableInsertBy before item accumulator)]
      simp only [stableInsertBy_toMultiset]
      rw [show ((item :: rest : List Alpha) : Multiset Alpha) =
        {item} + (rest : Multiset Alpha) by rfl]
      ac_rfl

@[simp]
theorem stableKeySort_toMultiset {Alpha : Type} (key : Alpha → String)
    (items : List Alpha) :
    (stableKeySort key items : Multiset Alpha) = (items : Multiset Alpha) := by
  simpa [stableKeySort, stableSortBy] using
    foldl_stableInsertBy_toMultiset
      (fun left right => decide (key left < key right)) items []

theorem RawCostProc.normalize_fromComponents : ∀ items : List RawCostProc,
    items.Forall RawCostProc.IsComponent →
    items.Forall (fun proc => proc.normalize = proc) →
    KeySorted RawCostProc.key items →
    (RawCostProc.fromComponents items).normalize =
      RawCostProc.fromComponents items
  | [], _, _, _ => rfl
  | [proc], components, fixed, _ => by
      simpa [RawCostProc.fromComponents] using fixed
  | proc :: next :: rest, components, fixed, sorted => by
      obtain ⟨proc_component, tail_components⟩ :=
        (List.forall_cons RawCostProc.IsComponent proc (next :: rest)).mp components
      obtain ⟨proc_fixed, tail_fixed⟩ :=
        (List.forall_cons (fun item : RawCostProc => item.normalize = item)
          proc (next :: rest)).mp fixed
      have tail_sorted : KeySorted RawCostProc.key (next :: rest) :=
        (List.pairwise_cons.mp sorted).2
      have tail_normalized := RawCostProc.normalize_fromComponents
        (next :: rest) tail_components tail_fixed tail_sorted
      rw [RawCostProc.fromComponents, RawCostProc.normalize, proc_fixed,
        tail_normalized]
      rw [RawCostProc.components_eq_singleton_of_isComponent proc_component]
      rw [RawCostProc.components_fromComponents (next :: rest) tail_components]
      simp only [List.singleton_append]
      rw [stableKeySort_eq_self_of_keySorted RawCostProc.key sorted]

theorem RawCostTerm.normalize_fromComponents : ∀ items : List RawCostTerm,
    items.Forall RawCostTerm.IsComponent →
    items.Forall (fun term => term.normalize = term) →
    KeySorted RawCostTerm.key items →
    (RawCostTerm.fromComponents items).normalize =
      RawCostTerm.fromComponents items
  | [], _, _, _ => rfl
  | [term], components, fixed, _ => by
      simpa [RawCostTerm.fromComponents] using fixed
  | term :: next :: rest, components, fixed, sorted => by
      obtain ⟨term_component, tail_components⟩ :=
        (List.forall_cons RawCostTerm.IsComponent term (next :: rest)).mp components
      obtain ⟨term_fixed, tail_fixed⟩ :=
        (List.forall_cons (fun item : RawCostTerm => item.normalize = item)
          term (next :: rest)).mp fixed
      have tail_sorted : KeySorted RawCostTerm.key (next :: rest) :=
        (List.pairwise_cons.mp sorted).2
      have tail_normalized := RawCostTerm.normalize_fromComponents
        (next :: rest) tail_components tail_fixed tail_sorted
      rw [RawCostTerm.fromComponents, RawCostTerm.normalize, term_fixed,
        tail_normalized]
      rw [RawCostTerm.components_eq_singleton_of_isComponent term_component]
      rw [RawCostTerm.components_fromComponents (next :: rest) tail_components]
      simp only [List.singleton_append]
      rw [stableKeySort_eq_self_of_keySorted RawCostTerm.key sorted]

/-- Normalizing a parallel presentation of already-normalized components
preserves its component multiset.  The executable order may change, but no
component is inserted, removed, or identified. -/
theorem RawCostTerm.normalize_fromComponents_toMultiset :
    ∀ (items : List RawCostTerm),
      items.Forall RawCostTerm.IsComponent →
      items.Forall (fun term => term.normalize = term) →
      ((RawCostTerm.fromComponents items).normalize.components :
          Multiset RawCostTerm) =
        (items : Multiset RawCostTerm) := by
  intro items components fixed
  induction items with
  | nil => rfl
  | cons head tail induction =>
      cases tail with
      | nil =>
          have headComponent :=
            (List.forall_cons RawCostTerm.IsComponent head []).mp components |>.1
          have headFixed :=
            (List.forall_cons (fun term : RawCostTerm => term.normalize = term)
              head []).mp fixed |>.1
          simp [RawCostTerm.fromComponents, headFixed,
            RawCostTerm.components_eq_singleton_of_isComponent headComponent]
      | cons next rest =>
          have headComponent :=
            (List.forall_cons RawCostTerm.IsComponent head (next :: rest)).mp
              components |>.1
          have tailComponents :=
            (List.forall_cons RawCostTerm.IsComponent head (next :: rest)).mp
              components |>.2
          have headFixed :=
            (List.forall_cons (fun term : RawCostTerm => term.normalize = term)
              head (next :: rest)).mp fixed |>.1
          have tailFixed :=
            (List.forall_cons (fun term : RawCostTerm => term.normalize = term)
              head (next :: rest)).mp fixed |>.2
          have tailMultiset := induction tailComponents tailFixed
          let sorted := stableKeySort RawCostTerm.key
            (head.normalize.components ++
              (RawCostTerm.fromComponents (next :: rest)).normalize.components)
          have sortedComponents : sorted.Forall RawCostTerm.IsComponent := by
            apply stableKeySort_forall
            rw [List.forall_append]
            exact ⟨RawCostTerm.components_forall_isComponent _,
              RawCostTerm.components_forall_isComponent _⟩
          change
            ((RawCostTerm.fromComponents sorted).components :
                Multiset RawCostTerm) = _
          rw [RawCostTerm.components_fromComponents sorted sortedComponents]
          rw [show (sorted : Multiset RawCostTerm) =
              ((head.normalize.components ++
                (RawCostTerm.fromComponents (next :: rest)).normalize.components :
                List RawCostTerm) : Multiset RawCostTerm) by
            exact stableKeySort_toMultiset _ _]
          rw [← Multiset.coe_add, headFixed,
            RawCostTerm.components_eq_singleton_of_isComponent headComponent,
            tailMultiset]
          rfl

/-! ## Idempotence of the mutually recursive syntax normalizer -/

/-- The strengthened process induction records componentwise canonicity. -/
structure RawCostProc.NormalizationResult (source : RawCostProc) : Prop where
  fixed : source.normalize.normalize = source.normalize
  components_fixed :
    source.normalize.components.Forall (fun proc => proc.normalize = proc)

/-- The strengthened term induction records componentwise canonicity. -/
structure RawCostTerm.NormalizationResult (source : RawCostTerm) : Prop where
  fixed : source.normalize.normalize = source.normalize
  components_fixed :
    source.normalize.components.Forall (fun term => term.normalize = term)

mutual
  @[simp]
  theorem RawCostName.normalize_idempotent : ∀ name : RawCostName,
      name.normalize.normalize = name.normalize
    | .bvar _ => rfl
    | .quote term => by
        have result := RawCostTerm.normalizationResult term
        have fixed := result.fixed
        simp only [RawCostName.normalize]
        generalize normalized_eq : term.normalize = normalized at fixed ⊢
        cases normalized with
        | nil => rfl
        | signed proc sig =>
            simp only [RawCostName.normalize, fixed]
        | par left right =>
            simp only [RawCostName.normalize, fixed]
        | drop name =>
            simp only [RawCostTerm.normalize] at fixed
            exact RawCostTerm.drop.inj fixed
        | purse location stack =>
            simp only [RawCostName.normalize, fixed]
    | .signature sig => by
        simp [RawCostName.normalize]

  theorem RawCostProc.normalizationResult : ∀ proc : RawCostProc,
      RawCostProc.NormalizationResult proc
    | .nil => ⟨rfl, by simp⟩
    | .par left right => by
        have left_result := RawCostProc.normalizationResult left
        have right_result := RawCostProc.normalizationResult right
        let items := stableKeySort RawCostProc.key
          (left.normalize.components ++ right.normalize.components)
        have items_components : items.Forall RawCostProc.IsComponent := by
          apply stableKeySort_forall
          rw [List.forall_append]
          exact ⟨RawCostProc.components_forall_isComponent left.normalize,
            RawCostProc.components_forall_isComponent right.normalize⟩
        have items_fixed :
            items.Forall (fun proc => proc.normalize = proc) := by
          apply stableKeySort_forall
          rw [List.forall_append]
          exact ⟨left_result.components_fixed,
            right_result.components_fixed⟩
        have items_sorted : KeySorted RawCostProc.key items :=
          stableKeySort_keySorted RawCostProc.key _
        have normalized_eq :
            (RawCostProc.par left right).normalize =
              RawCostProc.fromComponents items := rfl
        constructor
        · rw [normalized_eq]
          exact RawCostProc.normalize_fromComponents items items_components
            items_fixed items_sorted
        · rw [normalized_eq,
            RawCostProc.components_fromComponents items items_components]
          exact items_fixed
    | .send channel payload => by
        have channel_fixed := RawCostName.normalize_idempotent channel
        have payload_result := RawCostTerm.normalizationResult payload
        constructor <;>
          simp [RawCostProc.normalize, channel_fixed, payload_result.fixed]
    | .recv channel body => by
        have channel_fixed := RawCostName.normalize_idempotent channel
        have body_result := RawCostTerm.normalizationResult body
        constructor <;>
          simp [RawCostProc.normalize, channel_fixed, body_result.fixed]

  theorem RawCostTerm.normalizationResult : ∀ term : RawCostTerm,
      RawCostTerm.NormalizationResult term
    | .nil => ⟨rfl, by simp⟩
    | .signed proc sig => by
        have proc_result := RawCostProc.normalizationResult proc
        constructor <;>
          simp [RawCostTerm.normalize, proc_result.fixed]
    | .par left right => by
        have left_result := RawCostTerm.normalizationResult left
        have right_result := RawCostTerm.normalizationResult right
        let items := stableKeySort RawCostTerm.key
          (left.normalize.components ++ right.normalize.components)
        have items_components : items.Forall RawCostTerm.IsComponent := by
          apply stableKeySort_forall
          rw [List.forall_append]
          exact ⟨RawCostTerm.components_forall_isComponent left.normalize,
            RawCostTerm.components_forall_isComponent right.normalize⟩
        have items_fixed :
            items.Forall (fun term => term.normalize = term) := by
          apply stableKeySort_forall
          rw [List.forall_append]
          exact ⟨left_result.components_fixed,
            right_result.components_fixed⟩
        have items_sorted : KeySorted RawCostTerm.key items :=
          stableKeySort_keySorted RawCostTerm.key _
        have normalized_eq :
            (RawCostTerm.par left right).normalize =
              RawCostTerm.fromComponents items := rfl
        constructor
        · rw [normalized_eq]
          exact RawCostTerm.normalize_fromComponents items items_components
            items_fixed items_sorted
        · rw [normalized_eq,
            RawCostTerm.components_fromComponents items items_components]
          exact items_fixed
    | .drop name => by
        have name_fixed := RawCostName.normalize_idempotent name
        constructor <;> simp [RawCostTerm.normalize, name_fixed]
    | .purse location stack => by
        have location_fixed := RawCostName.normalize_idempotent location
        constructor <;>
          simp [RawCostTerm.normalize, location_fixed, List.map_map]
end

@[simp]
theorem RawCostProc.normalize_idempotent (proc : RawCostProc) :
    proc.normalize.normalize = proc.normalize :=
  (RawCostProc.normalizationResult proc).fixed

@[simp]
theorem RawCostTerm.normalize_idempotent (term : RawCostTerm) :
    term.normalize.normalize = term.normalize :=
  (RawCostTerm.normalizationResult term).fixed

/-- Every runtime configuration component is itself a canonical term. -/
theorem RawCostTerm.normalizeConfig_forall_normalized (term : RawCostTerm) :
    term.normalizeConfig.Forall (fun component => component.normalize = component) := by
  apply stableKeySort_forall
  exact (RawCostTerm.normalizationResult term).components_fixed

/-- Runtime configurations are ordered by the same key used by the matcher. -/
theorem RawCostTerm.normalizeConfig_keySorted (term : RawCostTerm) :
    KeySorted RawCostTerm.key term.normalizeConfig :=
  stableKeySort_keySorted RawCostTerm.key _

@[simp]
theorem RawCostTerm.normalizeConfig_normalize (term : RawCostTerm) :
    term.normalize.normalizeConfig = term.normalizeConfig := by
  simp [RawCostTerm.normalizeConfig]

/-- Canonicality is an intrinsic fixed-point property, not a runtime flag. -/
def RawCostTerm.Normalized (term : RawCostTerm) : Prop :=
  term.normalize = term

/-- Normalizing after COMM substitution produces a canonical contractum. -/
theorem RawCostTerm.commSubst_normalize_normalized
    (body payload : RawCostTerm) :
    (body.commSubst payload).normalize.Normalized := by
  exact RawCostTerm.normalize_idempotent _

/-- Every member presented to raw candidate enumeration is canonical. -/
theorem RawCostTerm.normalizeConfig_forall_Normalized (term : RawCostTerm) :
    term.normalizeConfig.Forall RawCostTerm.Normalized :=
  RawCostTerm.normalizeConfig_forall_normalized term

/-! ## Canonical decoding discipline -/

/-- Runtime signatures use their unique nondecreasing list representative. -/
def RawCostSig.EncodingCanonical (sig : RawCostSig) : Prop :=
  sig.Pairwise (· ≤ ·)

def RawCostStack.EncodingCanonical (stack : RawCostStack) : Prop :=
  stack.Forall RawCostSig.EncodingCanonical

mutual
  def RawCostName.EncodingCanonical : RawCostName → Prop
    | .bvar _ => True
    | .quote term => term.EncodingCanonical
    | .signature sig => sig.EncodingCanonical

  def RawCostProc.EncodingCanonical : RawCostProc → Prop
    | .nil => True
    | .par left right => left.EncodingCanonical ∧ right.EncodingCanonical
    | .send channel payload =>
        channel.EncodingCanonical ∧ payload.EncodingCanonical
    | .recv channel body =>
        channel.EncodingCanonical ∧ body.EncodingCanonical

  def RawCostTerm.EncodingCanonical : RawCostTerm → Prop
    | .nil => True
    | .signed proc sig => proc.EncodingCanonical ∧ sig.EncodingCanonical
    | .par left right => left.EncodingCanonical ∧ right.EncodingCanonical
    | .drop name => name.EncodingCanonical
    | .purse location stack =>
        location.EncodingCanonical ∧ stack.EncodingCanonical
end

theorem encodeCostSig_encodingCanonical (sig : CostSig String) :
    (encodeCostSig sig).EncodingCanonical := by
  exact Multiset.pairwise_sort (r := fun left right : String => left ≤ right) sig

mutual
  theorem encodeCostName_encodingCanonical :
      ∀ name : CostName String, (encodeCostName name).EncodingCanonical
    | .bvar _ => trivial
    | .quote term => encodeCostTerm_encodingCanonical term
    | .signature sig => encodeCostSig_encodingCanonical sig

  theorem encodeCostProc_encodingCanonical :
      ∀ proc : CostProc String, (encodeCostProc proc).EncodingCanonical
    | .nil => trivial
    | .par left right =>
        ⟨encodeCostProc_encodingCanonical left,
          encodeCostProc_encodingCanonical right⟩
    | .send channel payload =>
        ⟨encodeCostName_encodingCanonical channel,
          encodeCostTerm_encodingCanonical payload⟩
    | .recv channel body =>
        ⟨encodeCostName_encodingCanonical channel,
          encodeCostTerm_encodingCanonical body⟩

  theorem encodeCostTerm_encodingCanonical :
      ∀ term : CostTerm String, (encodeCostTerm term).EncodingCanonical
    | .nil => trivial
    | .signed proc sig =>
        ⟨encodeCostProc_encodingCanonical proc,
          encodeCostSig_encodingCanonical sig⟩
    | .par left right =>
        ⟨encodeCostTerm_encodingCanonical left,
          encodeCostTerm_encodingCanonical right⟩
    | .drop name => encodeCostName_encodingCanonical name
    | .purse location stack =>
        ⟨encodeCostName_encodingCanonical location,
          encodeCostStack_encodingCanonical stack⟩

  theorem encodeCostStack_encodingCanonical :
      ∀ stack : CostStack String, (encodeCostStack stack).EncodingCanonical
    | .empty => by simp [encodeCostStack, RawCostStack.EncodingCanonical]
    | .cons head tail => by
        simp only [encodeCostStack, RawCostStack.EncodingCanonical,
          List.forall_cons]
        exact ⟨encodeCostSig_encodingCanonical head,
          encodeCostStack_encodingCanonical tail⟩
end

theorem RawCostSig.normalize_encodingCanonical (sig : RawCostSig) :
    sig.normalize.EncodingCanonical := by
  exact stableKeySort_keySorted (fun atom : String => atom) sig

theorem RawCostStack.map_normalize_encodingCanonical :
    ∀ stack : RawCostStack,
      RawCostStack.EncodingCanonical (stack.map RawCostSig.normalize)
  | stack => by
      rw [RawCostStack.EncodingCanonical, List.forall_iff_forall_mem]
      intro normalized member
      obtain ⟨sig, _, rfl⟩ := List.mem_map.mp member
      exact RawCostSig.normalize_encodingCanonical sig

theorem RawCostProc.components_forall_encodingCanonical :
    ∀ {proc : RawCostProc}, proc.EncodingCanonical →
      proc.components.Forall RawCostProc.EncodingCanonical
  | .nil, _ => by simp
  | .par left right, canonical => by
      simp only [RawCostProc.EncodingCanonical] at canonical
      simp [RawCostProc.components,
        RawCostProc.components_forall_encodingCanonical canonical.1,
        RawCostProc.components_forall_encodingCanonical canonical.2]
  | .send channel payload, canonical => by
      simpa [RawCostProc.components] using canonical
  | .recv channel body, canonical => by
      simpa [RawCostProc.components] using canonical

theorem RawCostTerm.components_forall_encodingCanonical :
    ∀ {term : RawCostTerm}, term.EncodingCanonical →
      term.components.Forall RawCostTerm.EncodingCanonical
  | .nil, _ => by simp
  | .par left right, canonical => by
      simp only [RawCostTerm.EncodingCanonical] at canonical
      simp [RawCostTerm.components,
        RawCostTerm.components_forall_encodingCanonical canonical.1,
        RawCostTerm.components_forall_encodingCanonical canonical.2]
  | .signed proc sig, canonical => by
      simpa [RawCostTerm.components] using canonical
  | .drop name, canonical => by
      simpa [RawCostTerm.components] using canonical
  | .purse location stack, canonical => by
      simpa [RawCostTerm.components] using canonical

theorem RawCostProc.fromComponents_encodingCanonical :
    ∀ {items : List RawCostProc},
      items.Forall RawCostProc.EncodingCanonical →
        (RawCostProc.fromComponents items).EncodingCanonical
  | [], _ => by simp [RawCostProc.EncodingCanonical]
  | [proc], canonical => by
      simpa [RawCostProc.fromComponents] using canonical
  | proc :: next :: rest, canonical => by
      have canonical' := (List.forall_cons
        RawCostProc.EncodingCanonical proc (next :: rest)).mp canonical
      exact ⟨canonical'.1,
        RawCostProc.fromComponents_encodingCanonical canonical'.2⟩

theorem RawCostTerm.fromComponents_encodingCanonical :
    ∀ {items : List RawCostTerm},
      items.Forall RawCostTerm.EncodingCanonical →
        (RawCostTerm.fromComponents items).EncodingCanonical
  | [], _ => by simp [RawCostTerm.EncodingCanonical]
  | [term], canonical => by
      simpa [RawCostTerm.fromComponents] using canonical
  | term :: next :: rest, canonical => by
      have canonical' := (List.forall_cons
        RawCostTerm.EncodingCanonical term (next :: rest)).mp canonical
      exact ⟨canonical'.1,
        RawCostTerm.fromComponents_encodingCanonical canonical'.2⟩

mutual
  theorem RawCostName.normalize_encodingCanonical :
      ∀ name : RawCostName, name.normalize.EncodingCanonical
    | .bvar _ => trivial
    | .signature sig => RawCostSig.normalize_encodingCanonical sig
    | .quote term => by
        have term_canonical := RawCostTerm.normalize_encodingCanonical term
        simp only [RawCostName.normalize]
        generalize normalized_eq : term.normalize = normalized
          at term_canonical ⊢
        cases normalized with
        | nil => exact term_canonical
        | signed proc sig => exact term_canonical
        | par left right => exact term_canonical
        | drop name => exact term_canonical
        | purse location stack => exact term_canonical

  theorem RawCostProc.normalize_encodingCanonical :
      ∀ proc : RawCostProc, proc.normalize.EncodingCanonical
    | .nil => trivial
    | .par left right => by
        apply RawCostProc.fromComponents_encodingCanonical
        apply stableKeySort_forall
        rw [List.forall_append]
        exact ⟨RawCostProc.components_forall_encodingCanonical
            (RawCostProc.normalize_encodingCanonical left),
          RawCostProc.components_forall_encodingCanonical
            (RawCostProc.normalize_encodingCanonical right)⟩
    | .send channel payload =>
        ⟨RawCostName.normalize_encodingCanonical channel,
          RawCostTerm.normalize_encodingCanonical payload⟩
    | .recv channel body =>
        ⟨RawCostName.normalize_encodingCanonical channel,
          RawCostTerm.normalize_encodingCanonical body⟩

  theorem RawCostTerm.normalize_encodingCanonical :
      ∀ term : RawCostTerm, term.normalize.EncodingCanonical
    | .nil => trivial
    | .signed proc sig =>
        ⟨RawCostProc.normalize_encodingCanonical proc,
          RawCostSig.normalize_encodingCanonical sig⟩
    | .par left right => by
        apply RawCostTerm.fromComponents_encodingCanonical
        apply stableKeySort_forall
        rw [List.forall_append]
        exact ⟨RawCostTerm.components_forall_encodingCanonical
            (RawCostTerm.normalize_encodingCanonical left),
          RawCostTerm.components_forall_encodingCanonical
            (RawCostTerm.normalize_encodingCanonical right)⟩
    | .drop name => RawCostName.normalize_encodingCanonical name
    | .purse location stack =>
        ⟨RawCostName.normalize_encodingCanonical location,
          RawCostStack.map_normalize_encodingCanonical stack⟩
end

theorem RawCostTerm.normalizeConfig_forall_encodingCanonical
    (term : RawCostTerm) :
    term.normalizeConfig.Forall RawCostTerm.EncodingCanonical := by
  apply stableKeySort_forall
  exact RawCostTerm.components_forall_encodingCanonical
    (RawCostTerm.normalize_encodingCanonical term)

theorem RawCostSig.decode_injective_of_encodingCanonical
    {left right : RawCostSig}
    (left_canonical : left.EncodingCanonical)
    (right_canonical : right.EncodingCanonical)
    (decoded : decodeCostSig left = decodeCostSig right) : left = right := by
  exact (Multiset.coe_eq_coe.mp decoded).eq_of_pairwise'
    left_canonical right_canonical

theorem RawCostStack.decode_injective_of_encodingCanonical :
    ∀ {left right : RawCostStack},
      RawCostStack.EncodingCanonical left →
      RawCostStack.EncodingCanonical right →
      decodeCostStack left = decodeCostStack right → left = right
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, decoded => by simp [decodeCostStack] at decoded
  | _ :: _, [], _, _, decoded => by simp [decodeCostStack] at decoded
  | leftHead :: leftTail, rightHead :: rightTail,
      left_canonical, right_canonical, decoded => by
      have left_parts := (List.forall_cons RawCostSig.EncodingCanonical
        leftHead leftTail).mp left_canonical
      have right_parts := (List.forall_cons RawCostSig.EncodingCanonical
        rightHead rightTail).mp right_canonical
      have decoded_parts := CostStack.cons.inj decoded
      have head_eq := RawCostSig.decode_injective_of_encodingCanonical
        left_parts.1 right_parts.1 decoded_parts.1
      have tail_eq := RawCostStack.decode_injective_of_encodingCanonical
        left_parts.2 right_parts.2 decoded_parts.2
      rw [head_eq, tail_eq]

mutual
  theorem RawCostName.decode_injective_of_encodingCanonical
      {left right : RawCostName}
      (left_canonical : left.EncodingCanonical)
      (right_canonical : right.EncodingCanonical)
      (decoded : decodeCostName left = decodeCostName right) : left = right := by
    cases left <;> cases right <;>
      simp [decodeCostName] at decoded ⊢
    all_goals
      simp [RawCostName.EncodingCanonical] at left_canonical right_canonical
    · cases decoded
      rfl
    · exact RawCostTerm.decode_injective_of_encodingCanonical
        left_canonical right_canonical decoded
    · exact RawCostSig.decode_injective_of_encodingCanonical
        left_canonical right_canonical decoded

  theorem RawCostProc.decode_injective_of_encodingCanonical
      {left right : RawCostProc}
      (left_canonical : left.EncodingCanonical)
      (right_canonical : right.EncodingCanonical)
      (decoded : decodeCostProc left = decodeCostProc right) : left = right := by
    cases left <;> cases right <;>
      simp [decodeCostProc] at decoded ⊢
    all_goals
      simp [RawCostProc.EncodingCanonical] at left_canonical right_canonical
    · exact ⟨RawCostProc.decode_injective_of_encodingCanonical
          left_canonical.1 right_canonical.1 decoded.1,
        RawCostProc.decode_injective_of_encodingCanonical
          left_canonical.2 right_canonical.2 decoded.2⟩
    · exact ⟨RawCostName.decode_injective_of_encodingCanonical
          left_canonical.1 right_canonical.1 decoded.1,
        RawCostTerm.decode_injective_of_encodingCanonical
          left_canonical.2 right_canonical.2 decoded.2⟩
    · exact ⟨RawCostName.decode_injective_of_encodingCanonical
          left_canonical.1 right_canonical.1 decoded.1,
        RawCostTerm.decode_injective_of_encodingCanonical
          left_canonical.2 right_canonical.2 decoded.2⟩

  theorem RawCostTerm.decode_injective_of_encodingCanonical
      {left right : RawCostTerm}
      (left_canonical : left.EncodingCanonical)
      (right_canonical : right.EncodingCanonical)
      (decoded : decodeCostTerm left = decodeCostTerm right) : left = right := by
    cases left <;> cases right <;>
      simp [decodeCostTerm] at decoded ⊢
    all_goals
      simp [RawCostTerm.EncodingCanonical] at left_canonical right_canonical
    · exact ⟨RawCostProc.decode_injective_of_encodingCanonical
          left_canonical.1 right_canonical.1 decoded.1,
        RawCostSig.decode_injective_of_encodingCanonical
          left_canonical.2 right_canonical.2 decoded.2⟩
    · exact ⟨RawCostTerm.decode_injective_of_encodingCanonical
          left_canonical.1 right_canonical.1 decoded.1,
        RawCostTerm.decode_injective_of_encodingCanonical
          left_canonical.2 right_canonical.2 decoded.2⟩
    · exact RawCostName.decode_injective_of_encodingCanonical
        left_canonical right_canonical decoded
    · exact ⟨RawCostName.decode_injective_of_encodingCanonical
          left_canonical.1 right_canonical.1 decoded.1,
        RawCostStack.decode_injective_of_encodingCanonical
          left_canonical.2 right_canonical.2 decoded.2⟩
end

/-! ## Independent structural denotation -/

/-- Length framing keeps the denotation independent of parser punctuation. -/
def rawStructuralFrame (tag : String) (fields : List String) : String :=
  toString tag.length ++ ":" ++ tag ++
    String.join (fields.map fun field =>
      toString field.length ++ ":" ++ field)

/-- Canonical presentation of a multiplicity-preserving string multiset. -/
def rawStructuralMultisetFrame (tag : String) (items : Multiset String) : String :=
  rawStructuralFrame tag (items.sort (· ≤ ·))

/-- The term denotation keeps all top-level atoms and, separately, exactly the
top-level dequotable drops.  Both carriers are commutative multisets. -/
structure RawTermStructuralDenotation where
  atoms : Multiset String
  topDrops : Multiset String
  deriving DecidableEq

namespace RawTermStructuralDenotation

@[ext]
theorem ext {left right : RawTermStructuralDenotation}
    (atoms : left.atoms = right.atoms)
    (topDrops : left.topDrops = right.topDrops) : left = right := by
  cases left
  cases right
  simp_all

def empty : RawTermStructuralDenotation := ⟨0, 0⟩

def combine (left right : RawTermStructuralDenotation) :
    RawTermStructuralDenotation :=
  ⟨left.atoms + right.atoms, left.topDrops + right.topDrops⟩

/-- A term is dequotable exactly when its structural configuration contains
one atom and that atom is a drop. -/
def loneDrop? (denotation : RawTermStructuralDenotation) : Option String :=
  if denotation.atoms.card = 1 then
    match denotation.topDrops.sort (· ≤ ·) with
    | [name] => some name
    | _ => none
  else none

end RawTermStructuralDenotation

def RawCostStack.structuralFrames : RawCostStack → List String
  | [] => []
  | sig :: rest =>
      rawStructuralMultisetFrame "stack-cell" (sig : Multiset String) ::
        RawCostStack.structuralFrames rest

mutual
  /-- Independent algebraic denotation of raw names. -/
  def RawCostName.structuralDenote : RawCostName → String
    | .bvar index => rawStructuralFrame "bvar" [toString index]
    | .quote term =>
        let denotation := term.structuralDenote
        match denotation.loneDrop? with
        | some name => name
        | none => rawStructuralMultisetFrame "quote" denotation.atoms
    | .signature sig =>
        rawStructuralMultisetFrame "signature" (sig : Multiset String)

  /-- Independent algebraic denotation of process parallel composition. -/
  def RawCostProc.structuralDenote : RawCostProc → Multiset String
    | .nil => 0
    | .par left right => left.structuralDenote + right.structuralDenote
    | .send channel payload =>
        {rawStructuralFrame "send"
          [channel.structuralDenote,
            rawStructuralMultisetFrame "payload" payload.structuralDenote.atoms]}
    | .recv channel body =>
        {rawStructuralFrame "recv"
          [channel.structuralDenote,
            rawStructuralMultisetFrame "body" body.structuralDenote.atoms]}

  /-- Independent algebraic denotation of wrapped term composition. -/
  def RawCostTerm.structuralDenote : RawCostTerm → RawTermStructuralDenotation
    | .nil => .empty
    | .signed proc sig =>
        ⟨{rawStructuralFrame "signed"
            [rawStructuralMultisetFrame "proc" proc.structuralDenote,
              rawStructuralMultisetFrame "seal" (sig : Multiset String)]}, 0⟩
    | .par left right =>
        .combine left.structuralDenote right.structuralDenote
    | .drop name =>
        let denotedName := name.structuralDenote
        ⟨{rawStructuralFrame "drop" [denotedName]}, {denotedName}⟩
    | .purse location stack =>
        ⟨{rawStructuralFrame "purse"
            (location.structuralDenote :: stack.structuralFrames)}, 0⟩
end

/-- Structural name equivalence is equality in the independent denotation. -/
def RawCostName.StructurallyEquivalent (left right : RawCostName) : Prop :=
  left.structuralDenote = right.structuralDenote

/-- Structural process equivalence is equality in the free commutative
configuration denotation. -/
def RawCostProc.StructurallyEquivalent (left right : RawCostProc) : Prop :=
  left.structuralDenote = right.structuralDenote

/-- Structural term equivalence retains both multiplicity and dequotation
eligibility. -/
def RawCostTerm.StructurallyEquivalent (left right : RawCostTerm) : Prop :=
  left.structuralDenote = right.structuralDenote

instance RawCostName.instDecidableStructurallyEquivalent
    (left right : RawCostName) : Decidable (left.StructurallyEquivalent right) :=
  by unfold RawCostName.StructurallyEquivalent; infer_instance

instance RawCostProc.instDecidableStructurallyEquivalent
    (left right : RawCostProc) : Decidable (left.StructurallyEquivalent right) :=
  by unfold RawCostProc.StructurallyEquivalent; infer_instance

instance RawCostTerm.instDecidableStructurallyEquivalent
    (left right : RawCostTerm) : Decidable (left.StructurallyEquivalent right) :=
  by unfold RawCostTerm.StructurallyEquivalent; infer_instance

/-- Structural denotation counts one atom per flattened term component. -/
theorem RawCostTerm.structuralDenote_atoms_card : ∀ term : RawCostTerm,
    term.structuralDenote.atoms.card = term.components.length
  | .nil => by simp [RawCostTerm.structuralDenote,
      RawTermStructuralDenotation.empty, RawCostTerm.components]
  | .signed _ _ => by simp [RawCostTerm.structuralDenote, RawCostTerm.components]
  | .par left right => by
      simp [RawCostTerm.structuralDenote, RawTermStructuralDenotation.combine,
        RawCostTerm.components, RawCostTerm.structuralDenote_atoms_card left,
        RawCostTerm.structuralDenote_atoms_card right]
  | .drop _ => by simp [RawCostTerm.structuralDenote, RawCostTerm.components]
  | .purse _ _ => by simp [RawCostTerm.structuralDenote, RawCostTerm.components]

@[simp]
theorem RawCostSig.normalize_toMultiset (sig : RawCostSig) :
    (sig.normalize : Multiset String) = (sig : Multiset String) := by
  exact stableKeySort_toMultiset (fun atom : String => atom) sig

@[simp]
theorem RawCostStack.structuralFrames_map_normalize : ∀ stack : RawCostStack,
    RawCostStack.structuralFrames (stack.map RawCostSig.normalize) =
      stack.structuralFrames
  | [] => rfl
  | sig :: rest => by
      simp only [List.map_cons, RawCostStack.structuralFrames]
      rw [RawCostSig.normalize_toMultiset,
        RawCostStack.structuralFrames_map_normalize rest]

theorem RawCostProc.structuralDenote_components : ∀ proc : RawCostProc,
    (proc.components.map RawCostProc.structuralDenote).sum =
      proc.structuralDenote
  | .nil => by simp [RawCostProc.components, RawCostProc.structuralDenote]
  | .par left right => by
      simp [RawCostProc.components, RawCostProc.structuralDenote,
        RawCostProc.structuralDenote_components left,
        RawCostProc.structuralDenote_components right]
  | .send _ _ => by simp [RawCostProc.components, RawCostProc.structuralDenote]
  | .recv _ _ => by simp [RawCostProc.components, RawCostProc.structuralDenote]

theorem RawCostTerm.structuralAtoms_components : ∀ term : RawCostTerm,
    (term.components.map fun component =>
      component.structuralDenote.atoms).sum = term.structuralDenote.atoms
  | .nil => by simp [RawCostTerm.components, RawCostTerm.structuralDenote,
      RawTermStructuralDenotation.empty]
  | .signed _ _ => by simp [RawCostTerm.components, RawCostTerm.structuralDenote]
  | .par left right => by
      simp [RawCostTerm.components, RawCostTerm.structuralDenote,
        RawTermStructuralDenotation.combine,
        RawCostTerm.structuralAtoms_components left,
        RawCostTerm.structuralAtoms_components right]
  | .drop _ => by simp [RawCostTerm.components, RawCostTerm.structuralDenote]
  | .purse _ _ => by simp [RawCostTerm.components, RawCostTerm.structuralDenote]

theorem RawCostTerm.structuralDrops_components : ∀ term : RawCostTerm,
    (term.components.map fun component =>
      component.structuralDenote.topDrops).sum = term.structuralDenote.topDrops
  | .nil => by simp [RawCostTerm.components, RawCostTerm.structuralDenote,
      RawTermStructuralDenotation.empty]
  | .signed _ _ => by simp [RawCostTerm.components, RawCostTerm.structuralDenote]
  | .par left right => by
      simp [RawCostTerm.components, RawCostTerm.structuralDenote,
        RawTermStructuralDenotation.combine,
        RawCostTerm.structuralDrops_components left,
        RawCostTerm.structuralDrops_components right]
  | .drop _ => by simp [RawCostTerm.components, RawCostTerm.structuralDenote]
  | .purse _ _ => by simp [RawCostTerm.components, RawCostTerm.structuralDenote]

theorem RawCostProc.structuralDenote_fromComponents :
    ∀ items : List RawCostProc,
      (RawCostProc.fromComponents items).structuralDenote =
        (items.map RawCostProc.structuralDenote).sum
  | [] => by simp [RawCostProc.structuralDenote]
  | [proc] => by simp [RawCostProc.fromComponents]
  | proc :: next :: rest => by
      simp [RawCostProc.structuralDenote,
        RawCostProc.structuralDenote_fromComponents (next :: rest)]

theorem RawCostTerm.structuralDenote_fromComponents :
    ∀ items : List RawCostTerm,
      (RawCostTerm.fromComponents items).structuralDenote =
        ⟨(items.map fun term => term.structuralDenote.atoms).sum,
          (items.map fun term => term.structuralDenote.topDrops).sum⟩
  | [] => by
      simp [RawCostTerm.structuralDenote,
        RawTermStructuralDenotation.empty]
  | [term] => by simp [RawCostTerm.fromComponents]
  | term :: next :: rest => by
      rw [RawCostTerm.fromComponents, RawCostTerm.structuralDenote,
        RawCostTerm.structuralDenote_fromComponents (next :: rest)]
      rfl

theorem List.sum_map_stableKeySort {Alpha Beta : Type}
    [AddCommMonoid Beta] (key : Alpha → String) (measure : Alpha → Beta)
    (items : List Alpha) :
    ((stableKeySort key items).map measure).sum = (items.map measure).sum := by
  change ((stableKeySort key items : Multiset Alpha).map measure).sum =
    ((items : Multiset Alpha).map measure).sum
  rw [stableKeySort_toMultiset]

theorem RawCostTerm.fromComponents_eq_par_length_ge_two
    {items : List RawCostTerm} {left right : RawCostTerm}
    (components : items.Forall RawCostTerm.IsComponent)
    (shape : RawCostTerm.fromComponents items = .par left right) :
    2 ≤ items.length := by
  cases items with
  | nil => simp [RawCostTerm.fromComponents] at shape
  | cons first rest =>
      cases rest with
      | nil =>
          simp [RawCostTerm.fromComponents] at shape
          subst first
          simp [RawCostTerm.IsComponent] at components
      | cons second tail => simp

theorem RawCostTerm.fixed_par_components_length_ne_one
    {left right : RawCostTerm}
    (fixed : (RawCostTerm.par left right).normalize = .par left right) :
    (RawCostTerm.par left right).components.length ≠ 1 := by
  let items := stableKeySort RawCostTerm.key
    (left.normalize.components ++ right.normalize.components)
  have items_components : items.Forall RawCostTerm.IsComponent := by
    apply stableKeySort_forall
    rw [List.forall_append]
    exact ⟨RawCostTerm.components_forall_isComponent left.normalize,
      RawCostTerm.components_forall_isComponent right.normalize⟩
  have shape : RawCostTerm.fromComponents items = .par left right := by
    simpa [items, RawCostTerm.normalize] using fixed
  have at_least_two := RawCostTerm.fromComponents_eq_par_length_ge_two
    items_components shape
  have components_eq := RawCostTerm.components_fromComponents items items_components
  rw [shape] at components_eq
  rw [components_eq]
  omega

/-- The normal form exposes a lone dequotable drop syntactically; no hidden
parallel/unit presentation can remain. -/
theorem RawCostTerm.normalize_loneDrop? (term : RawCostTerm) :
    term.normalize.structuralDenote.loneDrop? =
      match term.normalize with
      | .drop name => some name.structuralDenote
      | _ => none := by
  have fixed := RawCostTerm.normalize_idempotent term
  generalize normalized_eq : term.normalize = normalized at fixed ⊢
  cases normalized with
  | nil =>
      simp [RawCostTerm.structuralDenote,
        RawTermStructuralDenotation.empty,
        RawTermStructuralDenotation.loneDrop?]
  | signed proc sig =>
      simp [RawCostTerm.structuralDenote,
        RawTermStructuralDenotation.loneDrop?]
  | par left right =>
      have length_ne := RawCostTerm.fixed_par_components_length_ne_one fixed
      have card_ne :
          (RawCostTerm.par left right).structuralDenote.atoms.card ≠ 1 := by
        simpa [RawCostTerm.structuralDenote_atoms_card] using length_ne
      simp [RawTermStructuralDenotation.loneDrop?, card_ne]
  | drop name =>
      simp [RawTermStructuralDenotation.loneDrop?, RawCostTerm.structuralDenote]
  | purse location stack =>
      simp [RawCostTerm.structuralDenote,
        RawTermStructuralDenotation.loneDrop?]

mutual
  /-- Name normalization is sound for the independent algebraic denotation. -/
  theorem RawCostName.structuralDenote_normalize : ∀ name : RawCostName,
      name.normalize.structuralDenote = name.structuralDenote
    | .bvar _ => rfl
    | .signature sig => by
        simp [RawCostName.structuralDenote]
    | .quote term => by
        have term_sound := RawCostTerm.structuralDenote_normalize term
        have exposed := RawCostTerm.normalize_loneDrop? term
        simp only [RawCostName.normalize]
        generalize normalized_eq : term.normalize = normalized at term_sound exposed ⊢
        cases normalized with
        | nil =>
            change RawCostTerm.nil.structuralDenote.loneDrop? = none at exposed
            change rawStructuralMultisetFrame "quote"
                RawCostTerm.nil.structuralDenote.atoms =
              match term.structuralDenote.loneDrop? with
              | some name => name
              | none => rawStructuralMultisetFrame "quote"
                  term.structuralDenote.atoms
            rw [← term_sound, exposed]
        | signed proc sig =>
            change (RawCostTerm.signed proc sig).structuralDenote.loneDrop? =
              none at exposed
            simp only [RawCostName.structuralDenote]
            rw [exposed]
            change rawStructuralMultisetFrame "quote"
                (RawCostTerm.signed proc sig).structuralDenote.atoms =
              match term.structuralDenote.loneDrop? with
              | some name => name
              | none => rawStructuralMultisetFrame "quote"
                  term.structuralDenote.atoms
            rw [← term_sound, exposed]
        | par left right =>
            change (RawCostTerm.par left right).structuralDenote.loneDrop? =
              none at exposed
            simp only [RawCostName.structuralDenote]
            rw [exposed]
            change rawStructuralMultisetFrame "quote"
                (RawCostTerm.par left right).structuralDenote.atoms =
              match term.structuralDenote.loneDrop? with
              | some name => name
              | none => rawStructuralMultisetFrame "quote"
                  term.structuralDenote.atoms
            rw [← term_sound, exposed]
        | drop denotedName =>
            change (RawCostTerm.drop denotedName).structuralDenote.loneDrop? =
              some denotedName.structuralDenote at exposed
            change denotedName.structuralDenote =
              match term.structuralDenote.loneDrop? with
              | some name => name
              | none => rawStructuralMultisetFrame "quote"
                  term.structuralDenote.atoms
            rw [← term_sound, exposed]
        | purse location stack =>
            change (RawCostTerm.purse location stack).structuralDenote.loneDrop? =
              none at exposed
            simp only [RawCostName.structuralDenote]
            rw [exposed]
            change rawStructuralMultisetFrame "quote"
                (RawCostTerm.purse location stack).structuralDenote.atoms =
              match term.structuralDenote.loneDrop? with
              | some name => name
              | none => rawStructuralMultisetFrame "quote"
                  term.structuralDenote.atoms
            rw [← term_sound, exposed]

  /-- Process normalization is sound for the independent algebraic
  denotation. -/
  theorem RawCostProc.structuralDenote_normalize : ∀ proc : RawCostProc,
      proc.normalize.structuralDenote = proc.structuralDenote
    | .nil => rfl
    | .send channel payload => by
        simp [RawCostProc.structuralDenote,
          RawCostName.structuralDenote_normalize channel,
          RawCostTerm.structuralDenote_normalize payload]
    | .recv channel body => by
        simp [RawCostProc.structuralDenote,
          RawCostName.structuralDenote_normalize channel,
          RawCostTerm.structuralDenote_normalize body]
    | .par left right => by
        rw [RawCostProc.normalize,
          RawCostProc.structuralDenote_fromComponents]
        rw [List.sum_map_stableKeySort RawCostProc.key
          RawCostProc.structuralDenote]
        simp only [List.map_append, List.sum_append]
        rw [RawCostProc.structuralDenote_components,
          RawCostProc.structuralDenote_components,
          RawCostProc.structuralDenote_normalize left,
          RawCostProc.structuralDenote_normalize right]
        rfl

  /-- Term normalization is sound for the independent algebraic denotation. -/
  theorem RawCostTerm.structuralDenote_normalize : ∀ term : RawCostTerm,
      term.normalize.structuralDenote = term.structuralDenote
    | .nil => rfl
    | .signed proc sig => by
        simp [RawCostTerm.structuralDenote,
          RawCostProc.structuralDenote_normalize proc]
    | .drop name => by
        simp [RawCostTerm.structuralDenote,
          RawCostName.structuralDenote_normalize name]
    | .purse location stack => by
        simp only [RawCostTerm.structuralDenote]
        rw [RawCostName.structuralDenote_normalize location]
        rw [RawCostStack.structuralFrames_map_normalize]
    | .par left right => by
        rw [RawCostTerm.normalize,
          RawCostTerm.structuralDenote_fromComponents]
        apply RawTermStructuralDenotation.ext
        · simp only
          rw [List.sum_map_stableKeySort RawCostTerm.key
            (fun term => term.structuralDenote.atoms)]
          simp only [List.map_append, List.sum_append]
          rw [RawCostTerm.structuralAtoms_components,
            RawCostTerm.structuralAtoms_components,
            RawCostTerm.structuralDenote_normalize left,
            RawCostTerm.structuralDenote_normalize right]
          rfl
        · simp only
          rw [List.sum_map_stableKeySort RawCostTerm.key
            (fun term => term.structuralDenote.topDrops)]
          simp only [List.map_append, List.sum_append]
          rw [RawCostTerm.structuralDrops_components,
            RawCostTerm.structuralDrops_components,
            RawCostTerm.structuralDenote_normalize left,
            RawCostTerm.structuralDenote_normalize right]
          rfl
end

/-- Every executable normalization step remains in the independently defined
name-equivalence class. -/
theorem RawCostName.normalize_structurallyEquivalent (name : RawCostName) :
    name.normalize.StructurallyEquivalent name :=
  RawCostName.structuralDenote_normalize name

/-- Every executable normalization step remains in the independently defined
process-equivalence class. -/
theorem RawCostProc.normalize_structurallyEquivalent (proc : RawCostProc) :
    proc.normalize.StructurallyEquivalent proc :=
  RawCostProc.structuralDenote_normalize proc

/-- Every executable normalization step remains in the independently defined
term-equivalence class. -/
theorem RawCostTerm.normalize_structurallyEquivalent (term : RawCostTerm) :
    term.normalize.StructurallyEquivalent term :=
  RawCostTerm.structuralDenote_normalize term


end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
