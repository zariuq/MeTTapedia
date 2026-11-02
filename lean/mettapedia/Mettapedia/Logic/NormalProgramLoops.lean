import Mettapedia.Logic.ClarkCompletion
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Sublists

/-!
# Loop formulas for finite ground normal programs

Loops use positive-length paths in the induced dependency graph, including a
self-edge for a singleton. The executable test uses finite predecessor-closed
subsets; it is proved equivalent to this path definition. Loop formulas require
external support, including selected base facts, and strengthen completion to
the Gelfond–Lifschitz stable-model semantics.

The dependency relation is the existing body-to-head convention. Reversing
all edges preserves the loop condition. Reference: the corrected Lin–Zhao
account, https://cse.hkust.edu.hk/faculty/flin/papers/assat-aij-revised.pdf.
Enumerating vertex subsets can be exponential; no scalability bound is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.NormalProgramLoops

open LP BDDCore NormalProgramSemantics ClarkCompletion PropositionalTseitin
open LO.Propositional (Formula)

namespace FiniteLoops

variable {A : Type*} [DecidableEq A]

def inside (R : A → A → Prop) (L : Finset A) (a b : A) : Prop := a ∈ L ∧ b ∈ L ∧ R a b

def IsLoop (R : A → A → Prop) (L : Finset A) : Prop :=
  L.Nonempty ∧ ∀ a ∈ L, ∀ b ∈ L, Relation.TransGen (inside R L) a b

def PredClosed (R : A → A → Prop) (L C : Finset A) : Prop :=
  ∀ a ∈ L, ∀ b ∈ C, R a b → a ∈ C

theorem predClosed_path {R : A → A → Prop} {L C : Finset A} (closed : PredClosed R L C)
    {a b : A} (path : Relation.ReflTransGen (inside R L) a b) : b ∈ C → a ∈ C := by
  induction path with
  | refl => exact id
  | @tail b c path edge ih => exact fun member => ih (closed _ edge.1 _ member edge.2.2)

/-- Positive strong connectivity is characterized by closed cuts and one internal edge. -/
theorem loop_iff_cuts (R : A → A → Prop) (L : Finset A) : IsLoop R L ↔
    L.Nonempty ∧ (∃ a ∈ L, ∃ b ∈ L, R a b) ∧
      ∀ C ⊆ L, C.Nonempty → PredClosed R L C → C = L := by
  classical
  constructor
  · rintro ⟨nonempty, connected⟩
    refine ⟨nonempty, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := nonempty
      obtain ⟨b, _, edge⟩ := Relation.TransGen.tail'_iff.mp (connected a ha a ha)
      exact ⟨b, edge.1, a, ha, edge.2.2⟩
    · intro C subset inhabited closed
      obtain ⟨b, hb⟩ := inhabited
      apply Finset.Subset.antisymm subset
      intro a ha
      exact predClosed_path closed (connected a ha b (subset hb)).to_reflTransGen hb
  · rintro ⟨nonempty, ⟨u, hu, v, hv, edge⟩, cuts⟩
    have reachable : ∀ a ∈ L, ∀ b ∈ L, Relation.ReflTransGen (inside R L) a b := by
      intro a ha b hb
      let C := L.filter fun c => Relation.ReflTransGen (inside R L) c b
      have subset : C ⊆ L := Finset.filter_subset _ _
      have inhabited : C.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, .refl⟩⟩
      have closed : PredClosed R L C := by
        intro c hc d hd hcd
        obtain ⟨hdL, path⟩ := Finset.mem_filter.mp hd
        exact Finset.mem_filter.mpr ⟨hc, path.head ⟨hc, hdL, hcd⟩⟩
      have equal := cuts C subset inhabited closed
      have member : a ∈ C := equal.symm ▸ ha
      exact (Finset.mem_filter.mp member).2
    refine ⟨nonempty, fun a ha b hb => ?_⟩
    exact (Relation.TransGen.tail' (reachable a ha u hu) ⟨hu, hv, edge⟩).trans_left (reachable v hv b hb)

theorem loop_reverse (R : A → A → Prop) (L : Finset A) :
    IsLoop (Function.swap R) L ↔ IsLoop R L := by
  have reversed : inside (Function.swap R) L = Function.swap (inside R L) := by
    funext a b
    exact propext (by simp [inside, Function.swap, and_comm, and_left_comm, and_assoc])
  simp only [IsLoop, reversed, Relation.transGen_swap]
  exact and_congr_right fun _ => ⟨fun h a ha b hb => h b hb a ha, fun h a ha b hb => h b hb a ha⟩

instance predClosedDecidable (R : A → A → Prop) [DecidableRel R] (L C : Finset A) :
    Decidable (PredClosed R L C) := by unfold PredClosed; infer_instance

/-- A finite structural test; no transitive-closure oracle is used by the implementation. -/
def check (R : A → A → Prop) [DecidableRel R] (L : Finset A) : Bool :=
  decide (L.Nonempty ∧ (∃ a ∈ L, ∃ b ∈ L, R a b) ∧
    ∀ C ∈ L.powerset, C.Nonempty → PredClosed R L C → C = L)

theorem check_correct (R : A → A → Prop) [DecidableRel R] (L : Finset A) :
    check R L = true ↔ IsLoop R L := by
  simp only [check, decide_eq_true_eq, loop_iff_cuts, Finset.mem_powerset]

/-- A finite set with an incoming edge at every vertex contains a predecessor-closed loop. -/
theorem exists_closed_loop (R : A → A → Prop) (U : Finset A) (nonempty : U.Nonempty)
    (incoming : ∀ a ∈ U, ∃ b ∈ U, R b a) :
    ∃ L, L ⊆ U ∧ IsLoop R L ∧ PredClosed R U L := by
  classical
  let candidates := U.powerset.filter fun C => C.Nonempty ∧ PredClosed R U C
  have candidate : U ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset_self U, nonempty, fun _ member _ _ _ => member⟩
  obtain ⟨L, member, minimal⟩ := candidates.exists_min_image Finset.card ⟨U, candidate⟩
  obtain ⟨subset, inhabited, closed⟩ := Finset.mem_filter.mp member
  have subset : L ⊆ U := Finset.mem_powerset.mp subset
  refine ⟨L, subset, (loop_iff_cuts R L).mpr ⟨inhabited, ?_, ?_⟩, closed⟩
  · obtain ⟨a, ha⟩ := inhabited
    obtain ⟨b, hb, edge⟩ := incoming a (subset ha)
    exact ⟨b, closed b hb a ha edge, a, ha, edge⟩
  · intro C subC nonemptyC closedC
    have closedU : PredClosed R U C := by
      intro a ha b hb edge
      exact closedC a (closed a ha b (subC hb) edge) b hb edge
    have memberC : C ∈ candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (subC.trans subset), nonemptyC, closedU⟩
    exact Finset.eq_of_subset_of_card_le subC (minimal C memberC)

end FiniteLoops

variable {σ : LPSignature} [DecidableEq (GroundAtom σ)]

abbrev IsLoop (rules : List (NormalClause σ)) (L : Finset (GroundAtom σ)) : Prop :=
  FiniteLoops.IsLoop (PositiveDependency rules) L

def ExternalRule (L : Finset (GroundAtom σ)) (c : NormalClause σ) : Prop :=
  c.head ∈ L ∧ ∀ a ∈ positiveBody c, a ∉ L

def ExternalSupport (rules : List (NormalClause σ)) (base S : Set (GroundAtom σ))
    (L : Finset (GroundAtom σ)) : Prop :=
  (∃ a ∈ L, a ∈ base) ∨ ∃ c ∈ rules, ExternalRule L c ∧ normalClauseBodyHolds c S S

def LoopSatisfied (rules : List (NormalClause σ)) (base S : Set (GroundAtom σ))
    (L : Finset (GroundAtom σ)) : Prop :=
  (∃ a ∈ L, a ∈ S) → ExternalSupport rules base S L

/-- Every nonempty true part of a stable model has external support; loophood is unnecessary here. -/
theorem stable_external {rules : List (NormalClause σ)} {base S : Set (GroundAtom σ)}
    (stable : StableModel rules base S) (L : Finset (GroundAtom σ)) : LoopSatisfied rules base S L := by
  classical
  rintro ⟨a, inL, inS⟩
  by_contra unsupported
  have supported := stable_supported stable
  have closed : T_normal_orderHom rules base S (S \ (L : Set (GroundAtom σ))) ⊆ S \ (L : Set (GroundAtom σ)) := by
    rintro b (hb | ⟨c, hc, rfl, body⟩)
    · exact ⟨supported.subset (Or.inl hb), fun hL => unsupported (Or.inl ⟨b, hL, hb⟩)⟩
    · obtain ⟨enabled, positives⟩ := (body_iff c _ S).mp body
      have bodyS : normalClauseBodyHolds c S S :=
        (body_iff c S S).mpr ⟨enabled, fun b hb => (positives b hb).1⟩
      refine ⟨supported.subset (Or.inr ⟨c, hc, rfl, bodyS⟩), fun headL => ?_⟩
      exact unsupported (Or.inr ⟨c, hc, ⟨headL, fun b hb => (positives b hb).2⟩, bodyS⟩)
  have below := OrderHom.lfp_le (T_normal_orderHom rules base S) closed
  have contained : S ⊆ S \ (L : Set (GroundAtom σ)) := ((stable_iff rules base S).mp stable).subset.trans below
  exact (contained inS).2 inL

/-- A completion model that is not stable contains a true loop with no external support. -/
theorem unsupported_loop {rules : List (NormalClause σ)} {base S : Set (GroundAtom σ)}
    (supported : SupportedModel rules base S) (notStable : ¬ StableModel rules base S) :
    ∃ L : Finset (GroundAtom σ), (↑L : Set (GroundAtom σ)) ⊆ S ∧ IsLoop rules L ∧
      ¬ ExternalSupport rules base S L := by
  classical
  let N := (T_normal_orderHom rules base S).lfp
  have fixed : base ∪ T_normal rules N S = N := OrderHom.map_lfp (T_normal_orderHom rules base S)
  have below : N ⊆ S := OrderHom.lfp_le _ supported.le
  have baseN : base ⊆ N := lfp_contains_base rules base S
  have finite : (S \ N).Finite := by
    apply ((rules.map NormalClause.head).toFinset.finite_toSet).subset
    rintro a ⟨present, absent⟩
    rw [← supported] at present
    rcases present with hb | ⟨c, hc, rfl, _⟩
    · exact (absent (baseN hb)).elim
    · simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
      exact ⟨c, hc, rfl⟩
  let U := finite.toFinset
  have memberU (a : GroundAtom σ) : a ∈ U ↔ a ∈ S ∧ a ∉ N := finite.mem_toFinset
  have nonempty : U.Nonempty := by
    have notBelow : ¬ S ⊆ N := fun h =>
      notStable ((stable_iff rules base S).mpr (Set.Subset.antisymm h below))
    obtain ⟨a, inS, notN⟩ := Set.not_subset.mp notBelow
    exact ⟨a, (memberU a).mpr ⟨inS, notN⟩⟩
  have needsMissing (c : NormalClause σ) (hc : c ∈ rules) (headU : c.head ∈ U)
      (body : normalClauseBodyHolds c S S) : ∃ b ∈ U, GoalLit.pos b ∈ c.body := by
    obtain ⟨enabled, positives⟩ := (body_iff c S S).mp body
    by_contra noWitness
    have allN : ∀ b ∈ positiveBody c, b ∈ N := by
      intro b hb
      by_contra absent
      exact noWitness ⟨b, (memberU b).mpr ⟨positives b hb, absent⟩, (mem_positiveBody c b).mp hb⟩
    exact ((memberU c.head).mp headU).2
      (fixed.subset (Or.inr ⟨c, hc, rfl, (body_iff c N S).mpr ⟨enabled, allN⟩⟩))
  have incoming : ∀ a ∈ U, ∃ b ∈ U, PositiveDependency rules b a := by
    intro a ha
    have present := ((memberU a).mp ha).1
    rw [← supported] at present
    rcases present with hb | ⟨c, hc, rfl, body⟩
    · exact (((memberU a).mp ha).2 (baseN hb)).elim
    · obtain ⟨b, hb, member⟩ := needsMissing c hc ha body
      exact ⟨b, hb, c, hc, rfl, member⟩
  obtain ⟨L, subset, loop, closed⟩ := FiniteLoops.exists_closed_loop (PositiveDependency rules) U nonempty incoming
  refine ⟨L, fun a ha => ((memberU a).mp (subset ha)).1, loop, ?_⟩
  rintro (⟨a, inL, inBase⟩ | ⟨c, hc, external, body⟩)
  · exact ((memberU a).mp (subset inL)).2 (baseN inBase)
  · obtain ⟨b, hb, member⟩ := needsMissing c hc (subset external.1) body
    have inL := closed b hb c.head external.1 ⟨c, hc, rfl, member⟩
    exact external.2 b ((mem_positiveBody c b).mpr member) inL

/-- Lin–Zhao correspondence, with selected base facts included in external support. -/
theorem stable_iff_supported_loops (rules : List (NormalClause σ)) (base S : Set (GroundAtom σ)) :
    StableModel rules base S ↔ SupportedModel rules base S ∧
      ∀ L, IsLoop rules L → LoopSatisfied rules base S L := by
  constructor
  · intro stable
    exact ⟨stable_supported stable, fun L _ => stable_external stable L⟩
  · rintro ⟨supported, loops⟩
    by_contra notStable
    obtain ⟨L, subset, loop, unsupported⟩ := unsupported_loop supported notStable
    obtain ⟨a, ha⟩ := loop.1
    exact unsupported (loops L loop ⟨a, ha, subset ha⟩)

theorem loop_member_head {rules : List (NormalClause σ)} {L : Finset (GroundAtom σ)}
    (loop : IsLoop rules L) {a : GroundAtom σ} (ha : a ∈ L) : ∃ c ∈ rules, c.head = a := by
  obtain ⟨_, _, edge⟩ := Relation.TransGen.tail'_iff.mp (loop.2 a ha a ha)
  obtain ⟨c, hc, head, _⟩ := edge.2.2
  exact ⟨c, hc, head⟩

instance positiveDependencyDecidable (rules : List (NormalClause σ)) : DecidableRel (PositiveDependency rules) :=
  fun a b => decidable_of_iff (∃ c ∈ rules, c.head = b ∧ a ∈ positiveBody c)
    (by simp only [mem_positiveBody, PositiveDependency])

instance externalRuleDecidable (L : Finset (GroundAtom σ)) (c : NormalClause σ) :
    Decidable (ExternalRule L c) := by unfold ExternalRule; infer_instance

def loopCheck (rules : List (NormalClause σ)) (L : Finset (GroundAtom σ)) : Bool :=
  FiniteLoops.check (PositiveDependency rules) L

theorem loopCheck_correct (rules : List (NormalClause σ)) (L : Finset (GroundAtom σ)) :
    loopCheck rules L = true ↔ IsLoop rules L := FiniteLoops.check_correct _ _

/-- Enumerate vertex subsets in the supplied atom-table order, then test their induced graphs. -/
def loopSets (table : AtomTable (GroundAtom σ)) (rules : List (NormalClause σ)) :
    List (Finset (GroundAtom σ)) :=
  (table.atoms.sublists.map List.toFinset).filter (loopCheck rules)

theorem mem_loopSets (table : AtomTable (GroundAtom σ)) (rules : List (NormalClause σ))
    (L : Finset (GroundAtom σ)) :
    L ∈ loopSets table rules ↔ L ⊆ table.atoms.toFinset ∧ IsLoop rules L := by
  constructor
  · intro member
    obtain ⟨mapped, checked⟩ := List.mem_filter.mp member
    obtain ⟨nodes, sublist, rfl⟩ := List.mem_map.mp mapped
    refine ⟨?_, (loopCheck_correct _ _).mp checked⟩
    intro a ha
    exact List.mem_toFinset.mpr ((List.mem_sublists.mp sublist).subset (List.mem_toFinset.mp ha))
  · rintro ⟨subset, loop⟩
    let nodes := table.atoms.filter fun a => a ∈ L
    have equal : nodes.toFinset = L := by
      ext a
      simp only [nodes, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun ha => ⟨List.mem_toFinset.mp (subset ha), ha⟩⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨nodes, List.mem_sublists.mpr List.filter_sublist, equal⟩,
      (loopCheck_correct _ _).mpr loop⟩

theorem covers_loop {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    {L : Finset (GroundAtom σ)} (loop : IsLoop rules L) : L ⊆ table.atoms.toFinset := by
  intro a ha
  obtain ⟨c, hc, rfl⟩ := loop_member_head loop ha
  exact List.mem_toFinset.mpr (covers.2 c hc)

theorem loopSets_complete {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (L : Finset (GroundAtom σ)) (loop : IsLoop rules L) : L ∈ loopSets table rules :=
  (mem_loopSets table rules L).mpr ⟨covers_loop table facts rules covers loop, loop⟩

theorem loopSets_nil_of_tight (table : AtomTable (GroundAtom σ)) (rules : List (NormalClause σ))
    (tight : Tight rules) : loopSets table rules = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro L member
  have loop := ((mem_loopSets table rules L).mp member).2
  obtain ⟨a, ha⟩ := loop.1
  have path := Relation.TransGen.mono (fun _ _ h => h.2.2) a a (loop.2 a ha a ha)
  exact (tight_iff_acyclic rules).mp tight a path

def externalSupportFormula {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (L : Finset (GroundAtom σ)) : Formula (Fin (n + table.atoms.length)) :=
  .or (((List.finRange n).filter (fun i => facts i ∈ L)).map
      (fun i => Formula.atom (Fin.castAdd table.atoms.length i))).disj
    ((rules.filter (fun c => ExternalRule L c)).map (fun c => goalsFormula table n c.body)).disj

theorem externalSupportFormula_correct {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (L : Finset (GroundAtom σ)) (choice : Fin n → Bool)
    (values : Fin table.atoms.length → Bool) :
    eval (Fin.addCases choice values) (externalSupportFormula table facts rules L) = true ↔
      ExternalSupport rules (chosenFacts facts choice) (table.interpretation values) L := by
  have selected : (∃ i, facts i ∈ L ∧ choice i = true) ↔ ∃ a ∈ L, a ∈ chosenFacts facts choice := by
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨facts i, hi, i, hx, rfl⟩
    · rintro ⟨a, ha, i, hx, rfl⟩
      exact ⟨i, ha, hx⟩
  simpa [externalSupportFormula, eval, ExternalSupport, normalClauseBodyHolds, and_assoc] using
    or_congr selected (Iff.rfl : (∃ c ∈ rules, ExternalRule L c ∧
      normalClauseBodyHolds c (table.interpretation values) (table.interpretation values)) ↔ _)

def loopFormula {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (L : Finset (GroundAtom σ)) : Formula (Fin (n + table.atoms.length)) :=
  .imp (((table.atoms.filter (fun a => a ∈ L)).map (atomFormula table n)).disj)
    (externalSupportFormula table facts rules L)

theorem loopFormula_correct {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (L : Finset (GroundAtom σ)) (contained : L ⊆ table.atoms.toFinset)
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) :
    eval (Fin.addCases choice values) (loopFormula table facts rules L) = true ↔
      LoopSatisfied rules (chosenFacts facts choice) (table.interpretation values) L := by
  have antecedent : eval (Fin.addCases choice values)
      (((table.atoms.filter (fun a => a ∈ L)).map (atomFormula table n)).disj) = true ↔
        ∃ a ∈ L, a ∈ table.interpretation values := by
    simp only [eval_disj, List.mem_map, List.mem_filter, decide_eq_true_eq, exists_exists_and_eq_and,
      eval_atomFormula, AtomTable.interpretation, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, ⟨_, ha⟩, present⟩
      exact ⟨a, ha, present⟩
    · rintro ⟨a, ha, present⟩
      exact ⟨a, ⟨List.mem_toFinset.mp (contained ha), ha⟩, present⟩
  have implication (first second : Formula (Fin (n + table.atoms.length))) :
      eval (Fin.addCases choice values) (.imp first second) = true ↔
        (eval (Fin.addCases choice values) first = true → eval (Fin.addCases choice values) second = true) := by
    cases hf : eval (Fin.addCases choice values) first <;>
      cases hs : eval (Fin.addCases choice values) second <;> simp [eval, hf, hs]
  rw [loopFormula, implication, antecedent, externalSupportFormula_correct]
  rfl

@[simp] theorem eval_conj₂ {α : Type*} (world : α → Bool) (formulas : List (Formula α)) :
    eval world formulas.conj₂ = true ↔ ∀ f ∈ formulas, eval world f = true := by
  induction formulas with
  | nil => simp [List.conj₂, eval]
  | cons f rest ih => cases rest <;> simp_all [List.conj₂, eval]

/-- Completion plus every induced positive loop formula, with no additional program atoms. -/
def loopCompletion {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) : Formula (Fin (n + table.atoms.length)) :=
  (completion table facts rules :: (loopSets table rules).map (loopFormula table facts rules)).conj₂

theorem loopCompletion_models {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) :
    eval (Fin.addCases choice values) (loopCompletion table facts rules) = true ↔
      StableModel rules (chosenFacts facts choice) (table.interpretation values) := by
  rw [stable_iff_supported_loops]
  simp only [loopCompletion, eval_conj₂, List.forall_mem_cons, List.forall_mem_map,
    completion_models table facts rules covers]
  apply and_congr_right
  intro _
  constructor
  · intro formulas L loop
    exact (loopFormula_correct table facts rules L (covers_loop table facts rules covers loop) choice values).mp
      (formulas L (loopSets_complete table facts rules covers L loop))
  · intro loops L member
    obtain ⟨contained, loop⟩ := (mem_loopSets table rules L).mp member
    exact (loopFormula_correct table facts rules L contained choice values).mpr (loops L loop)

theorem loopCompletion_eq_of_tight {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (tight : Tight rules) :
    loopCompletion table facts rules = completion table facts rules := by
  rw [loopCompletion, loopSets_nil_of_tight table rules tight]
  rfl

theorem loopCompletion_iff_modelValues {n : Nat} (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s)
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) :
    eval (Fin.addCases choice values) (loopCompletion table facts rules) = true ↔
      values = modelValues table facts rules s choice := by
  rw [loopCompletion_models table facts rules covers,
    stable_iff_eq_full rules (chosenFacts facts choice) s stratified,
    ← modelValues_interpretation table facts rules covers s stratified choice]
  exact table.interpretation_injective.eq_iff

theorem loopCompletion_unique_extension {n : Nat} (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s) (choice : Fin n → Bool) :
    ∃! values, eval (Fin.addCases choice values) (loopCompletion table facts rules) = true := by
  simp only [loopCompletion_iff_modelValues table facts rules covers s stratified]
  exact existsUnique_eq

def loopQuery {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (goals : List (GoalLit σ)) : Formula (Fin (n + table.atoms.length)) :=
  .and (loopCompletion table facts rules) (goalsFormula table n goals)

theorem loopQuery_correct {n : Nat} (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s)
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) (goals : List (GoalLit σ)) :
    eval (Fin.addCases choice values) (loopQuery table facts rules goals) = true ↔
      values = modelValues table facts rules s choice ∧
        ∀ g ∈ goals, goalLitHoldsIn (fullStratifiedModel rules (chosenFacts facts choice) s)
          (fullStratifiedModel rules (chosenFacts facts choice) s) g := by
  simp only [loopQuery, eval, Bool.and_eq_true,
    loopCompletion_iff_modelValues table facts rules covers s stratified, eval_goalsFormula]
  apply and_congr_right
  intro same
  rw [same, modelValues_interpretation table facts rules covers s stratified choice]

end Mettapedia.Logic.NormalProgramLoops
