import Mettapedia.Logic.LP.Stratification
import Mettapedia.GSLT.OpenEnded.PrologContrasts
import Mathlib.Order.WellFoundedSet

/-!
# Supported, stable and stratified ground-program models

The Gelfond–Lifschitz reduct is constructed by deleting blocked rules and
erasing negative literals and static guards. Its least model defines stability.
Supportedness instead reads negation against the same interpretation in one
immediate-consequence step. Tightness relates these two notions; stratification
establishes existence and uniqueness of a stable model independently of tightness.

Reference: Babovich, Erdem and Lifschitz, *Fages' Theorem and Answer Set
Programming*, https://arxiv.org/abs/cs/0003042.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.NormalProgramSemantics

open LP BDDCore

variable {σ : LPSignature}

def positiveBody (clause : NormalClause σ) : List (GroundAtom σ) :=
  clause.body.filterMap fun g => match g with | .pos a => some a | _ => none

@[simp] theorem mem_positiveBody (clause : NormalClause σ) (a : GroundAtom σ) :
    a ∈ positiveBody clause ↔ GoalLit.pos a ∈ clause.body := by
  simp only [positiveBody, List.mem_filterMap]
  constructor
  · rintro ⟨g, hg, value⟩
    cases g <;> simp_all
  · intro h
    exact ⟨.pos a, h, rfl⟩

def enabled (clause : NormalClause σ) (S : Set (GroundAtom σ)) : Prop :=
  ∀ g ∈ clause.body, match g with
    | .pos _ => True
    | .neg a => a ∉ S
    | .neq a b => a ≠ b

theorem body_iff (clause : NormalClause σ) (I S : Set (GroundAtom σ)) :
    normalClauseBodyHolds clause I S ↔ enabled clause S ∧ ∀ a ∈ positiveBody clause, a ∈ I := by
  constructor
  · intro h
    exact ⟨fun g hg => by cases g <;> first | trivial | exact h _ hg,
      fun a ha => h (.pos a) ((mem_positiveBody _ _).mp ha)⟩
  · rintro ⟨he, hp⟩ g hg
    cases g with
    | pos a => exact hp a ((mem_positiveBody _ _).mpr hg)
    | neg a => exact he _ hg
    | neq a b => exact he _ hg

/-- The finite positive reduct, supplied independently of its least model. -/
noncomputable def reduct (rules : List (NormalClause σ)) (S : Set (GroundAtom σ)) :
    List (LP.GroundClause σ) := by
  classical
  exact rules.filterMap fun c => if enabled c S then some ⟨c.head, positiveBody c⟩ else none

def positiveStep (rules : List (LP.GroundClause σ)) (I : Set (GroundAtom σ)) : Set (GroundAtom σ) :=
  {a | ∃ c ∈ rules, c.head = a ∧ ∀ b ∈ c.body, b ∈ I}

theorem reduct_step (rules : List (NormalClause σ)) (I S : Set (GroundAtom σ)) :
    positiveStep (reduct rules S) I = T_normal rules I S := by
  classical
  ext a
  constructor
  · rintro ⟨c, member, head, body⟩
    obtain ⟨r, hr, selected⟩ := List.mem_filterMap.mp member
    split_ifs at selected with active
    · have same : (⟨r.head, positiveBody r⟩ : LP.GroundClause σ) = c := Option.some.inj selected
      subst c
      exact ⟨r, hr, head, (body_iff r I S).mpr ⟨active, body⟩⟩
  · rintro ⟨c, member, head, body⟩
    obtain ⟨active, positive⟩ := (body_iff c I S).mp body
    refine ⟨⟨c.head, positiveBody c⟩, List.mem_filterMap.mpr ⟨c, member, ?_⟩, head, positive⟩
    simp [active]

noncomputable def reductOperator (rules : List (NormalClause σ)) (base S : Set (GroundAtom σ)) :
    Set (GroundAtom σ) →o Set (GroundAtom σ) where
  toFun I := base ∪ positiveStep (reduct rules S) I
  monotone' := by
    simp only [reduct_step]
    exact (T_normal_orderHom rules base S).monotone

theorem reductOperator_eq (rules : List (NormalClause σ)) (base S : Set (GroundAtom σ)) :
    reductOperator rules base S = T_normal_orderHom rules base S := by
  apply OrderHom.ext
  funext I
  exact congrArg (base ∪ ·) (reduct_step rules I S)

def StableModel (rules : List (NormalClause σ)) (base S : Set (GroundAtom σ)) : Prop :=
  S = (reductOperator rules base S).lfp

def SupportedModel (rules : List (NormalClause σ)) (base S : Set (GroundAtom σ)) : Prop :=
  base ∪ T_normal rules S S = S

theorem stable_iff (rules : List (NormalClause σ)) (base S : Set (GroundAtom σ)) :
    StableModel rules base S ↔ S = (T_normal_orderHom rules base S).lfp := by
  rw [StableModel, reductOperator_eq]

theorem stable_supported {rules : List (NormalClause σ)} {base S : Set (GroundAtom σ)}
    (stable : StableModel rules base S) : SupportedModel rules base S := by
  have fixed := OrderHom.map_lfp (T_normal_orderHom rules base S)
  rw [← (stable_iff rules base S).mp stable] at fixed
  exact fixed

def PositiveDependency (rules : List (NormalClause σ)) (body head : GroundAtom σ) : Prop :=
  ∃ c ∈ rules, c.head = head ∧ GoalLit.pos body ∈ c.body

def Tight (rules : List (NormalClause σ)) : Prop := WellFounded (PositiveDependency rules)

/-- A finite ranking is an independently checkable tightness certificate. -/
structure TightCertificate (rules : List (NormalClause σ)) where
  rank : GroundAtom σ → Nat
  decreases : ∀ c ∈ rules, ∀ a, GoalLit.pos a ∈ c.body → rank a < rank c.head

theorem TightCertificate.sound {rules : List (NormalClause σ)} (certificate : TightCertificate rules) :
    Tight rules := by
  apply (InvImage.wf certificate.rank Nat.lt_wfRel.wf).mono
  rintro a b ⟨c, hc, rfl, ha⟩
  exact certificate.decreases c hc a ha

/-- Fages' implication uses only positive dependency; negative cycles are allowed. -/
theorem supported_stable {rules : List (NormalClause σ)} (tight : Tight rules)
    {base S : Set (GroundAtom σ)} (supported : SupportedModel rules base S) : StableModel rules base S := by
  rw [stable_iff]
  let L := (T_normal_orderHom rules base S).lfp
  have fixed : base ∪ T_normal rules L S = L := OrderHom.map_lfp (T_normal_orderHom rules base S)
  have below : L ⊆ S := OrderHom.lfp_le _ supported.le
  apply Set.Subset.antisymm ?_ below
  intro a ha
  induction a using tight.induction with
  | h a ih =>
    rw [← supported] at ha
    apply fixed.subset
    rcases ha with hb | ⟨c, hc, head, body⟩
    · exact Or.inl hb
    · refine Or.inr ⟨c, hc, head, ?_⟩
      intro g hg
      cases g with
      | pos b => exact ih b ⟨c, hc, head, hg⟩ (body _ hg)
      | neg b => exact body _ hg
      | neq b d => exact body _ hg

theorem stable_iff_supported {rules : List (NormalClause σ)} (tight : Tight rules)
    (base S : Set (GroundAtom σ)) : StableModel rules base S ↔ SupportedModel rules base S :=
  ⟨stable_supported, supported_stable tight⟩

theorem lfp_contains_base (rules : List (NormalClause σ)) (base negative : Set (GroundAtom σ)) :
    base ⊆ (T_normal_orderHom rules base negative).lfp := by
  intro a ha
  exact (OrderHom.map_lfp (T_normal_orderHom rules base negative)).subset (Or.inl ha)

theorem body_congr_negative (c : NormalClause σ) (I S T : Set (GroundAtom σ))
    (agree : ∀ a, GoalLit.neg a ∈ c.body → (a ∈ S ↔ a ∈ T)) :
    normalClauseBodyHolds c I S ↔ normalClauseBodyHolds c I T := by
  apply forall_congr'
  intro g
  apply forall_congr'
  intro hg
  cases g with
  | pos a => rfl
  | neg a => exact not_congr (agree a hg)
  | neq a b => rfl

theorem step_congr_negative (rules : List (NormalClause σ)) (I S T : Set (GroundAtom σ))
    (agree : ∀ c ∈ rules, ∀ a, GoalLit.neg a ∈ c.body → (a ∈ S ↔ a ∈ T)) :
    T_normal rules I S = T_normal rules I T := by
  ext a
  simp only [T_normal, Set.mem_ofPred_eq]
  apply exists_congr
  intro c
  apply and_congr_right
  intro hc
  rw [body_congr_negative c I S T (agree c hc)]

section Strata

variable (rules : List (NormalClause σ)) (base : Set (GroundAtom σ)) (s : Stratification σ)

def stratumBase : Nat → Set (GroundAtom σ)
  | 0 => base
  | k+1 => stratifiedModel rules base s k

theorem stage_fixed (k : Nat) :
    stratumBase rules base s k ∪
      T_normal (rulesAtStratum rules s k) (stratifiedModel rules base s k) (stratumBase rules base s k) =
        stratifiedModel rules base s k := by
  have fixed := OrderHom.map_lfp (T_normal_orderHom (rulesAtStratum rules s k)
    (stratumBase rules base s k) (stratumBase rules base s k))
  cases k <;> exact fixed

theorem stage_monotone : Monotone (stratifiedModel rules base s) :=
  monotone_nat_of_le_succ (stratifiedModel_mono rules base s)

theorem stage_adds_only_current (k : Nat) :
    stratifiedModel rules base s k ⊆ stratumBase rules base s k ∪ {a | s a = k} := by
  have upper : (T_normal_orderHom (rulesAtStratum rules s k) (stratumBase rules base s k)
      (stratumBase rules base s k)).lfp ⊆ stratumBase rules base s k ∪ {a | s a = k} := by
    apply OrderHom.lfp_le
    rintro a (hb | ⟨c, hc, rfl, _⟩)
    · exact Or.inl hb
    · exact Or.inr (by simpa [rulesAtStratum] using (List.mem_filter.mp hc).2)
  cases k <;> exact upper

/-- Later strata cannot add a new atom at a lower level. Base facts remain visible throughout. -/
theorem full_at_stage (a : GroundAtom σ) (k : Nat) (low : s a ≤ k) :
    a ∈ fullStratifiedModel rules base s ↔ a ∈ stratifiedModel rules base s k := by
  constructor
  · intro member
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp member
    induction j with
    | zero => exact stage_monotone rules base s (Nat.zero_le k) hj
    | succ j ih =>
      by_cases earlier : j < k
      · exact stage_monotone rules base s earlier hj
      · rcases stage_adds_only_current rules base s (j+1) hj with old | level
        · exact ih old
        · change s a = j+1 at level
          omega
  · intro member
    exact stratifiedModel_subset_full rules base s k member

theorem stratumBase_subset_full (k : Nat) :
    stratumBase rules base s k ⊆ fullStratifiedModel rules base s := by
  cases k with
  | zero => exact (base_subset_stratifiedModel rules base s 0).trans (stratifiedModel_subset_full rules base s 0)
  | succ k => exact stratifiedModel_subset_full rules base s k

variable (stratified : ∀ c ∈ rules, respectsStratification c s)
include stratified

theorem body_previous_full (c : NormalClause σ) (member : c ∈ rules) (k : Nat) (level : s c.head = k)
    (I : Set (GroundAtom σ)) :
    normalClauseBodyHolds c I (stratumBase rules base s k) ↔
      normalClauseBodyHolds c I (fullStratifiedModel rules base s) := by
  apply body_congr_negative
  intro a ha
  have lower := stratified c member (.neg a) ha
  change s a < s c.head at lower
  rw [level] at lower
  cases k with
  | zero => omega
  | succ k => exact (full_at_stage rules base s a k (by omega)).symm

theorem full_supported : SupportedModel rules base (fullStratifiedModel rules base s) := by
  apply Set.Subset.antisymm
  · rintro a (hb | ⟨c, hc, rfl, body⟩)
    · exact stratumBase_subset_full rules base s 0 hb
    · apply stratifiedModel_subset_full rules base s (s c.head)
      apply (stage_fixed rules base s (s c.head)).subset
      refine Or.inr ⟨c, ?_, rfl, ?_⟩
      · simp [rulesAtStratum, hc]
      · apply (body_previous_full rules base s stratified c hc (s c.head) rfl _).mpr
        intro g hg
        cases g with
        | pos b =>
          exact (full_at_stage rules base s b (s c.head) (stratified c hc _ hg)).mp (body _ hg)
        | neg b => exact body _ hg
        | neq b d => exact body _ hg
  · intro a present
    obtain ⟨k, member⟩ := Set.mem_iUnion.mp present
    induction k with
    | zero =>
      rw [← stage_fixed rules base s 0] at member
      rcases member with hb | ⟨c, hc, head, body⟩
      · exact Or.inl hb
      · have cm := (List.mem_filter.mp hc).1
        have level : s c.head = 0 := by simpa using (List.mem_filter.mp hc).2
        refine Or.inr ⟨c, cm, head, ?_⟩
        have body := (body_previous_full rules base s stratified c cm 0 level _).mp body
        intro g hg
        cases g with
        | pos b => exact stratifiedModel_subset_full rules base s 0 (body _ hg)
        | neg b => exact body _ hg
        | neq b d => exact body _ hg
    | succ k ih =>
      rw [← stage_fixed rules base s (k+1)] at member
      rcases member with old | ⟨c, hc, head, body⟩
      · exact ih old
      · have cm := (List.mem_filter.mp hc).1
        have level : s c.head = k+1 := by simpa using (List.mem_filter.mp hc).2
        have body := (body_previous_full rules base s stratified c cm (k+1) level _).mp body
        refine Or.inr ⟨c, cm, head, ?_⟩
        intro g hg
        cases g with
        | pos b => exact stratifiedModel_subset_full rules base s (k+1) (body _ hg)
        | neg b => exact body _ hg
        | neq b d => exact body _ hg

theorem full_stable : StableModel rules base (fullStratifiedModel rules base s) := by
  rw [stable_iff]
  let L := (T_normal_orderHom rules base (fullStratifiedModel rules base s)).lfp
  have fixed : base ∪ T_normal rules L (fullStratifiedModel rules base s) = L :=
    OrderHom.map_lfp (T_normal_orderHom rules base (fullStratifiedModel rules base s))
  apply Set.Subset.antisymm ?_ (OrderHom.lfp_le _ (full_supported rules base s stratified).le)
  intro a present
  obtain ⟨k, member⟩ := Set.mem_iUnion.mp present
  have stages : ∀ k, stratifiedModel rules base s k ⊆ L := by
    intro k
    induction k with
    | zero =>
      apply OrderHom.lfp_le
      rintro b (hb | ⟨c, hc, head, body⟩)
      · exact lfp_contains_base rules base _ hb
      · have cm := (List.mem_filter.mp hc).1
        have level : s c.head = 0 := by simpa using (List.mem_filter.mp hc).2
        exact fixed.subset (Or.inr ⟨c, cm, head,
          (body_previous_full rules base s stratified c cm 0 level L).mp body⟩)
    | succ k ih =>
      apply OrderHom.lfp_le
      rintro b (hb | ⟨c, hc, head, body⟩)
      · exact ih hb
      · have cm := (List.mem_filter.mp hc).1
        have level : s c.head = k+1 := by simpa using (List.mem_filter.mp hc).2
        exact fixed.subset (Or.inr ⟨c, cm, head,
          (body_previous_full rules base s stratified c cm (k+1) level L).mp body⟩)
  exact stages k member

def lowerRules (k : Nat) : List (NormalClause σ) := rules.filter fun c => s c.head ≤ k

/-- Restricting the positive reduct to lower heads commutes with its least model. -/
theorem reduct_cut (negative : Set (GroundAtom σ)) (k : Nat) :
    (T_normal_orderHom rules base negative).lfp ∩ {a | s a ≤ k} =
      (T_normal_orderHom (lowerRules rules s k) (base ∩ {a | s a ≤ k}) negative).lfp := by
  let L := (T_normal_orderHom (lowerRules rules s k) (base ∩ {a | s a ≤ k}) negative).lfp
  have fixed : (base ∩ {a | s a ≤ k}) ∪ T_normal (lowerRules rules s k) L negative = L :=
    OrderHom.map_lfp (T_normal_orderHom (lowerRules rules s k) (base ∩ {a | s a ≤ k}) negative)
  have bounded : L ⊆ {a | s a ≤ k} := by
    apply OrderHom.lfp_le
    rintro a (hb | ⟨c, hc, rfl, _⟩)
    · exact hb.2
    · exact of_decide_eq_true (List.mem_filter.mp hc).2
  have below : L ⊆ (T_normal_orderHom rules base negative).lfp := by
    apply OrderHom.lfp_le
    rintro a (hb | ⟨c, hc, head, body⟩)
    · exact lfp_contains_base rules base negative hb.1
    · exact (OrderHom.map_lfp (T_normal_orderHom rules base negative)).subset
        (Or.inr ⟨c, (List.mem_filter.mp hc).1, head, body⟩)
  have upper : (T_normal_orderHom rules base negative).lfp ⊆ L ∪ {a | k < s a} := by
    apply OrderHom.lfp_le
    rintro a (hb | ⟨c, hc, rfl, body⟩)
    · by_cases low : s a ≤ k
      · exact Or.inl (lfp_contains_base (lowerRules rules s k) _ negative ⟨hb, low⟩)
      · exact Or.inr (by change k < s a; omega)
    · by_cases low : s c.head ≤ k
      · apply Or.inl
        apply fixed.subset
        refine Or.inr ⟨c, ?_, rfl, ?_⟩
        · simp [lowerRules, hc, low]
        · intro g hg
          cases g with
          | pos b =>
            rcases body _ hg with present | high
            · exact present
            · have order : s b ≤ s c.head := stratified c hc _ hg
              change k < s b at high
              omega
          | neg b => exact body _ hg
          | neq b d => exact body _ hg
      · exact Or.inr (by change k < s c.head; omega)
  apply Set.Subset.antisymm
  · rintro a ⟨member, low⟩
    rcases upper member with present | high
    · exact present
    · change s a ≤ k at low
      change k < s a at high
      omega
  · intro a member
    exact ⟨below member, bounded member⟩

/-- Stratification gives uniqueness of stable models, even with positive recursion. -/
theorem stable_unique (S T : Set (GroundAtom σ))
    (stableS : StableModel rules base S) (stableT : StableModel rules base T) : S = T := by
  have eqS := (stable_iff rules base S).mp stableS
  have eqT := (stable_iff rules base T).mp stableT
  have levels : ∀ k, ∀ a, s a ≤ k → (a ∈ S ↔ a ∈ T) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have operators : T_normal_orderHom (lowerRules rules s k) (base ∩ {a | s a ≤ k}) S =
          T_normal_orderHom (lowerRules rules s k) (base ∩ {a | s a ≤ k}) T := by
        apply OrderHom.ext
        funext I
        apply congrArg ((base ∩ {a | s a ≤ k}) ∪ ·)
        apply step_congr_negative
        intro c hc a ha
        have cm := (List.mem_filter.mp hc).1
        have upper : s c.head ≤ k := of_decide_eq_true (List.mem_filter.mp hc).2
        have lower : s a < s c.head := stratified c cm (.neg a) ha
        exact ih (s a) (by omega) a le_rfl
      have sameCut : S ∩ {a | s a ≤ k} = T ∩ {a | s a ≤ k} := calc
        _ = (T_normal_orderHom rules base S).lfp ∩ {a | s a ≤ k} := congrArg (· ∩ {a | s a ≤ k}) eqS
        _ = (T_normal_orderHom (lowerRules rules s k) (base ∩ {a | s a ≤ k}) S).lfp :=
          reduct_cut rules base s stratified S k
        _ = (T_normal_orderHom (lowerRules rules s k) (base ∩ {a | s a ≤ k}) T).lfp := congrArg OrderHom.lfp operators
        _ = (T_normal_orderHom rules base T).lfp ∩ {a | s a ≤ k} :=
          (reduct_cut rules base s stratified T k).symm
        _ = _ := congrArg (· ∩ {a | s a ≤ k}) eqT.symm
      intro a low
      simpa only [Set.mem_inter_iff, Set.mem_ofPred_eq, low, and_true] using Set.ext_iff.mp sameCut a
  ext a
  exact levels (s a) a le_rfl

theorem stable_iff_eq_full (S : Set (GroundAtom σ)) :
    StableModel rules base S ↔ S = fullStratifiedModel rules base s :=
  ⟨fun stable => stable_unique rules base s stratified S _ stable (full_stable rules base s stratified),
    fun same => same ▸ full_stable rules base s stratified⟩

theorem supported_iff_eq_full (tight : Tight rules) (S : Set (GroundAtom σ)) :
    SupportedModel rules base S ↔ S = fullStratifiedModel rules base s := by
  rw [← stable_iff_supported tight, stable_iff_eq_full rules base s stratified]

end Strata

def ruleView (c : NormalClause σ) : Mettapedia.GSLT.OpenEnded.PrologContrasts.NormalRule (GroundAtom σ) where
  head := c.head
  pos := {a | GoalLit.pos a ∈ c.body}
  neg := {a | GoalLit.neg a ∈ c.body}

/-- Interpret list clauses and base facts in the existing supported-model carrier. -/
def ruleProgram (rules : List (NormalClause σ)) (base : Set (GroundAtom σ)) :
    Set (Mettapedia.GSLT.OpenEnded.PrologContrasts.NormalRule (GroundAtom σ)) :=
  {r | ∃ c ∈ rules, enabled c ∅ ∧ r = ruleView c} ∪ {r | ∃ a ∈ base, r = ⟨a, ∅, ∅⟩}

theorem nafStep_ruleProgram (rules : List (NormalClause σ)) (base S : Set (GroundAtom σ)) :
    Mettapedia.GSLT.OpenEnded.PrologContrasts.nafStep (ruleProgram rules base) S =
      base ∪ T_normal rules S S := by
  ext a
  constructor
  · rintro ⟨r, member, head, pos, neg⟩
    rcases member with ⟨c, hc, guard, rfl⟩ | ⟨b, hb, rfl⟩
    · refine Or.inr ⟨c, hc, head, ?_⟩
      intro g hg
      cases g with
      | pos b => exact pos hg
      | neg b => exact neg b hg
      | neq b d => exact guard _ hg
    · exact Or.inl (head ▸ hb)
  · rintro (hb | ⟨c, hc, head, body⟩)
    · exact ⟨⟨a, ∅, ∅⟩, Or.inr ⟨a, hb, rfl⟩, rfl, Set.empty_subset _, fun _ h => h.elim⟩
    · refine ⟨ruleView c, Or.inl ⟨c, hc, ?_, rfl⟩, head, ?_, ?_⟩
      · intro g hg
        cases g with
        | pos b => trivial
        | neg b => exact Set.notMem_empty b
        | neq b d => exact body _ hg
      · intro b hb
        exact body (.pos b) hb
      · intro b hb
        exact body (.neg b) hb

theorem supported_iff_nafStep (rules : List (NormalClause σ)) (base S : Set (GroundAtom σ)) :
    SupportedModel rules base S ↔
      Mettapedia.GSLT.OpenEnded.PrologContrasts.nafStep (ruleProgram rules base) S = S := by
  rw [nafStep_ruleProgram]
  rfl

def PositiveAcyclic (rules : List (NormalClause σ)) : Prop :=
  ∀ a, ¬ Relation.TransGen (PositiveDependency rules) a a

/-- On a finite rule list, well-founded positive dependency is exactly absence of positive cycles. -/
theorem tight_iff_acyclic (rules : List (NormalClause σ)) : Tight rules ↔ PositiveAcyclic rules := by
  classical
  constructor
  · intro tight a loop
    exact tight.transGen.irrefl.irrefl a loop
  · intro acyclic
    let heads : Set (GroundAtom σ) := {a | ∃ c ∈ rules, c.head = a}
    have finite : heads.Finite := by
      have image := (rules.toFinset.finite_toSet).image NormalClause.head
      apply image.subset
      rintro a ⟨c, hc, head⟩
      exact ⟨c, by simpa using hc, head⟩
    have : IsStrictOrder (GroundAtom σ) (Relation.TransGen (PositiveDependency rules)) := {
      irrefl := acyclic
      trans _ _ _ := Relation.TransGen.trans }
    have within := finite.wellFoundedOn (r := Relation.TransGen (PositiveDependency rules))
    have outside (a : GroundAtom σ) (absent : a ∉ heads) : Acc (PositiveDependency rules) a := by
      constructor
      rintro b ⟨c, hc, head, _⟩
      exact (absent ⟨c, hc, head⟩).elim
    have restricted := Set.wellFoundedOn_iff.mp within
    have inside (a : GroundAtom σ) (ha : a ∈ heads) : Acc (PositiveDependency rules) a := by
      induction a using restricted.induction with
      | h a ih =>
        constructor
        intro b edge
        by_cases present : b ∈ heads
        · exact ih b ⟨Relation.TransGen.single edge, present, ha⟩ present
        · exact outside b present
    constructor
    intro a
    by_cases present : a ∈ heads
    · exact inside a present
    · exact outside a present

end Mettapedia.Logic.NormalProgramSemantics
