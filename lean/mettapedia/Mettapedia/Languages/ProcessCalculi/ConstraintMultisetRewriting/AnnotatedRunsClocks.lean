import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAnnotations

/-!
# Vector clocks of runs, characterized by the causal order

Logical time needs no clock reading: it is determined by the causal order. A **vector clock**
counts, at each site, the events of an event's causal past there (Mattern 1989, Fidge 1988).

## Positions, the causal order and the clock

For a word over an alphabet with an independence relation, a position **directly precedes** a
later one when their letters are dependent (`DirectlyBefore`), and the **causal order** is the
reflexive and transitive closure (`Causal`). Given a map from letters to finite sets of sites, the
**vector clock** of a position counts, at each site, the positions of its causal past whose letter
is at that site (`clock`).

## The characterization

When the sites **cover the dependence** of the word's letters, i.e. two letters are dependent
exactly when they share a site, and no letter is independent of itself, a position precedes another
causally exactly when its vector clock lies below the other's at every site
(`causal_iff_clock_le`). The events at one site form a chain, and the causal past of an event meets
each chain in a prefix. The clock of the last event at a site counts every event there
(`clock_last`).

Both hypotheses are needed:
* `ClockControls.shared_site_without_dependence`: two independent letters sharing a site have
  comparable clocks and no causal relation;
* `ClockControls.siteless_letter`: a letter with no site has the zero clock, below every clock.

## Vector clocks are a property of the trace

Exchanging two adjacent independent letters moves their positions and keeps every other one
(`swapPositions`, `swapPositions_getElem`). Direct precedence, the causal order and every vector
clock are kept by the exchange (`directlyBefore_swap`, `causal_swap`, `clock_swap`). Hence
trace-equivalent words have a bijection of positions that keeps the letters, the causal order and
every clock (`clock_traceEquiv`): the vector clock of each event is a property of the trace,
for any assignment of sites. Exchanging two dependent letters is no such bijection: the clocks separate the two orders
(`ClockControls.dependent_orders_separated`).

## Sites for the candidate step

For firings without guards, predicate queries or reads that write something, the occurrence
identities each firing takes or makes cover the Mazurkiewicz dependence of the candidate step
(`written_cover`): two such firings are dependent exactly when they write a common identity.
So, for runs of such firings, the vector clock indexed by occurrence identities characterizes
the causal order (`causal_iff_written_clock_le`), and for every run it is a property of the static
trace (`written_clock_traceEquiv`). The **run clock**, how many firings of a run write each identity,
is an account of runs into a commutative monoid, hence a functor on static and on contextual traces
(`runClock_factors_static`, `runClock_factors_contextual`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-! ## The causal order and the vector clock of a word -/

section Clocks

universe uα uSite
variable {α : Type uα} {Site : Type uSite} [DecidableEq Site]
variable (I : α → α → Prop) (loc : α → Finset Site) (w : List α)

/-- One position precedes another directly: it is earlier, and their letters are dependent. -/
def DirectlyBefore (i j : Fin w.length) : Prop := i < j ∧ ¬ I w[i] w[j]

/-- **The causal order** on the positions of a word. -/
def Causal : Fin w.length → Fin w.length → Prop := Relation.ReflTransGen (DirectlyBefore I w)

variable {I w} in
theorem Causal.le {i j : Fin w.length} (causal : Causal I w i j) : i ≤ j := by
  induction causal with
  | refl => exact le_refl _
  | tail _ step ih => exact le_trans ih (le_of_lt step.1)

open Classical in
/-- **The causal past** of a position. -/
noncomputable def past (j : Fin w.length) : Finset (Fin w.length) :=
  Finset.univ.filter fun i => Causal I w i j

theorem mem_past {i j : Fin w.length} : i ∈ past I w j ↔ Causal I w i j := by
  classical
  simp [past]

/-- The positions whose letter is at a site. -/
def atSite (s : Site) : Finset (Fin w.length) := Finset.univ.filter fun i => s ∈ loc w[i]

theorem mem_atSite {i : Fin w.length} {s : Site} : i ∈ atSite loc w s ↔ s ∈ loc w[i] := by
  simp [atSite]

/-- **The vector clock** of a position: at each site, the number of events of its causal past
there. -/
noncomputable def clock (j : Fin w.length) (s : Site) : ℕ := (past I w j ∩ atSite loc w s).card

/-- **Sites cover the dependence** of the word's letters: two of them are dependent exactly when
they share a site. -/
def SitesCover : Prop := ∀ a ∈ w, ∀ b ∈ w, ¬ I a b ↔ (loc a ∩ loc b).Nonempty

variable {I loc w}

/-- **The events at one site form a causal chain.** -/
theorem chain_at_site (cover : SitesCover I loc w) {s : Site} {k k' : Fin w.length}
    (atK : k ∈ atSite loc w s) (atK' : k' ∈ atSite loc w s) (lt : k < k') : Causal I w k k' := by
  refine Relation.ReflTransGen.single ⟨lt, ?_⟩
  exact (cover _ (List.getElem_mem _) _ (List.getElem_mem _)).mpr
    ⟨s, Finset.mem_inter.mpr ⟨(mem_atSite loc w).mp atK, (mem_atSite loc w).mp atK'⟩⟩

/-- **Vector clocks characterize the causal order.** When the sites cover the dependence and no
letter of the word is independent of itself, a position precedes another causally exactly when
its vector clock is below the other's at every site. -/
theorem causal_iff_clock_le (cover : SitesCover I loc w) (irrefl : ∀ a ∈ w, ¬ I a a)
    (i j : Fin w.length) : Causal I w i j ↔ ∀ s, clock I loc w i s ≤ clock I loc w j s := by
  constructor
  · intro causal s
    apply Finset.card_le_card
    intro k member
    obtain ⟨inPast, inSite⟩ := Finset.mem_inter.mp member
    exact Finset.mem_inter.mpr
      ⟨(mem_past I w).mpr (((mem_past I w).mp inPast).trans causal), inSite⟩
  · intro below
    obtain ⟨s, site⟩ : (loc w[i]).Nonempty := by
      obtain ⟨s, member⟩ := (cover _ (List.getElem_mem _) _ (List.getElem_mem _)).mp
        (irrefl _ (List.getElem_mem _))
      exact ⟨s, (Finset.mem_inter.mp member).1⟩
    have iAtSite : i ∈ atSite loc w s := (mem_atSite loc w).mpr site
    by_contra notCausal
    have sub : past I w j ∩ atSite loc w s ⊆ (atSite loc w s).filter (· < i) := by
      intro k member
      obtain ⟨inPast, inSite⟩ := Finset.mem_inter.mp member
      refine Finset.mem_filter.mpr ⟨inSite, ?_⟩
      by_contra notLt
      rcases (not_lt.mp notLt).lt_or_eq with lt | same
      · exact notCausal ((chain_at_site cover iAtSite inSite lt).trans ((mem_past I w).mp inPast))
      · subst same
        exact notCausal ((mem_past I w).mp inPast)
    have earlier : (atSite loc w s).filter (· < i) ⊆ past I w i ∩ atSite loc w s := by
      intro k member
      obtain ⟨inSite, lt⟩ := Finset.mem_filter.mp member
      exact Finset.mem_inter.mpr ⟨(mem_past I w).mpr (chain_at_site cover inSite iAtSite lt), inSite⟩
    have strict : (atSite loc w s).filter (· < i) ⊂ past I w i ∩ atSite loc w s :=
      (Finset.ssubset_iff_of_subset earlier).mpr
        ⟨i, Finset.mem_inter.mpr ⟨(mem_past I w).mpr .refl, iAtSite⟩,
          fun member => lt_irrefl i (Finset.mem_filter.mp member).2⟩
    have smaller := Finset.card_lt_card strict
    have bounded := Finset.card_le_card sub
    have atS := below s
    unfold clock at atS
    omega

/-- **The clock of the last event at a site counts every event there.** -/
theorem clock_last (cover : SitesCover I loc w) {j : Fin w.length} {s : Site}
    (atJ : j ∈ atSite loc w s) (last : ∀ k ∈ atSite loc w s, k ≤ j) :
    clock I loc w j s = (atSite loc w s).card := by
  unfold clock
  congr 1
  refine Finset.inter_eq_right.mpr fun k atK => (mem_past I w).mpr ?_
  rcases (last k atK).lt_or_eq with lt | same
  · exact chain_at_site cover atK atJ lt
  · rw [same]
    exact .refl

/-- Every clock lies below the number of events at the site. -/
theorem clock_le_card (j : Fin w.length) (s : Site) :
    clock I loc w j s ≤ (atSite loc w s).card :=
  Finset.card_le_card Finset.inter_subset_right

end Clocks

/-! ## Vector clocks are a property of the trace -/

section Swaps

universe uα uSite

/-- The exchange of the indices `p` and `p + 1`. -/
def swapIndex (p k : ℕ) : ℕ := if k = p then p + 1 else if k = p + 1 then p else k

theorem swapIndex_involutive (p k : ℕ) : swapIndex p (swapIndex p k) = k := by
  unfold swapIndex
  split_ifs <;> omega

theorem swapIndex_succ (p k : ℕ) : swapIndex (p + 1) (k + 1) = swapIndex p k + 1 := by
  unfold swapIndex
  split_ifs <;> omega

theorem swapIndex_of_ne {p k : ℕ} (first : k ≠ p) (second : k ≠ p + 1) : swapIndex p k = k := by
  unfold swapIndex
  rw [if_neg first, if_neg second]

theorem swapIndex_zero_succ (p : ℕ) : swapIndex (p + 1) 0 = 0 := by
  unfold swapIndex
  split_ifs <;> omega

theorem swapIndex_lt {p n k : ℕ} (pair : p + 1 < n) (inside : k < n) : swapIndex p k < n := by
  unfold swapIndex
  split_ifs <;> omega

theorem swapIndex_lt_iff {p i j : ℕ} (notPair : ¬ (i = p ∧ j = p + 1))
    (notPair' : ¬ (i = p + 1 ∧ j = p)) : swapIndex p i < swapIndex p j ↔ i < j := by
  unfold swapIndex
  split_ifs <;> omega

variable {α : Type uα} {Site : Type uSite} [DecidableEq Site]

/-- **Exchanging an adjacent pair moves its letters and keeps every other letter.** -/
theorem getElem_swapIndex (a b : α) (v : List α) : ∀ (u : List α) (k : ℕ)
    (inside : k < (u ++ a :: b :: v).length) (inside' : swapIndex u.length k < (u ++ b :: a :: v).length),
    (u ++ b :: a :: v)[swapIndex u.length k] = (u ++ a :: b :: v)[k]
  | [], 0, _, _ => by simp [swapIndex]
  | [], 1, _, _ => by simp [swapIndex]
  | [], k + 2, _, _ => by
      have unmoved : swapIndex ([] : List α).length (k + 2) = k + 2 :=
        swapIndex_of_ne (by simp only [List.length_nil]; omega) (by simp only [List.length_nil]; omega)
      simp only [unmoved]
      rfl
  | x :: u, 0, _, _ => by simp [swapIndex_zero_succ]
  | x :: u, k + 1, inside, _ => by
      have inside₁ : k < (u ++ a :: b :: v).length := by
        simp only [List.cons_append, List.length_cons] at inside
        omega
      have inside₁' : swapIndex u.length k < (u ++ b :: a :: v).length :=
        swapIndex_lt (by simp only [List.length_append, List.length_cons]; omega)
          (by simp only [List.length_append, List.length_cons] at inside₁ ⊢; omega)
      have later := getElem_swapIndex a b v u k inside₁ inside₁'
      simp only [List.cons_append, List.length_cons, swapIndex_succ, List.getElem_cons_succ]
      exact later

theorem getElem_length_append (u l : List α) (a : α) (inside : u.length < (u ++ a :: l).length) :
    (u ++ a :: l)[u.length] = a := by
  induction u with
  | nil => rfl
  | cons x u ih =>
      simp only [List.cons_append, List.length_cons, List.getElem_cons_succ]
      exact ih (by simp)

variable (u v : List α) (a b : α)

/-- **The positions of a word and of the word with one adjacent pair exchanged.** -/
def swapPositions : Fin (u ++ a :: b :: v).length ≃ Fin (u ++ b :: a :: v).length where
  toFun k := ⟨swapIndex u.length k, swapIndex_lt (by simp only [List.length_append, List.length_cons]; omega)
    (by have := k.isLt; simp only [List.length_append, List.length_cons] at this ⊢; omega)⟩
  invFun k := ⟨swapIndex u.length k, swapIndex_lt (by simp only [List.length_append, List.length_cons]; omega)
    (by have := k.isLt; simp only [List.length_append, List.length_cons] at this ⊢; omega)⟩
  left_inv k := Fin.ext (swapIndex_involutive _ _)
  right_inv k := Fin.ext (swapIndex_involutive _ _)

theorem swapPositions_val (k : Fin (u ++ a :: b :: v).length) :
    (swapPositions u v a b k).val = swapIndex u.length k := rfl

theorem swapPositions_getElem (k : Fin (u ++ a :: b :: v).length) :
    (u ++ b :: a :: v)[swapPositions u v a b k] = (u ++ a :: b :: v)[k] :=
  getElem_swapIndex a b v u k k.isLt (swapPositions u v a b k).isLt

theorem getElem_first_of_pair (k : Fin (u ++ a :: b :: v).length) (atPair : k.val = u.length) :
    (u ++ a :: b :: v)[k] = a := by
  obtain ⟨k, inside⟩ := k
  simp only at atPair
  subst atPair
  exact getElem_length_append u (b :: v) a inside

theorem getElem_length_succ_append (inside : u.length + 1 < (u ++ a :: b :: v).length) :
    (u ++ a :: b :: v)[u.length + 1] = b := by
  induction u with
  | nil => rfl
  | cons x u ih =>
      simp only [List.cons_append, List.length_cons, List.getElem_cons_succ]
      exact ih (by simp only [List.length_append, List.length_cons]; omega)

theorem getElem_second_of_pair (k : Fin (u ++ a :: b :: v).length) (atPair : k.val = u.length + 1) :
    (u ++ a :: b :: v)[k] = b := by
  obtain ⟨k, inside⟩ := k
  simp only at atPair
  subst atPair
  exact getElem_length_succ_append u v a b inside

variable {u v a b}

/-- **Direct precedence survives the exchange of an independent pair.** -/
theorem directlyBefore_swap (I : α → α → Prop) (symm : ∀ x y, I x y → I y x) (independent : I a b)
    (i j : Fin (u ++ a :: b :: v).length) :
    DirectlyBefore I (u ++ b :: a :: v) (swapPositions u v a b i) (swapPositions u v a b j) ↔
      DirectlyBefore I (u ++ a :: b :: v) i j := by
  unfold DirectlyBefore
  rw [swapPositions_getElem, swapPositions_getElem]
  have notPairs : ¬ I (u ++ a :: b :: v)[i] (u ++ a :: b :: v)[j] →
      ¬ (i.val = u.length ∧ j.val = u.length + 1) ∧ ¬ (i.val = u.length + 1 ∧ j.val = u.length) := by
    intro dependent
    refine ⟨fun ⟨atI, atJ⟩ => dependent ?_, fun ⟨atI, atJ⟩ => dependent ?_⟩
    · rw [getElem_first_of_pair u v a b i atI, getElem_second_of_pair u v a b j atJ]
      exact independent
    · rw [getElem_second_of_pair u v a b i atI, getElem_first_of_pair u v a b j atJ]
      exact symm _ _ independent
  constructor
  · rintro ⟨lt, dependent⟩
    obtain ⟨notPair, notPair'⟩ := notPairs dependent
    exact ⟨(swapIndex_lt_iff notPair notPair').mp lt, dependent⟩
  · rintro ⟨lt, dependent⟩
    obtain ⟨notPair, notPair'⟩ := notPairs dependent
    exact ⟨(swapIndex_lt_iff notPair notPair').mpr lt, dependent⟩

/-- **The causal order survives the exchange of an independent pair.** -/
theorem causal_swap (I : α → α → Prop) (symm : ∀ x y, I x y → I y x) (independent : I a b)
    (i j : Fin (u ++ a :: b :: v).length) :
    Causal I (u ++ b :: a :: v) (swapPositions u v a b i) (swapPositions u v a b j) ↔
      Causal I (u ++ a :: b :: v) i j := by
  constructor
  · intro causal
    have lifted := Relation.ReflTransGen.lift (swapPositions u v a b).symm (fun x y step => by
      have := (directlyBefore_swap I symm independent ((swapPositions u v a b).symm x)
        ((swapPositions u v a b).symm y)).mp
      simp only [Equiv.apply_symm_apply] at this
      exact this step) _ _ causal
    have unwrapped : Causal I (u ++ a :: b :: v) ((swapPositions u v a b).symm (swapPositions u v a b i))
        ((swapPositions u v a b).symm (swapPositions u v a b j)) := lifted
    simpa using unwrapped
  · intro causal
    exact Relation.ReflTransGen.lift (swapPositions u v a b)
      (fun x y step => (directlyBefore_swap I symm independent x y).mpr step) _ _ causal

/-- **Every vector clock survives the exchange of an independent pair.** -/
theorem clock_swap (I : α → α → Prop) (loc : α → Finset Site) (symm : ∀ x y, I x y → I y x)
    (independent : I a b) (j : Fin (u ++ a :: b :: v).length) (s : Site) :
    clock I loc (u ++ b :: a :: v) (swapPositions u v a b j) s =
      clock I loc (u ++ a :: b :: v) j s := by
  unfold clock
  have pastEq : past I (u ++ b :: a :: v) (swapPositions u v a b j) =
      (past I (u ++ a :: b :: v) j).map (swapPositions u v a b).toEmbedding := by
    ext k
    rw [Finset.mem_map_equiv, mem_past, mem_past, ← causal_swap I symm independent,
      Equiv.apply_symm_apply]
  have siteEq : atSite loc (u ++ b :: a :: v) s =
      (atSite loc (u ++ a :: b :: v) s).map (swapPositions u v a b).toEmbedding := by
    ext k
    rw [Finset.mem_map_equiv, mem_atSite, mem_atSite, ← swapPositions_getElem u v a b]
    simp only [Equiv.apply_symm_apply]
  rw [pastEq, siteEq, ← Finset.map_inter, Finset.card_map]

/-- **Vector clocks are a property of the trace.** Words related by swaps of adjacent independent
letters have a bijection of positions that keeps the letters, the causal order and every vector
clock. -/
theorem clock_traceEquiv (I : α → α → Prop) (loc : α → Finset Site) (symm : ∀ x y, I x y → I y x)
    {w w' : List α} (equivalent : Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv I w w') :
    ∃ π : Fin w.length ≃ Fin w'.length, (∀ k, w'[π k] = w[k]) ∧
      (∀ i j, Causal I w' (π i) (π j) ↔ Causal I w i j) ∧
        ∀ j s, clock I loc w' (π j) s = clock I loc w j s := by
  induction equivalent with
  | rel _ _ swapped =>
      cases swapped with
      | swap u v independent =>
          exact ⟨swapPositions u v _ _, swapPositions_getElem u v _ _,
            causal_swap I symm independent, fun j s => clock_swap I loc symm independent j s⟩
  | refl => exact ⟨Equiv.refl _, fun _ => rfl, fun _ _ => Iff.rfl, fun _ _ => rfl⟩
  | symm _ _ _ ih =>
      obtain ⟨π, letters, causal, clocks⟩ := ih
      refine ⟨π.symm, fun k => ?_, fun i j => ?_, fun j s => ?_⟩
      · have := letters (π.symm k)
        simp only [Equiv.apply_symm_apply] at this
        exact this.symm
      · have := causal (π.symm i) (π.symm j)
        simp only [Equiv.apply_symm_apply] at this
        exact this.symm
      · have := clocks (π.symm j) s
        simp only [Equiv.apply_symm_apply] at this
        exact this.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      obtain ⟨π₁, letters₁, causal₁, clocks₁⟩ := ih₁
      obtain ⟨π₂, letters₂, causal₂, clocks₂⟩ := ih₂
      refine ⟨π₁.trans π₂, fun k => ?_, fun i j => ?_, fun j s => ?_⟩
      · simp only [Equiv.trans_apply]
        rw [letters₂, letters₁]
      · simp only [Equiv.trans_apply]
        rw [causal₂, causal₁]
      · simp only [Equiv.trans_apply]
        rw [clocks₂, clocks₁]

end Swaps

/-! ## Sites for the candidate step: the identities a firing writes -/

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Written

/-- The occurrence identities a firing writes: what it takes and what it makes. -/
def written (f : Firing T S O) : Finset O := (f.selection.taken ++ f.selection.made).toFinset

/-- Firings whose independence is decided by what they write: no guards, no predicate queries,
no reads. -/
structure WritesOnly (f : Firing T S O) : Prop where
  checks : f.rule.checks = []
  queries : f.queries = []
  reads : f.selection.read = []

theorem commit_of_writesOnly {f : Firing T S O} (only : WritesOnly f) :
    f.selection.commit (T := T) = ⟨f.selection.taken.toFinset, ∅, f.selection.made.toFinset, []⟩ := by
  simp only [Selection.commit, only.reads, List.toFinset_nil]

/-- **For firings that only write, static independence is disjointness of what they write.** -/
theorem staticIndependent_iff_written [Nonempty S] {label : O → T} {f g : Firing T S O}
    (fOnly : WritesOnly f) (gOnly : WritesOnly g) :
    StaticIndependent label f g ↔ Disjoint (written f) (written g) := by
  have fFoot : ∀ σ : S, f.footprintAt σ = f.selection.commit (T := T) :=
    Firing.footprintAt_of_queries_nil fOnly.queries
  have gFoot : ∀ σ : S, g.footprintAt σ = g.selection.commit (T := T) :=
    Firing.footprintAt_of_queries_nil gOnly.queries
  have fStatic : f.Static :=
    ⟨fOnly.checks, by intro query member; rw [fOnly.queries] at member; cases member⟩
  have gStatic : g.Static :=
    ⟨gOnly.checks, by intro query member; rw [gOnly.queries] at member; cases member⟩
  have ground : MeTTaCalculus.OccurrenceCommits.TraceIndependent label
      (f.selection.commit (T := T)) (g.selection.commit (T := T)) ↔
        Disjoint (written f) (written g) := by
    rw [commit_of_writesOnly fOnly, commit_of_writesOnly gOnly]
    unfold written
    rw [List.toFinset_append, List.toFinset_append]
    constructor
    · rintro ⟨⟨noClash, -, -⟩, fMade, gMade⟩
      have taken : Disjoint f.selection.taken.toFinset g.selection.taken.toFinset := by
        by_contra clash
        exact noClash (Or.inl clash)
      have made : Disjoint f.selection.made.toFinset g.selection.made.toFinset := by
        by_contra clash
        exact noClash (Or.inr clash)
      have fMadeTaken : Disjoint f.selection.made.toFinset g.selection.taken.toFinset := by
        simpa [MeTTaCalculus.OccurrenceCommits.Commit.uses] using fMade
      have gMadeTaken : Disjoint g.selection.made.toFinset f.selection.taken.toFinset := by
        simpa [MeTTaCalculus.OccurrenceCommits.Commit.uses] using gMade
      rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨taken, gMadeTaken.symm⟩, ⟨fMadeTaken, made⟩⟩
    · intro apart
      rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
        at apart
      obtain ⟨⟨taken, takenMade⟩, ⟨madeTaken, made⟩⟩ := apart
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · rintro (clash | clash)
        · exact clash taken
        · exact clash made
      · rintro (spoiled | ⟨read, member, _⟩)
        · exact spoiled (Finset.disjoint_empty_right _)
        · cases member
      · rintro (spoiled | ⟨read, member, _⟩)
        · exact spoiled (Finset.disjoint_empty_right _)
        · cases member
      · simpa [MeTTaCalculus.OccurrenceCommits.Commit.uses] using madeTaken
      · simpa [MeTTaCalculus.OccurrenceCommits.Commit.uses] using takenMade.symm
  constructor
  · rintro ⟨-, -, independent⟩
    have atOne := independent (Classical.arbitrary S)
    rw [fFoot, gFoot] at atOne
    exact ground.mp atOne
  · intro apart
    refine ⟨fStatic, gStatic, fun σ => ?_⟩
    rw [fFoot, gFoot]
    exact ground.mpr apart

/-- **The identities a firing writes cover the Mazurkiewicz dependence** of a run of firings that
only write, each writing something. -/
theorem written_cover [Nonempty S] {label : O → T} {w : List (Firing T S O)}
    (only : ∀ f ∈ w, WritesOnly f) (writes : ∀ f ∈ w, (written f).Nonempty) :
    SitesCover (MazurkiewiczIndependent label) written w := by
  intro f inF g inG
  rw [← Finset.not_disjoint_iff_nonempty_inter]
  constructor
  · intro dependent apart
    by_cases same : f = g
    · subst same
      obtain ⟨o, member⟩ := writes f inF
      exact Finset.disjoint_left.mp apart member member
    · exact dependent ⟨same, (staticIndependent_iff_written (only f inF) (only g inG)).mpr apart⟩
  · rintro notApart ⟨-, independent⟩
    exact notApart ((staticIndependent_iff_written (only f inF) (only g inG)).mp independent)

/-- **For runs of firings that only write, vector clocks over occurrence identities characterize
the causal order of the candidate step.** -/
theorem causal_iff_written_clock_le [Nonempty S] {label : O → T} {w : List (Firing T S O)}
    (only : ∀ f ∈ w, WritesOnly f) (writes : ∀ f ∈ w, (written f).Nonempty) (i j : Fin w.length) :
    Causal (MazurkiewiczIndependent label) w i j ↔
      ∀ o, clock (MazurkiewiczIndependent label) written w i o ≤
        clock (MazurkiewiczIndependent label) written w j o :=
  causal_iff_clock_le (written_cover only writes) (fun f _ => MazurkiewiczIndependent.irrefl label f)
    i j

/-- **The vector clock over occurrence identities is a property of the static trace**: statically
trace-equivalent runs have a bijection of positions that keeps the firings, the causal order and
every clock. -/
theorem written_clock_traceEquiv {label : O → T} {w w' : List (Firing T S O)}
    (equivalent : Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv (MazurkiewiczIndependent label)
      w w') :
    ∃ π : Fin w.length ≃ Fin w'.length, (∀ k, w'[π k] = w[k]) ∧
      (∀ i j, Causal (MazurkiewiczIndependent label) w' (π i) (π j) ↔
        Causal (MazurkiewiczIndependent label) w i j) ∧
        ∀ j o, clock (MazurkiewiczIndependent label) written w' (π j) o =
          clock (MazurkiewiczIndependent label) written w j o :=
  clock_traceEquiv _ written (fun _ _ independent => independent.symm) equivalent

variable (A : SubstitutionAction T S) (label : O → T)

/-- **The run clock**: at each identity, how many firings of the run write it. -/
def runClock : Mettapedia.Effects.RunAccount (Runs A label) (Multiplicative (O → ℕ)) :=
  siteAccount A label fun f => Multiplicative.ofAdd fun o => if o ∈ written f then 1 else 0

/-- **The run clock is a functor on static traces.** -/
theorem runClock_factors_static :
    ∃ traced : Mettapedia.Effects.RunAccount (StaticTraces A label) (Multiplicative (O → ℕ)),
      traced.comap (Mettapedia.GSLT.Causality.TraceCostValuation.traceFunctor _) = runClock A label :=
  siteAccount_factors_static A label _

/-- **The run clock is a functor on contextual traces.** -/
theorem runClock_factors_contextual :
    ∃ traced : Mettapedia.Effects.RunAccount (ContextualTraces A label) (Multiplicative (O → ℕ)),
      traced.comap (Mettapedia.GSLT.Causality.TraceCostValuation.traceFunctor _) = runClock A label :=
  siteAccount_factors_contextual A label _

end Written

/-! ## Controls -/

namespace ClockControls

/-- Two letters. -/
abbrev Letter := Bool

/-- Independence of two different letters. -/
abbrev apartLetters (a b : Letter) : Prop := a ≠ b

/-- One site, shared by both letters. -/
def sharedSite (_ : Letter) : Finset ℕ := {0}

/-- The word `false, true`. -/
def word : List Letter := [false, true]

def first : Fin word.length := ⟨0, by decide⟩
def second : Fin word.length := ⟨1, by decide⟩

theorem not_causal_first_second : ¬ Causal apartLetters word first second := by
  intro causal
  have step : DirectlyBefore apartLetters word first second := by
    rcases Relation.ReflTransGen.cases_tail causal with same | ⟨k, toK, last⟩
    · exact absurd (congrArg Fin.val same) (by decide)
    · have kLe : k < second := last.1
      have kZero : k = first := by
        apply Fin.ext
        have : k.val < 1 := kLe
        change k.val = 0
        omega
      subst kZero
      exact last
  exact step.2 (by decide)

/-- **Negative control: a shared site without dependence.** The two letters are independent and share
a site; the first clock lies below the second, and the first event does not precede the second. -/
theorem shared_site_without_dependence :
    (∀ s, clock apartLetters sharedSite word first s ≤ clock apartLetters sharedSite word second s) ∧
      ¬ Causal apartLetters word first second := by
  refine ⟨fun s => ?_, not_causal_first_second⟩
  have pastFirst : past apartLetters word first = {first} := by
    ext k
    rw [mem_past, Finset.mem_singleton]
    constructor
    · intro causal
      apply Fin.ext
      have := causal.le
      have : k.val ≤ 0 := this
      change k.val = 0
      omega
    · rintro rfl
      exact .refl
  have secondInPast : second ∈ past apartLetters word second := (mem_past _ _).mpr .refl
  unfold clock
  rw [pastFirst]
  by_cases atS : s = 0
  · subst atS
    have one : ({first} ∩ atSite sharedSite word 0 : Finset (Fin word.length)).card ≤ 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans (Finset.card_singleton _).le
    have pos : 1 ≤ (past apartLetters word second ∩ atSite sharedSite word 0).card :=
      Finset.card_pos.mpr ⟨second, Finset.mem_inter.mpr ⟨secondInPast,
        (mem_atSite _ _).mpr (by simp [sharedSite])⟩⟩
    omega
  · have empty : ({first} ∩ atSite sharedSite word s : Finset (Fin word.length)) = ∅ := by
      ext k
      simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      intro _ atK
      exact atS (by simpa [sharedSite] using (mem_atSite _ _).mp atK)
    rw [empty]
    exact Nat.zero_le _

/-- No site at all. -/
def noSite (_ : Letter) : Finset ℕ := ∅

/-- **Negative control: a letter with no site.** Its clock is zero, below every clock, whatever the
causal order. -/
theorem siteless_letter (j : Fin word.length) (s : ℕ) :
    clock apartLetters noSite word first s = 0 ∧
      clock apartLetters noSite word first s ≤ clock apartLetters noSite word j s := by
  have zero : ∀ k : Fin word.length, clock apartLetters noSite word k s = 0 := by
    intro k
    unfold clock
    rw [Finset.card_eq_zero]
    ext x
    simp [atSite, noSite]
  exact ⟨zero first, by rw [zero first]; exact Nat.zero_le _⟩

/-- Dependence of every two letters, and sites that cover it. -/
abbrev allDependent (_ _ : Letter) : Prop := False

/-- **Positive control: the characterization.** With every two letters dependent and one shared
site, the first event precedes the second, and the clocks agree. -/
theorem chain_characterized :
    Causal allDependent word first second ∧
      (∀ s, clock allDependent sharedSite word first s ≤ clock allDependent sharedSite word second s) := by
  have cover : SitesCover allDependent sharedSite word := by
    intro a _ b _
    simp [allDependent, sharedSite]
  have causal : Causal allDependent word first second :=
    Relation.ReflTransGen.single ⟨by decide, fun h => h⟩
  exact ⟨causal, (causal_iff_clock_le cover (fun _ _ h => h) first second).mp causal⟩

/-- The word in the other order. -/
def reversed : List Letter := [true, false]

/-- **Negative control: the clocks separate the two orders of a dependent pair.** With every two
letters dependent, no bijection of positions between `false, true` and `true, false` keeps the
letters and the clocks: the second event of the first word has seen two events, the same letter
first in the other word has seen one. -/
theorem dependent_orders_separated :
    ¬ ∃ π : Fin word.length ≃ Fin reversed.length, (∀ k, reversed[π k] = word[k]) ∧
      ∀ j s, clock allDependent sharedSite reversed (π j) s = clock allDependent sharedSite word j s := by
  rintro ⟨π, letters, clocks⟩
  have atZero : (π second).val = 0 := by
    have bound := (π second).isLt
    have letter := letters second
    change reversed[π second] = true at letter
    have : (π second).val < 2 := bound
    by_contra notZero
    have one : (π second).val = 1 := by omega
    have shape : π second = ⟨1, by decide⟩ := Fin.ext one
    simp only [shape] at letter
    simp [reversed] at letter
  have seenTwo : 2 ≤ clock allDependent sharedSite word second 0 := by
    unfold clock
    have both : ({first, second} : Finset (Fin word.length)) ⊆
        past allDependent word second ∩ atSite sharedSite word 0 := by
      intro k member
      rcases Finset.mem_insert.mp member with rfl | member
      · exact Finset.mem_inter.mpr ⟨(mem_past _ _).mpr (Relation.ReflTransGen.single
          ⟨by decide, fun h => h⟩), (mem_atSite _ _).mpr (by simp [sharedSite])⟩
      · obtain rfl := Finset.mem_singleton.mp member
        exact Finset.mem_inter.mpr ⟨(mem_past _ _).mpr .refl,
          (mem_atSite _ _).mpr (by simp [sharedSite])⟩
    have card : ({first, second} : Finset (Fin word.length)).card = 2 := by decide
    exact card ▸ Finset.card_le_card both
  have seenOne : clock allDependent sharedSite reversed (π second) 0 ≤ 1 := by
    unfold clock
    have only : past allDependent reversed (π second) ∩ atSite sharedSite reversed 0 ⊆ {π second} := by
      intro k member
      have causal := (mem_past _ _).mp (Finset.mem_inter.mp member).1
      have le : k.val ≤ (π second).val := causal.le
      exact Finset.mem_singleton.mpr (Fin.ext (by omega))
    exact (Finset.card_le_card only).trans (Finset.card_singleton _).le
  have same := clocks second 0
  omega

end ClockControls

#print axioms Causal.le
#print axioms chain_at_site
#print axioms causal_iff_clock_le
#print axioms clock_last
#print axioms clock_le_card
#print axioms getElem_swapIndex
#print axioms directlyBefore_swap
#print axioms causal_swap
#print axioms clock_swap
#print axioms clock_traceEquiv
#print axioms staticIndependent_iff_written
#print axioms written_cover
#print axioms causal_iff_written_clock_le
#print axioms written_clock_traceEquiv
#print axioms runClock_factors_static
#print axioms runClock_factors_contextual
#print axioms ClockControls.shared_site_without_dependence
#print axioms ClockControls.siteless_letter
#print axioms ClockControls.chain_characterized
#print axioms ClockControls.dependent_orders_separated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
