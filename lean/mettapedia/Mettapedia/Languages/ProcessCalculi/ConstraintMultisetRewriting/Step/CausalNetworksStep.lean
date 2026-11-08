import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CausalNetworks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Intervention

/-!
# A causal Bayesian network as a step program

## Cell systems realized by ground firings (`Realization`)

A cell system is **realized on the step** by an injective family of ground firings and a store
for every configuration, when a firing's commit is enabled at the store of a configuration exactly
when its event is a candidate there, and firing it gives the store of the grown configuration.

* The admitted firings at such a store are the candidates' firings (`mem_admitted`), so the
  linearizations of a history are the step's own runs, and the step's race total is the cell
  system's (`total_eq`).
* **The step's trace distribution is the cell system's jump chain** (`traceProb_eq`), for any
  weights on firings that agree with the cell system's on its firings.

## The network program (`Atom`, `firing`, `present`, `realization`)

The atoms are `(pend v)`, `(val v b)` and `(reg v r)`, all at the space handle of `v` (`handle`).
The firing of the event `⟨v, (row, r, b)⟩` is Meredith's variable gadget written on the step:
* it takes `(pend v)`;
* it reads `(reg v r)` and the parents' values `(val p (row p))`: **a join on the parents' rows**;
* it makes `(val v b)`. The firings of one row and regime race over the domain, with **the
  conditional probability table as weights**.

## On the step

* **The history likelihood is the Bayesian-network joint** (`step_likelihood_eq_jointWeight`): the
  sum, over the linearizations of the history of `x`, of the step's `Race.traceProb` from the
  store with every variable pending.
* **A do at the variables' handles gives the truncated factorization** (`step_do_likelihood`). The
  do is R103's `Intervention.DoAt` at the handle of each set variable, as a restriction of the
  weights (`Intervention.restrictWeight`), when the set values have positive probability on the
  history's rows. It reaches only the firings of the set variables, the only ones that make
  atoms at those handles (`doAt_other_variable`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalNetworksStep

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open CausalCells
open CausalNetworks
open Mettapedia.GSLT.Causality.DoCalculus
open Mettapedia.ProbabilityTheory.BayesianNetworks

universe uE uC uT uS uO

/-! ## Sums with one surviving term -/

theorem sum_ite_single {X : Type*} (p : X → Prop) (dec : DecidablePred p) (G : X → ℝ) {a : X} :
    ∀ (L : List X), L.Nodup → a ∈ L → (∀ f ∈ L, p f ↔ f = a) →
      (L.map fun f => @ite ℝ (p f) (dec f) (G f) 0).sum = G a
  | [], _, member, _ => absurd member (by simp)
  | f :: rest, nodup, member, iff => by
      rw [List.map_cons, List.sum_cons]
      by_cases head : f = a
      · subst head
        have restZero : (rest.map fun g => @ite ℝ (p g) (dec g) (G g) 0).sum = 0 := by
          apply List.sum_eq_zero
          intro z hz
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hz
          have notP : ¬ p g := fun hp =>
            (List.nodup_cons.mp nodup).1 (((iff g (List.mem_cons_of_mem _ hg)).mp hp) ▸ hg)
          exact if_neg notP
        rw [restZero, add_zero, if_pos ((iff f List.mem_cons_self).mpr rfl)]
      · have notP : ¬ p f := fun hp => head ((iff f List.mem_cons_self).mp hp)
        rw [if_neg notP, zero_add]
        have inRest : a ∈ rest := by
          rcases List.mem_cons.mp member with same | inside
          · exact absurd same.symm head
          · exact inside
        exact sum_ite_single p dec G rest (List.nodup_cons.mp nodup).2 inRest
          (fun g hg => iff g (List.mem_cons_of_mem _ hg))

/-! ## Cell systems realized by ground firings -/

section Realization

variable {E : Type uE} {C : Type uC} [DecidableEq E] [Fintype E] (K : CellSystem E C)
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] (label : O → T)

/-- **A realization of a cell system on the step**: ground firings for the events and a store for
every configuration, such that enabling is candidacy and firing grows the configuration. -/
structure Realization where
  firing : E → Firing T S O
  injective : Function.Injective firing
  ground : ∀ e, Race.Ground label (firing e)
  present : Finset E → Finset O
  enabled_iff : ∀ y e,
    Enabled label (present y) ((firing e).selection.commit (T := T)) ↔ e ∈ K.candidates y
  fire_eq : ∀ y e, fire (present y) ((firing e).selection.commit (T := T)) = present (insert e y)

namespace Realization

variable {K label} (P : Realization K (S := S) label)

/-- The program's alphabet: the firings of all events. -/
def alphabet : List (Firing T S O) := (Finset.univ : Finset E).toList.map P.firing

theorem alphabet_nodup : P.alphabet.Nodup := (Finset.nodup_toList _).map P.injective

theorem mem_alphabet (e : E) : P.firing e ∈ P.alphabet :=
  List.mem_map.mpr ⟨e, Finset.mem_toList.mpr (Finset.mem_univ e), rfl⟩

theorem queried : ∀ f ∈ P.alphabet, Contention.Queried label f [] := by
  intro f member
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp member
  have g := P.ground e
  exact ⟨⟨g.take, g.read, g.tell, g.checks, g.produce, rfl, g.taken_nodup, g.made_nodup⟩,
    by rw [g.queries]; rfl⟩

variable (A : SubstitutionAction T S)

/-- **The admitted firings at the store of a configuration are its candidates' firings.** -/
theorem mem_admitted {y : Finset E} {Cfg : Configuration T O} (present : Cfg.present = P.present y)
    (refl : Race.Reflexive Cfg.equations) (e : E) :
    P.firing e ∈ Race.admitted A label P.alphabet Cfg ↔ e ∈ K.candidates y := by
  rw [Contention.mem_admitted, (P.ground e).valid_iff A refl, present, P.enabled_iff]
  exact ⟨fun both => both.2, fun cand => ⟨P.mem_alphabet e, cand⟩⟩

theorem admitted_nodup (Cfg : Configuration T O) : (Race.admitted A label P.alphabet Cfg).Nodup := by
  classical
  rw [Contention.admitted_eq]
  exact P.alphabet_nodup.filter _

/-- **The step's race total is the cell system's**, for weights that agree on the firings. -/
theorem total_eq {w : Firing T S O → ℝ} (agree : ∀ e, w (P.firing e) = K.weight e)
    {y : Finset E} {Cfg : Configuration T O} (present : Cfg.present = P.present y)
    (refl : Race.Reflexive Cfg.equations) :
    Race.total A label P.alphabet w Cfg = K.total y := by
  classical
  unfold Race.total
  rw [← List.sum_toFinset w (P.admitted_nodup A Cfg)]
  have image : (Race.admitted A label P.alphabet Cfg).toFinset = (K.candidates y).image P.firing := by
    ext f
    rw [List.mem_toFinset, Finset.mem_image]
    constructor
    · intro member
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp (Contention.mem_admitted.mp member).1
      exact ⟨e, (P.mem_admitted A present refl e).mp member, rfl⟩
    · rintro ⟨e, cand, rfl⟩
      exact (P.mem_admitted A present refl e).mpr cand
  rw [image, Finset.sum_image (fun _ _ _ _ same => P.injective same), K.total_eq_sum_candidates]
  exact Finset.sum_congr rfl fun e _ => agree e

/-- **The step's trace distribution along a linearization is the cell system's jump chain.** -/
theorem traceProb_eq {w : Firing T S O → ℝ} (agree : ∀ e, w (P.firing e) = K.weight e) {X : Finset E} :
    ∀ {y : Finset E} {l : List E}, K.IsLin X y l → ∀ (Cfg : Configuration T O),
      Cfg.present = P.present y → Race.Reflexive Cfg.equations →
        Race.traceProb A label P.alphabet id w (l.map P.firing) Cfg = K.pathProb y l := by
  intro y l lin
  induction lin with
  | nil => intro _ _ _; rfl
  | @cons y e l cand _ _ ih =>
      intro Cfg present refl
      rw [List.map_cons, Race.traceProb]
      have single := sum_ite_single (fun f => id f = P.firing e) (fun _ => Classical.propDecidable _)
        (fun f => w f / Race.total A label P.alphabet w Cfg *
          Race.traceProb A label P.alphabet id w (l.map P.firing) (f.result label Cfg))
        (Race.admitted A label P.alphabet Cfg) (P.admitted_nodup A Cfg)
        ((P.mem_admitted A present refl e).mpr cand) (fun _ _ => Iff.rfl)
      rw [single, agree e, P.total_eq A agree present refl]
      have grown : ((P.firing e).result label Cfg).present = P.present (insert e y) := by
        show fire Cfg.present ((P.firing e).selection.commit (T := T)) = _
        rw [present, P.fire_eq]
      rw [ih _ grown ((P.ground e).reflexive_result refl)]
      rfl

end Realization

end Realization

/-! ## The network program -/

/-- **The atoms of the network program**: a pending variable, a value, and a regime. -/
inductive Atom (V β R : Type) where
  | pend : V → Atom V β R
  | val : V → β → Atom V β R
  | reg : V → R → Atom V β R
  deriving DecidableEq

variable {V β : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype β] [DecidableEq β] [MeasurableSpace β]
variable (graph : DirectedGraph V)
variable (acyclic : graph.IsAcyclic)
variable [DecidableRel graph.edges]
variable {R : Type} [Fintype R] [DecidableEq R]
variable {S : Type uS}

local notation "Ev" => Event (β := β) (R := R) graph

/-- **The space handle of an atom**: the variable it belongs to. -/
def handle : Atom V β R → V
  | .pend v => v
  | .val v _ => v
  | .reg v _ => v

/-- What the firing of an event reads: its regime and its parents' values. -/
def reads (e : Ev) : List (Atom V β R) :=
  .reg e.1 e.2.2.1 :: (Finset.univ : Finset (ParentIdx graph e.1)).toList.map
    fun p => .val p.1 (e.2.1 p)

/-- **The firing of an event**: take the pending atom, read the regime and the parents' row, make
the value. -/
def firing (e : Ev) : Firing (Atom V β R) S (Atom V β R) :=
  ⟨⟨[.pend e.1], reads graph e, [], [], [.val e.1 e.2.2.2]⟩, [],
    ⟨[.pend e.1], reads graph e, [.val e.1 e.2.2.2]⟩⟩

/-- **The store of a configuration**: the unfired variables pending, the values made, the regimes
installed. -/
def present (regime : V → R) (y : Finset Ev) : Finset (Atom V β R) :=
  (Finset.univ.filter fun v => ∀ e ∈ y, e.1 ≠ v).image Atom.pend ∪
    y.image (fun e => Atom.val e.1 e.2.2.2) ∪ Finset.univ.image fun v => Atom.reg v (regime v)

variable {graph}

omit [MeasurableSpace β] in
theorem mem_present_pend {regime : V → R} {y : Finset Ev} {w : V} :
    Atom.pend w ∈ present graph regime y ↔ ∀ e ∈ y, e.1 ≠ w := by
  simp [present]

omit [MeasurableSpace β] in
theorem mem_present_val {regime : V → R} {y : Finset Ev} {w : V} {b : β} :
    Atom.val w b ∈ present graph regime y ↔ ∃ e ∈ y, e.1 = w ∧ e.2.2.2 = b := by
  simp [present]

omit [MeasurableSpace β] in
theorem mem_present_reg {regime : V → R} {y : Finset Ev} {w : V} {r : R} :
    Atom.reg w r ∈ present graph regime y ↔ regime w = r := by
  simp [present]

omit [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β] [Fintype R] [DecidableEq R] in
theorem firing_injective : Function.Injective (firing (S := S) graph (R := R) (β := β)) := by
  rintro ⟨v, row, r, b⟩ ⟨v', row', r', b'⟩ same
  have made := congrArg (fun f : Firing (Atom V β R) S (Atom V β R) => f.selection.made) same
  have read := congrArg (fun f : Firing (Atom V β R) S (Atom V β R) => f.selection.read) same
  simp only [firing, List.cons.injEq, Atom.val.injEq, and_true] at made
  obtain ⟨rfl, rfl⟩ := made
  simp only [firing, reads, List.cons.injEq, Atom.reg.injEq, true_and] at read
  obtain ⟨rfl, rows⟩ := read
  have sameRow : row = row' := by
    funext p
    have := (List.map_inj_left.mp rows) p (Finset.mem_toList.mpr (Finset.mem_univ p))
    simpa using this
  subst sameRow
  rfl

omit [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β] [Fintype R] [DecidableEq R] in
theorem firing_ground (e : Ev) : Race.Ground id (firing (S := S) graph e) where
  take := rfl
  read := (List.map_id _).symm
  tell := rfl
  checks := rfl
  produce := rfl
  queries := rfl
  taken_nodup := List.nodup_singleton _
  made_nodup := List.nodup_singleton _

omit [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β] [Fintype R] [DecidableEq R] in
theorem val_mem_reads (e : Ev) (p : ParentIdx graph e.1) : Atom.val p.1 (e.2.1 p) ∈ reads graph e :=
  List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, Finset.mem_toList.mpr (Finset.mem_univ p), rfl⟩)

omit [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β] [Fintype R] [DecidableEq R] in
theorem reg_mem_reads (e : Ev) : Atom.reg e.1 e.2.2.1 ∈ reads graph e := List.mem_cons_self

omit [MeasurableSpace β] in
/-- The linearizations of the network do not depend on its weights. -/
theorem lins_table (regime : V → R) (t₁ t₂ : Ev → ℝ) :
    (cells graph regime t₁).lins = (cells graph regime t₂).lins := by
  funext X x
  unfold CellSystem.lins
  generalize (X \ x).card = n
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp only [CellSystem.linsN]
      congr 1
      funext e
      rw [ih]

omit [MeasurableSpace β] in
theorem enabled_iff (regime : V → R) (table : Ev → ℝ) (y : Finset Ev) (e : Ev) :
    Enabled id (present graph regime y)
        ((firing (S := S) graph e).selection.commit (T := Atom V β R)) ↔
      e ∈ (cells graph regime table).candidates y := by
  rw [CellSystem.mem_candidates, mem_enabled]
  have own : e ∈ (cells graph regime table).members ((cells graph regime table).cell e) :=
    Finset.mem_image.mpr ⟨e.2.2.2, Finset.mem_univ _, rfl⟩
  have readMem : ∀ a, a ∈ ((firing (S := S) graph e).selection.commit (T := Atom V β R)).kept ↔
      a ∈ reads graph e := by
    intro a
    simp [firing, Selection.commit]
  constructor
  · intro enabled
    have pending : Atom.pend e.1 ∈ present graph regime y :=
      enabled.taken_subset (by simp [firing, Selection.commit])
    have readIn : ∀ a ∈ reads graph e, a ∈ present graph regime y :=
      fun a ha => enabled.kept_subset ((readMem a).mpr ha)
    refine ⟨⟨mem_present_pend.mp pending, fun p => ?_, ?_⟩, own⟩
    · exact mem_present_val.mp (readIn _ (val_mem_reads e p))
    · exact (mem_present_reg.mp (readIn _ (reg_mem_reads e))).symm
  · rintro ⟨⟨unfired, rows, installed⟩, -⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      simp only [firing, Selection.commit, List.mem_toFinset, List.mem_singleton] at ha
      subst ha
      exact mem_present_pend.mpr unfired
    · intro a ha
      rw [readMem] at ha
      simp only [reads, List.mem_cons, List.mem_map, Finset.mem_toList, Finset.mem_univ,
        true_and] at ha
      rcases ha with rfl | ⟨p, rfl⟩
      · exact mem_present_reg.mpr installed.symm
      · exact mem_present_val.mpr (rows p)
    · rw [Finset.disjoint_left]
      intro a ha hb
      simp only [firing, Selection.commit, List.mem_toFinset, List.mem_singleton] at ha
      subst ha
      rw [readMem] at hb
      simp [reads] at hb
    · rw [Finset.disjoint_left]
      intro a ha hb
      simp only [firing, Selection.commit, List.mem_toFinset, List.mem_singleton] at ha
      subst ha
      obtain ⟨e', inY, var, _⟩ := mem_present_val.mp hb
      exact unfired e' inY var
    · intro query member
      simp [firing, Selection.commit] at member

omit [MeasurableSpace β] in
theorem fire_eq (regime : V → R) (y : Finset Ev) (e : Ev) :
    fire (present graph regime y) ((firing (S := S) graph e).selection.commit (T := Atom V β R)) =
      present graph regime (insert e y) := by
  ext a
  rw [mem_fire]
  simp only [firing, Selection.commit, List.mem_toFinset, List.mem_singleton]
  cases a with
  | pend w =>
      rw [mem_present_pend, mem_present_pend, Finset.forall_mem_insert]
      simp only [Atom.pend.injEq, reduceCtorEq, or_false]
      constructor
      · rintro ⟨unfired, other⟩
        exact ⟨fun h => other h.symm, unfired⟩
      · rintro ⟨first, unfired⟩
        exact ⟨unfired, fun h => first h.symm⟩
  | val w b =>
      rw [mem_present_val, mem_present_val, Finset.exists_mem_insert]
      simp only [reduceCtorEq, not_false_eq_true, and_true, Atom.val.injEq]
      constructor
      · rintro (made | ⟨rfl, rfl⟩)
        · exact Or.inr made
        · exact Or.inl ⟨rfl, rfl⟩
      · rintro (⟨rfl, rfl⟩ | made)
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl made
  | reg w r =>
      rw [mem_present_reg, mem_present_reg]
      simp

variable (graph)

/-- **The network program as a realization of the network's cell system.** -/
def realization (regime : V → R) (table : Ev → ℝ) :
    Realization (cells graph regime table) (S := S) (id : Atom V β R → Atom V β R) where
  firing := firing graph
  injective := firing_injective
  ground := firing_ground
  present := present graph regime
  enabled_iff := enabled_iff regime table
  fire_eq := fire_eq regime

/-- The store with every variable pending. -/
def start (regime : V → R) : Configuration (Atom V β R) (Atom V β R) :=
  ⟨[], present graph regime ∅⟩

/-- The weight a firing reads from the conditional probability table. -/
def stepWeight (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (f : Firing (Atom V β Unit) S (Atom V β Unit)) : ℝ := by
  classical
  exact if h : ∃ e, firing graph e = f then cptWeight graph acyclic cpt (Classical.choose h) else 0

/-- **The do at the handle of every set variable**: each make there is the set value. -/
def doKeep (assignment : V → Option β) (f : Firing (Atom V β Unit) S (Atom V β Unit)) : Prop :=
  ∀ v a, assignment v = some a → Intervention.DoAt handle id v (fun t => t = Atom.val v a) f

variable {graph}

omit [DecidableEq β] in
theorem stepWeight_firing (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (e : Event (β := β) (R := Unit) graph) :
    stepWeight (S := S) graph acyclic cpt (firing graph e) = cptWeight graph acyclic cpt e := by
  have found : ∃ e', firing (S := S) graph e' = firing graph e := ⟨e, rfl⟩
  unfold stepWeight
  rw [dif_pos found, firing_injective (Classical.choose_spec found)]

omit [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
/-- A do at the handle of `v` admits every firing of another variable: it makes nothing there. -/
theorem doAt_other_variable {v w : V} (other : w ≠ v) (φ : Atom V β Unit → Prop)
    (e : Event (β := β) (R := Unit) graph) (ofW : e.1 = w) :
    Intervention.DoAt handle id v φ (firing (S := S) graph e) := by
  intro o made atHandle
  simp only [firing, List.mem_singleton] at made
  subst made
  exact absurd (ofW.symm.trans atHandle) other

theorem restrict_doKeep (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (assignment : V → Option β) (e : Event (β := β) (R := Unit) graph) :
    Intervention.restrictWeight (doKeep (S := S) assignment) (stepWeight graph acyclic cpt)
        (firing graph e) = doWeight graph acyclic cpt assignment e := by
  classical
  unfold Intervention.restrictWeight doWeight
  rw [stepWeight_firing]
  have keepIff : doKeep (S := S) assignment (firing graph e) ↔
      ∀ a, assignment e.1 = some a → e.2.2.2 = a := by
    constructor
    · intro keep a set
      have := keep e.1 a set (Atom.val e.1 e.2.2.2) (by simp [firing]) rfl
      simpa using this
    · intro keep v a set o made atHandle
      simp only [firing, List.mem_singleton] at made
      subst made
      have var : e.1 = v := atHandle
      subst var
      simpa using keep a set
  by_cases keep : doKeep (S := S) assignment (firing graph e)
  · rw [if_pos keep]
    cases set : assignment e.1 with
    | none => rfl
    | some a =>
        dsimp only
        rw [if_pos ((keepIff.mp keep) a set)]
  · rw [if_neg keep]
    cases set : assignment e.1 with
    | none => exact absurd (keepIff.mpr fun a h => by rw [set] at h; cases h) keep
    | some a =>
        have notA : e.2.2.2 ≠ a := fun same => keep (keepIff.mpr fun a' set' => by
          rw [set] at set'
          cases set'
          exact same)
        dsimp only
        rw [if_neg notA]

variable (A : SubstitutionAction (Atom V β Unit) S)

/-- **The network program on the step: its history likelihood is the Bayesian-network joint.** -/
theorem step_likelihood_eq_jointWeight (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (x : V → β) (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order) :
    ∑ l ∈ (cells graph plain (cptWeight graph acyclic cpt)).lins (historyOf graph plain x) ∅,
        Race.traceProb A id (realization (S := S) graph plain (cptWeight graph acyclic cpt)).alphabet
          id (stepWeight graph acyclic cpt)
          (l.map (realization (S := S) graph plain (cptWeight graph acyclic cpt)).firing)
          (start graph plain) =
      (cpt.jointWeight x).toReal := by
  have bridge : ∀ l ∈ (cells graph plain (cptWeight graph acyclic cpt)).lins
      (historyOf graph plain x) ∅,
      Race.traceProb A id (realization (S := S) graph plain (cptWeight graph acyclic cpt)).alphabet
          id (stepWeight graph acyclic cpt)
          (l.map (realization (S := S) graph plain (cptWeight graph acyclic cpt)).firing)
          (start graph plain) =
        (cells graph plain (cptWeight graph acyclic cpt)).pathProb ∅ l := by
    intro l member
    exact (realization (S := S) graph plain (cptWeight graph acyclic cpt)).traceProb_eq A
      (stepWeight_firing acyclic cpt)
      (((cells graph plain _).mem_lins _ _ l).mp member) _ rfl Race.reflexive_nil
  rw [Finset.sum_congr rfl bridge]
  exact likelihood_eq_jointWeight acyclic cpt x order horder

/-- **A do at the variables' handles gives the truncated factorization on the step.** -/
theorem step_do_likelihood (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (assignment : V → Option β) (x : V → β) (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    (setPositive : ∀ v a, assignment v = some a →
      0 < (cptAt graph acyclic cpt v (parentFunOf graph x v) a).toReal) :
    ∑ l ∈ (cells graph plain (cptWeight graph acyclic cpt)).lins (historyOf graph plain x) ∅,
        Race.traceProb A id (realization (S := S) graph plain (cptWeight graph acyclic cpt)).alphabet
          id (Intervention.restrictWeight (doKeep (S := S) assignment) (stepWeight graph acyclic cpt))
          (l.map (realization (S := S) graph plain (cptWeight graph acyclic cpt)).firing)
          (start graph plain) =
      (truncatedWeight graph acyclic cpt assignment x).toReal := by
  have bridge : ∀ l ∈ (cells graph plain (doWeight graph acyclic cpt assignment)).lins
      (historyOf graph plain x) ∅,
      Race.traceProb A id
          (realization (S := S) graph plain (doWeight graph acyclic cpt assignment)).alphabet id
          (Intervention.restrictWeight (doKeep (S := S) assignment) (stepWeight graph acyclic cpt))
          (l.map (realization (S := S) graph plain (doWeight graph acyclic cpt assignment)).firing)
          (start graph plain) =
        (cells graph plain (doWeight graph acyclic cpt assignment)).pathProb ∅ l := by
    intro l member
    exact (realization (S := S) graph plain (doWeight graph acyclic cpt assignment)).traceProb_eq A
      (restrict_doKeep acyclic cpt assignment)
      (((cells graph plain _).mem_lins _ _ l).mp member) _ rfl Race.reflexive_nil
  rw [lins_table plain (cptWeight graph acyclic cpt) (doWeight graph acyclic cpt assignment)]
  exact (Finset.sum_congr rfl bridge).trans
    (likelihood_doWeight acyclic cpt assignment x order horder setPositive)

#print axioms sum_ite_single
#print axioms Realization.mem_admitted
#print axioms Realization.total_eq
#print axioms Realization.traceProb_eq
#print axioms firing_injective
#print axioms enabled_iff
#print axioms fire_eq
#print axioms restrict_doKeep
#print axioms doAt_other_variable
#print axioms step_likelihood_eq_jointWeight
#print axioms step_do_likelihood

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalNetworksStep

end
