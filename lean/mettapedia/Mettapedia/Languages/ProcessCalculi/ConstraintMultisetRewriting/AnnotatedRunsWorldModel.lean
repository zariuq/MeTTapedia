import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsPredicates
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsLogicEvidence
import Mettapedia.PLN.WorldModel.ObservationSemantics

/-!
# Evidence gathered by runs: the world-model state is a ledger read at the cut

Observations are occurrences of the candidate step. Each has its occurrence identity and records
an outcome in its label. A predicate on labels, the **evidence space**, says which occurrences are
observations.

## The world-model state at a cut

* **The ledger** at a configuration is the set of observation identities present in the evidence
  space (`ledger`). A predicate query of that space holds at the cut exactly when it saw the ledger
  (`ledgerQuery_holds_iff`).
* **The readout** of a query `φ` of outcomes is the ledger's evidence (`readout`): the
  identified-observation evidence of `EvidenceContracts.ledgerEvidence`, so the extraction of the
  ledger world model (`readout_eq_extract`). Strength and confidence are read from it
  (`truthAt`).

## Revision along runs is ledger union

* A firing updates the ledger by what it takes and what it makes (`ledger_result`). A firing that
  takes no observation revises it by union with the observations it makes
  (`ledger_result_of_keeps`), and these are fresh, so the union is disjoint
  (`disjoint_madeObservations`) and additive revision is exact along a run
  (`readout_result_of_keeps`, `readout_follow_of_keeps`).

## The readout is an observer of the ledger, hence of traces

* It depends on a configuration only through its present occurrences (`readout_congr`), so it
  is defined on configuration classes (`readoutClass`).
* Round-equivalent runs, the arrows of the contextual trace category, leave the same readout
  and the same truth value (`readout_roundEquiv`, `truthAt_roundEquiv`); so do statically
  trace-equivalent executable runs (`readout_staticTraceEquiv`). Every level set of the readout
  at the end of a history is a predicate on traces (`readout_tracePredicate`).

## Double counting

* **Additive readouts over the run word double-count.** The sum of the evidence each firing cites
  (`citedSum`) is at least the evidence of the cited ledger (`citedLedger_le_citedSum`), and equal
  to it exactly when the citations are pairwise disjoint
  (`citedSum_eq_iff_pairwise_disjoint`). It is still a site account into a commutative monoid,
  so it factors through traces (`citedAccount_factors_contextual`): trace invariance does not
  prevent double counting.
* **The ledger merge cannot double-count.** Citing again what is already cited leaves the ledger
  as it is (`citedLedger_append_of_subset`), while the additive readout grows
  (`citedSum_append`).
* **Interleavings.** All interleavings of one trace leave one ledger. Summing the readout over the
  interleavings counts it once per interleaving, while the merged ledger counts it once
  (`interleavings_sum`, `interleavings_merge`). The two agree exactly when the ledger is empty
  (`interleaving_sum_eq_merge_iff`), since zero is the only idempotent evidence: this is the
  evidence form of the double count of graded support over the interleavings of one square
  (`AnnotatedRuns.GradeControls.denote_counts_interleavings` against `orBool_square`).
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace WorldModelRuns

open Mettapedia.Effects (RunAccount)

open MeTTaCalculus.OccurrenceCommits (regionOf PredicateQuery fire mem_regionOf mem_fire)
open GuardFreeProcessOrders (SameUpTo)
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)
open Mettapedia.GSLT.Causality.TraceCostValuation (traceFunctor)
open Mettapedia.GSLT.Distinction.CausalGluing (TraceEquiv)

universe uT uS uO uW
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {W : Type uW}

/-! ## The ledger and its predicate query -/

section Ledger

variable (label : O → T) (space : T → Bool)

/-- **The ledger at a cut**: the identities of the observations present in the evidence space. -/
def ledger (C : Configuration T O) : Finset O := regionOf label C.present space

/-- The predicate query of the evidence space that saw `seen`. -/
def ledgerQuery (seen : Finset O) : PredicateQuery O T := ⟨space, seen⟩

omit [DecidableEq O] in
/-- **The world-model state is read by a predicate query**: the query of the evidence space holds
at a cut exactly when what it saw is the ledger. -/
theorem ledgerQuery_holds_iff (C : Configuration T O) (seen : Finset O) :
    (ledgerQuery space seen).Holds label C.present ↔ ledger label space C = seen := Iff.rfl

omit [DecidableEq O] in
theorem mem_ledger {C : Configuration T O} {o : O} :
    o ∈ ledger label space C ↔ o ∈ C.present ∧ space (label o) = true := mem_regionOf

omit [DecidableEq O] in
theorem ledger_congr {C D : Configuration T O} (present : C.present = D.present) :
    ledger label space C = ledger label space D := by
  unfold ledger
  rw [present]

/-- The observations a firing makes into the evidence space. -/
def madeObservations (f : Firing T S O) : Finset O :=
  f.selection.made.toFinset.filter fun o => space (label o) = true

/-- A firing that takes no observation: it never consumes evidence. -/
def KeepsEvidence (f : Firing T S O) : Prop := ∀ o ∈ f.selection.taken, space (label o) = false

/-- **A firing updates the ledger by what it takes and what it makes.** -/
theorem ledger_result (f : Firing T S O) (C : Configuration T O) :
    ledger label space (f.result label C) =
      (ledger label space C \ f.selection.taken.toFinset) ∪ madeObservations label space f := by
  ext o
  simp only [ledger, madeObservations, Firing.result, Selection.result, mem_regionOf, mem_fire,
    Selection.commit, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter, List.mem_toFinset]
  tauto

/-- **Revision is ledger union**: a firing that takes no observation adds the observations it
makes. -/
theorem ledger_result_of_keeps {f : Firing T S O} (keeps : KeepsEvidence label space f)
    (C : Configuration T O) :
    ledger label space (f.result label C) =
      ledger label space C ∪ madeObservations label space f := by
  rw [ledger_result]
  congr 1
  apply Finset.sdiff_eq_self_of_disjoint
  rw [Finset.disjoint_left]
  intro o inLedger taken
  have inSpace := ((mem_ledger label space).mp inLedger).2
  rw [keeps o (List.mem_toFinset.mp taken)] at inSpace
  cases inSpace

/-- **Made observations are fresh**: an admitted firing makes no identity already in the ledger. -/
theorem disjoint_madeObservations {A : SubstitutionAction T S} {f : Firing T S O}
    {C : Configuration T O} (valid : f.Valid A label C) :
    Disjoint (ledger label space C) (madeObservations label space f) := by
  rw [Finset.disjoint_left]
  intro o inLedger inMade
  have present := ((mem_ledger label space).mp inLedger).1
  have made : o ∈ (f.selection.commit (T := T)).made := by
    simp only [madeObservations, Finset.mem_filter, List.mem_toFinset] at inMade
    simpa [Selection.commit] using inMade.1
  exact Finset.disjoint_left.mp valid.firing.occurrences.fresh made present

end Ledger

/-! ## The readout -/

section Readout

variable (label : O → T) (space : T → Bool) (outcome : T → W)

/-- What an observation records: the outcome its label carries. -/
def recorded (o : O) : W := outcome (label o)

/-- **The evidence of the world model for `φ` at a cut**: the evidence of the ledger. -/
def readout (φ : W → Bool) (C : Configuration T O) : Evidence ℕ :=
  ledgerEvidence (recorded label outcome) φ (ledger label space C)

/-- **The readout is the extraction of the ledger world model** at the ledger of the cut. -/
theorem readout_eq_extract (φ : W → Bool) (C : Configuration T O) :
    readout label space outcome φ C =
      (ledgerOverlapModel (recorded label outcome)).extract (ledger label space C) φ := rfl

/-- PLN strength in the rationals: `n⁺ / (n⁺ + n⁻)`, read as `0` without samples. -/
def strengthQ (e : Evidence ℕ) : ℚ := Evidence.strength (Evidence.map (Nat.castRingHom ℚ) e)

/-- PLN confidence with prior weight `k`: `n / (n + k)`. -/
def confidenceQ (k : ℚ) (e : Evidence ℕ) : ℚ := (e.total : ℚ) / ((e.total : ℚ) + k)

/-- The truth value read from evidence: strength and confidence. -/
def truthValue (k : ℚ) (e : Evidence ℕ) : ℚ × ℚ := (strengthQ e, confidenceQ k e)

/-- **The truth value at a cut**, read from the ledger. -/
def truthAt (k : ℚ) (φ : W → Bool) (C : Configuration T O) : ℚ × ℚ :=
  truthValue k (readout label space outcome φ C)

omit [DecidableEq O] in
/-- **The truth value factors through the ledger**: cuts with one ledger have one truth value. -/
theorem truthAt_eq_of_ledger_eq (k : ℚ) (φ : W → Bool) {C D : Configuration T O}
    (same : ledger label space C = ledger label space D) :
    truthAt label space outcome k φ C = truthAt label space outcome k φ D := by
  unfold truthAt readout
  rw [same]

omit [DecidableEq O] in
/-- **The readout depends only on the present occurrences.** -/
theorem readout_congr {A : SubstitutionAction T S} (φ : W → Bool) {C D : Configuration T O}
    (same : SameUpTo A C D) :
    readout label space outcome φ C = readout label space outcome φ D := by
  unfold readout
  rw [ledger_congr label space same.2]

/-- The readout on configuration classes. -/
def readoutClass (A : SubstitutionAction T S) (φ : W → Bool) :
    ConfigurationClass A O → Evidence ℕ :=
  Quotient.lift (readout label space outcome φ) fun _ _ same =>
    readout_congr label space outcome φ same

omit [DecidableEq O] in
theorem readoutClass_mk (A : SubstitutionAction T S) (φ : W → Bool) (C : Configuration T O) :
    readoutClass label space outcome A φ (ConfigurationClass.mk A C) =
      readout label space outcome φ C := rfl

/-- **Revision along one firing is exact**: a firing that takes no observation adds the evidence of
the fresh observations it makes. -/
theorem readout_result_of_keeps {A : SubstitutionAction T S} (φ : W → Bool) {f : Firing T S O}
    {C : Configuration T O} (keeps : KeepsEvidence label space f) (valid : f.Valid A label C) :
    readout label space outcome φ (f.result label C) =
      readout label space outcome φ C +
        ledgerEvidence (recorded label outcome) φ (madeObservations label space f) := by
  unfold readout
  rw [ledger_result_of_keeps label space keeps C]
  exact ledgerEvidence_union_of_disjoint _ φ (disjoint_madeObservations label space valid)

/-- The evidence a run makes, firing by firing. -/
def madeEvidence (φ : W → Bool) : List (Firing T S O) → Evidence ℕ
  | [] => 0
  | f :: rest =>
      ledgerEvidence (recorded label outcome) φ (madeObservations label space f) +
        madeEvidence φ rest

/-- **Additive revision is exact along a run that consumes no evidence**: identities are fresh. -/
theorem readout_follow_of_keeps {A : SubstitutionAction T S} (φ : W → Bool) :
    ∀ {C : Configuration T O} {w : List (Firing T S O)},
      (∀ f ∈ w, KeepsEvidence label space f) → Executable A label C w →
        readout label space outcome φ (follow label C w) =
          readout label space outcome φ C + madeEvidence label space outcome φ w
  | C, [], _, _ => by simp [follow, madeEvidence]
  | C, f :: rest, keeps, executable => by
      have later := readout_follow_of_keeps (A := A) φ (C := f.result label C) (w := rest)
        (fun g member => keeps g (List.mem_cons_of_mem f member)) executable.2
      change readout label space outcome φ (follow label (f.result label C) rest) = _
      rw [later, readout_result_of_keeps label space outcome φ (keeps f List.mem_cons_self)
        executable.1, madeEvidence, add_assoc]

end Readout

/-! ## The readout factors through traces -/

section Traces

variable (A : SubstitutionAction T S) (label : O → T) (space : T → Bool) (outcome : T → W)

/-- **Round-equivalent runs leave one readout**, without any executability hypothesis. -/
theorem readout_roundEquiv (φ : W → Bool) {C : Configuration T O} {w w' : List (Firing T S O)}
    (equivalent : RoundEquiv A label C w w') :
    readout label space outcome φ (follow label C w) =
      readout label space outcome φ (follow label C w') :=
  readout_congr label space outcome φ
    (AnnotatedRunBranchCollection.RoundEquiv.follow_sameUpTo A label equivalent)

/-- **Statically trace-equivalent executable runs leave one readout.** -/
theorem readout_staticTraceEquiv (φ : W → Bool) {C : Configuration T O}
    {w w' : List (Firing T S O)} (equivalent : TraceEquiv (StaticIndependent label) w w')
    (executable : Executable A label C w) :
    readout label space outcome φ (follow label C w) =
      readout label space outcome φ (follow label C w') :=
  readout_congr label space outcome φ ((traceEquiv_executable A label equivalent C).2 executable)

/-- **Every level set of the readout is a predicate on contextual traces.** -/
theorem readout_tracePredicate (φ : W → Bool) (C₀ : Configuration T O) (y : Runs A label)
    (e : Evidence ℕ) :
    ∃ ψ, pullbackAlong (runObject A label C₀) (traceFunctor (concurrency A label).tiles) ψ =
      {p : runObject A label C₀ ⟶ y |
        readout label space outcome φ (follow label C₀ (OccurrencePath.sites p)) = e} := by
  refine (tracePredicate_iff A label C₀ _).mpr ?_
  intro p q equivalent
  change readout label space outcome φ (follow label C₀ (OccurrencePath.sites p)) = e ↔
    readout label space outcome φ (follow label C₀ (OccurrencePath.sites q)) = e
  rw [readout_roundEquiv A label space outcome φ equivalent]

/-- **The truth value, strength and confidence, is the same on round-equivalent runs.** -/
theorem truthAt_roundEquiv (k : ℚ) (φ : W → Bool) {C : Configuration T O}
    {w w' : List (Firing T S O)} (equivalent : RoundEquiv A label C w w') :
    truthAt label space outcome k φ (follow label C w) =
      truthAt label space outcome k φ (follow label C w') :=
  congrArg (truthValue k) (readout_roundEquiv A label space outcome φ equivalent)

end Traces

/-! ## Double counting -/

section DoubleCounting

variable (label : O → T) (space : T → Bool) (outcome : T → W)

/-- The observations a firing cites: those it reads from the evidence space. -/
def cited (f : Firing T S O) : Finset O :=
  f.selection.read.toFinset.filter fun o => space (label o) = true

/-- The ledger a run cites. -/
def citedLedger : List (Firing T S O) → Finset O
  | [] => ∅
  | f :: rest => cited label space f ∪ citedLedger rest

/-- **The additive readout of a run word**: the sum of the evidence each firing cites. -/
def citedSum (φ : W → Bool) : List (Firing T S O) → Evidence ℕ
  | [] => 0
  | f :: rest =>
      ledgerEvidence (recorded label outcome) φ (cited label space f) + citedSum φ rest

theorem mem_citedLedger {w : List (Firing T S O)} {o : O} :
    o ∈ citedLedger label space w ↔ ∃ f ∈ w, o ∈ cited label space f := by
  induction w with
  | nil => simp [citedLedger]
  | cons f rest ih => simp [citedLedger, ih]

/-- **The ledger is a lower bound of the additive readout.** -/
theorem citedLedger_le_citedSum (φ : W → Bool) :
    ∀ w : List (Firing T S O),
      ledgerEvidence (recorded label outcome) φ (citedLedger label space w) ≤
        citedSum label space outcome φ w
  | [] => le_of_eq (by simp [citedLedger, citedSum, ledgerEvidence])
  | f :: rest => by
      have later := citedLedger_le_citedSum φ rest
      have bound := (unknown_overlap_bounds (recorded label outcome) φ (cited label space f)
        (citedLedger label space rest)).2
      change ledgerEvidence _ φ (cited label space f ∪ citedLedger label space rest) ≤
        ledgerEvidence _ φ (cited label space f) + citedSum label space outcome φ rest
      exact bound.trans (add_le_add le_rfl later)

/-- **The additive readout is exact exactly for pairwise disjoint citations.** -/
theorem citedSum_eq_iff_pairwise_disjoint (φ : W → Bool) :
    ∀ w : List (Firing T S O),
      citedSum label space outcome φ w =
          ledgerEvidence (recorded label outcome) φ (citedLedger label space w) ↔
        w.Pairwise fun f g => Disjoint (cited label space f) (cited label space g)
  | [] => by simp [citedSum, citedLedger, ledgerEvidence]
  | f :: rest => by
      have ih := citedSum_eq_iff_pairwise_disjoint φ rest
      have lower := citedLedger_le_citedSum label space outcome φ rest
      have split := ledgerEvidence_union_add_inter (recorded label outcome) φ (cited label space f)
        (citedLedger label space rest)
      rw [List.pairwise_cons]
      have disjointIff : Disjoint (cited label space f) (citedLedger label space rest) ↔
          ∀ g ∈ rest, Disjoint (cited label space f) (cited label space g) := by
        constructor
        · intro apart g member
          exact Finset.disjoint_of_subset_right
            (fun o inG => (mem_citedLedger label space).mpr ⟨g, member, inG⟩) apart
        · intro apart
          rw [Finset.disjoint_left]
          intro o inF inRest
          obtain ⟨g, member, inG⟩ := (mem_citedLedger label space).mp inRest
          exact Finset.disjoint_left.mp (apart g member) inF inG
      rw [← disjointIff, ← ih]
      change ledgerEvidence _ φ (cited label space f) + citedSum label space outcome φ rest =
          ledgerEvidence _ φ (cited label space f ∪ citedLedger label space rest) ↔ _
      obtain ⟨extra, extraEq⟩ := exists_add_of_le lower
      rw [extraEq]
      have sp := congrArg Evidence.pos split
      have sn := congrArg Evidence.neg split
      simp only [Evidence.add_pos, Evidence.add_neg] at sp sn
      constructor
      · intro exact
        have hp := congrArg Evidence.pos exact
        have hn := congrArg Evidence.neg exact
        simp only [Evidence.add_pos, Evidence.add_neg] at hp hn
        have overlapZero : ledgerEvidence (recorded label outcome) φ
            (cited label space f ∩ citedLedger label space rest) = 0 := by
          ext
          · simp only [Evidence.zero_pos]; omega
          · simp only [Evidence.zero_neg]; omega
        have extraZero : extra = 0 := by
          ext
          · simp only [Evidence.zero_pos]; omega
          · simp only [Evidence.zero_neg]; omega
        refine ⟨Finset.disjoint_iff_inter_eq_empty.mpr
          ((ledgerEvidence_eq_zero_iff _ φ _).mp overlapZero), ?_⟩
        rw [extraZero, add_zero]
      · rintro ⟨apart, exactRest⟩
        have hp := congrArg Evidence.pos exactRest
        have hn := congrArg Evidence.neg exactRest
        simp only [Evidence.add_pos, Evidence.add_neg] at hp hn
        have extraZero : extra = 0 := by
          ext
          · simp only [Evidence.zero_pos]; omega
          · simp only [Evidence.zero_neg]; omega
        rw [extraZero, add_zero]
        exact (ledgerEvidence_union_of_disjoint _ φ apart).symm

/-- **The ledger merge cannot double-count**: citing again what is already cited changes
nothing. -/
theorem citedLedger_append_of_subset {w : List (Firing T S O)} {f : Firing T S O}
    (again : cited label space f ⊆ citedLedger label space w) :
    citedLedger label space (w ++ [f]) = citedLedger label space w := by
  ext o
  simp only [mem_citedLedger, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨g, member | rfl, inG⟩
    · exact ⟨g, member, inG⟩
    · exact (mem_citedLedger label space).mp (again inG)
  · rintro ⟨g, member, inG⟩
    exact ⟨g, Or.inl member, inG⟩

/-- The additive readout of a repeated citation grows by its evidence again. -/
theorem citedSum_append (φ : W → Bool) (w : List (Firing T S O)) (f : Firing T S O) :
    citedSum label space outcome φ (w ++ [f]) =
      citedSum label space outcome φ w +
        ledgerEvidence (recorded label outcome) φ (cited label space f) := by
  induction w with
  | nil => simp [citedSum]
  | cons g rest ih =>
      change _ + citedSum label space outcome φ (rest ++ [f]) = (_ + _) + _
      rw [ih, add_assoc]

/-- The additive readout as a site account of runs, into the multiplicative monoid of evidence. -/
def citedAccount (A : SubstitutionAction T S) (φ : W → Bool) :
    RunAccount (Runs A label) (Multiplicative (Evidence ℕ)) :=
  siteAccount A label fun f =>
    Multiplicative.ofAdd (ledgerEvidence (recorded label outcome) φ (cited label space f))

theorem citedSum_eq_prod (φ : W → Bool) :
    ∀ w : List (Firing T S O),
      Multiplicative.ofAdd (citedSum label space outcome φ w) =
        (w.map fun f => Multiplicative.ofAdd
          (ledgerEvidence (recorded label outcome) φ (cited label space f))).prod
  | [] => rfl
  | f :: rest => by
      rw [List.map_cons, List.prod_cons, ← citedSum_eq_prod φ rest]
      rfl

/-- **The additive readout of a run is the site account of its path.** -/
theorem citedAccount_of (A : SubstitutionAction T S) (φ : W → Bool)
    {x y : (theory A label).Term} (p : OccurrencePath (presentation A label) x y) :
    (citedAccount label space outcome A φ).of p =
      Multiplicative.ofAdd (citedSum label space outcome φ (OccurrencePath.sites p)) :=
  (siteAccount_of_eq A label _ p).trans (citedSum_eq_prod label space outcome φ _).symm

/-- **Trace invariance does not prevent double counting**: the additive readout factors through
the contextual traces. -/
theorem citedAccount_factors_contextual (A : SubstitutionAction T S) (φ : W → Bool) :
    ∃ traced : RunAccount (ContextualTraces A label) (Multiplicative (Evidence ℕ)),
      traced.comap (traceFunctor _) = citedAccount label space outcome A φ :=
  siteAccount_factors_contextual A label _

end DoubleCounting

/-! ## Interleavings -/

section Interleavings

variable (A : SubstitutionAction T S) (label : O → T) (space : T → Bool) (outcome : T → W)

/-- **The sum over interleavings counts the ledger once per interleaving.** -/
theorem interleavings_sum (φ : W → Bool) {C : Configuration T O} {w : List (Firing T S O)}
    (routes : List (List (Firing T S O))) (equivalent : ∀ w' ∈ routes, RoundEquiv A label C w w') :
    (routes.map fun w' => readout label space outcome φ (follow label C w')).sum =
      routes.length • readout label space outcome φ (follow label C w) := by
  induction routes with
  | nil => simp
  | cons w' rest ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, succ_nsmul',
        ← readout_roundEquiv A label space outcome φ (equivalent w' List.mem_cons_self),
        ih fun w'' member => equivalent w'' (List.mem_cons_of_mem w' member)]

/-- **The merged ledger of the interleavings counts it once.** -/
theorem interleavings_merge {C : Configuration T O} {w : List (Firing T S O)}
    (routes : List (List (Firing T S O))) (equivalent : ∀ w' ∈ routes, RoundEquiv A label C w w') :
    (routes.map fun w' => ledger label space (follow label C w')).foldr (· ∪ ·)
        (ledger label space (follow label C w)) =
      ledger label space (follow label C w) := by
  induction routes with
  | nil => rfl
  | cons w' rest ih =>
      rw [List.map_cons, List.foldr_cons,
        ih fun w'' member => equivalent w'' (List.mem_cons_of_mem w' member),
        ← ledger_congr label space
          (AnnotatedRunBranchCollection.RoundEquiv.follow_sameUpTo A label
            (equivalent w' List.mem_cons_self)).2,
        ledger_merge_idem]

/-- **Zero is the only idempotent evidence.** -/
theorem evidence_add_self_eq_iff (e : Evidence ℕ) : e + e = e ↔ e = 0 := by
  constructor
  · intro same
    have pos := congrArg Evidence.pos same
    have neg := congrArg Evidence.neg same
    simp only [Evidence.add_pos, Evidence.add_neg] at pos neg
    ext
    · simp only [Evidence.zero_pos]; omega
    · simp only [Evidence.zero_neg]; omega
  · rintro rfl
    exact add_zero 0

/-- **The sum over two interleavings agrees with their merge exactly when the ledger is
empty.** -/
theorem interleaving_sum_eq_merge_iff (φ : W → Bool) {C : Configuration T O}
    {w w' : List (Firing T S O)} (equivalent : RoundEquiv A label C w w') :
    readout label space outcome φ (follow label C w) +
          readout label space outcome φ (follow label C w') =
        ledgerEvidence (recorded label outcome) φ
          (ledger label space (follow label C w) ∪ ledger label space (follow label C w')) ↔
      ledger label space (follow label C w) = ∅ := by
  rw [← ledger_congr label space
      (AnnotatedRunBranchCollection.RoundEquiv.follow_sameUpTo A label equivalent).2,
    ledger_merge_idem, ← readout_roundEquiv A label space outcome φ equivalent]
  change readout label space outcome φ (follow label C w) +
      readout label space outcome φ (follow label C w) =
    readout label space outcome φ (follow label C w) ↔ _
  rw [evidence_add_self_eq_iff]
  exact ledgerEvidence_eq_zero_iff _ φ _

end Interleavings

end WorldModelRuns

open WorldModelRuns

#print axioms ledgerQuery_holds_iff
#print axioms ledger_result
#print axioms ledger_result_of_keeps
#print axioms disjoint_madeObservations
#print axioms readout_eq_extract
#print axioms truthAt_eq_of_ledger_eq
#print axioms readout_congr
#print axioms readout_result_of_keeps
#print axioms readout_follow_of_keeps
#print axioms readout_roundEquiv
#print axioms readout_staticTraceEquiv
#print axioms readout_tracePredicate
#print axioms truthAt_roundEquiv
#print axioms citedLedger_le_citedSum
#print axioms citedSum_eq_iff_pairwise_disjoint
#print axioms citedLedger_append_of_subset
#print axioms citedSum_append
#print axioms citedAccount_of
#print axioms citedAccount_factors_contextual
#print axioms interleavings_sum
#print axioms interleavings_merge
#print axioms evidence_add_self_eq_iff
#print axioms interleaving_sum_eq_merge_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
