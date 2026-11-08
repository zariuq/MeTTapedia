import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceExperiments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceProbability

/-!
# Contention on the step: inhibition belongs to it

Meredith's contention (graded where-clauses, Def. 2.4) relates two candidates that share a message
or a linear receive. On the step that is a shared take (`SharesTake`). The step also has reads and
predicate queries, so a firing can disable another without sharing anything with it:

* **an asymmetric conflict**: one takes what the other reads (`TakesRead`);
* **inhibition**: one takes or makes inside the region of a predicate query of the other
  (`Inhibits`). An absence query is a predicate query whose census is empty.

**Contention** (`Contends`) is the symmetric closure of the three. Each of them breaks the step's
static independence (`not_independent_of_contends`), and inhibition refuses the inhibited firing
(`refused_after_inhibitor`).

## Ground firings with fixed predicate queries (`Queried`)

A ground firing whose predicate queries have fixed regions is admitted, at a configuration with
reflexive equations and under every substitution action, exactly when its commit is enabled and its
queries hold (`Queried.valid_iff`). The admitted members of an alphabet of such firings are then a
filter of the alphabet (`admitted_eq_filter`).

## No context forces an inhibitor-free race (Meredith, Prop. 3.3)

A firing whose checks are equations and which has no predicate queries is **inhibitor-free**
(`InhibitorFree`). Adding an occurrence it does not make keeps it admitted (`valid_addAtom`,
`valid_addAll`). So while an inhibitor-free competitor of positive weight is admitted, no firing
fires first with probability `1`, whatever atoms a context adds (`prob_lt_one`,
`no_context_forces`).

## Local normalization (`contentionTotal`, `localProb`)

For a contention relation, the likelihood of a run with each firing normalized inside its
contention set at the configuration it fires at. With `SharesTake` this is Meredith's Eq. (1).

## Controls (`Controls`)

Four ground firings over the tokens `a, b, p, out`, for every substitution action.

* **Inhibition and mass** (`inhibition_control`). `maker` takes `a` and makes `p`; `guarded` takes `b`
  under the absence query of `p`. They share nothing. The maximal runs are `[maker]` and
  `[guarded, maker]`.
  - With sharing contention each firing is its own contention set and both runs get likelihood `1`:
    **total mass `2`**.
  - With contention including inhibition, the local likelihoods are `w_m/(w_m+w_g)` and
    `w_g/(w_m+w_g)`, the step's own jump chain (`Race.traceProb`) gives the same, and the mass is
    `1`.
* **One atom forces a race** (`forcing_control`). `racer` and `vetoed` both take `a`; `vetoed` has the
  absence query of `p`. Adding one occurrence of `p` refuses `vetoed`, and `racer` fires with
  probability `1`. The other way no context can force (`cannot_force_vetoed`): `racer` is
  inhibitor-free.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Contention

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire PredicateQuery regionOf mem_regionOf)
open Race (Reflexive Ground admitted total prob traceProb addAtom)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Contention -/

section Relations

/-- **Meredith's contention on the step**: the two firings take a common occurrence. -/
def SharesTake (f g : Firing T S O) : Prop := ∃ o ∈ f.selection.taken, o ∈ g.selection.taken

/-- The first takes an occurrence that the second reads: an asymmetric conflict. -/
def TakesRead (f g : Firing T S O) : Prop := ∃ o ∈ f.selection.taken, o ∈ g.selection.read

/-- **Inhibition**: the first takes or makes an occurrence inside the region of a predicate query
of the second, at some solution. -/
def Inhibits (label : O → T) (f g : Firing T S O) : Prop :=
  ∃ query ∈ g.queries, ∃ σ : S, ∃ o ∈ f.selection.taken ++ f.selection.made,
    query.region σ (label o) = true

/-- **Contention on the step**: a shared take, a take of what the other reads, or inhibition, in
either direction. -/
def Contends (label : O → T) (f g : Firing T S O) : Prop :=
  SharesTake f g ∨ TakesRead f g ∨ TakesRead g f ∨ Inhibits label f g ∨ Inhibits label g f

variable {label : O → T} {f g : Firing T S O}

omit [DecidableEq O] in
theorem SharesTake.symm (shares : SharesTake f g) : SharesTake g f := by
  obtain ⟨o, inF, inG⟩ := shares
  exact ⟨o, inG, inF⟩

omit [DecidableEq O] in
theorem Contends.symm (contends : Contends label f g) : Contends label g f := by
  rcases contends with shares | read | read | inhibits | inhibits
  · exact Or.inl shares.symm
  · exact Or.inr (Or.inr (Or.inl read))
  · exact Or.inr (Or.inl read)
  · exact Or.inr (Or.inr (Or.inr (Or.inr inhibits)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl inhibits)))

omit [DecidableEq O] in
/-- Sharing is contention. -/
theorem SharesTake.contends (shares : SharesTake f g) : Contends label f g := Or.inl shares

/-- **Contending firings are not statically independent**: at any solution, a shared take is a
clash, a take of what the other reads spoils the reader, and inhibition writes into a query
region. -/
theorem not_independent_of_contends (σ : S) (contends : Contends label f g) :
    ¬ AnnotatedRuns.Independent label f g := by
  intro independent
  have trace := independent σ
  rcases contends with ⟨o, inF, inG⟩ | ⟨o, inF, inG⟩ | ⟨o, inG, inF⟩ |
      ⟨query, member, τ, o, written, inRegion⟩ | ⟨query, member, τ, o, written, inRegion⟩
  · exact trace.1.1 (Or.inl (Finset.not_disjoint_iff.mpr ⟨o, by simpa using inF, by simpa using inG⟩))
  · exact trace.1.2.1
      (Or.inl (Finset.not_disjoint_iff.mpr ⟨o, by simpa using inF, by simpa using inG⟩))
  · exact trace.1.2.2
      (Or.inl (Finset.not_disjoint_iff.mpr ⟨o, by simpa using inG, by simpa using inF⟩))
  · have outside := AnnotatedRuns.Independent.writesOutside independent τ query member o
      (by simpa [Selection.commit] using written)
    rw [outside] at inRegion
    exact Bool.false_ne_true inRegion
  · have outside := AnnotatedRuns.Independent.writesOutside independent.symm τ query member o
      (by simpa [Selection.commit] using written)
    rw [outside] at inRegion
    exact Bool.false_ne_true inRegion

/-- **Inhibition refuses**: a firing with an empty census of a region is refused after any firing
that makes an occurrence inside that region. -/
theorem refused_after_inhibitor (A : SubstitutionAction T S) {C : Configuration T O}
    {query : PredicateQuery O T} (member : PredicateQueryAdmission.Query.fixed query ∈ g.queries)
    (empty : query.seen = ∅) {o : O} (made : o ∈ f.selection.made)
    (inRegion : query.region (label o) = true) :
    ¬ g.Valid A label (f.result label C) := by
  intro valid
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  have holds : regionOf label (f.result label C).present query.region = query.seen :=
    valid.observations _ member σ solved
  have present : o ∈ (f.result label C).present :=
    mem_fire.mpr (Or.inr (by simpa [Selection.commit] using made))
  have inside : o ∈ regionOf label (f.result label C).present query.region :=
    mem_regionOf.mpr ⟨present, inRegion⟩
  rw [holds, empty] at inside
  simp at inside

end Relations

/-! ## Ground firings with fixed predicate queries -/

section Queried

/-- **A ground firing with fixed predicate queries**: without its queries it is ground, and its
queries are the given ones with fixed regions. -/
structure Queried (label : O → T) (f : Firing T S O) (queries : List (PredicateQuery O T)) :
    Prop where
  ground : Ground label (⟨f.rule, [], f.selection⟩ : Firing T S O)
  fixed : f.queries = queries.map PredicateQueryAdmission.Query.fixed

variable {label : O → T} {f : Firing T S O} {queries : List (PredicateQuery O T)}

/-- **Admission of a ground firing with fixed queries** is enabling of its commit together with its
queries, at a reflexive configuration and for every substitution action. -/
theorem Queried.valid_iff (A : SubstitutionAction T S) (queried : Queried label f queries)
    {C : Configuration T O} (refl : Reflexive C.equations) :
    f.Valid A label C ↔
      Enabled label C.present (f.selection.commit (T := T)) ∧
        ∀ query ∈ queries, query.Holds label C.present := by
  have plain : f.selection.Valid A label f.rule C ↔
      Enabled label C.present (f.selection.commit (T := T)) :=
    (PredicateQueryAdmission.valid_empty_iff A label f.rule C f.selection).symm.trans
      (queried.ground.valid_iff A refl)
  show PredicateQueryAdmission.Valid A label f.rule f.queries C f.selection ↔ _
  rw [queried.fixed, PredicateQueryAdmission.valid_fixed_iff, plain]

/-- The result of a ground firing with fixed queries has reflexive equations. -/
theorem Queried.reflexive_result (queried : Queried label f queries) {C : Configuration T O}
    (refl : Reflexive C.equations) : Reflexive (f.result label C).equations :=
  queried.ground.reflexive_result refl

variable {A : SubstitutionAction T S} {alphabet : List (Firing T S O)}

open Classical in
/-- The admitted members of an alphabet, as a filter of the alphabet. -/
theorem admitted_eq (C : Configuration T O) :
    admitted A label alphabet C = alphabet.filter (fun h => decide (h ∈ alphabet ∧ h.Valid A label C)) :=
  Race.map_filterMap_dite (fun h => h ∈ alphabet ∧ h.Valid A label C)
    (fun h p => (⟨⟨h, p.1⟩, p.2⟩ :
      {g : {f : Firing T S O // f ∈ alphabet} // (Race.program A label alphabet).Admits (s := C) g}))
    (fun g => g.1.1) (fun _ _ => rfl) alphabet

/-- A firing is admitted exactly when it is in the alphabet and valid. -/
theorem mem_admitted {C : Configuration T O} {h : Firing T S O} :
    h ∈ admitted A label alphabet C ↔ h ∈ alphabet ∧ h.Valid A label C := by
  classical
  rw [admitted_eq, List.mem_filter, decide_eq_true_iff]
  exact ⟨fun both => both.2, fun both => ⟨both.1, both⟩⟩

/-- **For alphabets of ground firings with fixed queries, the admitted members are the enabled
members whose queries hold**, at reflexive configurations. -/
theorem admitted_eq_filter (queriesOf : Firing T S O → List (PredicateQuery O T))
    (queried : ∀ h ∈ alphabet, Queried label h (queriesOf h)) {C : Configuration T O}
    (refl : Reflexive C.equations) :
    admitted A label alphabet C = alphabet.filter (fun h =>
      decide (Enabled label C.present (h.selection.commit (T := T)) ∧
        ∀ query ∈ queriesOf h, query.Holds label C.present)) := by
  classical
  rw [admitted_eq]
  apply List.filter_congr
  intro h member
  rw [decide_eq_decide]
  exact ⟨fun both => ((queried h member).valid_iff A refl).mp both.2,
    fun holds => ⟨member, ((queried h member).valid_iff A refl).mpr holds⟩⟩

end Queried

/-! ## No context forces an inhibitor-free race -/

section Forcing

/-- **An inhibitor-free firing**: its checks are equations, and it has no predicate queries. -/
structure InhibitorFree (f : Firing T S O) : Prop where
  checks : ∀ check ∈ f.rule.checks, ∃ left right, check = Check.equal left right
  queries : f.queries = []

/-- Add occurrences one after another, knowledge unchanged. -/
def addAll (C : Configuration T O) : List O → Configuration T O
  | [] => C
  | o :: rest => addAll (addAtom C o) rest

theorem enabled_insert {label : O → T} {store : Finset O} {c : MeTTaCalculus.OccurrenceCommits.Commit O T}
    {o : O} (enabled : Enabled label store c) (noQueries : c.queries = []) (fresh : o ∉ c.made) :
    Enabled label (insert o store) c :=
  ⟨enabled.taken_subset.trans (Finset.subset_insert o store),
    enabled.kept_subset.trans (Finset.subset_insert o store), enabled.apart,
    Finset.disjoint_insert_right.mpr ⟨fresh, enabled.fresh⟩, by rw [noQueries]; simp⟩

variable {A : SubstitutionAction T S} {label : O → T}

/-- **Adding an occurrence keeps an inhibitor-free firing admitted**, unless it adds what the
firing makes. -/
theorem valid_addAtom {f : Firing T S O} (free : InhibitorFree f) {C : Configuration T O} {o : O}
    (valid : f.Valid A label C) (fresh : o ∉ f.selection.made) :
    f.Valid A label (addAtom C o) := by
  obtain ⟨firing, _⟩ := valid
  refine ⟨⟨firing.take_distinct, firing.output_distinct, firing.take_length, firing.read_length,
    firing.outputs, enabled_insert firing.occurrences rfl (by simpa [Selection.commit] using fresh),
    firing.consistent, ?_⟩, ?_⟩
  · intro check member σ solved
    obtain ⟨left, right, rfl⟩ := free.checks check member
    exact firing.checks _ member σ solved
  · intro query member
    rw [free.queries] at member
    simp at member

theorem valid_addAll {f : Firing T S O} (free : InhibitorFree f) :
    ∀ {C : Configuration T O} (os : List O), f.Valid A label C →
      (∀ o ∈ os, o ∉ f.selection.made) → f.Valid A label (addAll C os)
  | _, [], valid, _ => valid
  | _, o :: rest, valid, fresh =>
      valid_addAll free rest (valid_addAtom free valid (fresh o List.mem_cons_self))
        (fun o' member => fresh o' (List.mem_cons_of_mem _ member))

omit [DecidableEq O] in
theorem sum_map_le {X : Type*} {num w : X → ℝ} (upper : ∀ h, num h ≤ w h) :
    ∀ L : List X, (L.map num).sum ≤ (L.map w).sum
  | [] => le_rfl
  | x :: rest => by
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (upper x) (sum_map_le upper rest)

omit [DecidableEq O] in
/-- A pointwise bound that is strict at one member is strict for the sum. -/
theorem sum_map_lt {X : Type*} {num w : X → ℝ} (upper : ∀ h, num h ≤ w h) {g : X}
    (zero : num g = 0) (positive : 0 < w g) :
    ∀ {L : List X}, g ∈ L → (L.map num).sum < (L.map w).sum
  | [], member => by simp at member
  | x :: rest, member => by
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp member with same | inRest
      · subst same
        exact add_lt_add_of_lt_of_le (by rw [zero]; exact positive) (sum_map_le upper rest)
      · exact add_lt_add_of_le_of_lt (upper x) (sum_map_lt upper zero positive inRest)

variable {alphabet : List (Firing T S O)} {weight : Firing T S O → ℝ}

/-- **A positive competitor keeps a race below `1`**: while a firing other than `f` with positive
weight is admitted, `f` fires first with probability below `1`. -/
theorem prob_lt_one (nonneg : ∀ h, 0 ≤ weight h) {C : Configuration T O} {f g : Firing T S O}
    (apart : g ≠ f) (gIn : g ∈ alphabet) (gValid : g.Valid A label C) (positive : 0 < weight g) :
    prob A label alphabet id weight C f Set.univ < 1 := by
  classical
  have gMem : g ∈ admitted A label alphabet C := mem_admitted.mpr ⟨gIn, gValid⟩
  have totalPos : 0 < total A label alphabet weight C := by
    unfold total
    refine lt_of_lt_of_le positive (List.single_le_sum (fun x member => ?_) _
      (List.mem_map.mpr ⟨g, gMem, rfl⟩))
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp member
    exact nonneg h
  unfold prob
  rw [div_lt_one totalPos]
  unfold total
  exact sum_map_lt (fun h => by split_ifs <;> simp [nonneg]) (by simp [apart]) positive gMem

/-- **No context forces an inhibitor-free race** (Meredith's Prop. 3.3 on the step): whatever
occurrences a context adds, other than those the competitor makes, an admitted inhibitor-free
competitor of positive weight stays admitted and keeps `f` below probability `1`. -/
theorem no_context_forces (nonneg : ∀ h, 0 ≤ weight h) {C : Configuration T O}
    {f g : Firing T S O} (apart : g ≠ f) (gIn : g ∈ alphabet) (free : InhibitorFree g)
    (positive : 0 < weight g) (gValid : g.Valid A label C) (os : List O)
    (fresh : ∀ o ∈ os, o ∉ g.selection.made) :
    prob A label alphabet id weight (addAll C os) f Set.univ < 1 :=
  prob_lt_one nonneg apart gIn (valid_addAll free os gValid fresh) positive

end Forcing

/-! ## Local normalization -/

section Local

variable (A : SubstitutionAction T S) (label : O → T) (alphabet : List (Firing T S O))
  (weight : Firing T S O → ℝ) (contends : Firing T S O → Firing T S O → Prop)

open Classical in
/-- The weight of a firing's contention set at a configuration: the admitted firings that are it
or contend with it. -/
noncomputable def contentionTotal (C : Configuration T O) (f : Firing T S O) : ℝ :=
  (((admitted A label alphabet C).filter fun g => decide (g = f ∨ contends f g)).map weight).sum

/-- **Local normalization**: the likelihood of a run, each firing normalized inside its contention
set at the configuration it fires at. -/
noncomputable def localProb : Configuration T O → List (Firing T S O) → ℝ
  | _, [] => 1
  | C, f :: rest =>
      weight f / contentionTotal A label alphabet weight contends C f * localProb (f.result label C) rest

end Local

/-! ## Controls -/

namespace Controls

/-- The tokens. -/
inductive Tok where
  | a
  | b
  | p
  | out
  deriving DecidableEq

/-- The occurrence identities. -/
inductive Site where
  | ta
  | tb
  | mp
  | go
  | ro
  | vo
  deriving DecidableEq

/-- The labels: `ta` carries `a`, `tb` carries `b`, `mp` carries `p`, the others `out`. -/
def label : Site → Tok
  | .ta => .a
  | .tb => .b
  | .mp => .p
  | .go => .out
  | .ro => .out
  | .vo => .out

/-- **The absence query of `p`**: the census of the region `p` is empty. -/
def absentP : PredicateQuery Site Tok := ⟨fun t => decide (t = Tok.p), ∅⟩

variable {S : Type uS} (A : SubstitutionAction Tok S)

/-- Takes `a`, makes `p`. -/
def maker : Firing Tok S Site := ⟨⟨[.a], [], [], [], [.p]⟩, [], ⟨[.ta], [], [.mp]⟩⟩

/-- Takes `b` under the absence query of `p`, makes `out`. -/
def guarded : Firing Tok S Site :=
  ⟨⟨[.b], [], [], [], [.out]⟩, [PredicateQueryAdmission.Query.fixed absentP], ⟨[.tb], [], [.go]⟩⟩

/-- Takes `a`, makes `out`. -/
def racer : Firing Tok S Site := ⟨⟨[.a], [], [], [], [.out]⟩, [], ⟨[.ta], [], [.ro]⟩⟩

/-- Takes `a` under the absence query of `p`, makes `out`. -/
def vetoed : Firing Tok S Site :=
  ⟨⟨[.a], [], [], [], [.out]⟩, [PredicateQueryAdmission.Query.fixed absentP], ⟨[.ta], [], [.vo]⟩⟩

/-- The fixed queries of the four firings. -/
def queriesOf (f : Firing Tok S Site) : List (PredicateQuery Site Tok) :=
  if f.selection.made = [.go] ∨ f.selection.made = [.vo] then [absentP] else []

def inhibition : List (Firing Tok S Site) := [maker, guarded]

def race : List (Firing Tok S Site) := [racer, vetoed]

theorem config_ext {C D : Configuration Tok Site} (equations : C.equations = D.equations)
    (present : C.present = D.present) : C = D := by
  cases C
  cases D
  cases equations
  cases present
  rfl

/-- The start of the inhibition control. -/
def C0 : Configuration Tok Site := ⟨[], {.ta, .tb}⟩
/-- After `maker`. -/
def C1 : Configuration Tok Site := ⟨[(.a, .a)], {.tb, .mp}⟩
/-- After `guarded`. -/
def C2 : Configuration Tok Site := ⟨[(.b, .b)], {.ta, .go}⟩
/-- After `guarded` and `maker`. -/
def C3 : Configuration Tok Site := ⟨[(.b, .b), (.a, .a)], {.go, .mp}⟩
/-- The start of the forcing control. -/
def D0 : Configuration Tok Site := ⟨[], {.ta}⟩

theorem maker_queried : Queried label (maker (S := S)) [] :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, List.nodup_singleton _, List.nodup_singleton _⟩, rfl⟩

theorem guarded_queried : Queried label (guarded (S := S)) [absentP] :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, List.nodup_singleton _, List.nodup_singleton _⟩, rfl⟩

theorem racer_queried : Queried label (racer (S := S)) [] :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, List.nodup_singleton _, List.nodup_singleton _⟩, rfl⟩

theorem vetoed_queried : Queried label (vetoed (S := S)) [absentP] :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, List.nodup_singleton _, List.nodup_singleton _⟩, rfl⟩

theorem inhibition_queried : ∀ f ∈ inhibition (S := S), Queried label f (queriesOf f) := by
  intro f member
  simp only [inhibition, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact maker_queried
  · exact guarded_queried

theorem race_queried : ∀ f ∈ race (S := S), Queried label f (queriesOf f) := by
  intro f member
  simp only [race, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact racer_queried
  · exact vetoed_queried

theorem reflexive_C0 : Reflexive C0.equations := by unfold Race.Reflexive; decide
theorem reflexive_C1 : Reflexive C1.equations := by unfold Race.Reflexive; decide
theorem reflexive_C2 : Reflexive C2.equations := by unfold Race.Reflexive; decide
theorem reflexive_C3 : Reflexive C3.equations := by unfold Race.Reflexive; decide
theorem reflexive_D0 : Reflexive D0.equations := by unfold Race.Reflexive; decide

theorem result_maker_C0 : (maker (S := S)).result label C0 = C1 :=
  config_ext rfl (of_decide_eq_true rfl)
theorem result_guarded_C0 : (guarded (S := S)).result label C0 = C2 :=
  config_ext rfl (of_decide_eq_true rfl)
theorem result_maker_C2 : (maker (S := S)).result label C2 = C3 :=
  config_ext rfl (of_decide_eq_true rfl)

theorem guarded_ne_maker : (guarded (S := S)) ≠ maker := by
  intro same
  have := congrArg (fun f : Firing Tok S Site => f.selection.taken) same
  simp [guarded, maker] at this

theorem maker_ne_guarded : (maker (S := S)) ≠ guarded := fun same => guarded_ne_maker same.symm

theorem vetoed_ne_racer : (vetoed (S := S)) ≠ racer := by
  intro same
  have := congrArg (fun f : Firing Tok S Site => f.selection.made) same
  simp [vetoed, racer] at this

theorem racer_ne_vetoed : (racer (S := S)) ≠ vetoed := fun same => vetoed_ne_racer same.symm

theorem admitted_C0 : admitted A label (inhibition (S := S)) C0 = [maker, guarded] := by
  rw [admitted_eq_filter queriesOf inhibition_queried reflexive_C0]
  rfl

theorem admitted_C1 : admitted A label (inhibition (S := S)) C1 = [] := by
  rw [admitted_eq_filter queriesOf inhibition_queried reflexive_C1]
  rfl

theorem admitted_C2 : admitted A label (inhibition (S := S)) C2 = [maker] := by
  rw [admitted_eq_filter queriesOf inhibition_queried reflexive_C2]
  rfl

theorem admitted_C3 : admitted A label (inhibition (S := S)) C3 = [] := by
  rw [admitted_eq_filter queriesOf inhibition_queried reflexive_C3]
  rfl

theorem admitted_D0 : admitted A label (race (S := S)) D0 = [racer, vetoed] := by
  rw [admitted_eq_filter queriesOf race_queried reflexive_D0]
  rfl

theorem admitted_D0_vetoed : admitted A label (race (S := S)) (addAtom D0 .mp) = [racer] := by
  rw [admitted_eq_filter (C := addAtom D0 .mp) queriesOf race_queried reflexive_D0]
  rfl

/-! ### Contention among the four firings -/

theorem not_shares_maker_guarded : ¬ SharesTake (maker (S := S)) guarded := by
  rintro ⟨o, inMaker, inGuarded⟩
  simp only [maker, guarded, List.mem_singleton] at inMaker inGuarded
  rw [inMaker] at inGuarded
  exact absurd inGuarded (by decide)

theorem not_shares_guarded_maker : ¬ SharesTake (guarded (S := S)) maker :=
  fun shares => not_shares_maker_guarded shares.symm

include A in
/-- **`maker` inhibits `guarded`**: it makes `p`, inside `guarded`'s absence query. -/
theorem maker_inhibits_guarded : Inhibits label (maker (S := S)) guarded :=
  ⟨_, List.mem_singleton_self _, A.identity, .mp, by simp [maker], rfl⟩

include A in
theorem contends_maker_guarded : Contends label (maker (S := S)) guarded :=
  Or.inr (Or.inr (Or.inr (Or.inl (maker_inhibits_guarded A))))

include A in
theorem contends_guarded_maker : Contends label (guarded (S := S)) maker :=
  (contends_maker_guarded A).symm

include A in
/-- **Inhibition breaks static independence**, though the two share nothing. -/
theorem maker_guarded_dependent :
    ¬ SharesTake (maker (S := S)) guarded ∧ ¬ AnnotatedRuns.Independent label (maker (S := S)) guarded :=
  ⟨not_shares_maker_guarded, not_independent_of_contends A.identity (contends_maker_guarded A)⟩

/-- **`guarded` is refused after `maker`.** -/
theorem guarded_refused : ¬ (guarded (S := S)).Valid A label ((maker (S := S)).result label C0) :=
  refused_after_inhibitor A (f := maker) (List.mem_singleton_self _) rfl
    (List.mem_singleton_self Site.mp) rfl

/-! ### The inhibition control -/

variable (weight : Firing Tok S Site → ℝ)

theorem total_C0 : total A label inhibition weight C0 = weight maker + weight guarded := by
  simp [total, admitted_C0]

theorem total_C2 : total A label inhibition weight C2 = weight maker := by
  simp [total, admitted_C2]

/-- **The step's jump chain on the two maximal runs.** -/
theorem jump_chain (positive : 0 < weight maker) :
    traceProb A label inhibition id weight [maker] C0 = weight maker / (weight maker + weight guarded) ∧
      traceProb A label inhibition id weight [guarded, maker] C0 =
        weight guarded / (weight maker + weight guarded) := by
  constructor
  · simp [traceProb, admitted_C0, total_C0, guarded_ne_maker]
  · simp [traceProb, admitted_C0, admitted_C2, result_guarded_C0, total_C0, total_C2,
      maker_ne_guarded, positive.ne']

theorem shares_totals :
    contentionTotal A label inhibition weight SharesTake C0 maker = weight maker ∧
      contentionTotal A label inhibition weight SharesTake C0 guarded = weight guarded ∧
      contentionTotal A label inhibition weight SharesTake C2 maker = weight maker := by
  refine ⟨?_, ?_, ?_⟩
  · simp [contentionTotal, admitted_C0, guarded_ne_maker, not_shares_maker_guarded]
  · simp [contentionTotal, admitted_C0, maker_ne_guarded, not_shares_guarded_maker]
  · simp [contentionTotal, admitted_C2]

theorem contends_totals :
    contentionTotal A label inhibition weight (Contends label) C0 maker =
        weight maker + weight guarded ∧
      contentionTotal A label inhibition weight (Contends label) C0 guarded =
        weight maker + weight guarded ∧
      contentionTotal A label inhibition weight (Contends label) C2 maker = weight maker := by
  refine ⟨?_, ?_, ?_⟩
  · simp [contentionTotal, admitted_C0, contends_maker_guarded A]
  · simp [contentionTotal, admitted_C0, contends_guarded_maker A]
  · simp [contentionTotal, admitted_C2]

/-- **The inhibition control.** The two maximal runs from `C0` are `[maker]` and
`[guarded, maker]` (nothing is admitted after either). Normalized inside sharing contention sets,
both have likelihood `1`, total mass `2`. Normalized inside contention sets that include inhibition,
they have the step's jump-chain likelihoods, total mass `1`. -/
theorem inhibition_control (positiveM : 0 < weight maker) (positiveG : 0 < weight guarded) :
    admitted A label inhibition ((maker (S := S)).result label C0) = [] ∧
      admitted A label inhibition ((maker (S := S)).result label ((guarded (S := S)).result label C0)) = [] ∧
      localProb A label inhibition weight SharesTake C0 [maker] +
          localProb A label inhibition weight SharesTake C0 [guarded, maker] = 2 ∧
      localProb A label inhibition weight (Contends label) C0 [maker] =
          traceProb A label inhibition id weight [maker] C0 ∧
      localProb A label inhibition weight (Contends label) C0 [guarded, maker] =
          traceProb A label inhibition id weight [guarded, maker] C0 ∧
      traceProb A label inhibition id weight [maker] C0 +
          traceProb A label inhibition id weight [guarded, maker] C0 = 1 := by
  obtain ⟨s0m, s0g, s2m⟩ := shares_totals A weight
  obtain ⟨c0m, c0g, c2m⟩ := contends_totals A weight
  obtain ⟨j1, j2⟩ := jump_chain A weight positiveM
  have sum : weight maker + weight guarded ≠ 0 := (add_pos positiveM positiveG).ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [result_maker_C0]
    exact admitted_C1 A
  · rw [result_guarded_C0, result_maker_C2]
    exact admitted_C3 A
  · simp only [localProb, s0m, s0g, result_guarded_C0, s2m, div_self positiveM.ne',
      div_self positiveG.ne', mul_one]
    norm_num
  · rw [j1]
    simp only [localProb, c0m, mul_one]
  · rw [j2]
    simp only [localProb, c0g, result_guarded_C0, c2m, div_self positiveM.ne', mul_one]
  · rw [j1, j2, ← add_div, div_self sum]

/-! ### The forcing control -/

/-- **One atom forces a race.** At `D0`, `racer` fires first with probability `w_r/(w_r+w_v)`,
below `1`. After a context adds one occurrence of `p`, `vetoed` is refused and `racer` fires with
probability `1`. -/
theorem forcing_control (positiveR : 0 < weight racer) (positiveV : 0 < weight vetoed) :
    prob A label race id weight D0 racer Set.univ = weight racer / (weight racer + weight vetoed) ∧
      prob A label race id weight D0 racer Set.univ < 1 ∧
      prob A label race id weight (addAtom D0 .mp) racer Set.univ = 1 := by
  have first : prob A label race id weight D0 racer Set.univ =
      weight racer / (weight racer + weight vetoed) := by
    simp [prob, total, admitted_D0, vetoed_ne_racer]
  refine ⟨first, ?_, ?_⟩
  · rw [first, div_lt_one (add_pos positiveR positiveV)]
    linarith
  · simp [prob, total, admitted_D0_vetoed, positiveR.ne']

/-- `racer` is inhibitor-free. -/
theorem racer_free : InhibitorFree (racer (S := S)) :=
  ⟨fun check member => by simp [racer] at member, rfl⟩

/-- **The other way no context forces**: whatever occurrences a context adds, other than what
`racer` makes, `vetoed` fires first with probability below `1`. -/
theorem cannot_force_vetoed (nonneg : ∀ h, 0 ≤ weight h) (positiveR : 0 < weight racer)
    (os : List Site) (fresh : ∀ o ∈ os, o ∉ (racer (S := S)).selection.made) :
    prob A label race id weight (addAll D0 os) vetoed Set.univ < 1 := by
  have racerValid : (racer (S := S)).Valid A label D0 :=
    (mem_admitted.mp (by rw [admitted_D0]; exact List.mem_cons_self)).2
  exact no_context_forces nonneg racer_ne_vetoed (by simp [race]) racer_free positiveR
    racerValid os fresh

end Controls

#print axioms not_independent_of_contends
#print axioms refused_after_inhibitor
#print axioms Queried.valid_iff
#print axioms mem_admitted
#print axioms admitted_eq_filter
#print axioms valid_addAtom
#print axioms valid_addAll
#print axioms prob_lt_one
#print axioms no_context_forces
#print axioms Controls.admitted_C0
#print axioms Controls.maker_guarded_dependent
#print axioms Controls.guarded_refused
#print axioms Controls.jump_chain
#print axioms Controls.inhibition_control
#print axioms Controls.forcing_control
#print axioms Controls.cannot_force_vetoed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Contention
