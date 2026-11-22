import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection.DataLaw
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection.QuotedNames

/-!
# Footprints of transforms that install transforms

A transform's template may build a rule: `whenever` written inside a template, with variables bound
by the outer firing. When the outer transform fires, the rule is installed with those bindings. This
module answers how far static footprints reach.

## Installed rules are closures

An installed rule is a **closure**: a rule text of the program and the environment the installing
firing bound (`ClosureFires`). Its rows are the rows of the text from that environment, so bindings
flow into the rule exactly as they flow from one source to the next.

* **Every firing of every installed instance lies within the text's static footprint**
  (`closure_within_text`), whatever the environment. Static apartness of two texts makes all firings
  of all their instances independent (`closures_independent_of_staticApart`).
* **Text-closed programs** (`TextClosed`): every rule that a text's template can build decodes to a
  closure of a text of the program. Then the store never holds a rule from outside the program
  (`rulesFromTexts_fire`), and **every firing at every depth of installation lies within the static
  footprint of a program text** (`ReflectiveRun.within`). Static footprints extend to higher-order
  transforms unchanged.

## Where precision is lost, and where it comes back

* **A variable in a key position gives the key `any`** (`FootprintControls.variable_channel_any`): a listener
  installed on a channel bound by the outer firing has no static key below everything.
* **The footprint is precise at installation** (`closure_within_specialized`): once the environment
  is known, the keys of the text read through the environment (`specHeadKeys`) are sound for every
  firing of that closure (`specHeadKeys_soundFrom`, through `static_covers_from`, the static
  footprint relative to an environment). For the listener they are the channel's own key
  (`FootprintControls.listener_specialized`). Reflection with closures does not need footprints computed
  during a commit; it needs them computed when the rule is installed.

## Rules from data

When a rule is not a closure of a program text but code read from data and decoded, nothing in the
program bounds it: **every label is taken by some decodable rule** (`ground_take_rule_fires`). With a
decoding that reaches every rule text, no list of keys that misses a label bounds the rules that can be
installed (`no_static_bound_for_data_rules`). Their footprint is the static footprint of the decoded
text, computed at the installing commit, after an explicit `eval` or decode of the code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative

universe uO uV uT uP uK uF

variable {O : Type uO} [DecidableEq O] {V : Type uV} {T : Type uT} {P : Type uP} {K : Type uK}

/-! ## Closures -/

section Closures

variable (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) (S : Finset O)

/-- **A closure fires a commit**: the rule text's rows from the environment `σ` give a linear row,
and the commit is of its footprint. -/
def ClosureFires (t : Transform V T P) (σ : Subst V T) (c : Commit O T) : Prop :=
  ∃ x ∈ rows L m label S t.template t.sources σ, (footprintOf x.2).Linear ∧
    IsCommitOf label S (footprintOf x.2) c

variable {L m label S}

/-- With the empty environment, a closure fires what its text fires. -/
theorem closureFires_empty_iff {t : Transform V T P} {c : Commit O T} :
    ClosureFires L m label S t (fun _ => none) c ↔ Fires L m label S t c := Iff.rfl

theorem ClosureFires.enabled {t : Transform V T P} {σ : Subst V T} {c : Commit O T}
    (fires : ClosureFires L m label S t σ c) : Enabled label S c := by
  obtain ⟨x, member, linear, commit⟩ := fires
  exact (commit.enabled_iff commit.fresh).mpr ⟨holds_of_mem_rows member, linear.2⟩

/-- **Every firing of every installed instance lies within the text's static footprint.** -/
theorem closure_within_text {R : RegionKeys T P K} (sound : Matcher.Sound L m) (keysSound : R.Sound L)
    {t : Transform V T P} {σ : Subst V T} {c : Commit O T} (fires : ClosureFires L m label S t σ c) :
    ∃ fp, IsCommitOf label S fp c ∧ Within R label fp (t.static R) := by
  obtain ⟨x, member, -, commit⟩ := fires
  exact ⟨_, commit, static_covers sound keysSound member⟩

/-- What a closure makes is an instance of its text's template. -/
theorem closure_made_is_instance (sound : Matcher.Sound L m) {t : Transform V T P} {σ : Subst V T}
    {c : Commit O T} (fires : ClosureFires L m label S t σ c) {o : O} (made : o ∈ c.made) :
    ∃ q ∈ t.template, ∃ τ, L.Solves τ q (label o) := by
  obtain ⟨x, member, -, commit⟩ := fires
  have within := static_covers (R := instanceKeys L) sound (instanceKeys_sound L) member
  obtain ⟨q, inKeys, τ, solves⟩ := commit.made_covered within made
  rw [static_makes] at inKeys
  simp only [instanceKeys, List.flatMap_singleton'] at inKeys
  exact ⟨q, by simpa using inKeys, τ, solves⟩

/-- **Statically apart texts have independent instances**, for every pair of environments. -/
theorem closures_independent_of_staticApart {R : RegionKeys T P K} (sound : Matcher.Sound L m)
    (keysSound : R.Sound L) {t t' : Transform V T P} (apart : (t.static R).Apart R (t'.static R))
    {σ σ' : Subst V T} {S' : Finset O} {c d : Commit O T}
    (fires : ClosureFires L m label S t σ c) (fires' : ClosureFires L m label S' t' σ' d)
    (freshApart : Disjoint c.made d.made) : Independent label c d := by
  obtain ⟨x, member, -, commit⟩ := fires
  obtain ⟨x', member', -, commit'⟩ := fires'
  exact independent_of_apart commit commit' (static_covers sound keysSound member)
    (static_covers sound keysSound member') apart freshApart

end Closures

/-! ## Text-closed programs -/

section Programs

variable {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}
variable (decodeRule : T → Option (Transform V T P × Subst V T)) (texts : List (Transform V T P))

/-- Every rule in the store decodes to a closure of a program text. -/
def RulesFromTexts (label : O → T) (S : Finset O) : Prop :=
  ∀ o ∈ S, ∀ t σ, decodeRule (label o) = some (t, σ) → t ∈ texts

/-- **A program is text-closed** when every rule a text's template can build decodes to a closure of
a program text. -/
def TextClosed (L : TermLayer V T P) : Prop :=
  ∀ t ∈ texts, ∀ q ∈ t.template, ∀ τ u, L.Solves τ q u →
    ∀ t' σ', decodeRule u = some (t', σ') → t' ∈ texts

/-- One step of a reflective program: some rule in the store fires its closure. -/
def ReflectiveStep (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) (S : Finset O)
    (c : Commit O T) : Prop :=
  ∃ r ∈ S, ∃ t σ, decodeRule (label r) = some (t, σ) ∧ ClosureFires L m label S t σ c

/-- A run of a reflective program. -/
inductive ReflectiveRun (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) :
    Finset O → List (Commit O T) → Prop
  | nil (S : Finset O) : ReflectiveRun L m label S []
  | cons {S : Finset O} {c : Commit O T} {rest : List (Commit O T)} :
      ReflectiveStep decodeRule L m label S c → ReflectiveRun L m label (fire S c) rest →
        ReflectiveRun L m label S (c :: rest)

variable {decodeRule texts}

/-- **A text-closed program never installs a rule from outside its texts.** -/
theorem rulesFromTexts_fire (sound : Matcher.Sound L m) (closed : TextClosed decodeRule texts L)
    {S : Finset O} (inv : RulesFromTexts decodeRule texts label S) {c : Commit O T}
    (step : ReflectiveStep decodeRule L m label S c) :
    RulesFromTexts decodeRule texts label (fire S c) := by
  obtain ⟨r, inS, t, σ, decoded, fires⟩ := step
  have textIn : t ∈ texts := inv r inS t σ decoded
  intro o member t' σ' decoded'
  rcases mem_fire.mp member with ⟨old, -⟩ | made
  · exact inv o old t' σ' decoded'
  · obtain ⟨q, inTemplate, τ, solves⟩ := closure_made_is_instance sound fires made
    exact closed t textIn q inTemplate τ (label o) solves t' σ' decoded'

/-- **Static footprints reach every depth of installation.** In a run of a text-closed program that
starts with rules from its texts, every commit lies within the static footprint of a program text. -/
theorem ReflectiveRun.within {R : RegionKeys T P K} (sound : Matcher.Sound L m)
    (keysSound : R.Sound L) (closed : TextClosed decodeRule texts L) :
    ∀ {S : Finset O} {run : List (Commit O T)}, ReflectiveRun decodeRule L m label S run →
      RulesFromTexts decodeRule texts label S →
      ∀ c ∈ run, ∃ t ∈ texts, ∃ S' fp, IsCommitOf label S' fp c ∧ Within R label fp (t.static R) := by
  intro S run reflective inv
  induction reflective with
  | nil => simp
  | @cons S c rest step _ ih =>
      intro d member
      rcases List.mem_cons.mp member with rfl | inRest
      · obtain ⟨r, inS, t, σ, decoded, fires⟩ := step
        obtain ⟨fp, commit, within⟩ := closure_within_text sound keysSound fires
        exact ⟨t, inv r inS t σ decoded, S, fp, commit, within⟩
      · exact ih (rulesFromTexts_fire sound closed inv step) d inRest

end Programs

/-! ## Static footprints relative to an environment -/

section Relative

variable {L : TermLayer V T P} {m : Matcher V T P} {label : O → T} {R : RegionKeys T P K}

/-- Keys **sound from an environment**: they cover every value a pattern solves under a substitution
that extends the environment. -/
def KeysSoundFrom (R : RegionKeys T P K) (L : TermLayer V T P) (σ₀ : Subst V T) : Prop :=
  ∀ τ, Extends σ₀ τ → ∀ p t, L.Solves τ p t → R.CoveredBy (R.keys p) t

theorem keysSoundFrom_of_sound (keysSound : R.Sound L) (σ₀ : Subst V T) : KeysSoundFrom R L σ₀ :=
  fun τ _ p t solves => keysSound τ p t solves

theorem region_covered_from (sound : Matcher.Sound L m) {σ₀ σ : Subst V T}
    (keysSound : KeysSoundFrom R L σ₀) (grows : Extends σ₀ σ) {p : P} {t : T}
    (inRegion : Matcher.region m σ p t = true) : R.CoveredBy (R.keys p) t := by
  obtain ⟨τ, step⟩ := sound.covers inRegion
  exact keysSound τ (grows.trans step.extends_) p t step.solves

theorem answer_covered_from (sound : Matcher.Sound L m) {σ₀ σ τ : Subst V T}
    (keysSound : KeysSoundFrom R L σ₀) (grows : Extends σ₀ σ) {p : P} {t : T}
    (answer : τ ∈ m p σ t) : R.CoveredBy (R.keys p) t :=
  keysSound τ (grows.trans (sound answer).extends_) p t (sound answer).solves

omit [DecidableEq O] in
theorem within_full_from (sound : Matcher.Sound L m) {σ₀ σ : Subst V T}
    (keysSound : KeysSoundFrom R L σ₀) (grows : Extends σ₀ σ) {S : Finset O} {p : P} (consume : Bool)
    (takeKeys : List K)
    (takesCovered : consume = true → ∀ t, R.CoveredBy (R.keys p) t → R.CoveredBy takeKeys t) :
    Within R label
      (Pick.query ⟨Matcher.region m σ p, regionOf label S (Matcher.region m σ p)⟩ consume).footprint
      ⟨takeKeys, [], R.keys p, []⟩ := by
  refine ⟨fun o member => ?_, by simp, fun r member t inRegion => ?_, by simp⟩
  · simp only [footprint_query] at member
    split_ifs at member with consumed
    · obtain ⟨-, inRegion⟩ := mem_regionOf.mp (Finset.mem_val.mp member)
      exact takesCovered consumed _ (region_covered_from sound keysSound grows inRegion)
    · simp at member
  · simp only [footprint_query, Multiset.mem_singleton] at member
    subst member
    exact region_covered_from sound keysSound grows inRegion

theorem within_stepRows_from (sound : Matcher.Sound L m) {σ₀ σ : Subst V T}
    (keysSound : KeysSoundFrom R L σ₀) (grows : Extends σ₀ σ) {S : Finset O} {s : Source V T P}
    {x : Subst V T × Pick O T} (member : x ∈ stepRows m label S s σ) :
    Within R label x.2.footprint (s.static R) := by
  cases s with
  | read p =>
      obtain ⟨o, -, τ, answer, rfl⟩ := mem_stepRows_read.mp member
      exact ⟨by simp, fun o' h => by
        simp only [footprint_keep, Multiset.mem_singleton] at h
        subst h
        exact answer_covered_from sound keysSound grows answer, by simp, by simp⟩
  | take p =>
      obtain ⟨o, -, τ, answer, rfl⟩ := mem_stepRows_take.mp member
      exact ⟨fun o' h => by
        simp only [footprint_take, Multiset.mem_singleton] at h
        subst h
        exact answer_covered_from sound keysSound grows answer, by simp, by simp, by simp⟩
  | absent p =>
      obtain ⟨-, rfl⟩ := mem_stepRows_absent.mp member
      refine ⟨by simp, by simp, fun r h t inRegion => ?_, by simp⟩
      simp only [footprint_query, Multiset.mem_singleton] at h
      subst h
      exact region_covered_from sound keysSound grows inRegion
  | unique access p =>
      obtain ⟨-, o, -, τ, -, rfl⟩ := mem_stepRows_unique.mp member
      exact within_full_from sound keysSound grows _ _ fun consumed t covered => by
        simp only [decide_eq_true_eq] at consumed
        simpa [Source.static, consumed] using covered
  | collect access p coll fold =>
      obtain ⟨τ, -, rfl⟩ := mem_stepRows_collect.mp member
      exact within_full_from sound keysSound grows _ _ fun consumed t covered => by
        simp only [decide_eq_true_eq] at consumed
        simpa [Source.static, consumed] using covered
  | letBind p eval =>
      obtain ⟨i, value, -, τ, -, rfl⟩ := mem_stepRows_letBind.mp member
      exact Within.zero _

theorem complRegions_covered_from (sound : Matcher.Sound L m) {σ₀ σ : Subst V T}
    (keysSound : KeysSoundFrom R L σ₀) (grows : Extends σ₀ σ) :
    ∀ {src : SourceList V T P} {r : T → Bool}, r ∈ complRegions m src σ →
      ∀ t, r t = true → R.CoveredBy (src.regionKeys R) t
  | .done, r, member, _, _ => by simp [complRegions] at member
  | .cons s rest, r, member, t, inRegion => by
      simp only [complRegions, List.mem_append] at member
      rcases member with inS | inRest
      · refine RegionKeys.CoveredBy.append_left ?_
        cases s <;> simp only [Source.regions, List.mem_singleton, List.not_mem_nil] at inS <;>
          subst inS <;> exact region_covered_from sound keysSound grows inRegion
      · exact RegionKeys.CoveredBy.append_right
          (complRegions_covered_from sound keysSound grows inRest t inRegion)
  | .absent query rest, r, member, t, inRegion => by
      simp only [complRegions, List.mem_append] at member
      rcases member with first | second
      · exact RegionKeys.CoveredBy.append_left
          (complRegions_covered_from sound keysSound grows first t inRegion)
      · exact RegionKeys.CoveredBy.append_right
          (complRegions_covered_from sound keysSound grows second t inRegion)
  | .every rest, r, member, t, inRegion =>
      complRegions_covered_from sound keysSound grows (src := rest) member t inRegion

/-- **The static footprint relative to an environment over-approximates the rows from it.** -/
theorem static_covers_from (sound : Matcher.Sound L m) {σ₀ : Subst V T}
    (keysSound : KeysSoundFrom R L σ₀) {S : Finset O} {template : List P} :
    ∀ {src : SourceList V T P} {σ : Subst V T} {x : Subst V T × List (Pick O T)}, Extends σ₀ σ →
      x ∈ rows L m label S template src σ → Within R label (footprintOf x.2) (src.static R template)
  | .done, σ, x, grows, member => by
      rw [rows_done] at member
      split at member
      · rename_i ts instEq
        rw [Multiset.mem_singleton] at member
        subst member
        refine ⟨by simp [footprintOf_cons], by simp [footprintOf_cons], by simp [footprintOf_cons],
          fun t inMakes => ?_⟩
        simp only [footprintOf_cons, footprint_make, footprintOf_nil, add_zero,
          Multiset.mem_coe] at inMakes
        obtain ⟨q, inTemplate, instQ⟩ := instTemplate_mem instEq t inMakes
        obtain ⟨k, inKeys, covers⟩ := keysSound σ grows q t ⟨t, instQ, L.equivalence.refl t⟩
        exact ⟨k, List.mem_flatMap.mpr ⟨q, inTemplate, inKeys⟩, covers⟩
      · simp at member
  | .cons s rest, σ, x, grows, member => by
      obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
      rw [footprintOf_cons]
      exact (within_stepRows_from sound keysSound grows inStep).add
        (static_covers_from sound keysSound (grows.trans (extends_of_mem_stepRows sound inStep)) inRest)
  | .absent query rest, σ, x, grows, member => by
      obtain ⟨_, y, inRest, rfl⟩ := mem_rows_absent.mp member
      rw [footprintOf_cons, footprint_amalgam]
      apply Within.add _ (static_covers_from sound keysSound grows inRest)
      refine ⟨by simp [complQueries], by simp [complQueries], ?_, by simp [complQueries]⟩
      intro r member t inRegion
      simp only [complQueries, Multiset.mem_coe, List.mem_map] at member
      obtain ⟨r', inRegions, rfl⟩ := member
      exact complRegions_covered_from sound keysSound grows inRegions t inRegion
  | .every rest, σ, x, grows, member => by
      rw [rows_every, Multiset.mem_singleton] at member
      subst member
      simp only [footprintOf_cons, footprint_amalgam, footprintOf_nil, add_zero]
      unfold everyFootprint
      refine Within.add (Within.sum fun fp inMap => ?_) ?_
      · obtain ⟨y, inFilter, rfl⟩ := Multiset.mem_map.mp inMap
        exact static_covers_from sound keysSound grows (Multiset.mem_of_mem_filter inFilter)
      · refine ⟨by simp [complQueries], by simp [complQueries], fun r member t inRegion => ?_,
          by simp [complQueries]⟩
        simp only [complQueries, Multiset.mem_coe, List.mem_map] at member
        obtain ⟨r', inRegions, rfl⟩ := member
        exact complRegions_covered_from sound keysSound grows inRegions t inRegion

end Relative

/-! ## Head keys read through an environment -/

section Specialized

variable {F : Type uF} [DecidableEq F] {X : Type uV} [DecidableEq X]

/-- Head keys of a pattern read through an environment: a bound variable has the key of its value's
head symbol. -/
def specHeadKeys (σ : Subst X (Tm F)) : Pat X F → List (Key F)
  | .var v =>
      match σ v with
      | some u => [.head u.head]
      | none => [.any]
  | .leaf a => [.head a]
  | .node f _ _ => [.head f]

/-- **Head keys read through an environment are sound from it**, for every declaration of commuting
symbols. -/
theorem specHeadKeys_soundFrom (comm : F → Bool) (σ : Subst X (Tm F)) :
    KeysSoundFrom (regionKeys (specHeadKeys σ)) (termLayer (V := X) comm) σ := by
  intro τ grows p t solves
  cases p with
  | var v =>
      cases bound : σ v with
      | none => exact ⟨.any, by simp [regionKeys, specHeadKeys, bound], trivial⟩
      | some u =>
          refine ⟨.head u.head, by simp [regionKeys, specHeadKeys, bound], ?_⟩
          obtain ⟨w, inst, rel⟩ := solves
          have tauV : τ v = some u := grows v u bound
          have same : w = u := by
            have h : (Pat.var v : Pat X F).inst τ = some w := inst
            simp only [Pat.inst, tauV, Option.some.injEq] at h
            exact h.symm
          subst same
          exact (head_eq_of_ceq rel).symm
  | leaf a =>
      rw [solves_leaf solves]
      exact ⟨.head a, by simp [regionKeys, specHeadKeys], rfl⟩
  | node f p q =>
      obtain ⟨u, v, l, r, -, -, rfl, -⟩ := solves_node solves
      exact ⟨.head f, by simp [regionKeys, specHeadKeys], rfl⟩

variable {O : Type uO} [DecidableEq O] {label : O → Tm F} {S : Finset O}

/-- **The footprint is precise at installation.** Every firing of a closure lies within the static
footprint of its text read through its environment. -/
theorem closure_within_specialized (comm : F → Bool) {t : Transform X (Tm F) (Pat X F)}
    {σ : Subst X (Tm F)} {c : Commit O (Tm F)}
    (fires : ClosureFires (termLayer comm) (cmatch comm) label S t σ c) :
    ∃ fp, IsCommitOf label S fp c ∧
      Within (regionKeys (specHeadKeys σ)) label fp (t.static (regionKeys (specHeadKeys σ))) := by
  obtain ⟨x, member, -, commit⟩ := fires
  exact ⟨_, commit, static_covers_from (cmatch_sound (comm := comm))
    (specHeadKeys_soundFrom comm σ) (Extends.refl σ) member⟩

end Specialized

/-! ## Rules from data -/

section DataRules

variable {F : Type uF} [DecidableEq F] {X : Type uV} [DecidableEq X]

theorem rawMatch_groundPat (σ : Subst X (Tm F)) :
    ∀ u : Tm F, rawMatch (fun _ => false) (groundPat u) σ u = [σ]
  | .leaf a => by simp [groundPat, rawMatch]
  | .node f l r => by
      simp [groundPat, rawMatch, rawMatch_groundPat σ l, rawMatch_groundPat σ r]

theorem cmatch_groundPat (σ : Subst X (Tm F)) (u : Tm F) :
    cmatch (fun _ => false) (groundPat u) σ u = [σ] := by
  rw [cmatch, rawMatch_groundPat, List.pwFilter_cons_of_pos (by simp), List.pwFilter_nil]

/-- The rule that takes one occurrence of the value `u`. -/
def groundTake (u : Tm F) : Transform X (Tm F) (Pat X F) := ⟨.cons (.take (groundPat u)) .done, []⟩

/-- **Every label is taken by some decodable rule**: the ground take rule of `u` fires at a store
holding `u` and takes it. -/
theorem ground_take_rule_fires (u : Tm F) (n : ℕ) :
    ∃ c, ClosureFires (termLayer (V := X) (fun _ => false)) (cmatch (fun _ => false)) Prod.fst
      ({(u, n)} : Finset (Tm F × ℕ)) (groundTake u) (fun _ => none) c ∧ (u, n) ∈ c.taken := by
  let x : Subst X (Tm F) × List (Pick (Tm F × ℕ) (Tm F)) :=
    ((fun _ => none), [.take (u, n), .make 0])
  have member : x ∈ rows (termLayer (V := X) (fun _ => false)) (cmatch (fun _ => false)) Prod.fst
      ({(u, n)} : Finset (Tm F × ℕ)) (groundTake u).template (groundTake u).sources (fun _ => none) := by
    refine mem_rows_cons.mpr ⟨((fun _ => none), .take (u, n)), ?_, ((fun _ => none), [.make 0]), ?_, rfl⟩
    · refine mem_stepRows_take.mpr ⟨(u, n), by simp, fun _ => none, ?_, rfl⟩
      rw [cmatch_groundPat]
      simp
    · simp [groundTake, rows_done, instTemplate]
  have linear : (footprintOf x.2).Linear := by
    simp [x, footprintOf, Footprint.Linear]
  let c : Commit (Tm F × ℕ) (Tm F) := ⟨{(u, n)}, ∅, ∅, []⟩
  refine ⟨c, ⟨x, member, linear, ⟨?_, ?_, ?_, ?_, ?_⟩⟩, by simp [c]⟩
  · simp [c, x, footprintOf]
  · simp [c, x, footprintOf]
  · intro r
    simp [c, x, footprintOf]
  · simp [c]
  · simp [c, x, footprintOf, labels]

/-- **No static bound for rules from data.** If the decoding of rules reaches every rule text, then a
list of keys that misses some label `u` does not bound the rules that can be installed: some decodable
rule fires a commit that takes an occurrence labelled `u`. -/
theorem no_static_bound_for_data_rules
    (decodeRule : Tm F → Option (Transform X (Tm F) (Pat X F) × Subst X (Tm F)))
    (universal : ∀ t, ∃ code, decodeRule code = some (t, fun _ => none))
    (ks : List (Key F)) (u : Tm F) (missed : ¬ (regionKeys (V := X) headKeys).CoveredBy ks u) :
    ∃ code t σ c, decodeRule code = some (t, σ) ∧
      ClosureFires (termLayer (V := X) (fun _ => false)) (cmatch (fun _ => false)) Prod.fst
        ({(u, 0)} : Finset (Tm F × ℕ)) t σ c ∧
      ∃ o ∈ c.taken, ¬ (regionKeys (V := X) headKeys).CoveredBy ks o.1 := by
  obtain ⟨code, decoded⟩ := universal (groundTake u)
  obtain ⟨c, fires, taken⟩ := ground_take_rule_fires (X := X) u 0
  exact ⟨code, groundTake u, fun _ => none, c, decoded, fires, (u, 0), taken, missed⟩

end DataRules

/-! ## Controls -/

namespace FootprintControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection.DataControls
  (CSig Occ lbl Ls ms headR un)

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection.DataControls.CSig

/-- A listener installed on a channel bound by the outer firing: take any message equal to the
channel's value. -/
def listener : Transform ℕ (Tm CSig) (Pat ℕ CSig) := ⟨.cons (.take (.var 0)) .done, []⟩

/-- **A variable in a key position gives the key `any`.** -/
theorem variable_channel_any : (listener.static headR).takes = [.any] := rfl

/-- The environment binding the channel to `bank`. -/
def onBank : Subst ℕ (Tm CSig) := fun v => if v = 0 then some (.leaf .bank) else none

/-- **Precise at installation**: read through its environment, the listener's static takes are the
channel's own head key. -/
theorem listener_specialized :
    (listener.static (regionKeys (specHeadKeys onBank))).takes = [.head .bank] := rfl

/-- The installed listener fires at a store holding a `bank` message, and nowhere else. -/
theorem listener_fires :
    ∃ x ∈ rows Ls ms lbl ({(.leaf .bank, 0), (.leaf .bal, 1)} : Finset Occ) listener.template
        listener.sources onBank,
      (footprintOf x.2).Linear ∧ (footprintOf x.2).takes = {(.leaf .bank, 0)} :=
  Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection.DataControls.copy_row.exists_of_not_forall
    (by decide)

end FootprintControls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection
