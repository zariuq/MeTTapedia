import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Card

/-!
# The candidate-selection (match-decision) contract, as an algebra

A rule-dispatch index answers: *given what is currently known about a query,
which stored equations could still apply?*  This module states that contract
algebraically and proves its laws.

The single organizing object is the **partial skeleton**: an assignment of
constructor observations to term positions, with `none` meaning
unknown/unavailable.  Observations of a query, left-hand-side patterns of
stored equations, and fully known terms are all skeletons; a total term
realizes an observation and matches a pattern through the *same* relation
(`Realizes`), and skeletons are ordered by information (`⊑`).

A decision backend samples finitely many positions and may *refute*
candidates only on observed disagreement.  The laws proved:

* `realizes_iff_not_conflicts` — a query state and a pattern have a common
  realization iff they nowhere visibly disagree.  So pointwise refutation is
  not only sound but *exactly* the most precise sound refutation-only
  decision, at this level of the model.
* `candidates_sublist` — the decision is a sublist of the source
  enumeration: source order and multiplicity are preserved (the filter is
  definitional, so every copy of a kept candidate is kept).
* `mem_candidates_of_realizes` — completeness: any candidate jointly
  realizable with the observation survives.  No false negatives.
* `candidates_antitone_obs` / `conflictsOn_mono_obs` — **availability
  monotonicity**: growing information only shrinks the candidate list, and
  refutations, once made, persist.  This is Kripke persistence for the
  information order, and it is the oracle-free property test: force more,
  candidates only shrink, refutations never retract.
* `candidates_nil_samples` / `candidates_bot` — with no samples, or no
  information, the decision *is* the linear enumeration: the oracle sits at
  the bottom of both parameters.
* `candidates_antitone_samples` — more sampled positions prune more,
  soundly (the fingerprint-family tuning law).
* `candidates_candidates` — composing two decisions equals one decision on
  the combined samples: refutation-only backends stack without
  renegotiation.
* `candidates_prefix_mono` — a prefix of the decision is determined by a
  prefix of the source: filtering is continuous for the prefix order, which
  is exactly what lazy (stream) enumeration needs.
* `eqRefutes_sound` / `eqRefutes_none_left`, `eqRefutes_none_right` /
  `eqRefutes_mono` — the non-linear (repeated-variable) refuter: sound,
  silent unless *both* of its positions are observed (no strictness
  introduced), and persistent.
* The `Shaped` layer re-proves the entire suite with a third observation —
  `absent` — over shaped terms (`Path → Option V`): the six-row per-point
  compatibility table `Shaped.Obs.conflictB` (sound and exact pointwise;
  the semantic core an executable decision policy consumes), skeleton-level
  exactness with *no* `Nonempty` assumption, the same monotonicity,
  completeness, order/multiplicity, fusion, and prefix-continuity laws, an
  eq-refuter that additionally fires on shape difference, and a coherence
  layer: `Shaped.saturate` derives the absences a term's arity discipline
  entails — extensive (`le_saturate`), sound for coherent terms
  (`saturate_sound`), pruning-only (`candidates_saturate_sublist`), and
  completeness-preserving (`mem_candidates_saturate_of_coherent`).  That is
  fingerprint-`N` behaviour derived, not assumed.

Scope, stated honestly.  The two-valued layer's exactness is relative to
unconstrained completions; the `Shaped` layer makes absence a first-class
observation and proves saturation extensive and sound, so refutation after
saturation never loses a coherently realizable candidate.  What remains
open: the *presence* direction of coherence ("present with arity `k`
entails children below `k` present with some tag") is a disjunctive fact
not representable as a single observation, so exactness relative to fully
coherent completions is not claimed — a tag-set-valued refinement would owe
it.  `saturate` is likewise not claimed monotone or idempotent on
incoherent observations.  Nothing here claims conformance of any concrete C
implementation; that authority belongs to differential testing against the
linear enumeration.
-/

namespace Mettapedia.GSLT.LanguageDef.MatchDecisionContract

/-- Positions in a term tree, addressed by child indices. -/
abbrev Path := List Nat

/-- What is known at each position: `some v` is an observed (or required)
constructor tag, `none` is unknown — an unforced argument, a pattern
variable, an unsampled position.  Observations, patterns, and terms are all
skeletons. -/
abbrev Skeleton (V : Type*) := Path → Option V

variable {V : Type*}

/-- Information order: `o ⊑ o'` when everything `o` knows, `o'` knows
identically.  Forcing an argument moves an observation strictly up this
order. -/
def Skeleton.LE (o o' : Skeleton V) : Prop :=
  ∀ p v, o p = some v → o' p = some v

@[inherit_doc] scoped infix:50 " ⊑ " => Skeleton.LE

theorem Skeleton.LE.refl (o : Skeleton V) : o ⊑ o := fun _ _ h => h

theorem Skeleton.LE.trans {a b c : Skeleton V} (hab : a ⊑ b) (hbc : b ⊑ c) :
    a ⊑ c := fun p v h => hbc p v (hab p v h)

theorem Skeleton.LE.antisymm {a b : Skeleton V} (hab : a ⊑ b) (hba : b ⊑ a) :
    a = b := by
  funext p
  cases ha : a p with
  | some v => exact (hab p v ha).symm
  | none =>
    cases hb : b p with
    | some w => exact absurd (hba p w hb) (by simp [ha])
    | none => rfl

/-- The completely uninformed skeleton: bottom of the information order. -/
def Skeleton.bot : Skeleton V := fun _ => none

theorem Skeleton.bot_le (o : Skeleton V) : Skeleton.bot ⊑ o := by
  intro p v h
  simp [Skeleton.bot] at h

/-- A total term `t` realizes a skeleton when it agrees with every
observation.  Read `Realizes t o` as "`t` completes the observation `o`" and
`Realizes t pat` as "`t` matches the pattern `pat`" — they are the same
relation, which is the point. -/
def Realizes (t : Path → V) (s : Skeleton V) : Prop :=
  ∀ p v, s p = some v → t p = v

theorem Realizes.mono {t : Path → V} {s s' : Skeleton V}
    (hle : s ⊑ s') (h : Realizes t s') : Realizes t s :=
  fun p v hp => h p v (hle p v hp)

/-- Two skeletons visibly disagree: some position is observed by both, with
different tags.  This is the only ground on which a candidate may ever be
refuted. -/
def Conflicts (o s : Skeleton V) : Prop :=
  ∃ p v w, o p = some v ∧ s p = some w ∧ v ≠ w

theorem Conflicts.mono {o o' s : Skeleton V} (hle : o ⊑ o')
    (h : Conflicts o s) : Conflicts o' s := by
  obtain ⟨p, v, w, hov, hsw, hne⟩ := h
  exact ⟨p, v, w, hle p v hov, hsw, hne⟩

/-- **Exactness of pointwise refutation** (flat model): an observation and a
pattern admit a common realization iff they nowhere visibly disagree.
Soundness is the forward contrapositive; the backward direction says no
sound refutation-only decision can prune more than pointwise conflict
already licenses. -/
theorem realizes_iff_not_conflicts [Nonempty V] (o pat : Skeleton V) :
    (∃ t, Realizes t o ∧ Realizes t pat) ↔ ¬ Conflicts o pat := by
  constructor
  · rintro ⟨t, hto, htp⟩ ⟨p, v, w, hov, hpw, hne⟩
    exact hne ((hto p v hov).symm.trans (htp p w hpw))
  · intro hnc
    refine ⟨fun p => match o p with
      | some v => v
      | none => match pat p with
        | some w => w
        | none => Classical.arbitrary V, ?_, ?_⟩
    · intro p v hov
      simp [hov]
    · intro p w hpw
      cases hop : o p with
      | none => simp [hop, hpw]
      | some v =>
        have hvw : v = w := by
          by_contra hne
          exact hnc ⟨p, v, w, hop, hpw, hne⟩
        simp [hop, hvw]

/-! ## The finite decision: sampled positions, refutation only -/

variable [DecidableEq V]

/-- One sampled position votes to refute only when both sides are observed
there and disagree.  An unknown on either side contributes nothing — this is
where "a variable or unavailable observation cannot justify pruning" lives,
definitionally. -/
def posConflict (o s : Skeleton V) (p : Path) : Bool :=
  match o p, s p with
  | some v, some w => !(decide (v = w))
  | _, _ => false

theorem posConflict_eq_true_iff {o s : Skeleton V} {p : Path} :
    posConflict o s p = true ↔
      ∃ v w, o p = some v ∧ s p = some w ∧ v ≠ w := by
  unfold posConflict
  cases ho : o p with
  | none => simp
  | some v =>
    cases hs : s p with
    | none => simp
    | some w =>
      by_cases hvw : v = w <;> simp [hvw]

/-- Refute on a finite sample list of positions. -/
def conflictsOn (ps : List Path) (o s : Skeleton V) : Bool :=
  ps.any (posConflict o s)

theorem conflictsOn_sound {ps : List Path} {o s : Skeleton V}
    (h : conflictsOn ps o s = true) : Conflicts o s := by
  obtain ⟨p, _, hp⟩ := List.any_eq_true.mp h
  obtain ⟨v, w, hov, hsw, hne⟩ := posConflict_eq_true_iff.mp hp
  exact ⟨p, v, w, hov, hsw, hne⟩

/-- Refutations persist as information grows. -/
theorem conflictsOn_mono_obs {ps : List Path} {o o' s : Skeleton V}
    (hle : o ⊑ o') (h : conflictsOn ps o s = true) :
    conflictsOn ps o' s = true := by
  obtain ⟨p, hmem, hp⟩ := List.any_eq_true.mp h
  obtain ⟨v, w, hov, hsw, hne⟩ := posConflict_eq_true_iff.mp hp
  exact List.any_eq_true.mpr
    ⟨p, hmem, posConflict_eq_true_iff.mpr ⟨v, w, hle p v hov, hsw, hne⟩⟩

/-- More samples can only find more conflicts. -/
theorem conflictsOn_mono_samples {ps ps' : List Path} {o s : Skeleton V}
    (hsub : ∀ p, p ∈ ps → p ∈ ps') (h : conflictsOn ps o s = true) :
    conflictsOn ps' o s = true := by
  obtain ⟨p, hmem, hp⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨p, hsub p hmem, hp⟩

/-- A candidate: an occurrence of a stored equation, carrying its pattern
skeleton.  `id` stands for occurrence identity; two distinct source
occurrences with equal patterns stay distinct. -/
structure Candidate (V : Type*) where
  id : Nat
  pat : Skeleton V

/-- The decision: keep, in source order with multiplicity, every candidate
the samples cannot refute. -/
def candidates (ps : List Path) (o : Skeleton V)
    (source : List (Candidate V)) : List (Candidate V) :=
  source.filter fun c => !(conflictsOn ps o c.pat)

/-- Source order and multiplicity are preserved: the decision is a sublist
of the enumeration it filters. -/
theorem candidates_sublist (ps : List Path) (o : Skeleton V)
    (source : List (Candidate V)) :
    (candidates ps o source).Sublist source :=
  List.filter_sublist

/-- Completeness (no false negatives): any candidate jointly realizable with
the observation survives every sound sample set. -/
theorem mem_candidates_of_realizes {ps : List Path} {o : Skeleton V}
    {source : List (Candidate V)} {c : Candidate V} {t : Path → V}
    (hmem : c ∈ source) (hto : Realizes t o) (htp : Realizes t c.pat) :
    c ∈ candidates ps o source := by
  refine List.mem_filter.mpr ⟨hmem, ?_⟩
  by_contra h
  simp only [Bool.not_eq_true, Bool.not_eq_false'] at h
  obtain ⟨p, v, w, hov, hpw, hne⟩ := conflictsOn_sound h
  exact hne ((hto p v hov).symm.trans (htp p w hpw))

/-- **Availability monotonicity**: growing the observation only shrinks the
decision.  With `conflictsOn_mono_obs` (refutations never retract), this is
the oracle-free property test for any backend claiming this contract. -/
theorem candidates_antitone_obs {ps : List Path} {o o' : Skeleton V}
    (hle : o ⊑ o') (source : List (Candidate V)) :
    (candidates ps o' source).Sublist (candidates ps o source) := by
  apply List.monotone_filter_right
  intro c hc
  simp only [Bool.not_eq_true'] at hc ⊢
  by_contra h
  simp only [Bool.not_eq_false] at h
  exact absurd (conflictsOn_mono_obs hle h) (by simp [hc])

/-- More samples prune more (soundly): the fingerprint-family tuning law. -/
theorem candidates_antitone_samples {ps ps' : List Path} {o : Skeleton V}
    (hsub : ∀ p, p ∈ ps → p ∈ ps') (source : List (Candidate V)) :
    (candidates ps' o source).Sublist (candidates ps o source) := by
  apply List.monotone_filter_right
  intro c hc
  simp only [Bool.not_eq_true'] at hc ⊢
  by_contra h
  simp only [Bool.not_eq_false] at h
  exact absurd (conflictsOn_mono_samples hsub h) (by simp [hc])

/-- With no samples the decision is the linear enumeration. -/
theorem candidates_nil_samples (o : Skeleton V)
    (source : List (Candidate V)) : candidates [] o source = source := by
  simp [candidates, conflictsOn]

/-- With no information the decision is the linear enumeration: the oracle
sits at the bottom of the information order. -/
theorem candidates_bot (ps : List Path) (source : List (Candidate V)) :
    candidates ps Skeleton.bot source = source := by
  have hfalse : ∀ c : Candidate V,
      conflictsOn ps Skeleton.bot c.pat = false := by
    intro c
    rw [← Bool.not_eq_true]
    intro h
    obtain ⟨p, v, w, hov, _, _⟩ := conflictsOn_sound h
    simp [Skeleton.bot] at hov
  simp [candidates, hfalse]

/-- Backend stacking: deciding twice equals deciding once on the combined
samples.  Refutation-only backends compose without renegotiating the
contract. -/
theorem candidates_candidates (ps ps' : List Path) (o : Skeleton V)
    (source : List (Candidate V)) :
    candidates ps' o (candidates ps o source) =
      candidates (ps ++ ps') o source := by
  simp [candidates, List.filter_filter, conflictsOn, List.any_append,
    Bool.not_or, Bool.and_comm]

/-- Prefix continuity: a prefix of the source determines the corresponding
prefix of the decision.  This is the law that licenses replacing the
materialized candidate list by a lazy stream: consumers that stop early
never force the rest of the enumeration. -/
theorem candidates_prefix_mono {source source' : List (Candidate V)}
    (ps : List Path) (o : Skeleton V) (h : source <+: source') :
    (candidates ps o source) <+: (candidates ps o source') := by
  obtain ⟨rest, rfl⟩ := h
  exact ⟨candidates ps o rest, by simp [candidates, List.filter_append]⟩

/-! ## The non-linear refuter (repeated variables) -/

/-- A repeated variable in a pattern induces a cross-position equality
constraint.  It may refute only when *both* positions are observed and
disagree. -/
def eqRefutes (p q : Path) (o : Skeleton V) : Bool :=
  match o p, o q with
  | some v, some w => !(decide (v = w))
  | _, _ => false

theorem eqRefutes_eq_true_iff {p q : Path} {o : Skeleton V} :
    eqRefutes p q o = true ↔
      ∃ v w, o p = some v ∧ o q = some w ∧ v ≠ w := by
  unfold eqRefutes
  cases hop : o p with
  | none => simp
  | some v =>
    cases hoq : o q with
    | none => simp
    | some w =>
      by_cases hvw : v = w <;> simp [hvw]

/-- Soundness: an observed cross-position disagreement excludes every
realization that would have to identify the two positions. -/
theorem eqRefutes_sound {p q : Path} {o : Skeleton V} {t : Path → V}
    (h : eqRefutes p q o = true) (hto : Realizes t o) : t p ≠ t q := by
  obtain ⟨v, w, hpv, hqw, hne⟩ := eqRefutes_eq_true_iff.mp h
  rw [hto p v hpv, hto q w hqw]
  exact hne

/-- No strictness introduced: the refuter is silent while its first position
is unobserved. -/
theorem eqRefutes_none_left {p q : Path} {o : Skeleton V}
    (h : o p = none) : eqRefutes p q o = false := by
  rw [Bool.eq_false_iff]
  intro hcontra
  obtain ⟨v, _, hpv, _, _⟩ := eqRefutes_eq_true_iff.mp hcontra
  simp [h] at hpv

/-- No strictness introduced: the refuter is silent while its second
position is unobserved. -/
theorem eqRefutes_none_right {p q : Path} {o : Skeleton V}
    (h : o q = none) : eqRefutes p q o = false := by
  rw [Bool.eq_false_iff]
  intro hcontra
  obtain ⟨_, w, _, hqw, _⟩ := eqRefutes_eq_true_iff.mp hcontra
  simp [h] at hqw

/-- Equality refutations also persist as information grows. -/
theorem eqRefutes_mono {p q : Path} {o o' : Skeleton V} (hle : o ⊑ o')
    (h : eqRefutes p q o = true) : eqRefutes p q o' = true := by
  rw [eqRefutes_eq_true_iff] at h ⊢
  obtain ⟨v, w, hpv, hqw, hne⟩ := h
  exact ⟨v, w, hle p v hpv, hle q w hqw, hne⟩

/-! ## Examples

Positive and negative instances over a two-tag alphabet, checking each
concept in both directions. -/

section Examples

/-- Tags for examples: two constructors. -/
private inductive Tag where
  | A
  | B
  deriving DecidableEq

private instance : Nonempty Tag := ⟨Tag.A⟩

/-- An observation knowing only position `[0]`. -/
private def obsA : Skeleton Tag :=
  fun p => if p = [0] then some Tag.A else none

/-- A pattern requiring `B` at position `[0]`: visibly conflicts with
`obsA`. -/
private def patB : Skeleton Tag :=
  fun p => if p = [0] then some Tag.B else none

/-- A pattern requiring `B` at the *unobserved* position `[1]`: compatible
with `obsA`, so it must never be pruned. -/
private def patDeep : Skeleton Tag :=
  fun p => if p = [1] then some Tag.B else none

/-- Positive: the sampled position refutes the conflicting pattern. -/
example : conflictsOn [[0]] obsA patB = true := by rfl

/-- Negative: an unobserved position never refutes — `patDeep` constrains
only position `[1]`, which `obsA` has not forced. -/
example : conflictsOn [[0], [1]] obsA patDeep = false := by rfl

/-- Negative: sampling positions the pattern leaves free refutes nothing. -/
example : conflictsOn [[1]] obsA patB = false := by rfl

/-- The decision keeps the compatible candidate and drops the conflicted
one, in source order. -/
example :
    candidates [[0]] obsA [⟨0, patB⟩, ⟨1, patDeep⟩, ⟨2, patB⟩] =
      [⟨1, patDeep⟩] := by rfl

/-- Bottom recovers the oracle on a concrete source. -/
example :
    candidates [[0]] Skeleton.bot [⟨0, patB⟩, ⟨1, patDeep⟩] =
      [⟨0, patB⟩, ⟨1, patDeep⟩] := by rfl

/-- Positive: the equality refuter fires once both positions are observed
with different tags. -/
example :
    eqRefutes [0] [1]
      (fun p => if p = [0] then some Tag.A else
        if p = [1] then some Tag.B else none) = true := by rfl

/-- Negative: with the second position suspended, the same constraint stays
silent — the overlapping-supports discipline. -/
example : eqRefutes [0] [1] obsA = false := by rfl

end Examples

/-! ## Shaped terms: the absence-aware layer

The flat model above observes only unknown/known.  The C runtime also
observes that a position is *absent* — sampling below a nullary constructor
or beyond a node's arity.  This layer enriches the per-point observation to
`unknown | absent | present v` and re-proves every law.  Terms become
*shaped*: `Path → Option V`, with `none` meaning the position does not
exist.  Absence is knowledge, not ignorance: `unknown` is the bottom of the
per-point information order, while `absent` and `present v` are maximal. -/

namespace Shaped

/-- One point's observation: nothing yet, known absent, or known present
with tag `v`.  `absent` is an *available* observation (a forced position
found missing), not ignorance. -/
inductive Obs (V : Type*) where
  | unknown
  | absent
  | present (v : V)

/-- Shaped terms: `none` means the position does not exist in the term. -/
abbrev Term (V : Type*) := Path → Option V

/-- Skeletons over three-valued observations. -/
abbrev Skeleton (V : Type*) := Path → Obs V

namespace Obs

variable {V : Type*}

/-- Satisfaction of one observation by one term point. -/
def Holds : Option V → Obs V → Prop
  | _, unknown => True
  | none, absent => True
  | some _, absent => False
  | none, present _ => False
  | some w, present v => w = v

/-- Per-point information order: `unknown` below everything; `absent` and
`present v` are maximal. -/
def le : Obs V → Obs V → Prop
  | unknown, _ => True
  | absent, absent => True
  | present v, present w => v = w
  | _, _ => False

theorem le.refl : ∀ a : Obs V, le a a
  | unknown => trivial
  | absent => trivial
  | present _ => rfl

theorem le.trans {a b c : Obs V} (hab : le a b) (hbc : le b c) : le a c := by
  cases a <;> cases b <;> cases c <;> simp_all [le]

/-- Satisfiers only shrink as per-point information grows. -/
theorem holds_anti {a b : Obs V} (hle : le a b) {d : Option V}
    (h : Holds d b) : Holds d a := by
  cases a <;> cases b <;> cases d <;> simp_all [le, Holds]

/-- The six-row compatibility table — the semantic core an executable
decision policy consumes.  `unknown` on either side never conflicts;
`absent` conflicts exactly with `present`; two `present` observations
conflict exactly on distinct tags. -/
def conflictB [DecidableEq V] : Obs V → Obs V → Bool
  | unknown, _ => false
  | _, unknown => false
  | absent, absent => false
  | absent, present _ => true
  | present _, absent => true
  | present v, present w => !(decide (v = w))

theorem conflictB_unknown_left [DecidableEq V] (b : Obs V) :
    conflictB (unknown : Obs V) b = false := rfl

theorem conflictB_unknown_right [DecidableEq V] : ∀ a : Obs V,
    conflictB a (unknown : Obs V) = false
  | unknown => rfl
  | absent => rfl
  | present _ => rfl

/-- Table soundness: a conflict row excludes any common satisfier. -/
theorem conflictB_sound [DecidableEq V] {a b : Obs V} {d : Option V}
    (h : conflictB a b = true) (ha : Holds d a) (hb : Holds d b) : False := by
  cases a <;> cases b <;> cases d <;> simp_all [conflictB, Holds]

/-- Constructive per-point witness for compatible observations. -/
def witness : Obs V → Obs V → Option V
  | present v, _ => some v
  | _, present w => some w
  | _, _ => none

/-- Per-point exactness: compatible observations have a common satisfier —
with no `Nonempty` assumption, since `none` is always available. -/
theorem holds_witness [DecidableEq V] {a b : Obs V}
    (h : conflictB a b = false) :
    Holds (witness a b) a ∧ Holds (witness a b) b := by
  cases a <;> cases b <;> simp_all [conflictB, witness, Holds]

theorem conflictB_mono_left [DecidableEq V] {a a' b : Obs V}
    (hle : le a a') (h : conflictB a b = true) : conflictB a' b = true := by
  cases a <;> cases a' <;> cases b <;> simp_all [le, conflictB]

theorem conflictB_mono_right [DecidableEq V] {a b b' : Obs V}
    (hle : le b b') (h : conflictB a b = true) : conflictB a b' = true := by
  cases a <;> cases b <;> cases b' <;> simp_all [le, conflictB]

/-- The two-valued layer embeds: `none` was `unknown`, `some v` was
`present v` — the flat layer simply never spoke of absence. -/
def ofOption : Option V → Obs V
  | none => unknown
  | some v => present v

/-- Conservativity of the table over the flat fragment. -/
theorem conflictB_ofOption [DecidableEq V] (a b : Option V) :
    conflictB (ofOption a) (ofOption b) =
      match a, b with
      | some v, some w => !(decide (v = w))
      | _, _ => false := by
  cases a <;> cases b <;> rfl

end Obs

variable {V : Type*}

/-- Pointwise information order on shaped skeletons. -/
def Skeleton.LE (o o' : Skeleton V) : Prop := ∀ p, Obs.le (o p) (o' p)

@[inherit_doc] scoped infix:50 " ⊑ₛ " => Skeleton.LE

/-- No information at all. -/
def Skeleton.bot : Skeleton V := fun _ => Obs.unknown

theorem Skeleton.bot_le (o : Skeleton V) : Skeleton.bot ⊑ₛ o :=
  fun _ => trivial

/-- A shaped term realizes a skeleton when every point's observation holds.
As before, this is simultaneously "completes the observation" and "matches
the pattern". -/
def Realizes (t : Term V) (s : Skeleton V) : Prop :=
  ∀ p, Obs.Holds (t p) (s p)

theorem Realizes.anti {t : Term V} {s s' : Skeleton V}
    (hle : s ⊑ₛ s') (h : Realizes t s') : Realizes t s :=
  fun p => Obs.holds_anti (hle p) (h p)

variable [DecidableEq V]

/-- Skeleton-level conflict: some point's table row fires. -/
def Conflicts (o s : Skeleton V) : Prop :=
  ∃ p, Obs.conflictB (o p) (s p) = true

/-- **Exactness with absence** (flat-shaped model): joint realizability is
exactly pointwise table-compatibility. -/
theorem realizes_iff_not_conflicts (o pat : Skeleton V) :
    (∃ t, Realizes t o ∧ Realizes t pat) ↔ ¬ Conflicts o pat := by
  constructor
  · rintro ⟨t, hto, htp⟩ ⟨p, hp⟩
    exact Obs.conflictB_sound hp (hto p) (htp p)
  · intro hnc
    refine ⟨fun p => Obs.witness (o p) (pat p), fun p => ?_, fun p => ?_⟩ <;>
    · have hcompat : Obs.conflictB (o p) (pat p) = false := by
        rw [← Bool.not_eq_true]
        exact fun h => hnc ⟨p, h⟩
      first
        | exact (Obs.holds_witness hcompat).1
        | exact (Obs.holds_witness hcompat).2

/-- One sampled position votes to refute via the table. -/
def posConflict (o s : Skeleton V) (p : Path) : Bool :=
  Obs.conflictB (o p) (s p)

/-- Refute on a finite sample list of positions. -/
def conflictsOn (ps : List Path) (o s : Skeleton V) : Bool :=
  ps.any (posConflict o s)

theorem conflictsOn_sound {ps : List Path} {o s : Skeleton V}
    (h : conflictsOn ps o s = true) : Conflicts o s := by
  obtain ⟨p, _, hp⟩ := List.any_eq_true.mp h
  exact ⟨p, hp⟩

/-- Refutations persist as information grows. -/
theorem conflictsOn_mono_obs {ps : List Path} {o o' s : Skeleton V}
    (hle : o ⊑ₛ o') (h : conflictsOn ps o s = true) :
    conflictsOn ps o' s = true := by
  obtain ⟨p, hmem, hp⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨p, hmem, Obs.conflictB_mono_left (hle p) hp⟩

/-- More samples can only find more conflicts. -/
theorem conflictsOn_mono_samples {ps ps' : List Path} {o s : Skeleton V}
    (hsub : ∀ p, p ∈ ps → p ∈ ps') (h : conflictsOn ps o s = true) :
    conflictsOn ps' o s = true := by
  obtain ⟨p, hmem, hp⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨p, hsub p hmem, hp⟩

/-- A candidate occurrence with a shaped pattern. -/
structure Candidate (V : Type*) where
  id : Nat
  pat : Skeleton V

/-- The decision: keep, in source order with multiplicity, every candidate
the samples cannot refute. -/
def candidates (ps : List Path) (o : Skeleton V)
    (source : List (Candidate V)) : List (Candidate V) :=
  source.filter fun c => !(conflictsOn ps o c.pat)

theorem candidates_sublist (ps : List Path) (o : Skeleton V)
    (source : List (Candidate V)) :
    (candidates ps o source).Sublist source :=
  List.filter_sublist

/-- Completeness: any candidate jointly realizable with the observation
survives every sample set. -/
theorem mem_candidates_of_realizes {ps : List Path} {o : Skeleton V}
    {source : List (Candidate V)} {c : Candidate V} {t : Term V}
    (hmem : c ∈ source) (hto : Realizes t o) (htp : Realizes t c.pat) :
    c ∈ candidates ps o source := by
  refine List.mem_filter.mpr ⟨hmem, ?_⟩
  by_contra h
  simp only [Bool.not_eq_true, Bool.not_eq_false'] at h
  obtain ⟨p, hp⟩ := conflictsOn_sound h
  exact Obs.conflictB_sound hp (hto p) (htp p)

/-- Availability monotonicity, now with absence in the observation
alphabet. -/
theorem candidates_antitone_obs {ps : List Path} {o o' : Skeleton V}
    (hle : o ⊑ₛ o') (source : List (Candidate V)) :
    (candidates ps o' source).Sublist (candidates ps o source) := by
  apply List.monotone_filter_right
  intro c hc
  simp only [Bool.not_eq_true'] at hc ⊢
  by_contra h
  simp only [Bool.not_eq_false] at h
  exact absurd (conflictsOn_mono_obs hle h) (by simp [hc])

theorem candidates_antitone_samples {ps ps' : List Path} {o : Skeleton V}
    (hsub : ∀ p, p ∈ ps → p ∈ ps') (source : List (Candidate V)) :
    (candidates ps' o source).Sublist (candidates ps o source) := by
  apply List.monotone_filter_right
  intro c hc
  simp only [Bool.not_eq_true'] at hc ⊢
  by_contra h
  simp only [Bool.not_eq_false] at h
  exact absurd (conflictsOn_mono_samples hsub h) (by simp [hc])

theorem candidates_nil_samples (o : Skeleton V)
    (source : List (Candidate V)) : candidates [] o source = source := by
  simp [candidates, conflictsOn]

theorem candidates_bot (ps : List Path) (source : List (Candidate V)) :
    candidates ps Skeleton.bot source = source := by
  have hfalse : ∀ c : Candidate V,
      conflictsOn ps Skeleton.bot c.pat = false := by
    intro c
    rw [← Bool.not_eq_true]
    intro h
    obtain ⟨p, hp⟩ := conflictsOn_sound h
    simp [Skeleton.bot, Obs.conflictB_unknown_left] at hp
  simp [candidates, hfalse]

theorem candidates_candidates (ps ps' : List Path) (o : Skeleton V)
    (source : List (Candidate V)) :
    candidates ps' o (candidates ps o source) =
      candidates (ps ++ ps') o source := by
  simp [candidates, List.filter_filter, conflictsOn, List.any_append,
    Bool.not_or, Bool.and_comm]

theorem candidates_prefix_mono {source source' : List (Candidate V)}
    (ps : List Path) (o : Skeleton V) (h : source <+: source') :
    (candidates ps o source) <+: (candidates ps o source') := by
  obtain ⟨rest, rfl⟩ := h
  exact ⟨candidates ps o rest, by simp [candidates, List.filter_append]⟩

/-- The repeated-variable refuter over shaped observations is the table
applied to the two points — strictly stronger than the two-valued version:
it also fires on a shape difference (`present` vs `absent`). -/
def eqRefutes (p q : Path) (o : Skeleton V) : Bool :=
  Obs.conflictB (o p) (o q)

theorem eqRefutes_sound {p q : Path} {o : Skeleton V} {t : Term V}
    (h : eqRefutes p q o = true) (hto : Realizes t o) : t p ≠ t q := by
  intro heq
  have h2 : Obs.Holds (t p) (o q) := by
    rw [heq]
    exact hto q
  exact Obs.conflictB_sound h (hto p) h2

theorem eqRefutes_unknown_left {p q : Path} {o : Skeleton V}
    (h : o p = Obs.unknown) : eqRefutes p q o = false := by
  simp [eqRefutes, h, Obs.conflictB_unknown_left]

theorem eqRefutes_unknown_right {p q : Path} {o : Skeleton V}
    (h : o q = Obs.unknown) : eqRefutes p q o = false := by
  simp [eqRefutes, h, Obs.conflictB_unknown_right]

theorem eqRefutes_mono {p q : Path} {o o' : Skeleton V} (hle : o ⊑ₛ o')
    (h : eqRefutes p q o = true) : eqRefutes p q o' = true :=
  Obs.conflictB_mono_right (hle q) (Obs.conflictB_mono_left (hle p) h)

/-! ### Coherence: deriving the absences a term's arity discipline entails -/

/-- Arity discipline for shaped terms: a present child needs a present
parent with sufficient arity.  This one direction already yields downward
absence propagation and the beyond-arity absences. -/
def Coherent (ar : V → Nat) (t : Term V) : Prop :=
  ∀ p i, t (p ++ [i]) ≠ none → ∃ v, t p = some v ∧ i < ar v

omit [DecidableEq V] in
/-- Absence propagates to all descendants. -/
theorem Coherent.absent_extend {ar : V → Nat} {t : Term V}
    (hco : Coherent ar t) :
    ∀ (r p : Path), t p = none → t (p ++ r) = none := by
  intro r
  induction r with
  | nil =>
    intro p h
    simpa using h
  | cons i r ih =>
    intro p h
    have hchild : t (p ++ [i]) = none := by
      by_contra hne
      obtain ⟨v, hv, _⟩ := hco p i hne
      simp [h] at hv
    have hrec := ih (p ++ [i]) hchild
    simpa [List.append_assoc] using hrec

omit [DecidableEq V] in
/-- Children at or beyond a node's arity are absent. -/
theorem Coherent.absent_of_arity {ar : V → Nat} {t : Term V}
    (hco : Coherent ar t) {p : Path} {v : V} (hv : t p = some v) {i : Nat}
    (hi : ar v ≤ i) : t (p ++ [i]) = none := by
  by_contra hne
  obtain ⟨w, hw, hlt⟩ := hco p i hne
  rw [hv] at hw
  injection hw with hvw
  subst hvw
  omega

/-- One prefix step forces absence: the prefix is observed absent, or
observed present with the next child index at or beyond its arity. -/
def stepForcesAbsent (ar : V → Nat) : Obs V → Option Nat → Bool
  | Obs.absent, _ => true
  | Obs.present v, some i => decide (ar v ≤ i)
  | _, _ => false

omit [DecidableEq V] in
theorem stepForcesAbsent_eq_true_iff {ar : V → Nat} {ov : Obs V}
    {oi : Option Nat} :
    stepForcesAbsent ar ov oi = true ↔
      ov = Obs.absent ∨
        ∃ v i, ov = Obs.present v ∧ oi = some i ∧ ar v ≤ i := by
  cases ov <;> cases oi <;> simp [stepForcesAbsent]

/-- Does some proper prefix of `q` force `q` to be absent? -/
def entailedAbsent (ar : V → Nat) (o : Skeleton V) (q : Path) : Bool :=
  (List.range q.length).any fun k =>
    stepForcesAbsent ar (o (q.take k)) q[k]?

/-- Fill in the entailed absences.  Only `unknown` points are refined, so
saturation is extensive by construction.  (It is deliberately *not* claimed
monotone or idempotent on incoherent observations.) -/
def saturate (ar : V → Nat) (o : Skeleton V) : Skeleton V := fun q =>
  match o q, entailedAbsent ar o q with
  | Obs.unknown, true => Obs.absent
  | x, _ => x

omit [DecidableEq V] in
theorem le_saturate (ar : V → Nat) (o : Skeleton V) : o ⊑ₛ saturate ar o := by
  intro p
  unfold saturate
  cases h : o p <;> cases hb : entailedAbsent ar o p <;> simp [Obs.le]

omit [DecidableEq V] in
/-- Saturation soundness: a coherent term realizing an observation also
realizes its saturation — the derived absences are true of it. -/
theorem saturate_sound {ar : V → Nat} {t : Term V} {o : Skeleton V}
    (hco : Coherent ar t) (hre : Realizes t o) :
    Realizes t (saturate ar o) := by
  intro q
  unfold saturate
  cases hoq : o q with
  | absent =>
    have hh := hre q
    rw [hoq] at hh
    simpa using hh
  | present v =>
    have hh := hre q
    rw [hoq] at hh
    simpa using hh
  | unknown =>
    cases hent : entailedAbsent ar o q with
    | false => simp [Obs.Holds]
    | true =>
      have hqnone : t q = none := by
        obtain ⟨k, hkmem, hk⟩ := List.any_eq_true.mp hent
        rcases stepForcesAbsent_eq_true_iff.mp hk with
          hab | ⟨v, i, hpres, hidx, har⟩
        · have hnone : t (q.take k) = none := by
            have hh := hre (q.take k)
            rw [hab] at hh
            cases htk : t (q.take k) with
            | none => rfl
            | some w =>
              rw [htk] at hh
              simp [Obs.Holds] at hh
          have hext := hco.absent_extend (q.drop k) (q.take k) hnone
          rwa [List.take_append_drop] at hext
        · have hsome : t (q.take k) = some v := by
            have hh := hre (q.take k)
            rw [hpres] at hh
            cases htk : t (q.take k) with
            | none =>
              rw [htk] at hh
              simp [Obs.Holds] at hh
            | some w =>
              rw [htk] at hh
              simp only [Obs.Holds] at hh
              rw [hh]
          have hstep : t (q.take k ++ [i]) = none :=
            hco.absent_of_arity hsome har
          have htake : q.take (k + 1) = q.take k ++ [i] := by
            rw [List.take_add_one, hidx]
            rfl
          have hext :=
            hco.absent_extend (q.drop (k + 1)) (q.take k ++ [i]) hstep
          rw [← htake, List.take_append_drop] at hext
          exact hext
      simp [Obs.Holds, hqnone]

/-- Saturation only prunes: the derived absences are extra information. -/
theorem candidates_saturate_sublist (ar : V → Nat) (ps : List Path)
    (o : Skeleton V) (source : List (Candidate V)) :
    (candidates ps (saturate ar o) source).Sublist
      (candidates ps o source) :=
  candidates_antitone_obs (le_saturate ar o) source

/-- Completeness survives saturation for coherent terms: no coherently
realizable candidate is ever pruned by the derived absences.  This is
fingerprint-`N` behaviour, derived rather than assumed. -/
theorem mem_candidates_saturate_of_coherent {ar : V → Nat} {ps : List Path}
    {o : Skeleton V} {source : List (Candidate V)} {c : Candidate V}
    {t : Term V} (hco : Coherent ar t) (hmem : c ∈ source)
    (hto : Realizes t o) (htp : Realizes t c.pat) :
    c ∈ candidates ps (saturate ar o) source :=
  mem_candidates_of_realizes hmem (saturate_sound hco hto) htp

/-! ### Examples

Positive and negative instances, including the derived-absence pruning that
the two-valued layer cannot express. -/

section Examples

/-- Arities for the example tags: `A` nullary, `B` binary. -/
private def arTag : Tag → Nat
  | Tag.A => 0
  | Tag.B => 2

/-- Root observed as the nullary `A`; nothing else observed. -/
private def obsRootA : Skeleton Tag := fun p =>
  if p = [] then Obs.present Tag.A else Obs.unknown

/-- A pattern requiring a present child under the root. -/
private def patChild : Skeleton Tag := fun p =>
  if p = [0] then Obs.present Tag.B else Obs.unknown

/-- Positive: `A` is nullary, so position `[0]` is entailed absent. -/
example : entailedAbsent arTag obsRootA [0] = true := by rfl

/-- Positive: after saturation the child-requiring pattern is refuted —
pruning the two-valued layer could never justify. -/
example : conflictsOn [[0]] (saturate arTag obsRootA) patChild = true := by
  rfl

/-- Negative: without saturation the same pattern cannot be refuted; the
root observation says nothing at `[0]` pointwise. -/
example : conflictsOn [[0]] obsRootA patChild = false := by rfl

/-- Positive: shape difference refutes. -/
example :
    Obs.conflictB (Obs.absent : Obs Tag) (Obs.present Tag.A) = true := rfl

/-- Negative: two absences are compatible. -/
example : Obs.conflictB (Obs.absent : Obs Tag) Obs.absent = false := rfl

/-- Positive: absence satisfies an absent observation. -/
example : Obs.Holds (none : Option Tag) Obs.absent := trivial

/-- Negative: a present point violates an absent observation. -/
example : ¬ Obs.Holds (some Tag.A) Obs.absent := fun h => h

/-- Positive: the eq-refuter fires on shape difference between the two
positions. -/
example :
    eqRefutes [0] [1]
      (fun p => if p = [0] then Obs.absent else
        if p = [1] then Obs.present Tag.A else Obs.unknown) = true := by rfl

/-- Negative: with one side unknown the eq-refuter stays silent. -/
example :
    eqRefutes [0] [1]
      (fun p => if p = [0] then (Obs.absent : Obs Tag) else Obs.unknown) =
      false := by rfl

end Examples

end Shaped

/-! ### Exact-key compiled-artifact repositories

Candidate selection is normally invoked many times while an evaluation tree
remains pinned to one source revision and one semantic authority.  Compilation
may be shared across those invocations only when every input on which the
compiled decision depends is identical.  The key below deliberately includes
the ordered equation occurrences: changing order or multiplicity changes the
key even when the underlying set of equations is unchanged.

The small theorem in this section states the precise optimality available at
this abstraction layer.  Among repositories that retain one artifact for each
exact semantic key they cover, compiling the finite set of requested keys is
cardinality-minimal.  This is a compilation-count theorem, not a claim about
minimum bytes, latency, or machine instructions.
-/

section ArtifactRepository

/-- Every authority on which a compiled match decision depends.  Equation
occurrences are a list rather than a set so authored order and duplicates
remain observable parts of the key. -/
structure ArtifactKey
    (Revision Semantics Mode Head Equation : Type*) where
  revision : Revision
  semantics : Semantics
  mode : Mode
  head : Head
  arity : Nat
  orderedEquations : List Equation
deriving DecidableEq

variable {Key : Type*} [DecidableEq Key]

/-- The distinct exact keys demanded by a finite execution trace. -/
def requiredArtifacts (requests : List Key) : Finset Key :=
  requests.toFinset

/-- A repository covers a trace when it contains an artifact for every exact
key requested by that trace. -/
def RepositoryCovers (requests : List Key) (repository : Finset Key) : Prop :=
  requiredArtifacts requests ⊆ repository

/-- Compiling once per distinct exact key. -/
def compileOnceCost (requests : List Key) : Nat :=
  (requiredArtifacts requests).card

/-- The canonical exact-key repository covers every request. -/
theorem requiredArtifacts_covers (requests : List Key) :
    RepositoryCovers requests (requiredArtifacts requests) :=
  Finset.Subset.rfl

/-- Any exact-key repository covering the trace has at least as many entries
as there are distinct requested keys. -/
theorem repository_compile_lower_bound
    (requests : List Key) (repository : Finset Key)
    (h : RepositoryCovers requests repository) :
    compileOnceCost requests ≤ repository.card := by
  exact Finset.card_le_card h

/-- Hence the compile-once repository attains the exact-key cardinality lower
bound. -/
theorem requiredArtifacts_cardinality_minimal
    (requests : List Key) (repository : Finset Key)
    (h : RepositoryCovers requests repository) :
    (requiredArtifacts requests).card ≤ repository.card :=
  repository_compile_lower_bound requests repository h

private abbrev ExampleArtifactKey :=
  ArtifactKey Nat Bool Nat Nat Nat

private def artifactA : ExampleArtifactKey :=
  { revision := 7
    semantics := true
    mode := 2
    head := 11
    arity := 2
    orderedEquations := [20, 21, 20] }

private def artifactDifferentRevision : ExampleArtifactKey :=
  { artifactA with revision := 8 }

private def artifactDifferentOrder : ExampleArtifactKey :=
  { artifactA with orderedEquations := [20, 20, 21] }

/-- Positive: repeated requests for one exact key require one compilation. -/
example : compileOnceCost [artifactA, artifactA, artifactA] = 1 := by decide

/-- Negative: a revision change is a genuinely different artifact key. -/
example : compileOnceCost [artifactA, artifactDifferentRevision] = 2 := by
  decide

/-- Negative: authored equation order is not quotiented away. -/
example : compileOnceCost [artifactA, artifactDifferentOrder] = 2 := by decide

end ArtifactRepository

end Mettapedia.GSLT.LanguageDef.MatchDecisionContract
