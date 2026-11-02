import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceSemantics

/-!
# The step of the guarded rewriting calculus: the two-line law

A configuration is a bag of values (`Multiset T`). A **rule** gathers values (some it takes, some
it only reads), checks the state, and produces values. Values are compared by the declared theory
`E` of a term layer (`Sources.TermLayer`): a pattern `p` matches a value `t` under `σ` when
`pσ =_E t` (`TermLayer.Solves`). **The step** is

```
S ⊎ σT ⊎ σR  →  S ⊎ σR ⊎ σP
  if σ matches the take patterns T to distinct values σT, and the read patterns R to values of
  σR, and every check σC holds in the state before the step
```

(`Step`). What is taken is distinct copies, apart from what is read. What is read, σR, counts
each read value once: several read patterns may read one value (`Reads`). Reading consumes
nothing, so a value read twice is a value read once. The interaction semantics agrees (its
`Enabled` keeps a set of read occurrences, kept apart only from what is taken), and Datalog needs
it: `path(x, z) :- edge(x, y), edge(y, z)` over the loop `edge(a, a)` derives `path(a, a)` by
reading one edge twice (`Examples.shared_read_steps`). A take and a read never share a value
(`Examples.take_read_no_share`).

A **check** has a pattern and a condition on the bag of the values its pattern matches under `σ`
(`Check`): absence (`Check.absent`), a count (`Check.count`), or a fold of all the matches,
itself matched by a pattern (`Check.all`).

Example: the rule `take (ping $x), check absent (busy), produce (pong $x)` steps
`{ping 1, idle} → {pong 1, idle}` and does nothing at `{ping 1, busy}` (`Examples`).

## One substitution, or one per source

A transform's sources bind their variables one after another (`TermLayer.Step`). The two-line law
uses one substitution. `stepChain_iff` says they agree: a chain of per-pattern steps from the empty
substitution ends exactly at the substitutions that solve every pattern and bind nothing else.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uO uV uT uP

variable {V : Type uV} {T : Type uT} {P : Type uP}

/-! ## Rules and the step -/

/-- **A check**: a pattern, and a condition on the bag of the values it matches in the state
before the step. -/
structure Check (V : Type uV) (T : Type uT) (P : Type uP) where
  pattern : P
  holds : Subst V T → Multiset T → Prop

/-- **A rule**: what it takes, what it reads, what it checks, what it produces. -/
structure Rule (V : Type uV) (T : Type uT) (P : Type uP) where
  take : List P
  read : List P
  checks : List (Check V T P)
  produce : List P

namespace Check

/-- Nothing matches. -/
def absent (p : P) : Check V T P := ⟨p, fun _ bag => bag = 0⟩

/-- Exactly `n` values match. -/
def count (p : P) (n : ℕ) : Check V T P := ⟨p, fun _ bag => Multiset.card bag = n⟩

/-- All the matches, folded into one value, match `coll`. -/
def all (L : TermLayer V T P) (p coll : P) (fold : Multiset T → T) : Check V T P :=
  ⟨p, fun σ bag => L.Solves σ coll (fold bag)⟩

end Check

/-- The values of a bag that the pattern matches under `σ` (its matches). -/
noncomputable def matchesIn (L : TermLayer V T P) (σ : Subst V T) (p : P) (M : Multiset T) :
    Multiset T :=
  M.filter fun t => semRegion L σ p t = true

theorem mem_matchesIn {L : TermLayer V T P} {σ : Subst V T} {p : P} {M : Multiset T} {t : T} :
    t ∈ matchesIn L σ p M ↔ t ∈ M ∧ L.Covers σ p t := by
  simp [matchesIn, semRegion_eq_true]

/-- `σ` matches the patterns, position by position, to values forming the bag. -/
def Matches (L : TermLayer V T P) (σ : Subst V T) (ps : List P) (bag : Multiset T) : Prop :=
  ∃ ts : List T, List.Forall₂ (L.Solves σ) ps ts ∧ (ts : Multiset T) = bag

/-- **`σ` reads the patterns from the bag `kept`**: each read pattern matches a value of `kept`,
several patterns may read one value, and every value of `kept` is read. `kept` counts each read
value once: it is at most the list of values read, and holds each of them. -/
def Reads (L : TermLayer V T P) (σ : Subst V T) (ps : List P) (kept : Multiset T) : Prop :=
  ∃ ts : List T, List.Forall₂ (L.Solves σ) ps ts ∧ kept ≤ (ts : Multiset T) ∧ ∀ t ∈ ts, t ∈ kept

/-- `σ` binds nothing but the variables of the gather patterns. -/
def BindsOnlyGathers (L : TermLayer V T P) (r : Rule V T P) (σ : Subst V T) : Prop :=
  ∀ v, (∀ p ∈ r.take ++ r.read, v ∉ L.vars p) → σ v = none

/-- **The step (two-line law).** -/
def Step (L : TermLayer V T P) (r : Rule V T P) (M M' : Multiset T) : Prop :=
  ∃ (σ : Subst V T) (S taken kept : Multiset T) (made : List T),
    BindsOnlyGathers L r σ ∧ Matches L σ r.take taken ∧ Reads L σ r.read kept ∧
      M = S + taken + kept ∧ (∀ c ∈ r.checks, c.holds σ (matchesIn L σ c.pattern M)) ∧
      instTemplate L σ r.produce = some made ∧ M' = S + kept + made

/-- **Data stays data**: what a step adds is the instances of the rule's templates, nothing else. -/
theorem Step.made_are_instances {L : TermLayer V T P} {r : Rule V T P} {M M' : Multiset T}
    (step : Step L r M M') :
    ∃ (σ : Subst V T) (S kept : Multiset T) (made : List T),
      instTemplate L σ r.produce = some made ∧ M' = S + kept + made ∧ S + kept ≤ M := by
  obtain ⟨σ, S, taken, kept, made, -, -, -, hM, -, hmade, hM'⟩ := step
  refine ⟨σ, S, kept, made, hmade, hM', ?_⟩
  rw [hM, add_right_comm]
  exact Multiset.le_add_right _ _

/-- What a step reads stays: the read values are in the state after the step. -/
theorem Step.kept_stays {L : TermLayer V T P} {r : Rule V T P} {M M' : Multiset T}
    (step : Step L r M M') : ∃ (σ : Subst V T) (kept : Multiset T), Reads L σ r.read kept ∧
      kept ≤ M ∧ kept ≤ M' := by
  obtain ⟨σ, S, taken, kept, made, -, -, hk, hM, -, -, hM'⟩ := step
  refine ⟨σ, kept, hk, ?_, ?_⟩
  · rw [hM]; exact Multiset.le_add_left _ _
  · rw [hM', add_assoc]; exact (Multiset.le_add_right _ _).trans (by
      rw [add_comm S]; exact le_of_eq (by rw [add_assoc]))

/-! ## Parked rules: `whenever` -/

/-- **`whenever r`**: the rule is a value `rt` in the configuration; each step of it reads `rt`,
so the rule stays parked. -/
def Rule.whenever (ruleValue : P) (r : Rule V T P) : Rule V T P :=
  { r with read := ruleValue :: r.read }

/-- **`once r`**: the rule is consumed by its step. -/
def Rule.once (ruleValue : P) (r : Rule V T P) : Rule V T P :=
  { r with take := ruleValue :: r.take }

/-- **A `whenever` rule stays parked**: its value is read by the step, so it is still there after. -/
theorem whenever_stays {L : TermLayer V T P} {r : Rule V T P} {rt : P} {M M' : Multiset T}
    (step : Step L (r.whenever rt) M M') :
    ∃ (σ : Subst V T) (t : T), L.Solves σ rt t ∧ t ∈ M ∧ t ∈ M' := by
  obtain ⟨σ, S, taken, kept, made, -, -, ⟨ts, hts, -, support⟩, hM, -, -, hM'⟩ := step
  match ts, hts, support with
  | t :: _, .cons head _, support =>
      have inKept : t ∈ kept := support t (by simp)
      refine ⟨σ, t, head, ?_, ?_⟩
      · rw [hM]; exact Multiset.mem_add.mpr (Or.inr inKept)
      · rw [hM']; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr inKept)))

/-! ## One substitution or a chain of per-pattern steps -/

/-- A chain of per-pattern steps (`TermLayer.Step`), as a transform's sources bind. -/
inductive StepChain (L : TermLayer V T P) : Subst V T → List P → List T → Subst V T → Prop
  | nil (σ : Subst V T) : StepChain L σ [] [] σ
  | cons {σ τ υ : Subst V T} {p : P} {t : T} {ps : List P} {ts : List T} :
      L.Step σ p t τ → StepChain L τ ps ts υ → StepChain L σ (p :: ps) (t :: ts) υ

theorem solves_of_extends {L : TermLayer V T P} {σ τ : Subst V T} {p : P} {t : T}
    (solves : L.Solves σ p t) (grow : Extends σ τ) : L.Solves τ p t := by
  obtain ⟨u, hu, e⟩ := solves
  refine ⟨u, ?_, e⟩
  rw [← hu]
  refine L.inst_local τ σ p fun v mem => ?_
  have bound : (σ v).isSome := L.inst_bound σ p (by rw [hu]; rfl) v mem
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp bound
  rw [ha, grow v a ha]

/-- **A chain is one substitution.** From `σ`, a chain over the patterns ends at `υ` exactly when
`υ` extends `σ`, changes nothing outside the patterns' variables, and solves every pattern by its
value. -/
theorem stepChain_iff [DecidableEq V] (L : TermLayer V T P) :
    ∀ (ps : List P) (ts : List T) (σ υ : Subst V T),
      StepChain L σ ps ts υ ↔
        Extends σ υ ∧ (∀ v, (∀ p ∈ ps, v ∉ L.vars p) → υ v = σ v) ∧ List.Forall₂ (L.Solves υ) ps ts
  | [], ts, σ, υ => by
      constructor
      · rintro ⟨⟩; exact ⟨Extends.refl σ, fun _ _ => rfl, .nil⟩
      · rintro ⟨_, same, rel⟩
        cases rel
        have : υ = σ := funext fun v => same v (by simp)
        subst this
        exact .nil _
  | p :: ps, ts, σ, υ => by
      constructor
      · intro chain
        cases chain with
        | cons step rest =>
            rename_i τ t ts'
            obtain ⟨grow, same, rel⟩ := (stepChain_iff L ps ts' τ υ).mp rest
            refine ⟨step.extends_.trans grow, fun v notIn => ?_, .cons ?_ rel⟩
            · rw [same v (fun q mem => notIn q (by simp [mem])),
                step.only v (notIn p (by simp))]
            · exact solves_of_extends step.solves grow
      · rintro ⟨grow, same, rel⟩
        cases rel with
        | cons head tail =>
            rename_i t ts'
            let τ : Subst V T := L.onVars p σ υ
            have stepP : L.Step σ p t τ := by
              refine ⟨fun v a h => ?_, fun v notIn => ?_, ?_⟩
              · simp only [τ, TermLayer.onVars]
                split_ifs
                · exact grow v a h
                · exact h
              · simp [τ, TermLayer.onVars, notIn]
              · obtain ⟨u, hu, e⟩ := head
                refine ⟨u, ?_, e⟩
                rw [← hu]
                exact L.inst_local τ υ p fun v mem => by simp [τ, TermLayer.onVars, mem]
            refine .cons stepP ((stepChain_iff L ps ts' τ υ).mpr ⟨?_, ?_, tail⟩)
            · intro v a h
              simp only [τ, TermLayer.onVars] at h
              split_ifs at h
              · exact h
              · exact grow v a h
            · intro v notIn
              simp only [τ, TermLayer.onVars]
              split_ifs with mem
              · rfl
              · exact same v (fun q qmem => by
                  simp only [List.mem_cons] at qmem
                  rcases qmem with rfl | qmem
                  · exact mem
                  · exact notIn q qmem)

/-- From the empty substitution: a chain ends exactly at a substitution that binds only the
patterns' variables and solves each pattern. -/
theorem stepChain_empty_iff [DecidableEq V] (L : TermLayer V T P) (ps : List P) (ts : List T)
    (υ : Subst V T) :
    StepChain L (fun _ => none) ps ts υ ↔
      (∀ v, (∀ p ∈ ps, v ∉ L.vars p) → υ v = none) ∧ List.Forall₂ (L.Solves υ) ps ts := by
  rw [stepChain_iff]
  constructor
  · rintro ⟨_, same, rel⟩; exact ⟨same, rel⟩
  · rintro ⟨same, rel⟩; exact ⟨fun _ _ h => (by simp at h), same, rel⟩

theorem stepChain_append {L : TermLayer V T P} :
    ∀ {σ τ υ : Subst V T} {a b : List P} {ta tb : List T},
      StepChain L σ a ta τ → StepChain L τ b tb υ → StepChain L σ (a ++ b) (ta ++ tb) υ
  | _, _, _, _, _, _, _, .nil _, second => second
  | _, _, _, _, _, _, _, .cons step rest, second => .cons step (stepChain_append rest second)

theorem stepChain_split {L : TermLayer V T P} :
    ∀ {σ υ : Subst V T} {a b : List P} {ta tb : List T}, ta.length = a.length →
      StepChain L σ (a ++ b) (ta ++ tb) υ → ∃ τ, StepChain L σ a ta τ ∧ StepChain L τ b tb υ
  | σ, _, [], _, [], _, _, chain => ⟨σ, .nil σ, chain⟩
  | _, _, [], _, _ :: _, _, len, _ => by simp at len
  | _, _, _ :: _, _, [], _, len, _ => by simp at len
  | _, _, _ :: _, _, _ :: _, _, len, .cons step rest => by
      obtain ⟨τ, first, second⟩ := stepChain_split (by simpa using len) rest
      exact ⟨τ, .cons step first, second⟩

/-! ## The step is the compiled transform's step

A rule whose checks are absences compiles to a transform of the source layer: its takes, its
reads, its absences, then its templates (`Rule.transform`). **Its steps are exactly the transform's
steps**, seen as bags of values:

* `step_of_fires`: every firing of the transform (a `Commit`) steps the bag of the store to the bag
  after firing;
* `fires_of_step`: every step of the bag is the bag after such a firing, up to the declared theory
  on what it makes.

Two reads may pick one occurrence on both sides: the firing keeps the set of occurrences read, and
the step counts each read value once (`Reads`). -/

section Compiled

variable {O : Type uO} [DecidableEq O]

/-- Put sources in front of a source list. -/
def prepend (srcs : List (Source V T P)) (rest : SourceList V T P) : SourceList V T P :=
  srcs.foldr SourceList.cons rest

@[simp] theorem prepend_nil (rest : SourceList V T P) : prepend [] rest = rest := rfl

@[simp] theorem prepend_cons (s : Source V T P) (srcs : List (Source V T P))
    (rest : SourceList V T P) : prepend (s :: srcs) rest = .cons s (prepend srcs rest) := rfl

/-- The sources of a rule whose checks are the absences `absent`. -/
def Rule.sources (r : Rule V T P) (absent : List P) : List (Source V T P) :=
  r.take.map Source.take ++ r.read.map Source.read ++ absent.map Source.absent

/-- **The transform of a rule** whose checks are the absences `absent`. -/
def Rule.transform (r : Rule V T P) (absent : List P) : Transform V T P :=
  ⟨prepend (r.sources absent) .done, r.produce⟩

/-- A chain of declarative steps of sources (`DStep`). -/
inductive SourceChain (L : TermLayer V T P) (label : O → T) (S : Finset O) :
    List (Source V T P) → Subst V T → Subst V T → List (Pick O T) → Prop
  | nil (σ : Subst V T) : SourceChain L label S [] σ σ []
  | cons {s : Source V T P} {srcs : List (Source V T P)} {σ τ υ : Subst V T} {pick : Pick O T}
      {picks : List (Pick O T)} :
      DStep L label S s σ (τ, pick) → SourceChain L label S srcs τ υ picks →
      SourceChain L label S (s :: srcs) σ υ (pick :: picks)

variable {L : TermLayer V T P} {label : O → T} {S : Finset O}

omit [DecidableEq O] in
theorem sourceChain_cons_iff {s : Source V T P} {srcs : List (Source V T P)} {σ υ : Subst V T}
    {picks : List (Pick O T)} :
    SourceChain L label S (s :: srcs) σ υ picks ↔
      ∃ τ pick rest, DStep L label S s σ (τ, pick) ∧ SourceChain L label S srcs τ υ rest ∧
        picks = pick :: rest := by
  constructor
  · intro h
    cases h with
    | cons step chain => exact ⟨_, _, _, step, chain, rfl⟩
  · rintro ⟨τ, pick, rest, step, chain, rfl⟩
    exact .cons step chain

omit [DecidableEq O] in
theorem dRow_prepend (template : List P) :
    ∀ (srcs : List (Source V T P)) (rest : SourceList V T P) (σ : Subst V T)
      (x : Subst V T × List (Pick O T)),
      DRow L label S template (prepend srcs rest) σ x ↔
        ∃ υ picks z, SourceChain L label S srcs σ υ picks ∧ DRow L label S template rest υ z ∧
          x = (z.1, picks ++ z.2)
  | [], rest, σ, x => by
      constructor
      · intro row; exact ⟨σ, [], x, .nil σ, row, by simp⟩
      · rintro ⟨υ, picks, z, chain, row, rfl⟩
        cases chain
        simpa using row
  | s :: srcs, rest, σ, x => by
      rw [prepend_cons]
      constructor
      · rintro ⟨y, z, step, row, rfl⟩
        obtain ⟨υ, picks, w, chain, rowRest, rfl⟩ := (dRow_prepend template srcs rest y.1 z).mp row
        exact ⟨υ, y.2 :: picks, w, .cons step chain, rowRest, rfl⟩
      · rintro ⟨υ, picks, z, chain, row, rfl⟩
        obtain ⟨τ, pick, picks', step, chain', rfl⟩ := sourceChain_cons_iff.mp chain
        exact ⟨(τ, pick), (z.1, picks' ++ z.2), step,
          (dRow_prepend template srcs rest τ _).mpr ⟨υ, picks', z, chain', row, rfl⟩, rfl⟩

omit [DecidableEq O] in
theorem sourceChain_append :
    ∀ (a b : List (Source V T P)) (σ υ : Subst V T) (picks : List (Pick O T)),
      SourceChain L label S (a ++ b) σ υ picks ↔
        ∃ τ p₁ p₂, SourceChain L label S a σ τ p₁ ∧ SourceChain L label S b τ υ p₂ ∧
          picks = p₁ ++ p₂
  | [], b, σ, υ, picks => by
      constructor
      · intro chain; exact ⟨σ, [], picks, .nil σ, chain, rfl⟩
      · rintro ⟨τ, p₁, p₂, first, second, rfl⟩
        cases first
        exact second
  | s :: a, b, σ, υ, picks => by
      rw [List.cons_append, sourceChain_cons_iff]
      constructor
      · rintro ⟨τ, pick, rest, step, chain, rfl⟩
        obtain ⟨τ', p₁, p₂, first, second, rfl⟩ := (sourceChain_append a b τ υ rest).mp chain
        exact ⟨τ', pick :: p₁, p₂, .cons step first, second, rfl⟩
      · rintro ⟨τ', p₁, p₂, first, second, rfl⟩
        obtain ⟨τ, pick, rest, step, chain, rfl⟩ := sourceChain_cons_iff.mp first
        exact ⟨τ, pick, rest ++ p₂, step,
          (sourceChain_append a b τ υ _).mpr ⟨τ', rest, p₂, chain, second, rfl⟩, rfl⟩

omit [DecidableEq O] in
theorem dStep_take_iff {p : P} {σ τ : Subst V T} {pick : Pick O T} :
    DStep L label S (.take p) σ (τ, pick) ↔ ∃ o ∈ S, L.Step σ p (label o) τ ∧ pick = .take o := by
  constructor
  · intro h
    cases h with
    | take inS step => exact ⟨_, inS, step, rfl⟩
  · rintro ⟨o, inS, step, rfl⟩
    exact .take inS step

omit [DecidableEq O] in
theorem dStep_read_iff {p : P} {σ τ : Subst V T} {pick : Pick O T} :
    DStep L label S (.read p) σ (τ, pick) ↔ ∃ o ∈ S, L.Step σ p (label o) τ ∧ pick = .keep o := by
  constructor
  · intro h
    cases h with
    | read inS step => exact ⟨_, inS, step, rfl⟩
  · rintro ⟨o, inS, step, rfl⟩
    exact .read inS step

omit [DecidableEq O] in
theorem dStep_absent_iff {q : P} {σ τ : Subst V T} {pick : Pick O T} :
    DStep L label S (.absent q) σ (τ, pick) ↔
      regionOf label S (semRegion L σ q) = ∅ ∧ τ = σ ∧
        pick = .query ⟨semRegion L σ q, ∅⟩ false := by
  constructor
  · intro h
    cases h with
    | absent empty => exact ⟨empty, rfl, rfl⟩
  · rintro ⟨empty, rfl, rfl⟩
    exact .absent empty

omit [DecidableEq O] in
theorem sourceChain_take_iff :
    ∀ (ps : List P) (σ υ : Subst V T) (picks : List (Pick O T)),
      SourceChain L label S (ps.map Source.take) σ υ picks ↔
        ∃ os : List O, (∀ o ∈ os, o ∈ S) ∧ StepChain L σ ps (os.map label) υ ∧
          picks = os.map Pick.take
  | [], σ, υ, picks => by
      constructor
      · intro chain; cases chain; exact ⟨[], by simp, .nil σ, rfl⟩
      · rintro ⟨os, _, chain, rfl⟩
        cases os with
        | nil => cases chain; exact .nil σ
        | cons o os => cases chain
  | p :: ps, σ, υ, picks => by
      rw [List.map_cons, sourceChain_cons_iff]
      constructor
      · rintro ⟨τ, pick, rest, step, chain, rfl⟩
        obtain ⟨o, inS, stepP, rfl⟩ := dStep_take_iff.mp step
        obtain ⟨os, inS', chain', rfl⟩ := (sourceChain_take_iff ps τ υ rest).mp chain
        exact ⟨o :: os, fun o' m => by rcases List.mem_cons.mp m with rfl | m; exacts [inS, inS' o' m],
          .cons stepP chain', rfl⟩
      · rintro ⟨os, inS, chain, rfl⟩
        cases os with
        | nil => cases chain
        | cons o os =>
            cases chain with
            | cons stepP chain' =>
                exact ⟨_, _, _, dStep_take_iff.mpr ⟨o, inS o (by simp), stepP, rfl⟩,
                  (sourceChain_take_iff ps _ υ _).mpr ⟨os, fun o' m => inS o' (by simp [m]),
                    chain', rfl⟩, rfl⟩

omit [DecidableEq O] in
theorem sourceChain_read_iff :
    ∀ (ps : List P) (σ υ : Subst V T) (picks : List (Pick O T)),
      SourceChain L label S (ps.map Source.read) σ υ picks ↔
        ∃ os : List O, (∀ o ∈ os, o ∈ S) ∧ StepChain L σ ps (os.map label) υ ∧
          picks = os.map Pick.keep
  | [], σ, υ, picks => by
      constructor
      · intro chain; cases chain; exact ⟨[], by simp, .nil σ, rfl⟩
      · rintro ⟨os, _, chain, rfl⟩
        cases os with
        | nil => cases chain; exact .nil σ
        | cons o os => cases chain
  | p :: ps, σ, υ, picks => by
      rw [List.map_cons, sourceChain_cons_iff]
      constructor
      · rintro ⟨τ, pick, rest, step, chain, rfl⟩
        obtain ⟨o, inS, stepP, rfl⟩ := dStep_read_iff.mp step
        obtain ⟨os, inS', chain', rfl⟩ := (sourceChain_read_iff ps τ υ rest).mp chain
        exact ⟨o :: os, fun o' m => by rcases List.mem_cons.mp m with rfl | m; exacts [inS, inS' o' m],
          .cons stepP chain', rfl⟩
      · rintro ⟨os, inS, chain, rfl⟩
        cases os with
        | nil => cases chain
        | cons o os =>
            cases chain with
            | cons stepP chain' =>
                exact ⟨_, _, _, dStep_read_iff.mpr ⟨o, inS o (by simp), stepP, rfl⟩,
                  (sourceChain_read_iff ps _ υ _).mpr ⟨os, fun o' m => inS o' (by simp [m]),
                    chain', rfl⟩, rfl⟩

omit [DecidableEq O] in
theorem sourceChain_absent_iff :
    ∀ (qs : List P) (σ υ : Subst V T) (picks : List (Pick O T)),
      SourceChain L label S (qs.map Source.absent) σ υ picks ↔
        υ = σ ∧ (∀ q ∈ qs, regionOf label S (semRegion L σ q) = ∅) ∧
          picks = qs.map fun q => .query ⟨semRegion L σ q, ∅⟩ false
  | [], σ, υ, picks => by
      constructor
      · intro chain; cases chain; exact ⟨rfl, by simp, rfl⟩
      · rintro ⟨rfl, _, rfl⟩; exact .nil υ
  | q :: qs, σ, υ, picks => by
      rw [List.map_cons, sourceChain_cons_iff]
      constructor
      · rintro ⟨τ, pick, rest, step, chain, rfl⟩
        obtain ⟨empty, rfl, rfl⟩ := dStep_absent_iff.mp step
        obtain ⟨rfl, empties, rfl⟩ := (sourceChain_absent_iff qs τ υ rest).mp chain
        exact ⟨rfl, fun q' m => by rcases List.mem_cons.mp m with rfl | m; exacts [empty, empties q' m],
          rfl⟩
      · rintro ⟨rfl, empties, rfl⟩
        exact ⟨υ, _, _, dStep_absent_iff.mpr ⟨empties q (by simp), rfl, rfl⟩,
          (sourceChain_absent_iff qs υ υ _).mpr ⟨rfl, fun q' m => empties q' (by simp [m]), rfl⟩,
          rfl⟩

omit [DecidableEq O] in
/-- **The declarative rows of a rule's transform**: one substitution binding only the gather
variables, distinct-or-not picks in the store solving the take and read patterns, empty absence
checks, and the instantiated templates. -/
theorem dRow_transform_iff [DecidableEq V] (r : Rule V T P) (absent : List P)
    (y : Subst V T × List (Pick O T)) :
    DRow L label S r.produce (prepend (r.sources absent) .done) (fun _ => none) y ↔
      ∃ (σ : Subst V T) (os₁ os₂ : List O) (made : List T),
        (∀ o ∈ os₁ ++ os₂, o ∈ S) ∧ BindsOnlyGathers L r σ ∧
          List.Forall₂ (L.Solves σ) r.take (os₁.map label) ∧
          List.Forall₂ (L.Solves σ) r.read (os₂.map label) ∧
          (∀ q ∈ absent, regionOf label S (semRegion L σ q) = ∅) ∧
          instTemplate L σ r.produce = some made ∧
          y = (σ, os₁.map Pick.take ++ os₂.map Pick.keep ++
            absent.map (fun q => Pick.query ⟨semRegion L σ q, ∅⟩ false) ++ [.make (made : Multiset T)]) := by
  rw [dRow_prepend]
  constructor
  · rintro ⟨υ, picks, z, chain, ⟨made, inst, rfl⟩, rfl⟩
    obtain ⟨τ₂, p₁₂, p₃, chain₁₂, chain₃, rfl⟩ := (sourceChain_append _ _ _ _ _).mp chain
    obtain ⟨τ₁, p₁, p₂, chain₁, chain₂, rfl⟩ := (sourceChain_append _ _ _ _ _).mp chain₁₂
    obtain ⟨os₁, in₁, steps₁, rfl⟩ := (sourceChain_take_iff _ _ _ _).mp chain₁
    obtain ⟨os₂, in₂, steps₂, rfl⟩ := (sourceChain_read_iff _ _ _ _).mp chain₂
    obtain ⟨rfl, empties, rfl⟩ := (sourceChain_absent_iff _ _ _ _).mp chain₃
    obtain ⟨-, -, solves₁⟩ := (stepChain_iff L _ _ _ _).mp steps₁
    obtain ⟨grow₂, -, solves₂⟩ := (stepChain_iff L _ _ _ _).mp steps₂
    obtain ⟨only, -⟩ := (stepChain_empty_iff L _ _ _).mp (stepChain_append steps₁ steps₂)
    refine ⟨_, os₁, os₂, made, ?_, only, solves₁.imp fun _ _ h => solves_of_extends h grow₂,
      solves₂, empties, inst, rfl⟩
    intro o mem
    rcases List.mem_append.mp mem with m | m
    exacts [in₁ o m, in₂ o m]
  · rintro ⟨σ, os₁, os₂, made, inS, only, solves₁, solves₂, empties, inst, rfl⟩
    have chain := (stepChain_empty_iff L _ _ σ).mpr ⟨only, List.rel_append solves₁ solves₂⟩
    obtain ⟨τ, steps₁, steps₂⟩ := stepChain_split (by simpa using solves₁.length_eq.symm) chain
    refine ⟨σ, _, (σ, [.make (made : Multiset T)]), ?_, ⟨made, inst, rfl⟩, rfl⟩
    refine (sourceChain_append _ _ _ _ _).mpr ⟨σ, _, _, ?_,
      (sourceChain_absent_iff _ _ _ _).mpr ⟨rfl, empties, rfl⟩, rfl⟩
    refine (sourceChain_append _ _ _ _ _).mpr ⟨τ, _, _, ?_, ?_, rfl⟩
    · exact (sourceChain_take_iff _ _ _ _).mpr ⟨os₁, fun o m => inS o (by simp [m]), steps₁, rfl⟩
    · exact (sourceChain_read_iff _ _ _ _).mpr ⟨os₂, fun o m => inS o (by simp [m]), steps₂, rfl⟩

/-! ### Footprints and bags -/

omit [DecidableEq O] in
theorem footprintOf_append (a b : List (Pick O T)) :
    footprintOf (a ++ b) = footprintOf a + footprintOf b := by
  simp [footprintOf, List.map_append, List.sum_append]

omit [DecidableEq O] in
theorem footprintOf_takes : ∀ os : List O,
    footprintOf (os.map Pick.take : List (Pick O T)) = ⟨(os : Multiset O), 0, 0, 0⟩
  | [] => rfl
  | o :: os => by
      rw [List.map_cons, footprintOf_cons, footprintOf_takes os]
      apply Footprint.ext <;> simp

omit [DecidableEq O] in
theorem footprintOf_keeps : ∀ os : List O,
    footprintOf (os.map Pick.keep : List (Pick O T)) = ⟨0, (os : Multiset O), 0, 0⟩
  | [] => rfl
  | o :: os => by
      rw [List.map_cons, footprintOf_cons, footprintOf_keeps os]
      apply Footprint.ext <;> simp

omit [DecidableEq O] in
theorem footprintOf_queries {X : Type*} (f : X → PredicateQuery O T) : ∀ xs : List X,
    footprintOf (xs.map fun x => Pick.query (f x) false) = ⟨0, 0, ((xs.map f : List _) : Multiset _), 0⟩
  | [] => rfl
  | x :: xs => by
      rw [List.map_cons, footprintOf_cons, footprintOf_queries f xs]
      apply Footprint.ext <;> simp

omit [DecidableEq O] in
/-- The footprint of a row of a rule's transform. -/
theorem footprint_row (os₁ os₂ : List O) {X : Type*} (f : X → PredicateQuery O T) (xs : List X)
    (made : List T) :
    footprintOf (os₁.map Pick.take ++ os₂.map Pick.keep ++ xs.map (fun x => Pick.query (f x) false) ++
        [.make (made : Multiset T)]) =
      ⟨(os₁ : Multiset O), (os₂ : Multiset O), ((xs.map f : List _) : Multiset _), (made : Multiset T)⟩ := by
  rw [footprintOf_append, footprintOf_append, footprintOf_append, footprintOf_takes, footprintOf_keeps,
    footprintOf_queries]
  apply Footprint.ext <;> simp [footprintOf]

theorem labels_toFinset (label : O → T) {os : List O} (nodup : os.Nodup) :
    labels label os.toFinset = ((os.map label : List T) : Multiset T) := by
  simp [labels, List.toFinset_val, nodup.dedup]

omit [DecidableEq O] in
/-- The matches in the bag of a store are the labels of the matching occurrences. -/
theorem matchesIn_labels (σ : Subst V T) (q : P) :
    matchesIn L σ q (labels label S) = labels label (regionOf label S (semRegion L σ q)) := by
  simp only [matchesIn, labels, regionOf, Finset.filter_val, Multiset.filter_map]
  rfl

/-- Distinct occurrences carrying the values of a sub-bag. -/
theorem exists_occurrences (label : O → T) :
    ∀ (ts : List T) (X : Finset O), (ts : Multiset T) ≤ labels label X →
      ∃ os : List O, os.Nodup ∧ (∀ o ∈ os, o ∈ X) ∧ os.map label = ts
  | [], _, _ => ⟨[], List.nodup_nil, by simp, rfl⟩
  | t :: ts, X, le => by
      have mem : t ∈ labels label X := Multiset.mem_of_le le (Multiset.mem_cons_self t ts)
      obtain ⟨o, oX, rfl⟩ := Multiset.mem_map.mp mem
      have split : labels label X = label o ::ₘ labels label (X.erase o) := by
        simp only [labels, Finset.erase_val]
        rw [← Multiset.map_cons, Multiset.cons_erase (Finset.mem_val.mpr oX)]
      rw [split, ← Multiset.cons_coe, Multiset.cons_le_cons_iff] at le
      obtain ⟨os, nodup, inX, rfl⟩ := exists_occurrences label ts (X.erase o) le
      refine ⟨o :: os, List.nodup_cons.mpr ⟨fun m => ?_, nodup⟩, ?_, rfl⟩
      · exact (Finset.mem_erase.mp (inX o m)).1 rfl
      · intro o' m
        rcases List.mem_cons.mp m with rfl | m
        · exact oX
        · exact (Finset.mem_erase.mp (inX o' m)).2

theorem lets_transform (r : Rule V T P) (absent : List P) :
    (r.transform absent).sources.lets = [] := by
  have : ∀ srcs : List (Source V T P), (∀ s ∈ srcs, ∀ p e, s ≠ .letBind p e) →
      (prepend srcs .done).lets = [] := by
    intro srcs none_let
    induction srcs with
    | nil => rfl
    | cons s srcs ih =>
        rw [prepend_cons]
        cases s with
        | letBind p e => exact absurd rfl (none_let _ (by simp) p e)
        | _ => simpa [SourceList.lets] using ih (fun s' m => none_let s' (by simp [m]))
  exact this _ (by intro s hs p e he; subst he; simp [Rule.sources] at hs)

/-- The labels of the occurrences a list names, each once, are at most the list's labels, and hold
each of them: the occurrences a row reads, read as `Reads` does. -/
theorem labels_toFinset_reads (label : O → T) (os : List O) :
    labels label os.toFinset ≤ ((os.map label : List T) : Multiset T) ∧
      ∀ t ∈ os.map label, t ∈ labels label os.toFinset := by
  constructor
  · simp only [labels, List.toFinset_val, Multiset.map_coe]
    exact Multiset.coe_le.mpr ((List.dedup_sublist os).map label).subperm
  · intro t m
    obtain ⟨o, om, rfl⟩ := List.mem_map.mp m
    exact Multiset.mem_map_of_mem label (by simpa using om)

omit [DecidableEq O] in
/-- Occurrences carrying the values of a list, chosen from a set that holds each value. Several
values may be carried by one occurrence. -/
theorem exists_list_of_mem (label : O → T) (X : Finset O) :
    ∀ ts : List T, (∀ t ∈ ts, ∃ o ∈ X, label o = t) →
      ∃ os : List O, (∀ o ∈ os, o ∈ X) ∧ os.map label = ts
  | [], _ => ⟨[], by simp, rfl⟩
  | t :: ts, h => by
      obtain ⟨o, oX, rfl⟩ := h t (by simp)
      obtain ⟨os, inX, rfl⟩ := exists_list_of_mem label X ts (fun t' m => h t' (by simp [m]))
      refine ⟨o :: os, fun o' m => ?_, rfl⟩
      rcases List.mem_cons.mp m with rfl | m
      · exact oX
      · exact inX o' m

/-! ### The theorem -/

/-- **Every firing of a rule's transform is a step of the bags.** Reads that pick one occurrence
twice are read once. -/
theorem step_of_fires [DecidableEq V] [DecidableEq T] {m : Matcher V T P}
    (sound : Matcher.Sound L m) (complete : Matcher.Complete L m) (minimal : Matcher.Minimal L m)
    {r : Rule V T P} {absent : List P} (checks : r.checks = absent.map Check.absent)
    {c : Commit O T} (fires : Fires L m label S (r.transform absent) c) :
    Step L r (labels label S) (labels label (fire S c)) := by
  have enabled := fires.enabled
  obtain ⟨y, row, linear, commit⟩ := declarative_of_fires sound complete minimal
    (fun eval mem => by rw [lets_transform] at mem; cases mem) fires
  obtain ⟨σ, os₁, os₂, made, inS, only, solves₁, solves₂, empties, inst, rfl⟩ :=
    (dRow_transform_iff r absent y).mp row
  rw [footprint_row] at linear commit
  obtain ⟨nodup₁, apart⟩ := linear
  have nodup₁' : os₁.Nodup := by simpa using nodup₁
  have takenEq : c.taken = os₁.toFinset := by rw [commit.taken]; simp
  have disj : Disjoint os₁.toFinset os₂.toFinset :=
    Finset.disjoint_left.mpr fun o m₁ m₂ => apart o (by simpa using m₁) (by simpa using m₂)
  have sub : os₁.toFinset ∪ os₂.toFinset ⊆ S := by
    intro o m
    rcases Finset.mem_union.mp m with m | m <;> exact inS o (by simp_all)
  have whole : labels label S = labels label (S \ (os₁.toFinset ∪ os₂.toFinset)) +
      ((os₁.map label : List T) : Multiset T) + labels label os₂.toFinset := by
    rw [add_assoc, ← labels_toFinset label nodup₁', ← labels_union_of_disjoint label disj,
      ← labels_union_of_disjoint label Finset.sdiff_disjoint, Finset.sdiff_union_of_subset sub]
  obtain ⟨keptLe, support⟩ := labels_toFinset_reads label os₂
  refine ⟨σ, labels label (S \ (os₁.toFinset ∪ os₂.toFinset)), (os₁.map label : List T),
    labels label os₂.toFinset, made, only, ⟨_, solves₁, rfl⟩, ⟨_, solves₂, keptLe, support⟩, whole,
    ?_, inst, ?_⟩
  · intro ch mem
    rw [checks] at mem
    obtain ⟨q, qmem, rfl⟩ := List.mem_map.mp mem
    show matchesIn L σ q (labels label S) = 0
    rw [matchesIn_labels, empties q qmem]
    rfl
  · rw [labels_fire enabled, takenEq, commit.made, labels_toFinset label nodup₁', whole]
    rw [add_right_comm, add_tsub_cancel_right]

/-- **Every step of the bags is the bag after a firing of the rule's transform**, up to the declared
theory on what it makes, given fresh occurrences of every value. -/
theorem fires_of_step [DecidableEq V] [DecidableEq T] {m : Matcher V T P}
    (sound : Matcher.Sound L m) (complete : Matcher.Complete L m) (minimal : Matcher.Minimal L m)
    (supply : ∀ (X : Finset O) (t : T), ∃ o, o ∉ X ∧ label o = t)
    {r : Rule V T P} {absent : List P} (checks : r.checks = absent.map Check.absent)
    {M' : Multiset T} (step : Step L r (labels label S) M') :
    ∃ c, Fires L m label S (r.transform absent) c ∧
      Multiset.Rel L.E (labels label (fire S c)) M' := by
  obtain ⟨σ, rest, _, kept, made, only, ⟨ts₁, solves₁, rfl⟩, ⟨ts₂, solves₂, -, support⟩, hM, holds,
    inst, rfl⟩ := step
  have le₁ : ((ts₁ : List T) : Multiset T) ≤ labels label S := by
    rw [hM]; exact (Multiset.le_add_left _ _).trans (Multiset.le_add_right _ _)
  obtain ⟨os₁, nodup₁, inS₁, rfl⟩ := exists_occurrences label ts₁ S le₁
  have sub₁ : os₁.toFinset ⊆ S := fun o m => inS₁ o (by simpa using m)
  have restEq : labels label (S \ os₁.toFinset) = rest + kept := by
    have split : labels label S = labels label (S \ os₁.toFinset) + labels label os₁.toFinset := by
      rw [← labels_union_of_disjoint label Finset.sdiff_disjoint, Finset.sdiff_union_of_subset sub₁]
    rw [labels_toFinset label nodup₁, hM, add_right_comm] at split
    exact (add_right_cancel split).symm
  obtain ⟨os₂, inX₂, rfl⟩ := exists_list_of_mem label (S \ os₁.toFinset) ts₂ (fun t m => by
    have tin : t ∈ labels label (S \ os₁.toFinset) := by
      rw [restEq]; exact Multiset.mem_add.mpr (Or.inr (support t m))
    obtain ⟨o, om, rfl⟩ := Multiset.mem_map.mp tin
    exact ⟨o, Finset.mem_val.mp om, rfl⟩)
  have empties : ∀ q ∈ absent, regionOf label S (semRegion L σ q) = ∅ := by
    intro q qmem
    have h := holds (Check.absent q) (by rw [checks]; exact List.mem_map_of_mem qmem)
    change matchesIn L σ q (labels label S) = 0 at h
    rw [matchesIn_labels] at h
    simpa [labels] using h
  have inS : ∀ o ∈ os₁ ++ os₂, o ∈ S := by
    intro o m
    rcases List.mem_append.mp m with m | m
    · exact inS₁ o m
    · exact (Finset.mem_sdiff.mp (inX₂ o m)).1
  have row := (dRow_transform_iff (L := L) (label := label) (S := S) r absent _).mpr
    ⟨σ, os₁, os₂, made, inS, only, solves₁, solves₂, empties, inst, rfl⟩
  have linear : (footprintOf (σ, os₁.map Pick.take ++ os₂.map Pick.keep ++
      absent.map (fun q => Pick.query ⟨semRegion L σ q, ∅⟩ false) ++
        [.make (made : Multiset T)]).2).Linear := by
    rw [footprint_row]
    refine ⟨by simpa using nodup₁, fun o m₁ m₂ => ?_⟩
    have o₂ : o ∈ os₂ := by simpa using m₂
    have o₁ : o ∈ os₁ := by simpa using m₁
    exact (Finset.mem_sdiff.mp (inX₂ o o₂)).2 (by simpa using o₁)
  obtain ⟨c, fires, takenEq, -, -, madeRel⟩ := fires_of_declarative sound complete minimal supply
    (fun eval mem => by rw [lets_transform] at mem; cases mem) row linear
  rw [footprint_row] at takenEq madeRel
  have taken' : c.taken = os₁.toFinset := by rw [takenEq]; simp
  refine ⟨c, fires, ?_⟩
  rw [labels_fire fires.enabled, taken', labels_toFinset label nodup₁, hM, add_right_comm,
    add_tsub_cancel_right]
  exact Multiset.Rel.add (Multiset.rel_refl_of_refl_on fun x _ => L.equivalence.refl x) madeRel

end Compiled

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
