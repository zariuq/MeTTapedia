import Mettapedia.Logic.ASP.Nogoods
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchOutcome

/-!
# The conflict-driven solver as a transition system

A nondeterministic transition relation `Program.Step P` over solver
configurations, in the style of the abstract solvers of Nieuwenhuis, Oliveras
and Tinelli (abstract DPLL, JACM 2006) and Lierler (abstract answer set solvers
with backjumping and learning, TPLP 2011), over the nogoods of Gebser, Kaufmann
and Schaub (AIJ 2012). Any branching heuristic, any entailed learned nogood and
any restart that respects the fairness condition is a run of this system; a
concrete solver is correct when its steps are steps of this relation.

## States are data

A state (`State`) is a trail of entries `(lit, level, reason)`, newest first,
where the reason of a propagated literal is the nogood that propagated it and a
decision has no reason; the learned nogoods, each with its origin; and the
number of learned nogoods at the last restart. Results are `sat M`, with `M` a
finite set of atoms, or `unsat`.

## Rules

* `propagate`: a nogood of the database (completion, learned, or the loop
  nogood of a set without falsum atoms) has every literal but `l` on the trail
  and `l` unassigned; push the complement of `l`, with the nogood as its reason.
* `unfounded` (a derived rule, `Step.unfounded`): if `U`, a set without falsum
  atoms, is unfounded with respect to the trail, push `F a` for an unassigned
  `a ∈ U`, with the loop nogood of `a` and `U` as its reason. It is `propagate` on
  that loop nogood.
* `decide`: push an unassigned literal with no reason, one level up.
* `fail`: a database nogood is falsified at level 0.
* `backjump`: a database nogood is falsified; for an entailed nogood `ε` whose
  literals other than `l` all lie below some decision, cut the trail back below
  that decision and push the complement of `l` with reason `ε`.
* `learn`: add an entailed nogood over program variables with a new set of
  literals.
* `restart`: cut the trail back to a suffix without decisions, allowed only when
  something was learned since the previous restart (the fairness condition).
* `succeed`: every program variable is assigned and no completion nogood, nor
  loop nogood of a set without falsum atoms, is falsified; report the true atoms.

Falsum atoms (`Program.Falsum`) are false in every supported model, and the loop
nogoods of the sets without them already make a supported model stable
(`Program.stable_of_loops`); the rules of a falsum atom have no body variables,
so the loop nogood of a set holding one need not be over variables. A unit body
has no variable either: its literal is over an atom (`Program.isVar_lit`).

## Results

* **Invariant** (`Inv`, `reachable_inv`): trail variables are distinct program
  variables; every learned nogood and every reason on the trail is entailed
  (`learned_entailed`); and every stable model that agrees with the decisions of
  any suffix of the trail agrees with that whole suffix.
* **Conflict analysis** (`Derived`, `Derived.entailed`): resolving database
  nogoods and trail reasons, and weakening, yields entailed nogoods, which
  `learn` and `backjump` accept; first-UIP learning (`FirstUIP`) is one strategy
  for choosing them.
* **Soundness**: `sat M` is a stable model (`sat_sound`); `unsat` means there is
  no stable model (`unsat_sound`).
* **Progress**: every reachable running state has a step (`progress`); at a total
  trail with a conflict above level 0 the nogood of the decisions is entailed
  and drives a backjump. A reachable configuration without a step is finished
  (`stuck_done`).
* **Termination**: steps between running states raise a bounded measure
  (`measure_lt`, `measure_le`): the number of learned nogoods, then the restart
  mark, then the trail read as a base-3 numeral with decisions 1 and propagated
  literals 2 (`trailValue`). Learning needs a new set of literals over program
  variables, and a restart needs something learned since the previous one, so
  every run is finite (`terminates`, `no_infinite_run`).
* **Completeness**: some run finishes (`exists_finish`); a stable model exists
  exactly when a run reports `sat` (`stable_exists_iff`), and then every finished
  run reports a stable model (`finished_sat_of_stable`).

## Reading as transform steps

Each rule reads the trail (and the nogood database) and writes one new trail
entry or one learned nogood; nothing is consumed except the trail suffix a
backjump or restart discards. In the transform calculus of
`ConstraintMultisetRewriting.Step`, propagation is a firing that reads the
assignment, checks a nogood and makes a justified literal; decisions are firings
with no premise; learning makes a justified nogood. Linear take is reserved for
the discarded trail suffix. Configurations read out as search outcomes
(`Config.outcome`): a running configuration is cut off, never refuted
(`outcome_status_cutOff`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Relation

universe u

variable {A : Type u}

/-- A trail entry: a literal, its decision level, and its reason; a decision has no reason. -/
structure Entry (A : Type u) where
  lit : Lit A
  level : ℕ
  reason : Option (Nogood A)
  deriving DecidableEq

/-- A solver state: the trail (newest entry first), the learned nogoods, and the number of
learned nogoods at the last restart. -/
structure State (A : Type u) where
  trail : List (Entry A)
  learned : List (Nogood A)
  restartMark : ℕ
  deriving DecidableEq

/-- What a finished run reports. -/
inductive Result (A : Type u)
  | sat (model : Finset A)
  | unsat
  deriving DecidableEq

/-- A configuration: still running, or finished with a result. -/
inductive Config (A : Type u)
  | running (s : State A)
  | done (r : Result A)
  deriving DecidableEq

/-- The decision level of a trail: its number of decisions. -/
def levelOf (t : List (Entry A)) : ℕ := (t.filter fun e => e.reason.isNone).length

/-- The empty state. -/
def State.initial : State A := ⟨[], [], 0⟩

namespace State

variable (s : State A)

/-- The literals on the trail. -/
def lits : List (Lit A) := s.trail.map Entry.lit

/-- A variable has a value on the trail. -/
def Assigned (x : Var A) : Prop := ∃ e ∈ s.trail, e.lit.var = x

/-- Every literal of the nogood is on the trail. -/
def Falsifies (δ : Nogood A) : Prop := ∀ l ∈ δ.lits, l ∈ s.lits

/-- The nogood has every literal on the trail except `l`, which is unassigned. -/
def UnitOn (δ : Nogood A) (l : Lit A) : Prop :=
  l ∈ δ.lits ∧ (∀ m ∈ δ.lits, m ≠ l → m ∈ s.lits) ∧ ¬ s.Assigned l.var

/-- Push an entry. -/
def push (e : Entry A) : State A := { s with trail := e :: s.trail }

end State

section Solver

variable [DecidableEq A]

namespace Program

variable (P : Program A)

/-- The variables of the program: its atoms and the bodies of its rules whose head is no falsum
atom, except unit bodies. -/
def IsVar : Var A → Prop
  | .atom a => a ∈ P.atomSet
  | .body B => ∃ r ∈ P, ¬ P.Falsum r.head ∧ ¬ r.body.IsUnit ∧ r.body = B

/-- The body of a rule whose head is no falsum atom is a variable, unless it is a unit body. -/
theorem isVar_body {r : Rule A} (hr : r ∈ P) (hf : P.falsum r.head = false) (hu : ¬ r.body.IsUnit) :
    P.IsVar (.body r.body) :=
  ⟨r, hr, (P.falsum_eq_false_iff).mp hf, hu, rfl⟩

omit [DecidableEq A] in
/-- **The literal of the body of a rule whose head is no falsum atom is over a variable**: the body's
own variable, or for a unit body the atom of its literal. -/
theorem isVar_lit {r : Rule A} (hr : r ∈ P) (hf : ¬ P.Falsum r.head) : P.IsVar r.body.lit.var := by
  by_cases hu : r.body.IsUnit
  · obtain ⟨a, same, ha⟩ := Body.lit_var_of_isUnit hu
    rw [same]
    exact ⟨r, hr, Or.inr ha⟩
  · rw [Body.lit_of_not_isUnit hu]
    exact ⟨r, hr, hf, hu, rfl⟩

/-- The nogoods available to a state: completion nogoods, learned nogoods and the loop nogoods of
sets without falsum atoms. -/
def InDatabase (s : State A) (δ : Nogood A) : Prop :=
  δ ∈ P.completionNogoods ∨ δ ∈ s.learned ∨
    ∃ (U : Finset A), (∀ b ∈ U, ¬ P.Falsum b) ∧ ∃ a ∈ U, δ = P.loopNogood U a

/-- The model a trail reports: its true program atoms. -/
def trailModel (s : State A) : Finset A := (P.allAtoms.filter fun a => tAtom a ∈ s.lits).toFinset

/-- **The solver transition relation.** -/
inductive Step : Config A → Config A → Prop
  | propagate {s : State A} {δ : Nogood A} {l : Lit A} :
      P.InDatabase s δ → s.UnitOn δ l → P.IsVar l.var →
      Step (.running s) (.running (s.push ⟨l.compl, levelOf s.trail, some δ⟩))
  | decide {s : State A} {l : Lit A} :
      P.IsVar l.var → ¬ s.Assigned l.var →
      Step (.running s) (.running (s.push ⟨l, levelOf s.trail + 1, none⟩))
  | fail {s : State A} {δ : Nogood A} :
      P.InDatabase s δ → s.Falsifies δ → levelOf s.trail = 0 →
      Step (.running s) (.done .unsat)
  | backjump {s : State A} {δ ε : Nogood A} {l : Lit A} {newer older : List (Entry A)} {d : Entry A} :
      P.InDatabase s δ → s.Falsifies δ → s.trail = newer ++ d :: older → d.reason = none →
      P.Entailed ε.lits → l ∈ ε.lits → (∀ m ∈ ε.lits, m ≠ l → m ∈ older.map Entry.lit) →
      (∀ e ∈ older, e.lit.var ≠ l.var) → P.IsVar l.var →
      Step (.running s) (.running ⟨⟨l.compl, levelOf older, some ε⟩ :: older, s.learned, s.restartMark⟩)
  | learn {s : State A} {ε : Nogood A} :
      P.Entailed ε.lits → (∀ m ∈ ε.lits, P.IsVar m.var) →
      ε.lits.toFinset ∉ s.learned.map (fun η => η.lits.toFinset) →
      Step (.running s) (.running { s with learned := ε :: s.learned })
  | restart {s : State A} {newer older : List (Entry A)} :
      s.trail = newer ++ older → (∀ e ∈ older, e.reason ≠ none) → s.restartMark < s.learned.length →
      Step (.running s) (.running ⟨older, s.learned, s.learned.length⟩)
  | succeed {s : State A} :
      (∀ x, P.IsVar x → s.Assigned x) → (∀ δ ∈ P.completionNogoods, ¬ s.Falsifies δ) →
      (∀ (U : Finset A), (∀ b ∈ U, ¬ P.Falsum b) → ∀ a ∈ U, ¬ s.Falsifies (P.loopNogood U a)) →
      Step (.running s) (.done (.sat (P.trailModel s)))

/-- **Unfounded-set propagation** is unit propagation on the loop nogood of an unfounded set. -/
theorem Step.unfounded {s : State A} {U : Finset A} {a : A} (unfounded : P.UnfoundedBy s.lits U)
    (noFalsum : ∀ b ∈ U, ¬ P.Falsum b) (member : a ∈ U) (unassigned : ¬ s.Assigned (.atom a))
    (isVar : P.IsVar (.atom a)) :
    P.Step (.running s) (.running (s.push ⟨fAtom a, levelOf s.trail, some (P.loopNogood U a)⟩)) :=
  Step.propagate (l := tAtom a) (Or.inr (Or.inr ⟨U, noFalsum, a, member, rfl⟩))
    ⟨List.mem_cons_self, P.loopNogood_unit_of_unfounded unfounded a, unassigned⟩ isVar

/-! ## The invariant -/

/-- Every stable model agreeing with the decisions of the trail agrees with the whole trail. -/
def TrailSound (t : List (Entry A)) : Prop :=
  ∀ v, P.Admissible v → P.BodiesCorrect v → P.Stable v.atoms →
    (∀ e ∈ t, e.reason = none → e.lit.Sat v) → ∀ e ∈ t, e.lit.Sat v

/-- Every suffix of the trail is sound. -/
def SuffixSound (t : List (Entry A)) : Prop := ∀ newer older, t = newer ++ older → P.TrailSound older

/-- **The solver invariant.** -/
structure Inv (s : State A) : Prop where
  nodup : (s.trail.map fun e => e.lit.var).Nodup
  vars : ∀ e ∈ s.trail, P.IsVar e.lit.var
  learnedEntailed : ∀ ε ∈ s.learned, P.Entailed ε.lits
  learnedVars : ∀ ε ∈ s.learned, ∀ m ∈ ε.lits, P.IsVar m.var
  learnedDistinct : (s.learned.map fun ε => ε.lits.toFinset).Nodup
  mark : s.restartMark ≤ s.learned.length
  sound : P.SuffixSound s.trail
  reasons : ∀ e ∈ s.trail, ∀ δ, e.reason = some δ → P.Entailed δ.lits

omit [DecidableEq A] in
theorem trailSound_decision {t : List (Entry A)} (h : P.TrailSound t) (l : Lit A) (k : ℕ) :
    P.TrailSound (⟨l, k, none⟩ :: t) := by
  intro v admissible correct stable decisions
  have old := h v admissible correct stable fun e he => decisions e (List.mem_cons_of_mem _ he)
  rintro e (_ | ⟨_, he⟩)
  · exact decisions _ List.mem_cons_self rfl
  · exact old e he

omit [DecidableEq A] in
theorem trailSound_justified {t : List (Entry A)} (h : P.TrailSound t) {δ : Nogood A} {l : Lit A}
    (entailed : P.Entailed δ.lits) (rest : ∀ m ∈ δ.lits, m ≠ l → m ∈ t.map Entry.lit) (k : ℕ) :
    P.TrailSound (⟨l.compl, k, some δ⟩ :: t) := by
  intro v admissible correct stable decisions
  have old := h v admissible correct stable fun e he => decisions e (List.mem_cons_of_mem _ he)
  rintro e (_ | ⟨_, he⟩)
  · obtain ⟨m, hm, notSat⟩ := entailed v admissible correct stable
    by_cases same : m = l
    · subst m
      exact (Lit.sat_compl v _).mpr notSat
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp (rest m hm same)
      exact absurd (old e' he') notSat
  · exact old e he

omit [DecidableEq A] in
theorem suffixSound_cons {e : Entry A} {t : List (Entry A)} :
    P.SuffixSound (e :: t) ↔ P.TrailSound (e :: t) ∧ P.SuffixSound t := by
  constructor
  · intro h
    exact ⟨h [] _ rfl, fun newer older split => h (e :: newer) older (by rw [split]; rfl)⟩
  · rintro ⟨whole, rest⟩ newer older split
    rcases List.cons_eq_append_iff.mp split with ⟨rfl, rfl⟩ | ⟨newer', rfl, split'⟩
    · exact whole
    · exact rest newer' older split'

omit [DecidableEq A] in
theorem suffixSound_append {newer older : List (Entry A)} (h : P.SuffixSound (newer ++ older)) :
    P.SuffixSound older :=
  fun newer' older' split => h (newer ++ newer') older' (by rw [split, List.append_assoc])

theorem inv_initial : P.Inv State.initial where
  nodup := List.nodup_nil
  vars := by simp [State.initial]
  learnedEntailed := by simp [State.initial]
  learnedVars := by simp [State.initial]
  learnedDistinct := List.nodup_nil
  mark := le_rfl
  sound := by
    intro newer older split
    obtain ⟨-, rfl⟩ := List.append_eq_nil_iff.mp split.symm
    intro v _ _ _ _ e he
    simp at he
  reasons := by simp [State.initial]

/-- A database nogood is entailed, given the invariant. -/
theorem InDatabase.entailed {s : State A} (inv : P.Inv s) {δ : Nogood A} (h : P.InDatabase s δ) :
    P.Entailed δ.lits := by
  rcases h with completion | learned | ⟨U, -, a, ha, rfl⟩
  · exact P.completionNogood_entailed completion
  · exact inv.learnedEntailed δ learned
  · exact P.loopNogood_entailed U ha

/-- **Steps preserve the invariant.** -/
theorem Step.inv {s s' : State A} (step : P.Step (.running s) (.running s')) (inv : P.Inv s) : P.Inv s' := by
  cases step with
  | propagate database unit isVar =>
    obtain ⟨_, rest, unassigned⟩ := unit
    refine ⟨?_, ?_, inv.learnedEntailed, inv.learnedVars, inv.learnedDistinct, inv.mark, ?_, ?_⟩
    · refine List.nodup_cons.mpr ⟨fun h => unassigned ?_, inv.nodup⟩
      obtain ⟨e, he, same⟩ := List.mem_map.mp h
      exact ⟨e, he, same⟩
    · rintro e (_ | ⟨_, he⟩)
      · exact isVar
      · exact inv.vars e he
    · exact (P.suffixSound_cons).mpr ⟨P.trailSound_justified (inv.sound [] _ rfl)
        (InDatabase.entailed P inv database) rest _, inv.sound⟩
    · rintro e (_ | ⟨_, he⟩) δ' same
      · cases same
        exact InDatabase.entailed P inv database
      · exact inv.reasons e he δ' same
  | decide isVar unassigned =>
    refine ⟨?_, ?_, inv.learnedEntailed, inv.learnedVars, inv.learnedDistinct, inv.mark, ?_, ?_⟩
    · refine List.nodup_cons.mpr ⟨fun h => unassigned ?_, inv.nodup⟩
      obtain ⟨e, he, same⟩ := List.mem_map.mp h
      exact ⟨e, he, same⟩
    · rintro e (_ | ⟨_, he⟩)
      · exact isVar
      · exact inv.vars e he
    · exact (P.suffixSound_cons).mpr ⟨P.trailSound_decision (inv.sound [] _ rfl) _ _, inv.sound⟩
    · rintro e (_ | ⟨_, he⟩) δ' same
      · cases same
      · exact inv.reasons e he δ' same
  | @backjump _ δ ε l newer older d database falsified split decision entailed member rest outside isVar =>
    have olderSound : P.SuffixSound older :=
      ((P.suffixSound_cons).mp (P.suffixSound_append (split ▸ inv.sound))).2
    have olderNodup := split ▸ inv.nodup
    rw [List.map_append, List.map_cons] at olderNodup
    have olderNodup := (List.nodup_cons.mp (List.nodup_append.mp olderNodup).2.1).2
    refine ⟨?_, ?_, inv.learnedEntailed, inv.learnedVars, inv.learnedDistinct, inv.mark, ?_, ?_⟩
    · refine List.nodup_cons.mpr ⟨fun h => ?_, olderNodup⟩
      obtain ⟨e, he, same⟩ := List.mem_map.mp h
      exact outside e he same
    · rintro e (_ | ⟨_, he⟩)
      · exact isVar
      · exact inv.vars e (split ▸ List.mem_append_right _ (List.mem_cons_of_mem _ he))
    · exact (P.suffixSound_cons).mpr ⟨P.trailSound_justified (olderSound [] _ rfl) entailed rest _,
        olderSound⟩
    · rintro e (_ | ⟨_, he⟩) δ' same
      · cases same
        exact entailed
      · exact inv.reasons e (split ▸ List.mem_append_right _ (List.mem_cons_of_mem _ he)) δ' same
  | learn entailed vars fresh =>
    refine ⟨inv.nodup, inv.vars, ?_, ?_, ?_, ?_, inv.sound, inv.reasons⟩
    · rintro ε (_ | ⟨_, hε⟩)
      · exact entailed
      · exact inv.learnedEntailed ε hε
    · rintro ε (_ | ⟨_, hε⟩)
      · exact vars
      · exact inv.learnedVars ε hε
    · exact List.nodup_cons.mpr ⟨fresh, inv.learnedDistinct⟩
    · exact Nat.le_succ_of_le inv.mark
  | restart split _ _ =>
    refine ⟨?_, ?_, inv.learnedEntailed, inv.learnedVars, inv.learnedDistinct, le_rfl, ?_, ?_⟩
    · have nodup := split ▸ inv.nodup
      rw [List.map_append] at nodup
      exact (List.nodup_append.mp nodup).2.1
    · exact fun e he => inv.vars e (split ▸ List.mem_append_right _ he)
    · exact P.suffixSound_append (split ▸ inv.sound)
    · exact fun e he => inv.reasons e (split ▸ List.mem_append_right _ he)

/-- What conflict analysis may derive in a state: database nogoods, the reasons on the trail,
resolvents of these, and supersets (weakening, which also removes repeated literals). -/
inductive Derived (s : State A) : List (Lit A) → Prop
  | database {δ : Nogood A} : P.InDatabase s δ → Derived s δ.lits
  | reason {e : Entry A} {δ : Nogood A} : e ∈ s.trail → e.reason = some δ → Derived s δ.lits
  | resolve {x y : List (Lit A)} (l : Lit A) : Derived s x → Derived s y →
      Derived s (x.erase l ++ y.erase l.compl)
  | weaken {x y : List (Lit A)} : Derived s x → x ⊆ y → Derived s y

/-- **Conflict analysis is sound**: every nogood derived by resolution from the database and the
reasons on the trail is entailed, so it may be learned and may drive a backjump. -/
theorem Derived.entailed {s : State A} (inv : P.Inv s) {x : List (Lit A)} (h : P.Derived s x) :
    P.Entailed x := by
  induction h with
  | database member => exact InDatabase.entailed P inv member
  | reason he hδ => exact inv.reasons _ he _ hδ
  | resolve l _ _ ihx ihy => exact Entailed.resolve P l ihx ihy
  | weaken _ sub ih => exact Entailed.weaken P ih fun _ hl => sub hl

/-- Configurations reachable from the empty state. -/
def Reachable (c : Config A) : Prop := ReflTransGen P.Step (.running State.initial) c

theorem done_no_step {r : Result A} {c : Config A} : ¬ P.Step (.done r) c := by
  intro step
  cases step

/-- **Every reachable running state satisfies the invariant.** -/
theorem reachable_inv {s : State A} (h : P.Reachable (.running s)) : P.Inv s := by
  suffices ∀ c, P.Reachable c → ∀ s, c = .running s → P.Inv s from this _ h s rfl
  intro c reach
  induction reach with
  | refl =>
    intro s same
    cases same
    exact P.inv_initial
  | @tail b c _ step ih =>
    intro s same
    subst same
    cases b with
    | done r => exact absurd step P.done_no_step
    | running s₀ => exact step.inv P (ih s₀ rfl)

/-- **Every learned nogood of a reachable state is entailed.** -/
theorem learned_entailed {s : State A} (h : P.Reachable (.running s)) {ε : Nogood A} (member : ε ∈ s.learned) :
    P.Entailed ε.lits :=
  (P.reachable_inv h).learnedEntailed ε member

/-! ## Soundness -/

omit [DecidableEq A] in
theorem stable_canonical {S : Set A} (stable : P.Stable S) :
    P.Admissible (canonical S) ∧ P.BodiesCorrect (canonical S) ∧ P.Stable (canonical S).atoms := by
  refine ⟨P.canonical_admissible ?_, P.canonical_bodiesCorrect S, by rw [canonical_atoms]; exact stable⟩
  exact stable.subset_headSet.trans P.headSet_subset_atomSet

/-- The total assignment a trail determines: a variable is true when `T` of it is on the trail. -/
def trailValuation (s : State A) : Valuation A := fun x => decide (⟨x, true⟩ ∈ s.lits)

theorem sat_iff_mem {s : State A} (inv : P.Inv s) (total : ∀ x, P.IsVar x → s.Assigned x) {l : Lit A}
    (isVar : P.IsVar l.var) : l.Sat (trailValuation s) ↔ l ∈ s.lits := by
  obtain ⟨x, sign⟩ := l
  have unique : ∀ b c : Bool, (⟨x, b⟩ : Lit A) ∈ s.lits → (⟨x, c⟩ : Lit A) ∈ s.lits → b = c := by
    intro b c hb hc
    obtain ⟨e, he, hb⟩ := List.mem_map.mp hb
    obtain ⟨e', he', hc⟩ := List.mem_map.mp hc
    have same : e = e' := List.inj_on_of_nodup_map inv.nodup he he' (by
      show e.lit.var = e'.lit.var
      rw [hb, hc])
    subst same
    rw [hb] at hc
    exact congrArg Lit.sign hc
  cases sign with
  | true => simp [Lit.Sat, trailValuation]
  | false =>
    simp only [Lit.Sat, trailValuation, decide_eq_false_iff_not]
    constructor
    · intro notTrue
      obtain ⟨e, he, same⟩ := total x isVar
      have mem : e.lit ∈ s.lits := List.mem_map_of_mem he
      rcases hlit : e.lit with ⟨y, b⟩
      rw [hlit] at mem same
      simp only at same
      subst same
      cases b
      · exact mem
      · exact absurd mem notTrue
    · intro isFalse isTrue
      exact Bool.false_ne_true (unique false true isFalse isTrue)

theorem sat_true_iff (s : State A) (x : Var A) : (⟨x, true⟩ : Lit A).Sat (trailValuation s) ↔ ⟨x, true⟩ ∈ s.lits := by
  simp [Lit.Sat, trailValuation]

/-- The literals of completion nogoods are over program variables. -/
theorem completionNogoods_vars {δ : Nogood A} (h : δ ∈ P.completionNogoods) : ∀ l ∈ δ.lits, P.IsVar l.var := by
  have pos : ∀ r ∈ P, ∀ a ∈ r.pos, P.IsVar (.atom a) := fun r hr a ha => ⟨r, hr, Or.inr (Or.inl ha)⟩
  have neg : ∀ r ∈ P, ∀ a ∈ r.neg, P.IsVar (.atom a) := fun r hr a ha => ⟨r, hr, Or.inr (Or.inr ha)⟩
  have head : ∀ r ∈ P, P.IsVar (.atom r.head) := fun r hr => ⟨r, hr, Or.inl rfl⟩
  simp only [completionNogoods, List.mem_append, List.mem_flatMap, List.mem_map] at h
  rcases h with ⟨r, hr, hδ⟩ | ⟨a, ha, rfl⟩
  · unfold ruleNogoods at hδ
    by_cases hf : P.falsum r.head = true
    · rw [if_pos hf, List.mem_singleton] at hδ
      subst hδ
      intro l hl
      simp only [constraintNogood, List.mem_append, List.mem_map] at hl
      rcases hl with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
      · exact pos r hr b hb
      · exact neg r hr b (Rule.mem_group.mp hb).1
    rw [if_neg hf] at hδ
    have notFalsum : ¬ P.Falsum r.head := (P.falsum_eq_false_iff).mp (Bool.eq_false_iff.mpr hf)
    rcases List.mem_cons.mp hδ with rfl | hδ
    · intro l hl
      simp only [headNogood, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact P.isVar_lit hr notFalsum
      · exact head r hr
    by_cases hu : r.body.IsUnit
    · simp [bodyNogoods, hu] at hδ
    have body : P.IsVar (.body r.body) := ⟨r, hr, notFalsum, hu, rfl⟩
    simp only [bodyNogoods, if_neg hu, List.mem_cons, List.mem_append, List.mem_map] at hδ
    rcases hδ with (rfl | ⟨a, ha, rfl⟩) | ⟨b, hb, rfl⟩
    · intro l hl
      simp only [List.mem_cons, List.mem_append, List.mem_map] at hl
      rcases hl with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact body
      · exact pos r hr a ha
      · exact neg r hr b hb
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact body
      · exact pos r hr a ha
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact body
      · exact neg r hr b hb
  · intro l hl
    by_cases hf : P.falsum a = true
    · simp only [supportNogood, hf, ↓reduceIte, List.mem_singleton] at hl
      subst hl
      exact (P.mem_allAtoms).mp ha
    simp only [supportNogood, hf, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hl
    rcases hl with rfl | ⟨r, ⟨hr, rfl⟩, rfl⟩
    · exact (P.mem_allAtoms).mp ha
    · exact P.isVar_lit hr ((P.falsum_eq_false_iff).mp (Bool.eq_false_iff.mpr hf))

/-- The literals of the loop nogood of a set without falsum atoms are over program variables,
except perhaps its own atom: every external rule has its head in the set. -/
theorem loopNogood_vars {U : Finset A} {a : A} (noFalsum : ∀ b ∈ U, ¬ P.Falsum b) {l : Lit A}
    (h : l ∈ (P.loopNogood U a).lits) : l = tAtom a ∨ P.IsVar l.var := by
  simp only [loopNogood, externalBodies, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  rcases h with rfl | ⟨_, ⟨r, ⟨hr, external⟩, rfl⟩, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (P.isVar_lit hr (noFalsum _ external.1))

theorem mem_lits_isVar {s : State A} (inv : P.Inv s) {l : Lit A} (h : l ∈ s.lits) : P.IsVar l.var := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  exact inv.vars e he

theorem trailValuation_admissible {s : State A} (inv : P.Inv s) : P.Admissible (trailValuation s) :=
  fun a h => P.mem_lits_isVar inv ((sat_true_iff s (.atom a)).mp h)

theorem coe_trailModel {s : State A} (inv : P.Inv s) : (↑(P.trailModel s) : Set A) = (trailValuation s).atoms := by
  ext a
  simp only [trailModel, List.coe_toFinset, List.mem_filter, decide_eq_true_eq, Set.mem_ofPred_eq]
  constructor
  · exact fun h => (sat_true_iff s (.atom a)).mpr h.2
  · intro h
    have mem := (sat_true_iff s (.atom a)).mp h
    exact ⟨(P.mem_allAtoms).mpr (P.mem_lits_isVar inv mem), mem⟩

theorem completionSolution_of_total {s : State A} (inv : P.Inv s) (total : ∀ x, P.IsVar x → s.Assigned x)
    (completion : ∀ δ ∈ P.completionNogoods, ¬ s.Falsifies δ) : P.CompletionSolution (trailValuation s) :=
  fun δ hδ violated => completion δ hδ fun l hl =>
    (P.sat_iff_mem inv total (P.completionNogoods_vars hδ l hl)).mp (violated l hl)

/-- The `succeed` guard makes the reported atoms a stable model. -/
theorem succeed_stable {s : State A} (inv : P.Inv s) (total : ∀ x, P.IsVar x → s.Assigned x)
    (completion : ∀ δ ∈ P.completionNogoods, ¬ s.Falsifies δ)
    (loops : ∀ (U : Finset A), (∀ b ∈ U, ¬ P.Falsum b) → ∀ a ∈ U, ¬ s.Falsifies (P.loopNogood U a)) :
    P.Stable ↑(P.trailModel s) := by
  have admissible := P.trailValuation_admissible inv
  obtain ⟨supported, correct⟩ :=
    (P.completionSolution_iff _ admissible).mp (P.completionSolution_of_total inv total completion)
  rw [coe_trailModel P inv]
  refine P.stable_of_loops _ correct supported fun U noFalsum a ha violated => loops U noFalsum a ha ?_
  intro l hl
  rcases P.loopNogood_vars noFalsum hl with rfl | isVar
  · exact (sat_true_iff s (.atom a)).mp (violated _ hl)
  · exact (P.sat_iff_mem inv total isVar).mp (violated l hl)

/-- **The loop part of the `succeed` guard is the reduct check**: on a total trail violating no
completion nogood, no loop nogood is falsified exactly when the reported atoms pass `isStable`.
A solver may decide the guard by its unfounded-set check or by the reduct checker. -/
theorem loops_ok_iff_isStable {s : State A} (inv : P.Inv s) (total : ∀ x, P.IsVar x → s.Assigned x)
    (completion : ∀ δ ∈ P.completionNogoods, ¬ s.Falsifies δ) :
    (∀ (U : Finset A), (∀ b ∈ U, ¬ P.Falsum b) → ∀ a ∈ U, ¬ s.Falsifies (P.loopNogood U a)) ↔
      P.isStable (P.trailModel s) = true := by
  rw [isStable_iff]
  constructor
  · exact P.succeed_stable inv total completion
  · intro stable U _ a ha falsified
    have admissible := P.trailValuation_admissible inv
    have correct := ((P.completionSolution_iff _ admissible).mp
      (P.completionSolution_of_total inv total completion)).2
    rw [coe_trailModel P inv] at stable
    have loops := (P.loopSolution_iff_stable _ correct (P.stable_supported stable)).mpr stable
    apply loops U a ha
    intro l hl
    exact (P.sat_iff_mem inv total (P.mem_lits_isVar inv (falsified l hl))).mpr (falsified l hl)

/-- At level 0 a falsified database nogood refutes every stable model. -/
theorem fail_no_stable {s : State A} (inv : P.Inv s) {δ : Nogood A} (database : P.InDatabase s δ)
    (falsified : s.Falsifies δ) (ground : levelOf s.trail = 0) (S : Set A) : ¬ P.Stable S := by
  intro stable
  obtain ⟨admissible, correct, stable'⟩ := P.stable_canonical stable
  have noDecision : ∀ e ∈ s.trail, e.reason ≠ none := by
    intro e he decision
    have : e ∈ s.trail.filter fun e => e.reason.isNone := List.mem_filter.mpr ⟨he, by simp [decision]⟩
    rw [levelOf, List.length_eq_zero_iff] at ground
    rw [ground] at this
    exact List.not_mem_nil this
  have all := inv.sound [] s.trail rfl _ admissible correct stable' fun e he decision =>
    absurd decision (noDecision e he)
  obtain ⟨l, hl, notSat⟩ := InDatabase.entailed P inv database _ admissible correct stable'
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (falsified l hl)
  exact notSat (all e he)

theorem reachable_step_done {r : Result A} (h : P.Reachable (.done r)) :
    ∃ s, P.Reachable (.running s) ∧ P.Step (.running s) (.done r) := by
  rcases ReflTransGen.cases_tail h with same | ⟨c, reach, step⟩
  · cases same
  · cases c with
    | done r' => exact absurd step P.done_no_step
    | running s => exact ⟨s, reach, step⟩

/-- **Soundness of `sat`**: a reported model is a stable model. -/
theorem sat_sound {M : Finset A} (h : P.Reachable (.done (.sat M))) : P.Stable ↑M := by
  obtain ⟨s, reach, step⟩ := P.reachable_step_done h
  cases step with
  | succeed total completion loops => exact P.succeed_stable (P.reachable_inv reach) total completion loops

/-- **Soundness of `unsat`**: there is no stable model. -/
theorem unsat_sound (h : P.Reachable (.done .unsat)) (S : Set A) : ¬ P.Stable S := by
  obtain ⟨s, reach, step⟩ := P.reachable_step_done h
  cases step with
  | fail database falsified ground => exact P.fail_no_stable (P.reachable_inv reach) database falsified ground S

/-! ## Progress -/

omit [DecidableEq A] in
theorem exists_newest_decision : ∀ (t : List (Entry A)), (∃ e ∈ t, e.reason = none) →
    ∃ newer d older, t = newer ++ d :: older ∧ d.reason = none ∧ ∀ e ∈ newer, e.reason ≠ none
  | [], ⟨_, he, _⟩ => absurd he List.not_mem_nil
  | e :: t, h => by
    by_cases decision : e.reason = none
    · exact ⟨[], e, t, rfl, decision, by simp⟩
    · obtain ⟨e', he', decision'⟩ := h
      rcases List.mem_cons.mp he' with rfl | he'
      · exact absurd decision' decision
      · obtain ⟨newer, d, older, split, isDecision, before⟩ := exists_newest_decision t ⟨e', he', decision'⟩
        refine ⟨e :: newer, d, older, by rw [split]; rfl, isDecision, ?_⟩
        rintro e'' (_ | ⟨_, he''⟩)
        · exact decision
        · exact before e'' he''

/-- The decision literals of a trail. -/
def decisionLits (t : List (Entry A)) : List (Lit A) := (t.filter fun e => e.reason.isNone).map Entry.lit

/-- At a conflict, the nogood of all decisions is entailed. -/
theorem decisions_entailed {s : State A} (inv : P.Inv s) {δ : Nogood A} (database : P.InDatabase s δ)
    (falsified : s.Falsifies δ) : P.Entailed (decisionLits s.trail) := by
  intro v admissible correct stable
  by_contra allSat
  push Not at allSat
  have all := inv.sound [] s.trail rfl v admissible correct stable fun e he decision =>
    allSat e.lit (List.mem_map_of_mem (List.mem_filter.mpr ⟨he, by simp [decision]⟩))
  obtain ⟨l, hl, notSat⟩ := InDatabase.entailed P inv database v admissible correct stable
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (falsified l hl)
  exact notSat (all e he)

/-- **Progress**: every state satisfying the invariant has a step. -/
theorem progress {s : State A} (inv : P.Inv s) : ∃ c, P.Step (.running s) c := by
  classical
  by_cases total : ∀ x, P.IsVar x → s.Assigned x
  · by_cases conflict : ∃ δ, P.InDatabase s δ ∧ s.Falsifies δ
    · obtain ⟨δ, database, falsified⟩ := conflict
      by_cases ground : levelOf s.trail = 0
      · exact ⟨_, Step.fail database falsified ground⟩
      · have some : ∃ e ∈ s.trail, e.reason = none := by
          by_contra none
          push Not at none
          apply ground
          rw [levelOf, List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro e he
          simpa using none e he
        obtain ⟨newer, d, older, split, decision, before⟩ := exists_newest_decision s.trail some
        have newerFree : newer.filter (fun e => e.reason.isNone) = [] :=
          List.filter_eq_nil_iff.mpr fun e he => by simpa using before e he
        have lits : decisionLits s.trail = d.lit :: decisionLits older := by
          rw [decisionLits, split, List.filter_append, newerFree, List.nil_append, List.filter_cons_of_pos
            (by simp [decision]), List.map_cons]
          rfl
        have entailed := P.decisions_entailed inv database falsified
        rw [lits] at entailed
        have nodup := split ▸ inv.nodup
        rw [List.map_append, List.map_cons] at nodup
        have fresh := (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1
        refine ⟨_, Step.backjump (ε := ⟨d.lit :: decisionLits older, .learned 0⟩) (l := d.lit) database
          falsified split decision entailed List.mem_cons_self ?_ ?_ ?_⟩
        · intro m hm ne
          rcases List.mem_cons.mp hm with rfl | hm
          · exact absurd rfl ne
          · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
            exact List.mem_map_of_mem (List.mem_filter.mp he).1
        · intro e he same
          exact fresh (same ▸ List.mem_map_of_mem he)
        · exact inv.vars d (split ▸ List.mem_append_right _ List.mem_cons_self)
    · push Not at conflict
      exact ⟨_, Step.succeed total (fun δ h => conflict δ (Or.inl h))
        fun U noFalsum a ha => conflict _ (Or.inr (Or.inr ⟨U, noFalsum, a, ha, rfl⟩))⟩
  · push Not at total
    obtain ⟨x, isVar, unassigned⟩ := total
    exact ⟨_, Step.decide (l := ⟨x, true⟩) isVar unassigned⟩

/-- Every reachable configuration without a step is finished. -/
theorem stuck_done {c : Config A} (reach : P.Reachable c) (stuck : ∀ c', ¬ P.Step c c') : ∃ r, c = .done r := by
  cases c with
  | done r => exact ⟨r, rfl⟩
  | running s =>
    obtain ⟨c', step⟩ := P.progress (P.reachable_inv reach)
    exact absurd step (stuck c')

/-! ## Termination -/

omit [DecidableEq A] in
/-- The digit of an entry: decisions count 1, propagated literals 2. -/
def _root_.Mettapedia.Logic.ASP.Entry.digit (e : Entry A) : ℕ := if e.reason.isNone then 1 else 2

omit [DecidableEq A] in
theorem _root_.Mettapedia.Logic.ASP.Entry.digit_pos (e : Entry A) : 1 ≤ e.digit := by
  unfold Entry.digit; split <;> omega

omit [DecidableEq A] in
theorem _root_.Mettapedia.Logic.ASP.Entry.digit_le (e : Entry A) : e.digit ≤ 2 := by
  unfold Entry.digit; split <;> omega

/-- The value of a trail in base 3, the oldest entry most significant, padded to `n` digits. A
decision is the digit 1 and a propagated literal 2, so pushing an entry raises the value, and so
does replacing a decision and everything above it by a propagated literal. -/
def trailValue (n : ℕ) : List (Entry A) → ℕ
  | [] => 0
  | e :: t => trailValue n t + e.digit * 3 ^ (n - 1 - t.length)

omit [DecidableEq A] in
theorem trailValue_append_le (n : ℕ) (base : List (Entry A)) :
    ∀ x : List (Entry A), base.length + x.length ≤ n →
      trailValue n (x ++ base) + 3 ^ (n - (base.length + x.length)) ≤ trailValue n base + 3 ^ (n - base.length)
  | [], _ => by simp
  | y :: x, h => by
    rw [List.length_cons] at h
    have ih := trailValue_append_le n base x (by omega)
    rw [List.cons_append, trailValue, List.length_append, List.length_cons]
    obtain ⟨k, hk⟩ : ∃ k, n - (base.length + x.length) = k + 1 := ⟨n - (base.length + x.length) - 1, by omega⟩
    have e1 : n - 1 - (x.length + base.length) = k := by omega
    have e2 : n - (base.length + (x.length + 1)) = k := by omega
    rw [hk, pow_succ] at ih
    rw [e1, e2]
    have digit : y.digit * 3 ^ k ≤ 2 * 3 ^ k := Nat.mul_le_mul_right _ y.digit_le
    omega

omit [DecidableEq A] in
theorem trailValue_lt (n : ℕ) {t : List (Entry A)} (h : t.length ≤ n) : trailValue n t < 3 ^ n := by
  have := trailValue_append_le n [] t (by simpa using h)
  simp only [List.append_nil, List.length_nil, Nat.zero_add, trailValue, Nat.sub_zero] at this
  have : 0 < 3 ^ (n - t.length) := by positivity
  omega

omit [DecidableEq A] in
theorem trailValue_cons_lt (n : ℕ) (e : Entry A) (t : List (Entry A)) : trailValue n t < trailValue n (e :: t) := by
  rw [trailValue]
  have : 1 ≤ e.digit * 3 ^ (n - 1 - t.length) := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := e.digit_pos; omega) (by positivity))
  omega

omit [DecidableEq A] in
theorem trailValue_backjump_lt (n : ℕ) {newer older : List (Entry A)} {d e : Entry A}
    (decision : d.reason = none) (implied : e.reason ≠ none) (h : (newer ++ d :: older).length ≤ n) :
    trailValue n (newer ++ d :: older) < trailValue n (e :: older) := by
  have bound := trailValue_append_le n (d :: older) newer (by simp at h ⊢; omega)
  have dDigit : d.digit = 1 := by simp [Entry.digit, decision]
  have eDigit : e.digit = 2 := by
    unfold Entry.digit
    rw [if_neg (by simpa [Option.isNone_iff_eq_none] using implied)]
  simp only [trailValue, dDigit, eDigit, List.length_cons] at bound ⊢
  have e1 : n - (older.length + 1) = n - 1 - older.length := by omega
  rw [e1] at bound
  have : 0 < 3 ^ (n - (older.length + 1 + newer.length)) := by positivity
  omega

/-- The program variables, as a finite set. -/
def varFinset : Finset (Var A) := (P.allAtoms.map Var.atom ++ P.bodyRules.map fun r => Var.body r.body).toFinset

theorem mem_varFinset {x : Var A} : x ∈ P.varFinset ↔ P.IsVar x := by
  cases x with
  | atom a => simp [varFinset, IsVar, P.mem_allAtoms]
  | body B => simp [varFinset, IsVar, P.mem_bodyRules, and_assoc]

/-- The literals over program variables, as a finite set. -/
def litFinset : Finset (Lit A) := P.varFinset.biUnion fun x => {⟨x, true⟩, ⟨x, false⟩}

theorem mem_litFinset {l : Lit A} : l ∈ P.litFinset ↔ P.IsVar l.var := by
  obtain ⟨x, b⟩ := l
  simp only [litFinset, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Lit.mk.injEq,
    mem_varFinset]
  constructor
  · rintro ⟨y, hy, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ <;> exact hy
  · intro h
    exact ⟨x, h, by cases b <;> simp⟩

theorem trail_length_le {s : State A} (inv : P.Inv s) : s.trail.length ≤ P.varFinset.card := by
  have card := List.toFinset_card_of_nodup inv.nodup
  rw [List.length_map] at card
  rw [← card]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact (P.mem_varFinset).mpr (inv.vars e he)

theorem learned_length_le {s : State A} (inv : P.Inv s) : s.learned.length ≤ 2 ^ P.litFinset.card := by
  have card := List.toFinset_card_of_nodup inv.learnedDistinct
  rw [List.length_map] at card
  rw [← card, ← Finset.card_powerset]
  apply Finset.card_le_card
  intro L hL
  obtain ⟨ε, hε, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hL)
  rw [Finset.mem_powerset]
  intro l hl
  exact (P.mem_litFinset).mpr (inv.learnedVars ε hε l (List.mem_toFinset.mp hl))

/-- The termination measure: learned nogoods, then the restart mark, then the trail value. -/
def measure (s : State A) : ℕ :=
  (s.learned.length * (2 ^ P.litFinset.card + 1) + s.restartMark) * 3 ^ P.varFinset.card +
    trailValue P.varFinset.card s.trail

/-- The bound of the measure on states satisfying the invariant. -/
def measureBound : ℕ :=
  (2 ^ P.litFinset.card * (2 ^ P.litFinset.card + 1) + 2 ^ P.litFinset.card + 1) * 3 ^ P.varFinset.card

theorem measure_le {s : State A} (inv : P.Inv s) : P.measure s ≤ P.measureBound := by
  have learned := P.learned_length_le inv
  have value := trailValue_lt P.varFinset.card (P.trail_length_le inv)
  have mark := inv.mark
  unfold measure measureBound
  have h2 : (s.learned.length * (2 ^ P.litFinset.card + 1) + s.restartMark) * 3 ^ P.varFinset.card +
      3 ^ P.varFinset.card ≤
        (2 ^ P.litFinset.card * (2 ^ P.litFinset.card + 1) + 2 ^ P.litFinset.card + 1) * 3 ^ P.varFinset.card := by
    rw [← Nat.succ_mul]
    apply Nat.mul_le_mul_right
    have h1 : s.learned.length * (2 ^ P.litFinset.card + 1) ≤ 2 ^ P.litFinset.card * (2 ^ P.litFinset.card + 1) :=
      Nat.mul_le_mul_right _ learned
    omega
  omega

/-- **Every step between running states raises the measure.** -/
theorem measure_lt {s s' : State A} (step : P.Step (.running s) (.running s')) (inv : P.Inv s) :
    P.measure s < P.measure s' := by
  cases step with
  | @propagate _ δ l =>
    unfold measure State.push
    have := trailValue_cons_lt P.varFinset.card ⟨l.compl, levelOf s.trail, some δ⟩ s.trail
    simp only at this ⊢
    omega
  | @decide _ l =>
    unfold measure State.push
    have := trailValue_cons_lt P.varFinset.card ⟨l, levelOf s.trail + 1, none⟩ s.trail
    simp only at this ⊢
    omega
  | @backjump _ δ ε l newer older d database falsified split decision =>
    unfold measure
    have length := P.trail_length_le inv
    rw [split] at length
    have := trailValue_backjump_lt P.varFinset.card (e := ⟨l.compl, levelOf older, some ε⟩) decision
      (by simp) length
    rw [← split] at this
    simp only
    omega
  | learn =>
    unfold measure
    simp only [List.length_cons]
    have lt : s.learned.length * (2 ^ P.litFinset.card + 1) + s.restartMark <
        (s.learned.length + 1) * (2 ^ P.litFinset.card + 1) + s.restartMark := by
      rw [Nat.succ_mul]
      have : 0 < 2 ^ P.litFinset.card + 1 := by positivity
      omega
    have := Nat.mul_lt_mul_of_pos_right lt (show 0 < 3 ^ P.varFinset.card by positivity)
    omega
  | @restart _ newer older split _ fair =>
    unfold measure
    simp only
    have value := trailValue_lt P.varFinset.card (P.trail_length_le inv)
    have expand : (s.learned.length * (2 ^ P.litFinset.card + 1) + s.learned.length) * 3 ^ P.varFinset.card ≥
        (s.learned.length * (2 ^ P.litFinset.card + 1) + s.restartMark) * 3 ^ P.varFinset.card +
          3 ^ P.varFinset.card := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem acc_running {s : State A} (inv : P.Inv s) : Acc (fun c' c => P.Step c c') (.running s) := by
  induction h : P.measureBound - P.measure s using Nat.strong_induction_on generalizing s with
  | _ k ih =>
    constructor
    intro c step
    cases c with
    | done r => exact ⟨_, fun c' step' => absurd step' P.done_no_step⟩
    | running s' =>
      have inv' := step.inv P inv
      have up := P.measure_lt step inv
      have bound := P.measure_le inv'
      exact ih _ (by omega) inv' rfl

/-- **Termination**: there is no infinite run from a state satisfying the invariant; with the
fairness condition built into `restart`, every run from the empty state is finite. -/
theorem terminates : Acc (fun c' c => P.Step c c') (.running (State.initial : State A)) :=
  P.acc_running P.inv_initial

theorem no_infinite_run :
    ¬ ∃ f : ℕ → Config A, f 0 = .running State.initial ∧ ∀ n, P.Step (f n) (f (n + 1)) := by
  rintro ⟨f, start, steps⟩
  suffices ∀ c, Acc (fun c' c => P.Step c c') c → ∀ g : ℕ → Config A, g 0 = c →
      (∀ n, P.Step (g n) (g (n + 1))) → False from this _ P.terminates f start steps
  intro c acc
  induction acc with
  | intro c _ ih =>
    intro g start steps
    exact ih (g 1) (start ▸ steps 0) (fun n => g (n + 1)) rfl fun n => steps (n + 1)

theorem exists_finish_of_acc {c : Config A} (acc : Acc (fun c' c => P.Step c c') c)
    (inv : ∀ s, c = .running s → P.Inv s) : ∃ r, ReflTransGen P.Step c (.done r) := by
  induction acc with
  | intro c _ ih =>
    cases c with
    | done r => exact ⟨r, .refl⟩
    | running s =>
      obtain ⟨c', step⟩ := P.progress (inv s rfl)
      obtain ⟨r, run⟩ := ih c' step fun s' same => by
        subst same
        exact step.inv P (inv s rfl)
      exact ⟨r, ReflTransGen.head step run⟩

/-- **Some run from the empty state finishes.** -/
theorem exists_finish : ∃ r : Result A, P.Reachable (.done r) :=
  P.exists_finish_of_acc P.terminates fun s same => by
    cases same
    exact P.inv_initial

/-- **Completeness**: a stable model exists exactly when some run reports `sat`, and then every
finished run reports `sat`. -/
theorem stable_exists_iff : (∃ S, P.Stable S) ↔ ∃ M, P.Reachable (.done (.sat M)) := by
  constructor
  · rintro ⟨S, stable⟩
    obtain ⟨r, reach⟩ := P.exists_finish
    cases r with
    | sat M => exact ⟨M, reach⟩
    | unsat => exact absurd stable (P.unsat_sound reach S)
  · rintro ⟨M, reach⟩
    exact ⟨_, P.sat_sound reach⟩

theorem finished_sat_of_stable {S : Set A} (stable : P.Stable S) {r : Result A} (reach : P.Reachable (.done r)) :
    ∃ M, r = .sat M ∧ P.Stable ↑M := by
  cases r with
  | sat M => exact ⟨M, rfl, P.sat_sound reach⟩
  | unsat => exact absurd stable (P.unsat_sound reach S)

/-! ## Outcomes -/

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search in
/-- A configuration read as a search outcome: a running configuration is cut off with no
answer; `sat M` is finished with the answer `M`; `unsat` is refuted. -/
def _root_.Mettapedia.Logic.ASP.Config.outcome : Config A → Outcome (Finset A)
  | .running _ => Outcome.unknown
  | .done (.sat M) => Outcome.pure M
  | .done .unsat => Outcome.refuted

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search in
omit [DecidableEq A] in
/-- **Incomplete is never none**: an outcome is cut off exactly while the solver runs. -/
theorem outcome_status_cutOff (c : Config A) : c.outcome.status = .cutOff ↔ ∃ s, c = .running s := by
  rcases c with s | (M | _) <;> simp [Config.outcome, Outcome.refuted]

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search in
/-- Every answer of a reachable configuration is a stable model. -/
theorem outcome_answers_stable {c : Config A} (reach : P.Reachable c) {M : Finset A}
    (h : M ∈ c.outcome.answers) : P.Stable ↑M := by
  rcases c with s | (M' | _)
  · simp [Config.outcome] at h
  · simp only [Config.outcome, Outcome.pure_answers, Multiset.mem_singleton] at h
    subst h
    exact P.sat_sound reach
  · simp [Config.outcome, Outcome.refuted] at h

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search in
/-- A refuted outcome means there is no stable model. -/
theorem outcome_refuted {c : Config A} (reach : P.Reachable c) (h : c.outcome = Outcome.refuted) (S : Set A) :
    ¬ P.Stable S := by
  rcases c with s | (M | _)
  · have := congrArg Outcome.status h
    simp [Config.outcome, Outcome.refuted] at this
  · have := congrArg (fun o => Multiset.card o.answers) h
    simp [Config.outcome, Outcome.refuted] at this
  · exact P.unsat_sound reach S

end Program

end Solver

end Mettapedia.Logic.ASP
