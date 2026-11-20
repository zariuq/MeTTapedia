import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Numbers

/-!
# Recursion on the step: addition by structural recursion, bounded by the stage

The program of addition (`addProgram`) is three rules of the adder's schemas, run on the tree's
first-order step under a program (`ProgramAdequacy.program`):

* `start x y` takes the request `askAdd x y`, reads the rows `natRow x` and `natRow y` of the number
  region, and makes `runAdd x y`;
* `peel x y` takes `runAdd (succE x) y` and makes `runAdd x (succE y)`: the recursive case, on the
  immediate subterm;
* `finish y` takes `runAdd zeroE y` and makes the answer `outE y`.

**The rank** of a state is the sum of the weights of its rows (`rank`): `depth x + 2` for a request,
`depth x + 1` for a running addition, `0` otherwise. Every move lowers it by exactly one
(`rank_lowers`), so the length of every run is the drop of the rank (`Runs.length_eq`).

**On generated rows** (`addition_on_generated`): for a request whose arguments are generated rows
present in the store, with the request the only work row,

* every run has at most `a + 2` moves, where `x = numeral a`; read from the stage, a run has at most
  `m + 1` moves when `natRow x` is in stage `m` (`addition_bounded_by_stage`);
* every final state reached holds exactly one work row, the answer `outE (numeral (a + b))`, the
  value of addition;
* a run of exactly `a + 2` moves reaches such a final state: the "every run" statements are not
  vacuous.

**Control** (`junk_request_no_answer`): on the row `natRow junkE`, which no constructor makes, the
request starts, and a run of one move reaches a state with no move and no answer (the theorem
exhibits that run; it does not quantify over every run): the recursion covers the
constructors and nothing else, so its totality is a property closed under the constructors
(`Numbers.IsNumeralRow` is its region-side form), and a writer that does not follow them breaks it.

The rights of the adder (`adderRights`) give it `peek` on numbers and `send` and `receive` on work
rows; it writes no number row (`adder_writes`), so the recursion is a reader of the type, not a
writer: with the owner, membership holds on every run and every closure statement about number rows
survives the adder (`ownerAndAdder_facts`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes

open WhenTypesApply.ThatsAll
open WhenTypesApply.TwoKinds (stage)
open NamesOnTheStep NamesOnTheStep.IssuingControls
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open MeTTaCalculus.InteractionTypes (Rights Facet)
open StepSpan (Succ)
open ProgramAdequacy (program program_succ_iff)

namespace Recursion

/-! ## Runs of a given length, and a rank -/

/-- **Runs of a given length** of a relation. -/
inductive Runs {V : Type} (step : V → V → Prop) : ℕ → V → V → Prop
  | refl (s : V) : Runs step 0 s s
  | cons {n : ℕ} {s t u : V} : step s t → Runs step n t u → Runs step (n + 1) s u

theorem Runs.reflTransGen {V : Type} {step : V → V → Prop} {n : ℕ} {s u : V}
    (run : Runs step n s u) : Relation.ReflTransGen step s u := by
  induction run with
  | refl => exact .refl
  | cons moved _ ih => exact Relation.ReflTransGen.head moved ih

theorem Runs.of_reflTransGen {V : Type} {step : V → V → Prop} {s u : V}
    (run : Relation.ReflTransGen step s u) : ∃ n, Runs step n s u := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head moved _ ih =>
      obtain ⟨n, rest⟩ := ih
      exact ⟨n + 1, .cons moved rest⟩

/-- **A rank bounds every run**: when every step lowers a natural-number rank by one, the length of a
run is the drop of the rank. -/
theorem Runs.length_eq {V : Type} {step : V → V → Prop} (rank : V → ℕ)
    (lowers : ∀ s t, step s t → rank t + 1 = rank s) {n : ℕ} {s u : V} (run : Runs step n s u) :
    n + rank u = rank s := by
  induction run with
  | refl => simp
  | cons moved _ ih =>
      have := lowers _ _ moved
      omega

/-! ## The adder and its program -/

/-- Rights of the adder: keep number rows; make and take work rows. -/
def adderRights : Rights Handle := fun n f =>
  (decide (n = .num) && decide (f = .peek)) ||
    (decide (n = .work) && (decide (f = .send) || decide (f = .receive)))

/-- **The adder**: the three rules of addition installed. -/
def adder : SchemaPublicationAuthority.Process Schema Handle :=
  ⟨adderRights, [.start, .peel, .finish]⟩

/-- Start: take the request, read the rows of both arguments. -/
def startRule (x y : Expr) : RuleInstance Expr := rule [askAdd x y] [natRow x, natRow y] [runAdd x y]
/-- The recursive case. -/
def peelRule (x y : Expr) : RuleInstance Expr := rule [runAdd (succE x) y] [] [runAdd x (succE y)]
/-- The base case. -/
def finishRule (y : Expr) : RuleInstance Expr := rule [runAdd zeroE y] [] [outE y]

/-- **The program of addition**: the rules the adder's schemas activate. -/
def addProgram : Set (RuleInstance Expr) :=
  {ρ | ∃ schema ∈ adder.schemas, ∃ x, activate schema x = some ρ}

theorem mem_addProgram {ρ : RuleInstance Expr} : ρ ∈ addProgram ↔
    (∃ x y, ρ = startRule x y) ∨ (∃ x y, ρ = peelRule x y) ∨ ∃ y, ρ = finishRule y := by
  constructor
  · rintro ⟨schema, installed, inputs, computed⟩
    simp only [adder, List.mem_cons, List.not_mem_nil, or_false] at installed
    rcases installed with rfl | rfl | rfl
    · rcases inputs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
      · simp [activate] at computed
      · simp [activate] at computed
      · simp only [activate, Option.some.injEq] at computed
        exact Or.inl ⟨x, y, computed.symm⟩
      · simp [activate] at computed
    · rcases inputs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
      · simp [activate] at computed
      · simp [activate] at computed
      · simp only [activate, Option.some.injEq] at computed
        exact Or.inr (Or.inl ⟨x, y, computed.symm⟩)
      · simp [activate] at computed
    · rcases inputs with _ | ⟨y, _ | ⟨z, rest⟩⟩
      · simp [activate] at computed
      · simp only [activate, Option.some.injEq] at computed
        exact Or.inr (Or.inr ⟨y, computed.symm⟩)
      · simp [activate] at computed
  · rintro (⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨.start, List.mem_cons_self .., [x, y], rfl⟩
    · exact ⟨.peel, List.mem_cons_of_mem _ (List.mem_cons_self ..), [x, y], rfl⟩
    · exact ⟨.finish, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        [y], rfl⟩

/-- **A move of the program of addition** on the first-order step under a program. -/
abbrev addStep (C C' : Conf) : Prop := Succ (program ground Prod.fst addProgram) C C'

theorem addStep_iff {C C' : Conf} : addStep C C' ↔
    ∃ (ρ : RuleInstance Expr) (sel : Selection Occ), ρ ∈ addProgram ∧
      sel.Valid ground Prod.fst ρ C ∧ sel.result Prod.fst ρ C = C' :=
  program_succ_iff ground Prod.fst addProgram C C'

/-- The adder's formed moves are moves of its program. -/
theorem addStep_of_adder {C C' : Conf} (moved : processStep activate place adder C C') :
    addStep C C' := by
  obtain ⟨schema, installed, x, ρ, computed, sel, valid, -, rfl⟩ := moved
  exact addStep_iff.mpr ⟨ρ, sel, ⟨schema, installed, x, computed⟩, valid, rfl⟩

/-- **The adder writes no number row**: the recursion is a reader of the type. -/
theorem adder_writes : Writes activate place Numbers.inNum natRules adder := by
  refine writes_of_each fun schema installed x ρ computed => Or.inr ?_
  have member : ρ ∈ addProgram := ⟨schema, installed, x, computed⟩
  rcases mem_addProgram.mp member with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ <;>
    · intro t produced
      rw [List.mem_singleton.mp produced]
      simp

/-- The adder holds no `send` at the numbers. -/
theorem adder_noSend (e : Expr) (atNum : place e = .num) : adder.rights (place e) .send = false := by
  rw [atNum]
  rfl

/-- The owner of the numbers (`true`) and the adder. -/
def ownerAndAdder : Bool → SchemaPublicationAuthority.Process Schema Handle :=
  fun b => cond b Numbers.owner adder

/-- **Every fact of the numbers survives the adder**: with the owner and the adder, membership holds on
every run from the empty store, and every closure statement about number rows survives the adder's
moves. -/
theorem ownerAndAdder_facts :
    (∀ {C : Conf}, Relation.ReflTransGen (systemStep activate place ownerAndAdder)
        ProgramAdequacy.emptyStore C →
      ∀ r ∈ contents C, place r = .num → ∃ k, r = natRow (numeral k)) ∧
    ClosedReadingSurvives (fun actor => processStep activate place (ownerAndAdder actor)) contents
      (fun e => place e = .num) true := by
  have writes : ∀ b, Writes activate place Numbers.inNum natRules (ownerAndAdder b) := by
    intro b
    cases b
    · exact adder_writes
    · exact Numbers.owner_writes
  refine ⟨fun run r present atNum => Numbers.natRules_generated_iff.mp
    (membership writes run (closedBy_empty _ _) r present atNum), ?_⟩
  exact closure_of_soleSender (inType := Numbers.inNum) fun actor other e atNum => by
    cases actor
    · exact adder_noSend e atNum
    · exact absurd rfl other

/-! ## Weights and the rank -/

/-- The number of successors on top of a term. -/
def depth : Expr → ℕ
  | .app (.sym 101) x => depth x + 1
  | _ => 0

@[simp] theorem depth_succE (x : Expr) : depth (succE x) = depth x + 1 := rfl
@[simp] theorem depth_zeroE : depth zeroE = 0 := rfl

theorem depth_numeral (k : ℕ) : depth (numeral k) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show depth (numeral k) + 1 = k + 1
      rw [ih]

/-- The weight of a row: what remains of the addition it stands for. -/
def weight : Expr → ℕ
  | .app (.app (.sym 130) x) _ => depth x + 2
  | .app (.app (.sym 131) x) _ => depth x + 1
  | _ => 0

@[simp] theorem weight_askAdd (x y : Expr) : weight (askAdd x y) = depth x + 2 := rfl
@[simp] theorem weight_runAdd (x y : Expr) : weight (runAdd x y) = depth x + 1 := rfl
@[simp] theorem weight_outE (v : Expr) : weight (outE v) = 0 := rfl

/-- Only work rows weigh. -/
theorem place_of_weight {e : Expr} (pos : 0 < weight e) : place e = .work := by
  unfold weight at pos
  split at pos
  · rfl
  · rfl
  · omega

/-- **The rank of a state.** -/
def rank (C : Conf) : ℕ := ∑ o ∈ C.present, weight o.1

/-- **The rank across a firing**: the rows taken leave it, the rows made enter it. -/
theorem rank_fire {C : Conf} {ρ : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst ρ C) :
    rank (sel.result Prod.fst ρ C) + ∑ o ∈ sel.taken.toFinset, weight o.1 =
      rank C + ∑ o ∈ sel.made.toFinset, weight o.1 := by
  have takenSub : sel.taken.toFinset ⊆ C.present := valid.occurrences.taken_subset
  have fresh : Disjoint sel.made.toFinset C.present := valid.occurrences.fresh
  have apart : Disjoint (C.present \ sel.taken.toFinset) sel.made.toFinset :=
    fresh.symm.mono_left Finset.sdiff_subset
  show ∑ o ∈ (C.present \ sel.taken.toFinset) ∪ sel.made.toFinset, weight o.1 + _ = _
  rw [Finset.sum_union apart, add_right_comm, Finset.sum_sdiff takenSub]
  rfl

theorem single_taken {C : Conf} {ρ : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst ρ C) {t : Expr} (takes : ρ.take = [t]) :
    ∃ ot, sel.taken = [ot] ∧ ot.1 = t ∧ ot ∈ C.present := by
  have matched := takes_match valid
  rw [takes] at matched
  obtain ⟨ot, same, label⟩ := match_one matched
  exact ⟨ot, same, label.symm, taken_present valid (by rw [same]; exact List.mem_singleton_self _)⟩

theorem single_made {C : Conf} {ρ : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst ρ C) {p : Expr} (makes : ρ.produce = [p]) :
    ∃ om, sel.made = [om] ∧ om.1 = p ∧ om ∉ C.present := by
  have outputs := valid.outputs
  rw [makes] at outputs
  cases hm : sel.made with
  | nil =>
      rw [hm] at outputs
      simp at outputs
  | cons om rest =>
      rw [hm] at outputs
      cases rest with
      | cons _ _ => simp at outputs
      | nil =>
          have label : om.1 = p := by simpa using outputs
          have inMade : om ∈ (sel.commit (T := Expr)).made := by simp [Selection.commit, hm]
          exact ⟨om, rfl, label, Finset.disjoint_left.mp valid.occurrences.fresh inMade⟩

/-- A firing that takes one row and makes one changes the rank by their weights. -/
theorem rank_step {C : Conf} {ρ : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst ρ C) {t p : Expr} (takes : ρ.take = [t])
    (makes : ρ.produce = [p]) : rank (sel.result Prod.fst ρ C) + weight t = rank C + weight p := by
  obtain ⟨ot, takenEq, tLabel, -⟩ := single_taken valid takes
  obtain ⟨om, madeEq, pLabel, -⟩ := single_made valid makes
  have := rank_fire valid
  rw [takenEq, madeEq] at this
  simpa [tLabel, pLabel] using this

/-- **Every move of addition lowers the rank by one.** -/
theorem rank_lowers {C C' : Conf} (moved : addStep C C') : rank C' + 1 = rank C := by
  obtain ⟨ρ, sel, member, valid, rfl⟩ := addStep_iff.mp moved
  rcases mem_addProgram.mp member with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩
  · have := rank_step valid (t := askAdd x y) (p := runAdd x y) rfl rfl
    simp only [weight_askAdd, weight_runAdd] at this
    omega
  · have := rank_step valid (t := runAdd (succE x) y) (p := runAdd x (succE y)) rfl rfl
    simp only [weight_runAdd, depth_succE] at this
    omega
  · have := rank_step valid (t := runAdd zeroE y) (p := outE y) rfl rfl
    simp only [weight_runAdd, weight_outE, depth_zeroE] at this
    omega

/-- **Every run of addition is as long as the drop of the rank.** -/
theorem addRuns_length {n : ℕ} {C C' : Conf} (run : Runs addStep n C C') : n + rank C' = rank C :=
  Runs.length_eq rank (fun _ _ moved => rank_lowers moved) run

/-! ## States of one addition -/

/-- **The work region holds exactly one row**, the occurrence `o`. -/
def OnlyWork (C : Conf) (o : Occ) : Prop :=
  o ∈ C.present ∧ ∀ o' ∈ C.present, place o'.1 = .work → o' = o

/-- **A request**: consistent knowledge, the rows of both arguments present, the request the only
work row. -/
def Request (x y : Expr) (C : Conf) : Prop :=
  Plain C ∧ natRow x ∈ contents C ∧ natRow y ∈ contents C ∧ ∃ o, OnlyWork C o ∧ o.1 = askAdd x y

/-- The stages of one addition of `a` and `b`. -/
def Stage (a b : ℕ) (e : Expr) : Prop :=
  e = askAdd (numeral a) (numeral b) ∨ (∃ i j, i + j = a + b ∧ e = runAdd (numeral i) (numeral j)) ∨
    e = outE (numeral (a + b))

/-- **A state of one addition.** -/
def OnTheWay (a b : ℕ) (C : Conf) : Prop :=
  Plain C ∧ natRow (numeral a) ∈ contents C ∧ natRow (numeral b) ∈ contents C ∧
    ∃ o, OnlyWork C o ∧ Stage a b o.1

theorem rank_onlyWork {C : Conf} {o : Occ} (only : OnlyWork C o) : rank C = weight o.1 := by
  unfold rank
  rw [Finset.sum_eq_single_of_mem o only.1]
  intro o' present other
  by_contra pos
  exact other (only.2 o' present (place_of_weight (Nat.pos_of_ne_zero pos)))

theorem askAdd_inj {x y x' y' : Expr} (h : askAdd x y = askAdd x' y') : x = x' ∧ y = y' := by
  simp only [askAdd, Expr.app.injEq, true_and] at h
  exact h

theorem runAdd_inj {x y x' y' : Expr} (h : runAdd x y = runAdd x' y') : x = x' ∧ y = y' := by
  simp only [runAdd, Expr.app.injEq, true_and] at h
  exact h

theorem outE_inj {v v' : Expr} (h : outE v = outE v') : v = v' := by
  simp only [outE, Expr.app.injEq, true_and] at h
  exact h

theorem numeral_eq_succE {k : ℕ} {x : Expr} (h : numeral k = succE x) :
    ∃ k', k = k' + 1 ∧ x = numeral k' := by
  cases k with
  | zero => simp [numeral, zeroE, succE] at h
  | succ k' => exact ⟨k', rfl, (succE_injective h).symm⟩

theorem numeral_eq_zeroE {k : ℕ} (h : numeral k = zeroE) : k = 0 := by
  cases k with
  | zero => rfl
  | succ k' => simp [numeral, zeroE, succE] at h

/-- After a firing that takes the only work row and makes one, the made row is the only work row, and
every row outside the work region stays. -/
theorem onlyWork_after {C : Conf} {o : Occ} (only : OnlyWork C o) {ρ : RuleInstance Expr}
    {sel : Selection Occ} (valid : sel.Valid ground Prod.fst ρ C) {t p : Expr}
    (takes : ρ.take = [t]) (makes : ρ.produce = [p]) (tWork : place t = .work) :
    o.1 = t ∧ ∃ om, OnlyWork (sel.result Prod.fst ρ C) om ∧ om.1 = p ∧
      ∀ e, place e ≠ .work → e ∈ contents C → e ∈ contents (sel.result Prod.fst ρ C) := by
  obtain ⟨ot, takenEq, tLabel, otPresent⟩ := single_taken valid takes
  obtain ⟨om, madeEq, pLabel, -⟩ := single_made valid makes
  have same : ot = o := only.2 ot otPresent (by rw [tLabel]; exact tWork)
  rw [same] at takenEq tLabel
  refine ⟨tLabel, om, ⟨mem_fire.mpr (Or.inr (by simp [Selection.commit, madeEq])), ?_⟩, pLabel, ?_⟩
  · intro o' present work
    rcases mem_fire.mp present with ⟨old, notTaken⟩ | made
    · have isO : o' = o := only.2 o' old work
      exact (notTaken (by simp [Selection.commit, takenEq, isO])).elim
    · simpa [Selection.commit, madeEq] using made
  · rintro e notWork ⟨o', present, rfl⟩
    refine ⟨o', mem_fire.mpr (Or.inl ⟨present, fun taken => notWork ?_⟩), rfl⟩
    have isO : o' = o := by simpa [Selection.commit, takenEq] using taken
    rw [isO, tLabel]
    exact tWork

/-- **States of one addition are kept by its moves.** -/
theorem onTheWay_step {a b : ℕ} {C C' : Conf} (way : OnTheWay a b C) (moved : addStep C C') :
    OnTheWay a b C' := by
  obtain ⟨plain, hasA, hasB, o, only, stage⟩ := way
  obtain ⟨ρ, sel, member, valid, rfl⟩ := addStep_iff.mp moved
  have keepA := fun (after : ∀ e, place e ≠ .work → e ∈ contents C →
      e ∈ contents (sel.result Prod.fst ρ C)) => after _ (by simp) hasA
  have keepB := fun (after : ∀ e, place e ≠ .work → e ∈ contents C →
      e ∈ contents (sel.result Prod.fst ρ C)) => after _ (by simp) hasB
  rcases mem_addProgram.mp member with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨label, om, only', made, kept⟩ := onlyWork_after only valid (t := askAdd x y)
      (p := runAdd x y) rfl rfl rfl
    refine ⟨plain_of_valid valid, keepA kept, keepB kept, om, only', ?_⟩
    rcases stage with ask | ⟨i, j, _, run⟩ | out
    · obtain ⟨rfl, rfl⟩ := askAdd_inj (label.symm.trans ask)
      exact Or.inr (Or.inl ⟨a, b, rfl, made⟩)
    · simp [label, askAdd, runAdd] at run
    · simp [label, askAdd, outE] at out
  · obtain ⟨label, om, only', made, kept⟩ := onlyWork_after only valid
      (t := runAdd (succE x) y) (p := runAdd x (succE y)) rfl rfl rfl
    refine ⟨plain_of_valid valid, keepA kept, keepB kept, om, only', ?_⟩
    rcases stage with ask | ⟨i, j, sum, run⟩ | out
    · simp [label, askAdd, runAdd] at ask
    · obtain ⟨first, rfl⟩ := runAdd_inj (label.symm.trans run)
      obtain ⟨i', rfl, rfl⟩ := numeral_eq_succE first.symm
      exact Or.inr (Or.inl ⟨i', j + 1, by omega, made⟩)
    · simp [label, runAdd, outE] at out
  · obtain ⟨label, om, only', made, kept⟩ := onlyWork_after only valid
      (t := runAdd zeroE y) (p := outE y) rfl rfl rfl
    refine ⟨plain_of_valid valid, keepA kept, keepB kept, om, only', ?_⟩
    rcases stage with ask | ⟨i, j, sum, run⟩ | out
    · simp [label, askAdd, runAdd] at ask
    · obtain ⟨first, rfl⟩ := runAdd_inj (label.symm.trans run)
      have zero := numeral_eq_zeroE first.symm
      subst zero
      have total : j = a + b := by omega
      subst total
      exact Or.inr (Or.inr made)
    · simp [label, runAdd, outE] at out

/-- States of one addition are kept along runs. -/
theorem onTheWay_run {a b : ℕ} {C C' : Conf} (way : OnTheWay a b C)
    (run : Relation.ReflTransGen addStep C C') : OnTheWay a b C' := by
  induction run with
  | refl => exact way
  | tail _ moved ih => exact onTheWay_step ih moved

/-! ## Firing the rules -/

/-- **A rule that takes one row, reads some and makes one fires** where they are present. -/
theorem fires {C : Conf} (plain : Plain C) {ot : Occ} (present : ot ∈ C.present)
    {reads : List Occ} (readsPresent : ∀ o ∈ reads, o ∈ C.present) (apart : ot ∉ reads)
    {ρ : RuleInstance Expr} (takes : ρ.take = [ot.1]) (readsEq : ρ.read = reads.map Prod.fst)
    {p : Expr} (makes : ρ.produce = [p]) (noTells : ρ.tell = []) (noChecks : ρ.checks = []) :
    ∃ sel : Selection Occ, sel.Valid ground Prod.fst ρ C := by
  obtain ⟨om, fresh, labelled⟩ := ProgramAdequacy.occSupply C.present p
  refine ⟨⟨[ot], reads, [om]⟩, groundValid (List.nodup_singleton ot) (List.nodup_singleton om)
    (by rw [takes]; rfl) readsEq (by rw [makes]; simp [labelled]) ?_ plain noTells noChecks⟩
  refine ⟨by simp [Selection.commit, present], fun o member => ?_, by simp [Selection.commit, apart],
    by simp [Selection.commit, fresh], fun _ member => by simp [Selection.commit] at member⟩
  exact readsPresent o (List.mem_toFinset.mp (by simpa [Selection.commit] using member))

theorem weight_stage_pos {a b : ℕ} {e : Expr} (stage : Stage a b e)
    (notOut : e ≠ outE (numeral (a + b))) : 0 < weight e := by
  rcases stage with rfl | ⟨i, j, _, rfl⟩ | out
  · simp
  · simp
  · exact absurd out notOut

/-- **A state of one addition that has not answered can move.** -/
theorem step_exists {a b : ℕ} {C : Conf} (way : OnTheWay a b C) {o : Occ} (only : OnlyWork C o)
    (notOut : o.1 ≠ outE (numeral (a + b))) : ∃ C', addStep C C' := by
  obtain ⟨plain, hasA, hasB, o₀, only₀, stage⟩ := way
  have same : o₀ = o := only.2 o₀ only₀.1 (place_of_weight
    (by
      rcases stage with ask | ⟨i, j, _, run⟩ | out
      · rw [ask]; simp
      · rw [run]; simp
      · have : o₀ = o := only.2 o₀ only₀.1 (by rw [out]; rfl)
        rw [this] at out
        exact absurd out notOut))
  subst same
  rcases stage with ask | ⟨i, j, sum, run⟩ | out
  · obtain ⟨oa, presentA, labelA⟩ := hasA
    obtain ⟨ob, presentB, labelB⟩ := hasB
    have apart : o₀ ∉ [oa, ob] := by
      intro member
      rcases List.mem_cons.mp member with same | member
      · have := congrArg Prod.fst same
        rw [ask, labelA] at this
        simp [askAdd, natRow] at this
      · have := congrArg Prod.fst (List.mem_singleton.mp member)
        rw [ask, labelB] at this
        simp [askAdd, natRow] at this
    obtain ⟨sel, valid⟩ := fires plain only.1 (reads := [oa, ob])
      (fun o member => by
        rcases List.mem_cons.mp member with rfl | member
        · exact presentA
        · rw [List.mem_singleton.mp member]; exact presentB)
      apart (ρ := startRule (numeral a) (numeral b)) (by rw [ask]; rfl)
      (by simp [startRule, rule, labelA, labelB]) rfl rfl rfl
    exact ⟨_, addStep_iff.mpr ⟨_, sel, mem_addProgram.mpr (Or.inl ⟨_, _, rfl⟩), valid, rfl⟩⟩
  · cases i with
    | zero =>
        obtain ⟨sel, valid⟩ := fires plain only.1 (reads := []) (fun _ member => by simp at member)
          (by simp) (ρ := finishRule (numeral j)) (by rw [run]; rfl) rfl rfl rfl rfl
        exact ⟨_, addStep_iff.mpr ⟨_, sel, mem_addProgram.mpr (Or.inr (Or.inr ⟨_, rfl⟩)), valid,
          rfl⟩⟩
    | succ i =>
        obtain ⟨sel, valid⟩ := fires plain only.1 (reads := []) (fun _ member => by simp at member)
          (by simp) (ρ := peelRule (numeral i) (numeral j)) (by rw [run]; rfl) rfl rfl rfl rfl
        exact ⟨_, addStep_iff.mpr ⟨_, sel, mem_addProgram.mpr (Or.inr (Or.inl ⟨_, _, rfl⟩)),
          valid, rfl⟩⟩
  · exact absurd out notOut

/-- **The answer is final**: no move of addition takes it. -/
theorem out_final {C : Conf} {o : Occ} (only : OnlyWork C o) {v : Expr} (out : o.1 = outE v) :
    ∀ C', ¬ addStep C C' := by
  intro C' moved
  obtain ⟨ρ, sel, member, valid, rfl⟩ := addStep_iff.mp moved
  rcases mem_addProgram.mp member with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨label, -⟩ := onlyWork_after only valid (t := askAdd x y) (p := runAdd x y) rfl rfl rfl
    rw [out] at label
    simp [outE, askAdd] at label
  · obtain ⟨label, -⟩ := onlyWork_after only valid (t := runAdd (succE x) y)
      (p := runAdd x (succE y)) rfl rfl rfl
    rw [out] at label
    simp [outE, runAdd] at label
  · obtain ⟨label, -⟩ := onlyWork_after only valid (t := runAdd zeroE y) (p := outE y) rfl rfl rfl
    rw [out] at label
    simp [outE, runAdd] at label

/-- **From every state of one addition a run reaches the answer**, in as many moves as the rank. -/
theorem run_to_answer {a b : ℕ} : ∀ r : ℕ, ∀ C, OnTheWay a b C → rank C = r →
    ∃ C', Runs addStep r C C' ∧ ∃ o, OnlyWork C' o ∧ o.1 = outE (numeral (a + b))
  | 0, C, way, zero => by
      obtain ⟨_, _, _, o, only, stage⟩ := id way
      refine ⟨C, .refl C, o, only, ?_⟩
      by_contra notOut
      have := weight_stage_pos stage notOut
      rw [rank_onlyWork only] at zero
      omega
  | r + 1, C, way, ranked => by
      obtain ⟨_, _, _, o, only, -⟩ := id way
      have notOut : o.1 ≠ outE (numeral (a + b)) := by
        intro out
        rw [rank_onlyWork only, out] at ranked
        simp at ranked
      obtain ⟨C₁, moved⟩ := step_exists way only notOut
      have lowered := rank_lowers moved
      obtain ⟨C', run, answer⟩ := run_to_answer r C₁ (onTheWay_step way moved) (by omega)
      exact ⟨C', .cons moved run, answer⟩

/-! ## Addition on generated rows -/

theorem onTheWay_of_request {a b : ℕ} {C : Conf} (request : Request (numeral a) (numeral b) C) :
    OnTheWay a b C := by
  obtain ⟨plain, hasA, hasB, o, only, label⟩ := request
  exact ⟨plain, hasA, hasB, o, only, Or.inl label⟩

theorem rank_request {a b : ℕ} {C : Conf} (request : Request (numeral a) (numeral b) C) :
    rank C = a + 2 := by
  obtain ⟨_, _, _, o, only, label⟩ := request
  rw [rank_onlyWork only, label, weight_askAdd, depth_numeral]

/-- **Addition on generated rows**: for a request on two generated rows, every run has at most
`a + 2` moves, every final state reached holds exactly one work row, the value `a + b`, and a run of
`a + 2` moves reaches such a state. -/
theorem addition_on_generated {x y : Expr} (gx : Generated natRules ∅ (natRow x))
    (gy : Generated natRules ∅ (natRow y)) {C : Conf} (request : Request x y C) :
    ∃ a b, x = numeral a ∧ y = numeral b ∧
      (∀ n C', Runs addStep n C C' → n ≤ a + 2) ∧
      (∀ C', Relation.ReflTransGen addStep C C' → (∀ C'', ¬ addStep C' C'') →
        ∃ o, OnlyWork C' o ∧ o.1 = outE (numeral (a + b))) ∧
      ∃ C', Runs addStep (a + 2) C C' ∧ (∀ C'', ¬ addStep C' C'') ∧
        outE (numeral (a + b)) ∈ contents C' := by
  obtain ⟨a, hx⟩ := Numbers.natRules_generated_iff.mp gx
  obtain ⟨b, hy⟩ := Numbers.natRules_generated_iff.mp gy
  have xa : x = numeral a := natRow_injective hx
  have yb : y = numeral b := natRow_injective hy
  subst xa yb
  have way := onTheWay_of_request request
  refine ⟨a, b, rfl, rfl, fun n C' run => ?_, fun C' run final => ?_, ?_⟩
  · have := addRuns_length run
    rw [rank_request request] at this
    omega
  · obtain ⟨_, _, _, o, only, stage⟩ := onTheWay_run way run
    refine ⟨o, only, ?_⟩
    by_contra notOut
    obtain ⟨C'', moved⟩ := step_exists (onTheWay_run way run) only notOut
    exact final C'' moved
  · obtain ⟨C', run, o, only, out⟩ := run_to_answer (a + 2) C way (rank_request request)
    exact ⟨C', run, out_final only out, o, only.1, out⟩

/-- **The bound read from the stage**: when `natRow x` is in stage `m`, every run of a request on
`x` has at most `m + 1` moves. -/
theorem addition_bounded_by_stage {x y : Expr} {m : ℕ} (staged : natRow x ∈ stage natRules ∅ m)
    (gy : Generated natRules ∅ (natRow y)) {C : Conf} (request : Request x y C) {n : ℕ} {C' : Conf}
    (run : Runs addStep n C C') : n ≤ m + 1 := by
  have gx : Generated natRules ∅ (natRow x) :=
    (WhenTypesApply.TwoKinds.generated_iff_exists_stage natRules ∅ (natRow x)).mpr ⟨m, staged⟩
  obtain ⟨a, b, rfl, rfl, bounded, -, -⟩ := addition_on_generated gx gy request
  have below := (Numbers.numeral_mem_stage_iff a m).mp staged
  have := bounded n C' run
  omega

/-! ## Control: a row no constructor makes -/

/-- **On `natRow junkE` a run finishes without an answer**: the request starts, and some state reached
in one move has no move and no answer. -/
theorem junk_request_no_answer {y : Expr} {C : Conf} (request : Request junkE y C) :
    ∃ C', addStep C C' ∧ (∀ C'', ¬ addStep C' C'') ∧ ∀ v, outE v ∉ contents C' := by
  obtain ⟨plain, ⟨oa, presentA, labelA⟩, ⟨ob, presentB, labelB⟩, o, only, ask⟩ := request
  have apart : o ∉ [oa, ob] := by
    intro member
    rcases List.mem_cons.mp member with same | member
    · have := congrArg Prod.fst same
      rw [ask, labelA] at this
      simp [askAdd, natRow] at this
    · have := congrArg Prod.fst (List.mem_singleton.mp member)
      rw [ask, labelB] at this
      simp [askAdd, natRow] at this
  obtain ⟨sel, valid⟩ := fires plain only.1 (reads := [oa, ob])
    (fun o member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact presentA
      · rw [List.mem_singleton.mp member]; exact presentB)
    apart (ρ := startRule junkE y) (by rw [ask]; rfl)
    (by simp [startRule, rule, labelA, labelB]) rfl rfl rfl
  obtain ⟨-, om, only', made, -⟩ := onlyWork_after only valid (t := askAdd junkE y)
    (p := runAdd junkE y) rfl rfl rfl
  refine ⟨_, addStep_iff.mpr ⟨_, sel, mem_addProgram.mpr (Or.inl ⟨_, _, rfl⟩), valid, rfl⟩,
    fun C'' moved => ?_, fun v ⟨o', present, label⟩ => ?_⟩
  · obtain ⟨ρ, sel', member, valid', rfl⟩ := addStep_iff.mp moved
    rcases mem_addProgram.mp member with ⟨x', y', rfl⟩ | ⟨x', y', rfl⟩ | ⟨y', rfl⟩
    · obtain ⟨label, -⟩ := onlyWork_after only' valid' (t := askAdd x' y') (p := runAdd x' y')
        rfl rfl rfl
      rw [made] at label
      simp [askAdd, runAdd] at label
    · obtain ⟨label, -⟩ := onlyWork_after only' valid' (t := runAdd (succE x') y')
        (p := runAdd x' (succE y')) rfl rfl rfl
      rw [made] at label
      simp [runAdd, succE, junkE] at label
    · obtain ⟨label, -⟩ := onlyWork_after only' valid' (t := runAdd zeroE y') (p := outE y')
        rfl rfl rfl
      rw [made] at label
      simp [runAdd, zeroE, junkE] at label
  · have isOm : o' = om := only'.2 o' present (by rw [label]; rfl)
    rw [isOm, made] at label
    simp [runAdd, outE] at label

end Recursion

#print axioms Recursion.Runs.length_eq
#print axioms Recursion.adder_writes
#print axioms Recursion.ownerAndAdder_facts
#print axioms Recursion.rank_lowers
#print axioms Recursion.onTheWay_step
#print axioms Recursion.step_exists
#print axioms Recursion.out_final
#print axioms Recursion.run_to_answer
#print axioms Recursion.addition_on_generated
#print axioms Recursion.addition_bounded_by_stage
#print axioms Recursion.junk_request_no_answer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes
