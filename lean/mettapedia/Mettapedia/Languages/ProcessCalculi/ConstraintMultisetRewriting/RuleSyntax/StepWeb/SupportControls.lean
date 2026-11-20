import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.SupportSimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Controls for the support simulation

The two constructions are those of `SupportSimulation`. The one-match step of a program: a bag store
of labelled occurrences, one match per firing, guards asked after the firing's own tells, a fixed set
of rules, one equation store kept whole. The one-match set step: a set store of rows with the
knowledge solved away, one match per step, guards after or before the tells, the same fixed rules.

Small closed examples over first-order atoms (numerals as constants and as unknowns, no function
symbols), at the one frame, with natural numbers as occurrence identities unless said otherwise. The
row `a` is the constant `1`, the row `b` the constant `2`, and `x` is an unknown. Firings are built by
hand and admitted by evaluation, so the controls do not depend on the simulation theorems they test.

* **Stuttering is needed** (`again_stutters`): the propagation rule that reads `a` and makes `a` fires
  at one occurrence of `a`; its support stays `{a}`, and the set store has no step from `{a}` to
  itself.
* **A stutter through the knowledge** (`copy_stutters`): the propagation rule that reads any `x` and
  makes `x` fires with its unknown opened, so the new occurrence is labelled by the unknown, which the
  knowledge equates with `a`: the unknown is a label of the state and not a row of its support.
* **A step that changes the support** (`grow_steps`): reading `a` and making `b` maps to the one-match
  set step from `{a}` to `{a, b}`; the state it reaches is completed, the seed is not
  (`grow_completed`).
* **Two reads, one occurrence** (`twice_reads_one_occurrence`): a rule reading `a` twice fires where
  `a` occurs once, both reads selecting that occurrence, and maps to a one-match set step. Reads do
  not separate the bag store from the set store.
* **Counts separate them** (`count_breaks_support`): outside the fragment, a guard asking for exactly
  two rows `a` holds at two occurrences, and the bag step adds `b`; the set store holds one copy of
  `a`, the guard fails there, and the set store has no step from `{a}`.
* **Taking one of two equal copies** (`takeOne_stutters`): outside the fragment, a firing that takes
  one of two occurrences of `a` leaves the support `{a}`.
* **Taking two equal copies** (`takeTwo_breaks_support`): a firing that takes both occurrences of `a`
  empties the support, which is not a stutter, and the set store has no step from `{a}` at all
  (`takeTwo_no_set_step`): the one row cannot be taken twice. So no support simulation holds once
  rules consume (`no_support_simulation`), and positive rules, which may take, do not suffice
  (`positive_does_not_suffice`).
* **Identities that run out** (`identities_needed`): with one occurrence identity, already used,
  nothing fires, so the state is completed while its support is not closed.
* **Unknowns that run out** (`unknowns_needed`): with one unknown, once the knowledge mentions it no
  rule can be opened freshly (`no_fresh_opening`), so the state is completed while its support is not
  closed, although occurrence identities are infinitely many.
* **Divergence** (`again_diverges`): the bag store runs forever from one occurrence of `a`, while the
  set store has no step from `{a}`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Support.Controls

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open SetStoreSyntax
open LogicOverTheStep.StepSpan (Succ)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)

/-! ## Rows, rules and states -/

/-- The row `a`. -/
def a : Term atoms := .const 1

/-- The row `b`. -/
def b : Term atoms := .const 2

/-- An unknown. -/
def x : Term atoms := .var 0

/-- Read `a`, make `a`. -/
def again : Rule (Terms (Term atoms)) := ⟨PUnit.unit, ⟨[], [a], [], [], [a]⟩, []⟩

/-- Read any `x`, make `x`. -/
def copy : Rule (Terms (Term atoms)) := ⟨PUnit.unit, ⟨[], [x], [], [], [x]⟩, []⟩

/-- Read `a`, make `b`. -/
def grow : Rule (Terms (Term atoms)) := ⟨PUnit.unit, ⟨[], [a], [], [], [b]⟩, []⟩

/-- Take one `a`. -/
def takeOne : Rule (Terms (Term atoms)) := ⟨PUnit.unit, ⟨[a], [], [], [], []⟩, []⟩

/-- Take two `a`. -/
def takeTwo : Rule (Terms (Term atoms)) := ⟨PUnit.unit, ⟨[a, a], [], [], [], []⟩, []⟩

def againProgram : Program (Terms (Term atoms)) := {again}
def copyProgram : Program (Terms (Term atoms)) := {copy}
def growProgram : Program (Terms (Term atoms)) := {grow}
def takeOneProgram : Program (Terms (Term atoms)) := {takeOne}
def takeTwoProgram : Program (Terms (Term atoms)) := {takeTwo}

/-- One occurrence of `a`. -/
def oneA : State (Terms (Term atoms)) ℕ := ⟨PUnit.unit, [], {0}, fun _ => a⟩

/-- Two occurrences of `a`. -/
def twoA : State (Terms (Term atoms)) ℕ := ⟨PUnit.unit, [], {0, 1}, fun _ => a⟩

theorem a_ground : a.isGround := trivial

theorem b_ground : b.isGround := trivial

theorem b_ne_a : b ≠ a := fun same => absurd (Term.const.inj same) (by decide)

theorem x_ne_a : x ≠ a := fun same => by cases same

/-! ## Which rules propagate -/

theorem again_propagates : Propagates again :=
  ⟨rfl, rfl, ⟨fun _ inside => (by cases inside), rfl⟩, fun _ inside => inside,
    by simp [again, varsIn]⟩

theorem copy_propagates : Propagates copy :=
  ⟨rfl, rfl, ⟨fun _ inside => (by cases inside), rfl⟩, fun _ inside => inside,
    by simp [copy, varsIn]⟩

theorem grow_propagates : Propagates grow :=
  ⟨rfl, rfl, ⟨fun _ inside => (by cases inside), rfl⟩,
    by simp [grow, varsIn, a, b, Term.freeVars], by simp [grow, varsIn]⟩

theorem again_pure : ∀ r ∈ againProgram, Propagates r := by
  intro r member
  obtain rfl := Set.mem_singleton_iff.mp member
  exact again_propagates

theorem copy_pure : ∀ r ∈ copyProgram, Propagates r := by
  intro r member
  obtain rfl := Set.mem_singleton_iff.mp member
  exact copy_propagates

theorem grow_pure : ∀ r ∈ growProgram, Propagates r := by
  intro r member
  obtain rfl := Set.mem_singleton_iff.mp member
  exact grow_propagates

/-- **Taking is outside the fragment**, while the rules that take are positive. -/
theorem takers_positive_not_propagating :
    Scope.Positive takeOne ∧ ¬ Propagates takeOne ∧ Scope.Positive takeTwo ∧ ¬ Propagates takeTwo :=
  ⟨⟨fun _ inside => (by cases inside), rfl⟩, fun pure => List.cons_ne_nil _ _ pure.noTake,
    ⟨fun _ inside => (by cases inside), rfl⟩, fun pure => List.cons_ne_nil _ _ pure.noTake⟩

/-! ## Admission by evaluation -/

/-- A rule whose terms are constants is opened freshly by any opening (the tree's `fresh_of_ground`). -/
theorem fresh_of_constants {O : Type} {Q : Program (Terms (Term atoms))}
    (s : State (Terms (Term atoms)) O) (g : Firing O (E (signature := atoms)) Q s.frame)
    (constants : ∀ t ∈ g.rule.terms, t.isGround) : g.Fresh X s :=
  Examples.fresh_of_ground (FirstOrder.action atoms) s g fun t inside σ =>
    FirstOrder.ground_fixed σ t (constants t inside)

/-- Every term of these rules is the row `a` or the row `b`. -/
theorem constants_of_rows (r : Rule (Terms (Term atoms)))
    (rows : ∀ t ∈ r.terms, t = a ∨ t = b) : ∀ t ∈ r.terms, t.isGround := by
  intro t inside
  rcases rows t inside with rfl | rfl
  · exact a_ground
  · exact b_ground

theorem again_rows : ∀ t ∈ again.terms, t = a ∨ t = b := by
  intro t inside
  simp [again, Rule.terms] at inside
  exact Or.inl inside

theorem grow_rows : ∀ t ∈ grow.terms, t = a ∨ t = b := by
  intro t inside
  simp [grow, Rule.terms] at inside
  exact inside

theorem takeOne_rows : ∀ t ∈ takeOne.terms, t = a ∨ t = b := by
  intro t inside
  simp [takeOne, Rule.terms] at inside
  exact Or.inl inside

theorem takeTwo_rows : ∀ t ∈ takeTwo.terms, t = a ∨ t = b := by
  intro t inside
  simp [takeTwo, Rule.terms] at inside
  exact Or.inl inside

/-- The support of a state whose knowledge equates equal terms and whose rows are constants. -/
theorem support_of_constants {O : Type} (s : State (Terms (Term atoms)) O)
    (consistent : ∀ e ∈ s.knowledge, e.1 = e.2) (ground : ∀ o ∈ s.present, (s.label o).isGround) :
    support s = s.present.image s.label :=
  support_of_ground ⟨Subst.id atoms, fun e inside => congrArg _ (consistent e inside)⟩ ground

theorem oneA_support : support oneA = {a} := by
  rw [support_of_constants oneA (fun _ inside => by cases inside) fun _ _ => a_ground]
  exact Finset.image_singleton _ _

theorem twoA_support : support twoA = {a} := by
  rw [support_of_constants twoA (fun _ inside => by cases inside) fun _ _ => a_ground]
  exact Finset.image_const (Finset.insert_nonempty 0 {1}) a

theorem oneA_settled : Settled oneA :=
  settled_of_ground ⟨Subst.id atoms, fun _ inside => by cases inside⟩ fun _ _ => a_ground

/-! ## (a) Stuttering is needed -/

def againFiring : Firing ℕ (E (signature := atoms)) againProgram PUnit.unit :=
  ⟨again, rfl, PUnit.unit, Subst.id atoms, ⟨[], [0], [1]⟩, []⟩

theorem againFiring_admitted : againFiring.Admits X oneA := by
  have info : againFiring.information X oneA = [(a, a)] := rfl
  refine ⟨⟨fresh_of_constants oneA againFiring (constants_of_rows again again_rows), by decide,
    by decide, rfl, rfl, rfl, rfl⟩, by decide, ⟨PUnit.unit, Subst.id atoms, ?_⟩,
    fun _ _ _ => ⟨fun _ inside => (by cases inside), fun _ inside => (by cases inside)⟩⟩
  rw [info]
  intro e inside
  rw [List.mem_singleton] at inside
  subst inside
  rfl

theorem againFiring_labels (o : ℕ) : (againFiring.result X oneA).label o = a := by
  change (if o = 1 then (Subst.id atoms).applyTerm a else (Subst.id atoms).applyTerm a) = a
  split <;> rfl

theorem againFiring_present : (againFiring.result X oneA).present = {0, 1} := by decide

theorem againFiring_support : support (againFiring.result X oneA) = {a} := by
  rw [support_of_constants (againFiring.result X oneA) (fun e inside => by
      rw [show (againFiring.result X oneA).knowledge = [(a, a)] from rfl, List.mem_singleton] at inside
      subst inside
      rfl)
    (fun o _ => by rw [againFiring_labels]; exact a_ground), againFiring_present]
  rw [show (againFiring.result X oneA).label = fun _ => a from funext againFiring_labels]
  exact Finset.image_const (Finset.insert_nonempty 0 {1}) a

/-- **(a) Stuttering is needed.** Inside the fragment, a bag step whose made row is already present
leaves the support unchanged, and the set store has no step from that support to itself. -/
theorem again_stutters (timing : SetStore.AskTiming) :
    Succ (step X ℕ E againProgram).toStep oneA (againFiring.result X oneA) ∧
      support (againFiring.result X oneA) = support oneA ∧
      ¬ SetStore.Step timing againProgram (support oneA) (support (againFiring.result X oneA)) := by
  refine ⟨⟨againFiring, againFiring_admitted, rfl⟩, by rw [againFiring_support, oneA_support], ?_⟩
  rw [againFiring_support, oneA_support]
  exact SetStore.self_is_not_step timing {a}

/-! ## A stutter through the knowledge -/

def copyFiring : Firing ℕ (E (signature := atoms)) copyProgram PUnit.unit :=
  ⟨copy, rfl, PUnit.unit, Subst.id atoms, ⟨[], [0], [1]⟩, []⟩

/-- The constant instantiation, sending every unknown to `a`. -/
def toA : Subst atoms := fun _ => a

theorem copyFiring_fresh : copyFiring.Fresh X oneA := by
  intro _ g h
  refine ⟨h, fun t mentioned => ?_, fun t _ => ?_⟩
  · obtain (known | known | ⟨o, _, rfl⟩) := mentioned
    · cases known
    · cases known
    · rfl
  · change h.applyTerm ((Subst.id atoms).applyTerm t) = h.applyTerm t
    rw [Subst.applyTerm_id]

theorem copyFiring_admitted : copyFiring.Admits X oneA := by
  have info : copyFiring.information X oneA = [(x, a)] := rfl
  refine ⟨⟨copyFiring_fresh, by decide, by decide, rfl, rfl, rfl, rfl⟩, by decide,
    ⟨PUnit.unit, toA, ?_⟩,
    fun _ _ _ => ⟨fun _ inside => (by cases inside), fun _ inside => (by cases inside)⟩⟩
  rw [info]
  intro e inside
  rw [List.mem_singleton] at inside
  subst inside
  rfl

theorem copyFiring_present : (copyFiring.result X oneA).present = {0, 1} := by decide

/-- **A stutter through the knowledge.** The made occurrence is labelled by the opened unknown `x`;
the knowledge equates `x` with `a`, so `x` is a label of the state reached and not a row of its
support, which stays `{a}`. -/
theorem copy_stutters :
    Succ (step X ℕ E copyProgram).toStep oneA (copyFiring.result X oneA) ∧
      support (copyFiring.result X oneA) = {a} ∧
      x ∈ (copyFiring.result X oneA).present.image (copyFiring.result X oneA).label ∧
      x ∉ support (copyFiring.result X oneA) := by
  have settled := result_settled copyFiring copy_pure oneA_settled copyFiring_admitted
  have solves : (FirstOrder.action atoms).Models toA (copyFiring.result X oneA).knowledge := by
    change (FirstOrder.action atoms).Models toA [(x, a)]
    intro e inside
    rw [List.mem_singleton] at inside
    subst inside
    rfl
  have reads : ∀ o, toA.applyTerm ((copyFiring.result X oneA).label o) = a := by
    intro o
    change toA.applyTerm (if o = 1 then (Subst.id atoms).applyTerm x
      else (Subst.id atoms).applyTerm a) = a
    split <;> rfl
  have supportEq : support (copyFiring.result X oneA) = {a} := by
    rw [support_eq_of_models settled solves, copyFiring_present]
    rw [show (fun o => toA.applyTerm ((copyFiring.result X oneA).label o)) = fun _ => a from
      funext reads]
    exact Finset.image_const (Finset.insert_nonempty 0 {1}) a
  refine ⟨⟨copyFiring, copyFiring_admitted, rfl⟩, supportEq, ?_, ?_⟩
  · rw [copyFiring_present]
    exact Finset.mem_image.mpr ⟨1, by decide, rfl⟩
  · rw [supportEq, Finset.mem_singleton]
    exact x_ne_a

/-! ## A step that changes the support -/

def growFiring : Firing ℕ (E (signature := atoms)) growProgram PUnit.unit :=
  ⟨grow, rfl, PUnit.unit, Subst.id atoms, ⟨[], [0], [1]⟩, []⟩

theorem growFiring_admitted : growFiring.Admits X oneA := by
  have info : growFiring.information X oneA = [(a, a)] := rfl
  refine ⟨⟨fresh_of_constants oneA growFiring (constants_of_rows grow grow_rows), by decide,
    by decide, rfl, rfl, rfl, rfl⟩, by decide, ⟨PUnit.unit, Subst.id atoms, ?_⟩,
    fun _ _ _ => ⟨fun _ inside => (by cases inside), fun _ inside => (by cases inside)⟩⟩
  rw [info]
  intro e inside
  rw [List.mem_singleton] at inside
  subst inside
  rfl

theorem growFiring_present : (growFiring.result X oneA).present = {0, 1} := by decide

theorem growFiring_support : support (growFiring.result X oneA) = {a, b} := by
  have labels : ∀ o, (growFiring.result X oneA).label o = if o = 1 then b else a := by
    intro o
    change (if o = 1 then (Subst.id atoms).applyTerm b else (Subst.id atoms).applyTerm a) = _
    split <;> rfl
  rw [support_of_constants (growFiring.result X oneA) (fun e inside => by
      rw [show (growFiring.result X oneA).knowledge = [(a, a)] from rfl, List.mem_singleton] at inside
      subst inside
      rfl)
    (fun o _ => by rw [labels]; split; exacts [b_ground, a_ground]), growFiring_present]
  rw [Finset.image_insert, Finset.image_singleton, labels, labels]
  rfl

/-- The one ground instance of `grow`: every instance reads `{a}` and makes `{b}`. -/
theorem grow_instance (m : GroundMatch growProgram) :
    (consequence m).read = {a} ∧ (consequence m).made = {b} := by
  have rule : m.rule = grow := m.member
  have fixed : ∀ t : Term atoms, t.isGround → m.assignment.applyTerm t = t :=
    fun t ground => FirstOrder.ground_fixed _ t ground
  constructor
  · change (m.rule.body.read.map m.assignment.applyTerm).toFinset = {a}
    rw [rule]
    change ([m.assignment.applyTerm a]).toFinset = {a}
    rw [fixed a a_ground]
    simp
  · change (m.rule.body.produce.map m.assignment.applyTerm).toFinset = {b}
    rw [rule]
    change ([m.assignment.applyTerm b]).toFinset = {b}
    rw [fixed b b_ground]
    simp

/-- **A step that changes the support** maps to the one-match set step from `{a}` to `{a, b}`. -/
theorem grow_steps (timing : SetStore.AskTiming) :
    Succ (step X ℕ E growProgram).toStep oneA (growFiring.result X oneA) ∧
      DisciplinedStep .one timing growProgram {a} {a, b} := by
  have moved : Succ (step X ℕ E growProgram).toStep oneA (growFiring.result X oneA) :=
    ⟨growFiring, growFiring_admitted, rfl⟩
  refine ⟨moved, ?_⟩
  obtain ⟨-, same | next⟩ := forward_step timing grow_pure oneA_settled moved
  · rw [growFiring_support, oneA_support] at same
    exact absurd (same ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)) fun inside =>
      b_ne_a (Finset.mem_singleton.mp inside)
  · rwa [growFiring_support, oneA_support] at next

/-- **Completed and not completed.** The state that `grow` reaches is completed; the seed is not. -/
theorem grow_completed :
    Completed growProgram (growFiring.result X oneA) ∧ ¬ Completed growProgram oneA := by
  constructor
  · apply completed_of_closed grow_pure
      (result_settled growFiring grow_pure oneA_settled growFiring_admitted)
    intro m _
    rw [(grow_instance m).2, growFiring_support]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  · intro completed
    have same := completed (growFiring.result X oneA) ⟨growFiring, growFiring_admitted, rfl⟩
    rw [growFiring_support, oneA_support] at same
    have inside : b ∈ ({a} : Finset (Term atoms)) :=
      same ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    exact b_ne_a (Finset.mem_singleton.mp inside)

/-! ## Two reads, one occurrence -/

/-- Read `a` twice, make `b`. -/
def twice : Rule (Terms (Term atoms)) := ⟨PUnit.unit, ⟨[], [a, a], [], [], [b]⟩, []⟩

def twiceProgram : Program (Terms (Term atoms)) := {twice}

theorem twice_propagates : Propagates twice :=
  ⟨rfl, rfl, ⟨fun _ inside => (by cases inside), rfl⟩,
    by simp [twice, varsIn, a, b, Term.freeVars], by simp [twice, varsIn]⟩

theorem twice_pure : ∀ r ∈ twiceProgram, Propagates r := by
  intro r member
  obtain rfl := Set.mem_singleton_iff.mp member
  exact twice_propagates

theorem twice_rows : ∀ t ∈ twice.terms, t = a ∨ t = b := by
  intro t inside
  simp [twice, Rule.terms] at inside
  exact inside

/-- Both read patterns select the one occurrence `0`. -/
def twiceFiring : Firing ℕ (E (signature := atoms)) twiceProgram PUnit.unit :=
  ⟨twice, rfl, PUnit.unit, Subst.id atoms, ⟨[], [0, 0], [1]⟩, []⟩

theorem twiceFiring_admitted : twiceFiring.Admits X oneA := by
  have info : twiceFiring.information X oneA = [(a, a), (a, a)] := rfl
  refine ⟨⟨fresh_of_constants oneA twiceFiring (constants_of_rows twice twice_rows), by decide,
    by decide, rfl, rfl, rfl, rfl⟩, by decide, ⟨PUnit.unit, Subst.id atoms, ?_⟩,
    fun _ _ _ => ⟨fun _ inside => (by cases inside), fun _ inside => (by cases inside)⟩⟩
  rw [info]
  intro e inside
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at inside
  subst inside
  rfl

theorem twiceFiring_present : (twiceFiring.result X oneA).present = {0, 1} := by decide

theorem twiceFiring_support : support (twiceFiring.result X oneA) = {a, b} := by
  have labels : ∀ o, (twiceFiring.result X oneA).label o = if o = 1 then b else a := by
    intro o
    change (if o = 1 then (Subst.id atoms).applyTerm b else (Subst.id atoms).applyTerm a) = _
    split <;> rfl
  rw [support_of_constants (twiceFiring.result X oneA) (fun e inside => by
      rw [show (twiceFiring.result X oneA).knowledge = [(a, a), (a, a)] from rfl] at inside
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at inside
      subst inside
      rfl)
    (fun o _ => by rw [labels]; split; exacts [b_ground, a_ground]), twiceFiring_present]
  rw [Finset.image_insert, Finset.image_singleton, labels, labels]
  rfl

/-- **Two reads, one occurrence.** Both read patterns of `twice` select the one occurrence of `a`, the
bag step fires, and it maps to the one-match set step from `{a}` to `{a, b}`: reads do not separate the
bag store from the set store. -/
theorem twice_reads_one_occurrence (timing : SetStore.AskTiming) :
    twiceFiring.selection.read = [0, 0] ∧
      Succ (step X ℕ E twiceProgram).toStep oneA (twiceFiring.result X oneA) ∧
      DisciplinedStep .one timing twiceProgram {a} {a, b} := by
  have moved : Succ (step X ℕ E twiceProgram).toStep oneA (twiceFiring.result X oneA) :=
    ⟨twiceFiring, twiceFiring_admitted, rfl⟩
  refine ⟨rfl, moved, ?_⟩
  obtain ⟨-, same | next⟩ := forward_step timing twice_pure oneA_settled moved
  · rw [twiceFiring_support, oneA_support] at same
    have inside : b ∈ ({a} : Finset (Term atoms)) :=
      same ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    exact absurd (Finset.mem_singleton.mp inside) b_ne_a
  · rwa [twiceFiring_support, oneA_support] at next

/-! ## (b) Taking one of two equal copies -/

def takeOneFiring : Firing ℕ (E (signature := atoms)) takeOneProgram PUnit.unit :=
  ⟨takeOne, rfl, PUnit.unit, Subst.id atoms, ⟨[0], [], []⟩, []⟩

theorem takeOneFiring_admitted : takeOneFiring.Admits X twoA := by
  have info : takeOneFiring.information X twoA = [(a, a)] := rfl
  refine ⟨⟨fresh_of_constants twoA takeOneFiring (constants_of_rows takeOne takeOne_rows), by decide,
    by decide, rfl, rfl, rfl, rfl⟩, by decide, ⟨PUnit.unit, Subst.id atoms, ?_⟩,
    fun _ _ _ => ⟨fun _ inside => (by cases inside), fun _ inside => (by cases inside)⟩⟩
  rw [info]
  intro e inside
  rw [List.mem_singleton] at inside
  subst inside
  rfl

theorem takeOneFiring_present : (takeOneFiring.result X twoA).present = {1} := by decide

/-- **(b) Taking one of two equal copies projects to a stutter**: the support stays `{a}`. -/
theorem takeOne_stutters :
    Succ (step X ℕ E takeOneProgram).toStep twoA (takeOneFiring.result X twoA) ∧
      support (takeOneFiring.result X twoA) = support twoA := by
  refine ⟨⟨takeOneFiring, takeOneFiring_admitted, rfl⟩, ?_⟩
  rw [twoA_support, support_of_constants (takeOneFiring.result X twoA) (fun e inside => by
      rw [show (takeOneFiring.result X twoA).knowledge = [(a, a)] from rfl, List.mem_singleton] at inside
      subst inside
      rfl)
    (fun _ _ => a_ground), takeOneFiring_present]
  exact Finset.image_singleton _ _

/-! ## (c) Taking two equal copies -/

def takeTwoFiring : Firing ℕ (E (signature := atoms)) takeTwoProgram PUnit.unit :=
  ⟨takeTwo, rfl, PUnit.unit, Subst.id atoms, ⟨[0, 1], [], []⟩, []⟩

theorem takeTwoFiring_admitted : takeTwoFiring.Admits X twoA := by
  have info : takeTwoFiring.information X twoA = [(a, a), (a, a)] := rfl
  refine ⟨⟨fresh_of_constants twoA takeTwoFiring (constants_of_rows takeTwo takeTwo_rows), by decide,
    by decide, rfl, rfl, rfl, rfl⟩, by decide, ⟨PUnit.unit, Subst.id atoms, ?_⟩,
    fun _ _ _ => ⟨fun _ inside => (by cases inside), fun _ inside => (by cases inside)⟩⟩
  rw [info]
  intro e inside
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at inside
  subst inside
  rfl

theorem takeTwoFiring_present : (takeTwoFiring.result X twoA).present = ∅ := by decide

theorem takeTwoFiring_support : support (takeTwoFiring.result X twoA) = ∅ := by
  rw [support_of_constants (takeTwoFiring.result X twoA) (fun e inside => by
      rw [show (takeTwoFiring.result X twoA).knowledge = [(a, a), (a, a)] from rfl] at inside
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at inside
      subst inside
      rfl)
    (fun _ _ => a_ground), takeTwoFiring_present]
  rfl

/-- **The set store has no step from `{a}` for a rule that takes two `a`**: the one row is one
occurrence, and a firing takes distinct occurrences. -/
theorem takeTwo_no_set_step (timing : SetStore.AskTiming) (after : Finset (Term atoms)) :
    ¬ SetStore.Step timing takeTwoProgram {a} after := by
  rintro ⟨candidate, nonempty, admitted, -⟩
  have yes := SetStore.admitted_after admitted
  obtain ⟨member, inside⟩ := List.exists_mem_of_ne_nil candidate.members nonempty
  have rule : member.rule = takeTwo := member.member
  have takeLength : member.selection.taken.length = 2 := by
    rw [← (yes.1.2.2.2 member inside).1, rule]
    rfl
  have nodup : member.selection.taken.Nodup := (List.nodup_flatMap.mp yes.1.2.1).1 member inside
  have within : member.selection.taken.toFinset ⊆
      (SetStore.represent ({a} : Finset (Term atoms))).present :=
    (JointFirings.Bag.enabled_member yes.2.1 inside).taken_subset
  have card := Finset.card_le_card within
  rw [List.toFinset_card_of_nodup nodup, takeLength] at card
  have single : (SetStore.represent ({a} : Finset (Term atoms))).present.card = 1 := by
    simp [SetStore.represent]
  omega

/-- **(c) Taking two equal copies breaks the support.** The bag step empties the support, which is not
a stutter, and the set store has no step from `{a}`. -/
theorem takeTwo_breaks_support (timing : SetStore.AskTiming) :
    Succ (step X ℕ E takeTwoProgram).toStep twoA (takeTwoFiring.result X twoA) ∧
      support twoA = {a} ∧ support (takeTwoFiring.result X twoA) = ∅ ∧
      ∀ after, ¬ SetStore.Step timing takeTwoProgram {a} after :=
  ⟨⟨takeTwoFiring, takeTwoFiring_admitted, rfl⟩, twoA_support, takeTwoFiring_support,
    takeTwo_no_set_step timing⟩

/-- **No support simulation once rules consume.** -/
theorem no_support_simulation (timing : SetStore.AskTiming) :
    ¬ ∀ s s' : State (Terms (Term atoms)) ℕ, Succ (step X ℕ E takeTwoProgram).toStep s s' →
      support s' = support s ∨ SetStore.Step timing takeTwoProgram (support s) (support s') := by
  intro simulation
  rcases simulation twoA (takeTwoFiring.result X twoA) ⟨takeTwoFiring, takeTwoFiring_admitted, rfl⟩
    with same | moved
  · rw [takeTwoFiring_support, twoA_support] at same
    exact Finset.singleton_ne_empty a same.symm
  · rw [takeTwoFiring_support, twoA_support] at moved
    exact takeTwo_no_set_step timing ∅ moved

/-- **(d) Positive rules do not suffice**: every rule of the program is positive, none propagates, and
the support simulation fails. -/
theorem positive_does_not_suffice (timing : SetStore.AskTiming) :
    (∀ r ∈ takeTwoProgram, Scope.Positive r) ∧ (∀ r ∈ takeTwoProgram, ¬ Propagates r) ∧
      ¬ ∀ s s' : State (Terms (Term atoms)) ℕ, Succ (step X ℕ E takeTwoProgram).toStep s s' →
        support s' = support s ∨ SetStore.Step timing takeTwoProgram (support s) (support s') := by
  refine ⟨fun r member => ?_, fun r member => ?_, no_support_simulation timing⟩
  · obtain rfl := Set.mem_singleton_iff.mp member
    exact takers_positive_not_propagating.2.2.1
  · obtain rfl := Set.mem_singleton_iff.mp member
    exact takers_positive_not_propagating.2.2.2

/-! ## Counts separate the bag store from the set store -/

/-- Read `a` when exactly two rows match `a`, make `b`. -/
def countTwo : Rule (Terms (Term atoms)) := ⟨PUnit.unit, ⟨[], [a], [], [.count a 2], [b]⟩, []⟩

def countProgram : Program (Terms (Term atoms)) := {countTwo}

/-- A count guard is not an equation: the rule is not positive. -/
theorem countTwo_not_positive : ¬ Scope.Positive countTwo := by
  rintro ⟨equations, -⟩
  obtain ⟨_, _, same⟩ := equations (.count a 2) List.mem_cons_self
  cases same

theorem countTwo_rows : ∀ t ∈ countTwo.terms, t = a ∨ t = b := by
  intro t inside
  simp [countTwo, Rule.terms, checkTerms] at inside
  exact inside

def countFiring : Firing ℕ (E (signature := atoms)) countProgram PUnit.unit :=
  ⟨countTwo, rfl, PUnit.unit, Subst.id atoms, ⟨[], [0], [2]⟩, []⟩

theorem countFiring_admitted : countFiring.Admits X twoA := by
  have info : countFiring.information X twoA = [(a, a)] := rfl
  refine ⟨⟨fresh_of_constants twoA countFiring (constants_of_rows countTwo countTwo_rows), by decide,
    by decide, rfl, rfl, rfl, rfl⟩, by decide, ⟨PUnit.unit, Subst.id atoms, ?_⟩, ?_⟩
  · rw [info]
    intro e inside
    rw [List.mem_singleton] at inside
    subst inside
    rfl
  · intro b τ _
    cases b
    refine ⟨fun c inside => ?_, fun _ inside => (by cases inside)⟩
    change c ∈ [Check.count ((Subst.id atoms).applyTerm a) 2] at inside
    rw [List.mem_singleton] at inside
    subst inside
    change (matchesAt X (a := PUnit.unit) (b := PUnit.unit) τ (countFiring.row X twoA) twoA.present
      ((Subst.id atoms).applyTerm a)).card = 2
    have whole : matchesAt X (a := PUnit.unit) (b := PUnit.unit) τ (countFiring.row X twoA)
        twoA.present ((Subst.id atoms).applyTerm a) = twoA.present := by
      classical
      apply Finset.filter_true_of_mem
      intro _ _
      rfl
    rw [whole]
    decide

/-- **The set store has no step from `{a}` for the count guard**: one copy of `a` is one match. -/
theorem count_no_set_step (timing : SetStore.AskTiming) (after : Finset (Term atoms)) :
    ¬ SetStore.Step timing countProgram {a} after := by
  rintro ⟨candidate, nonempty, admitted, -⟩
  have yes := SetStore.admitted_after admitted
  obtain ⟨member, inside⟩ := List.exists_mem_of_ne_nil candidate.members nonempty
  have rule : member.rule = countTwo := member.member
  obtain ⟨⟨⟩, σ, solved⟩ := yes.2.2.1
  have holds := (yes.2.2.2 PUnit.unit σ solved member inside).1
    (Check.count (member.opening.applyTerm a) 2)
    (List.mem_map.mpr ⟨Check.count a 2, by
      show Check.count a 2 ∈ member.rule.body.checks
      rw [rule]
      exact List.mem_singleton_self _, rfl⟩)
  change (matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ
    (member.firing.row X (SetStore.represent ({a} : Finset (Term atoms))))
    (SetStore.represent ({a} : Finset (Term atoms))).present (member.opening.applyTerm a)).card = 2
    at holds
  have small : (matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ
      (member.firing.row X (SetStore.represent ({a} : Finset (Term atoms))))
      (SetStore.represent ({a} : Finset (Term atoms))).present (member.opening.applyTerm a)).card ≤
      (SetStore.represent ({a} : Finset (Term atoms))).present.card := by
    classical
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have single : (SetStore.represent ({a} : Finset (Term atoms))).present.card = 1 := by
    simp [SetStore.represent]
  omega

theorem countFiring_present : (countFiring.result X twoA).present = {0, 1, 2} := by decide

/-- **Counts separate the bag store from the set store.** At two occurrences of `a` the count guard
holds and the bag step adds `b` to the support, which is not a stutter; the set store holds one copy
of `a` and has no step from `{a}`. -/
theorem count_breaks_support (timing : SetStore.AskTiming) :
    Succ (step X ℕ E countProgram).toStep twoA (countFiring.result X twoA) ∧
      support (countFiring.result X twoA) ≠ support twoA ∧
      ∀ after, ¬ SetStore.Step timing countProgram {a} after := by
  have labels : ∀ o, (countFiring.result X twoA).label o = if o = 2 then b else a := by
    intro o
    change (if o = 2 then (Subst.id atoms).applyTerm b else (Subst.id atoms).applyTerm a) = _
    split <;> rfl
  have supportEq : support (countFiring.result X twoA) =
      (countFiring.result X twoA).present.image (countFiring.result X twoA).label :=
    support_of_constants (countFiring.result X twoA) (fun e inside => by
      rw [show (countFiring.result X twoA).knowledge = [(a, a)] from rfl, List.mem_singleton] at inside
      subst inside
      rfl)
    (fun o _ => by rw [labels]; split; exacts [b_ground, a_ground])
  refine ⟨⟨countFiring, countFiring_admitted, rfl⟩, fun same => ?_, count_no_set_step timing⟩
  have inside : b ∈ support (countFiring.result X twoA) := by
    rw [supportEq, countFiring_present]
    exact Finset.mem_image.mpr ⟨2, by decide, by rw [labels]; rfl⟩
  rw [same, twoA_support] at inside
  exact b_ne_a (Finset.mem_singleton.mp inside)

/-! ## Identities that run out -/

/-- One occurrence of `a`, under the only identity there is. -/
def onlyA : State (Terms (Term atoms)) Unit := ⟨PUnit.unit, [], {()}, fun _ => a⟩

theorem onlyA_stuck : ∀ s', ¬ Succ (step X Unit E growProgram).toStep onlyA s' := by
  rintro s' ⟨g, admitted, -⟩
  replace admitted : g.Admits X onlyA := admitted
  have rule : g.rule = grow := g.member
  have lengths : g.rule.body.produce.length = g.selection.made.length := admitted.1.2.2.2.2.2.1
  rw [rule] at lengths
  have positive : 0 < g.selection.made.length := by
    rw [← lengths]
    exact Nat.one_pos
  obtain ⟨o, inside⟩ := List.exists_mem_of_length_pos positive
  exact Finset.disjoint_left.mp admitted.2.1.fresh (List.mem_toFinset.mpr inside)
    (Finset.mem_singleton.mpr rfl)

/-- **Identities that run out.** With one occurrence identity, already used, no bag step exists, so
the state is completed, while its support is not closed: `completed_iff_closed` needs infinitely many
identities. -/
theorem identities_needed :
    Completed growProgram onlyA ∧
      ¬ SetStoreClosure.Closed (consequence (P := growProgram)) (support onlyA) := by
  have onlyA_support : support onlyA = {a} := by
    rw [support_of_constants onlyA (fun _ inside => by cases inside) fun _ _ => a_ground]
    exact Finset.image_singleton _ _
  let m : GroundMatch growProgram :=
    ⟨grow, rfl, grow_propagates, Subst.id atoms, fun _ inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact a_ground, fun _ _ inside => by cases inside⟩
  refine ⟨fun s' moved => absurd moved (onlyA_stuck s'), fun closed => ?_⟩
  have made := closed m (by
    intro v inside
    rw [(grow_instance m).1] at inside
    rw [onlyA_support]
    exact inside)
  rw [(grow_instance m).2, onlyA_support, Finset.singleton_subset_iff,
    Finset.mem_singleton] at made
  exact b_ne_a made

/-! ## Unknowns that run out -/

/-- Numerals as constants, and one unknown. -/
abbrev oneUnknown : LPSignature where
  constants := ℕ
  vars := Unit
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Empty
  functionArity := Empty.elim

/-- The one unknown. -/
def y : Term oneUnknown := .var ()

/-- The constant `n`. -/
def c (n : ℕ) : Term oneUnknown := .const n

/-- Read `y` equal to `1`, make `2`. -/
def first : Rule (Terms (Term oneUnknown)) := ⟨PUnit.unit, ⟨[], [y], [], [.equal y (c 1)], [c 2]⟩, []⟩

/-- Read `y` equal to `2`, make `3`. -/
def second : Rule (Terms (Term oneUnknown)) := ⟨PUnit.unit, ⟨[], [y], [], [.equal y (c 2)], [c 3]⟩, []⟩

def chain : Program (Terms (Term oneUnknown)) := {first, second}

theorem chain_pure : ∀ r ∈ chain, Propagates r := by
  intro r member
  rcases member with rfl | rfl
  · exact ⟨rfl, rfl, ⟨fun _ inside => ⟨y, c 1, List.mem_singleton.mp inside⟩, rfl⟩,
      by simp [first, varsIn, c, Term.freeVars], by simp [first, varsIn, checkTerms, c, Term.freeVars]⟩
  · exact ⟨rfl, rfl, ⟨fun _ inside => ⟨y, c 2, List.mem_singleton.mp inside⟩, rfl⟩,
      by simp [second, varsIn, c, Term.freeVars], by simp [second, varsIn, checkTerms, c, Term.freeVars]⟩

/-- One occurrence of `1`. -/
def seed : State (Terms (Term oneUnknown)) ℕ := ⟨PUnit.unit, [], {0}, fun _ => c 1⟩

def firstFiring : Firing ℕ (E (signature := oneUnknown)) chain PUnit.unit :=
  ⟨first, Or.inl rfl, PUnit.unit, Subst.id oneUnknown, ⟨[], [0], [1]⟩, []⟩

theorem firstFiring_admitted : firstFiring.Admits X seed := by
  have info : firstFiring.information X seed = [(y, c 1)] := rfl
  have fresh : firstFiring.Fresh X seed := by
    intro _ g h
    refine ⟨h, fun t mentioned => ?_, fun t _ => ?_⟩
    · obtain (known | known | ⟨o, _, rfl⟩) := mentioned
      · cases known
      · cases known
      · rfl
    · change h.applyTerm ((Subst.id oneUnknown).applyTerm t) = h.applyTerm t
      rw [Subst.applyTerm_id]
  refine ⟨⟨fresh, by decide, by decide, rfl, rfl, rfl, rfl⟩, by decide,
    ⟨PUnit.unit, fun _ => c 1, ?_⟩, ?_⟩
  · rw [info]
    intro e inside
    rw [List.mem_singleton] at inside
    subst inside
    rfl
  · intro b τ solved
    cases b
    refine ⟨fun check inside => ?_, fun _ inside => (by cases inside)⟩
    change check ∈ [Check.equal ((Subst.id oneUnknown).applyTerm y)
      ((Subst.id oneUnknown).applyTerm (c 1))] at inside
    rw [List.mem_singleton] at inside
    subst inside
    rw [info] at solved
    exact solved _ (List.mem_singleton_self _)

/-- The state after `first` fires: its knowledge equates the unknown with `1`. -/
def fired : State (Terms (Term oneUnknown)) ℕ := firstFiring.result X seed

theorem fired_knowledge : fired.knowledge = [(y, c 1)] := rfl

/-- **No rule of the program can be opened freshly once the state mentions the one unknown.** -/
theorem no_fresh_opening (g : Firing ℕ (E (signature := oneUnknown)) chain fired.frame) :
    ¬ g.Fresh X fired := by
  intro fresh
  have yRule : y ∈ g.rule.terms := by
    rcases g.member with rule | rule
    · rw [rule]
      simp [Rule.terms, first]
    · rw [rule]
      simp [Rule.terms, second]
  have mentioned : fired.Mentions y := Or.inl (by rw [fired_knowledge]; simp)
  cases opened : g.opening () with
  | var v =>
    obtain ⟨u, onState, onRule⟩ := fresh PUnit.unit (fun _ => c 0) (fun _ => c 5)
    have one : u () = c 0 := onState y mentioned
    have two : u.applyTerm (g.opening ()) = c 5 := onRule y yRule
    rw [opened] at two
    cases v
    have same : c 0 = c 5 := one.symm.trans two
    exact absurd (Term.const.inj same) (by decide)
  | const k =>
    obtain ⟨u, -, onRule⟩ := fresh PUnit.unit (fun _ => c 0) (fun _ => c (k + 1))
    have two : u.applyTerm (g.opening ()) = c (k + 1) := onRule y yRule
    rw [opened] at two
    exact absurd (Term.const.inj two) (Nat.ne_of_lt (Nat.lt_succ_self k))
  | app symbol _ => exact symbol.elim

/-- **Unknowns that run out.** With one unknown, the state that `first` reaches is mentioned by it, so
nothing fires there and the state is completed, while its support is not closed: `second` reads `2`
and makes `3`. `completed_iff_closed` needs infinitely many unknowns. -/
theorem unknowns_needed :
    Succ (step X ℕ E chain).toStep seed fired ∧ Settled fired ∧ Completed chain fired ∧
      ¬ SetStoreClosure.Closed (consequence (P := chain)) (support fired) := by
  have consistent : (FirstOrder.action oneUnknown).Consistent fired.knowledge := by
    refine ⟨fun _ => c 1, ?_⟩
    rw [fired_knowledge]
    intro e inside
    rw [List.mem_singleton] at inside
    subst inside
    rfl
  have labels : ∀ o, fired.label o = if o = 1 then c 2 else c 1 := by
    intro o
    change (if o = 1 then (Subst.id oneUnknown).applyTerm (c 2)
      else (Subst.id oneUnknown).applyTerm (c 1)) = _
    split <;> rfl
  have ground : ∀ o ∈ fired.present, (fired.label o).isGround := by
    intro o _
    rw [labels]
    split <;> trivial
  have supportEq : support fired = {c 1, c 2} := by
    rw [support_of_ground consistent ground, show fired.present = {0, 1} by decide,
      Finset.image_insert, Finset.image_singleton, labels, labels]
    rfl
  refine ⟨⟨firstFiring, firstFiring_admitted, rfl⟩, settled_of_ground consistent ground,
    fun s' ⟨g, admitted, _⟩ => absurd admitted.1.1 (no_fresh_opening g), fun closed => ?_⟩
  let toTwo : Subst oneUnknown := fun _ => c 2
  let m : GroundMatch chain :=
    ⟨second, Or.inr rfl, chain_pure second (Or.inr rfl), toTwo,
      fun _ inside => by
        obtain rfl := List.mem_singleton.mp inside
        trivial,
      fun _ _ inside => by
        obtain ⟨rfl, rfl⟩ := Check.equal.inj (List.mem_singleton.mp inside)
        rfl⟩
  have made := closed m (by
    intro v inside
    change v ∈ ([toTwo.applyTerm y]).toFinset at inside
    rw [List.mem_toFinset, List.mem_singleton] at inside
    rw [supportEq, inside]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have three : c 3 ∈ support fired := made (by
    change c 3 ∈ ([toTwo.applyTerm (c 3)]).toFinset
    exact List.mem_toFinset.mpr (List.mem_singleton.mpr rfl))
  rw [supportEq] at three
  simp only [Finset.mem_insert, Finset.mem_singleton] at three
  rcases three with same | same <;> exact absurd (Term.const.inj same) (by decide)

/-! ## Divergence -/

/-- **Divergence.** The bag store runs forever from one occurrence of `a`, every step a stutter,
while the set store has no step from `{a}`. -/
theorem again_diverges (timing : SetStore.AskTiming) :
    (∃ run : ℕ → State (Terms (Term atoms)) ℕ, run 0 = oneA ∧
      ∀ n, Succ (step X ℕ E againProgram).toStep (run n) (run (n + 1))) ∧
      ∀ after, ¬ SetStore.Step timing againProgram {a} after := by
  let m : GroundMatch againProgram :=
    ⟨again, rfl, again_propagates, Subst.id atoms, fun _ inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact a_ground, fun _ _ inside => by cases inside⟩
  have readA : (consequence m).read = {a} := by
    show ([a].map (Subst.id atoms).applyTerm).toFinset = {a}
    simp [Subst.applyTerm_id]
  constructor
  · exact diverges again_pure (Equiv.refl ℕ) oneA_settled m (by
      intro v inside
      rw [readA] at inside
      rw [oneA_support]
      exact inside)
  · apply closed_ground_terminal again_pure {a} (fun t inside => by
      rw [Finset.mem_singleton.mp inside]
      exact a_ground)
    intro other _
    have rule : other.rule = again := other.member
    change (other.rule.body.produce.map other.assignment.applyTerm).toFinset ⊆ {a}
    rw [rule]
    change ([other.assignment.applyTerm a]).toFinset ⊆ {a}
    rw [FirstOrder.ground_fixed _ a a_ground]
    intro v inside
    rw [List.mem_toFinset, List.mem_singleton] at inside
    rw [inside]
    exact Finset.mem_singleton_self a

#print axioms again_stutters
#print axioms copy_stutters
#print axioms grow_steps
#print axioms grow_completed
#print axioms twice_reads_one_occurrence
#print axioms count_breaks_support
#print axioms takeOne_stutters
#print axioms takeTwo_breaks_support
#print axioms no_support_simulation
#print axioms positive_does_not_suffice
#print axioms identities_needed
#print axioms unknowns_needed
#print axioms again_diverges

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Support.Controls
